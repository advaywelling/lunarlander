`default_nettype none
// Empty top module
module top (
  // I/O ports
  input  logic hz100, reset,
  input  logic [20:0] pb,
  output logic [7:0] left, right,
         ss7, ss6, ss5, ss4, ss3, ss2, ss1, ss0,
  output logic red, green, blue,
  // UART ports
  output logic [7:0] txdata,
  input  logic [7:0] rxdata,
  output logic txclk, rxclk,
  input  logic txready, rxready
);
  fa u1 (
  .a(pb[0]), 
  .b(pb[1]), 
  .ci(pb[2]), 
  .s(right[0]), 
  .co(right[1])
);
endmodule

module lunarlander #(
  parameter FUEL=16'h800,
  parameter ALTITUDE=16'h4500,
  parameter VELOCITY=16'h0,
  parameter THRUST=16'h5,
  parameter GRAVITY=16'h5
)(
  input logic hz100, reset,
  input logic [19:0] in,
  output logic [7:0] ss7, ss6, ss5, 
  output logic [7:0] ss3, ss2, ss1, ss0,
  output logic red, green
);

  logic [4:0] keyout;
  logic keyclk, crash, land, write_en, clk_hz;
  logic [15:0] thrust_n, alt_n, fuel_n, vel_n, alt, thrust, vel, fuel;
  logic [3:0] disp_ctrl;

  clock_psc clock(
	  .clk(hz100),
	  .rst(reset),
	  .lim(8'd24),
	  .hzX(clk_hz)
  );
  keysync key(
    .clk(hz100),
    .rst(reset),
    .keyin(in),
    .keyout(keyout),
    .keyclk(keyclk)
  );

  always_ff @(posedge keyclk) begin
    if (reset)
      thrust_n <= 16'h0;
    else if (~keyout[4])
      thrust_n <= {12'b0, keyout[3:0]};
  end

  assign disp_ctrl = {keyout == 5'd19, keyout == 5'd18, keyout == 5'd17, keyout == 5'd16}; 

  ll_control u1(
    .clk(clk_hz),
    .rst(reset),
    .alt(alt),
    .vel(vel),
    .crash(crash),
    .land(land),
    .wen(write_en)
  );

  ll_alu u2(
    .alt_n(alt_n),
    .vel_n(vel_n),
    .fuel_n(fuel_n),
    .thrust(thrust),
    .alt(alt),
    .vel(vel),
    .fuel(fuel)
  );

  ll_memory u3(
    .clk(clk_hz),
    .rst(reset),
    .alt_n(alt_n),
    .vel_n(vel_n),
    .fuel_n(fuel_n),
    .thrust_n(thrust_n),
    .alt(alt),
    .vel(vel),
    .fuel(fuel),
    .thrust(thrust),
	.wen(write_en)
  );

  ll_display u4(
    .clk(keyclk),
    .rst(reset),
    .disp_ctrl(disp_ctrl),
    .alt(alt),
    .vel(vel),
    .fuel(fuel),
    .thrust(thrust),
    .ss7(ss7),
    .ss6(ss6),
    .ss5(ss5),
    .ss3(ss3),
    .ss2(ss2),
    .ss1(ss1),
    .ss0(ss0),
    .red(red),
    .green(green),
	.crash(crash),
	.land(land)
  );

  endmodule

module clock_psc (
    input logic clk,      
    input logic rst,      
    input logic [7:0] lim, 
    output logic hzX       
);

    logic [7:0] ctr;       
    logic temp;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
        
            ctr <= 8'd0;
            temp <= 1'b0;
        end else if (lim == 8'd0) begin
            
            temp <= clk;
        end else if (ctr == lim) begin
            
            temp <= ~temp;
            ctr <= 8'd0;
        end else begin
            
            ctr <= ctr + 1;
        end
    end
    assign hzX = (lim == 8'd0) ? clk : temp;
endmodule

module keysync (
    input logic clk,
    input logic rst,
    input logic [19:0] keyin,
    output logic [4:0] keyout,
    output logic keyclk
);
	logic [1:0] delay;
	
	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			delay <= 2'b00;
		end else begin
			delay <= {delay[0], |keyin};
		end
	end
	assign keyclk = delay[1];
	assign keyout[0] = keyin[1] | keyin[3] | keyin[5] | keyin[7] | keyin[9] |
                    keyin[11] | keyin[13] | keyin[15] | keyin[17] | keyin[19];
	assign keyout[1] = keyin[2] | keyin[3] | keyin[6] | keyin[7] | keyin[10] |
                    keyin[11] | keyin[14] | keyin[15] | keyin[18] | keyin[19];
	assign keyout[2] = keyin[4] | keyin[5] | keyin[6] | keyin[7] | keyin[12] |
                    keyin[13] | keyin[14] | keyin[15];
	assign keyout[3] = keyin[8] | keyin[9] | keyin[10] | keyin[11] | keyin[12] |
                    keyin[13] | keyin[14] | keyin[15];
	assign keyout[4] = keyin[16] | keyin[17] | keyin[18] | keyin[19];

endmodule

module fa (
  input  logic a, b, ci,
  output logic s, co
);
  always_comb begin
    case ({a, b, ci})
      3'b000: begin s = 0; co = 0; end
      3'b001: begin s = 1; co = 0; end
      3'b010: begin s = 1; co = 0; end
      3'b011: begin s = 0; co = 1; end
      3'b100: begin s = 1; co = 0; end
      3'b101: begin s = 0; co = 1; end
      3'b110: begin s = 0; co = 1; end
      3'b111: begin s = 1; co = 1; end
      default: begin s = 0; co = 0; end
    endcase
  end
endmodule

module fa4 (
  input logic [3:0] a, b,
  input logic ci,
  output logic [3:0] s,
  output logic co
);
  logic c1, c2, c3;
  fa u1 (.a(a[0]), .b(b[0]), .ci(ci), .s(s[0]), .co(c1));
  fa u2 (.a(a[1]), .b(b[1]), .ci(c1), .s(s[1]), .co(c2));
  fa u3 (.a(a[2]), .b(b[2]), .ci(c2), .s(s[2]), .co(c3));
  fa u4 (.a(a[3]), .b(b[3]), .ci(c3), .s(s[3]), .co(co));
endmodule

module bcdadd1 (
  input  logic [3:0] a,      
  input  logic [3:0] b,      
  input  logic ci,     
  output logic [3:0] s,      
  output logic co      
);
  logic [3:0] bin_sum;       
  logic carry_out1, carry_out2;
  logic correction;
  fa4 i1 (
    .a(a),
    .b(b),
    .ci(ci),
    .s(bin_sum),
    .co(carry_out1)
  );
  assign correction = carry_out1 | (bin_sum > 4'd9);
  fa4 i2 (
    .a(bin_sum),
    .b({1'b0, correction, correction, 1'b0}),
    .ci(1'b0),
    .s(s),
    .co(carry_out2)
  ); 
  assign co = carry_out1 | carry_out2;

endmodule

module bcdadd4 (
  input  logic [15:0] a, b,
  input  logic ci,
  output logic [15:0] s,
  output logic co
);
  logic c1, c2, c3;
  bcdadd1 bcd0 (.a(a[3:0]), .b(b[3:0]), .ci(ci), .s(s[3:0]), .co(c1));
  bcdadd1 bcd1 (.a(a[7:4]), .b(b[7:4]), .ci(c1), .s(s[7:4]), .co(c2));
  bcdadd1 bcd2 (.a(a[11:8]), .b(b[11:8]), .ci(c2), .s(s[11:8]), .co(c3));
  bcdadd1 bcd3 (.a(a[15:12]), .b(b[15:12]), .ci(c3), .s(s[15:12]), .co(co));
endmodule

module bcd9comp1 (
  input  logic [3:0] in,
  output logic [3:0] out
);
  always_comb begin
    case (in)
      4'd0: out = 4'd9;
      4'd1: out = 4'd8;
      4'd2: out = 4'd7;
      4'd3: out = 4'd6;
      4'd4: out = 4'd5;
      4'd5: out = 4'd4;
      4'd6: out = 4'd3;
      4'd7: out = 4'd2;
      4'd8: out = 4'd1;
      4'd9: out = 4'd0;
      default: out = 4'bxxxx;
    endcase
  end
endmodule

module bcdaddsub4 (
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic op,
  output logic [15:0] s
);
  logic [3:0] b_comp[3:0];
  bcd9comp1 c1(.in(b[3:0]),   .out(b_comp[0]));
  bcd9comp1 c2(.in(b[7:4]),   .out(b_comp[1]));
  bcd9comp1 c3(.in(b[11:8]),  .out(b_comp[2]));
  bcd9comp1 c4(.in(b[15:12]), .out(b_comp[3]));
  logic [15:0] b_mux;
  assign b_mux = op ? {b_comp[3], b_comp[2], b_comp[1], b_comp[0]} : b;
  bcdadd4 adder (
    .a(a),
    .b(b_mux),
    .ci(op),
    .s(s),
    .co()
  );
endmodule

module ll_memory #(
    parameter ALTITUDE=16'h4500,
    parameter VELOCITY=16'h0000,
    parameter FUEL=16'h0800,
    parameter THRUST =16'h0005
)(
    input wire clk,
    input wire rst,
    input wire wen,
    input wire [15:0] alt_n,
    input wire [15:0] vel_n,
    input wire [15:0] fuel_n,
    input wire [15:0] thrust_n,
    output reg [15:0] alt,
    output reg [15:0] vel,
    output reg [15:0] fuel,
    output reg [15:0] thrust
);
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            alt    <= ALTITUDE;
            vel    <= VELOCITY;
            fuel   <= FUEL;
            thrust <= THRUST;
        end else if (wen) begin
            alt    <= alt_n;
            vel    <= vel_n;
            fuel   <= fuel_n;
            thrust <= thrust_n;
        end
    end
endmodule

module ll_alu #(
  parameter GRAVITY = 16'h5
) (
  input  logic [15:0] alt, vel, fuel, thrust,
  output logic [15:0] alt_n, vel_n, fuel_n
);

  logic [15:0] alt_c, vel_c, fuel_c;
  logic [15:0] grav, thrust_n;
  logic has_fuel;

  bcdaddsub4 f1 (
    .a(alt),
    .b(vel),
    .op(1'b0),
    .s(alt_c)
  );
  assign thrust_n = (fuel == 16'h0 ? 16'h0 : thrust);
  bcdaddsub4 f2 (
    .a(vel),
    .b(GRAVITY),
    .op(1'b1),
    .s(grav)
  );

  bcdaddsub4 f3 (
    .a(grav),
    .b(thrust_n),
    .op(1'b0),
    .s(vel_c)
  );

  bcdaddsub4 f4 (
    .a(fuel),
    .b(thrust),
    .op(1'b1),
    .s(fuel_c)
  );

  always_comb begin
    alt_n = (alt_c[15:12] == 4'h9 || alt_c == 16'h0) ? 16'h0 : alt_c;
    vel_n = (alt_c[15:12] == 4'h9 || alt_c == 16'h0) ? 16'h0 : vel_c;
    fuel_n = (fuel_c[15:12] == 4'h9) ? 16'h0 : fuel_c;
  end
endmodule

module ll_control (
    input logic clk,
    input logic rst,
    input logic [15:0] alt,
    input logic [15:0] vel,
    output logic land,
    output logic crash,
    output logic wen
);
    logic [15:0] alt_c;
    logic land_n, crash_n, wen_n;

    bcdaddsub4 sum (
        .a(alt),
        .b(vel),
        .op(1'b0),
        .s(alt_c)
    );

	always_comb begin
    land_n = (alt_c[15:12] == 4'h9 || alt_c == 16'h0000) && (vel >= 16'h996A);
    crash_n = (alt_c[15:12] == 4'h9 || alt_c == 16'h0000) && (vel < 16'h996A);
    wen_n = ~(alt_c[15:12] == 4'h9 || alt_c == 16'h0000);
	end


    always @(posedge clk or posedge rst) begin
        if (rst) begin
            land <= 1'b0;
            crash <= 1'b0;
            wen <= 1'b0;
        end else begin
            land <= land_n;
            crash <= crash_n;
            wen <= wen_n;
        end
    end
endmodule

module ssdec(
    input [3:0] in,      
    input enable,       
    output [6:0] out     
);
    assign out = (enable) ? (
        (in == 4'b0000) ? 7'b0111111 :
        (in == 4'b0001) ? 7'b0000110 : 
        (in == 4'b0010) ? 7'b1011011 : 
        (in == 4'b0011) ? 7'b1001111 : 
        (in == 4'b0100) ? 7'b1100110 : 
        (in == 4'b0101) ? 7'b1101101 : 
        (in == 4'b0110) ? 7'b1111101 : 
        (in == 4'b0111) ? 7'b0000111 : 
        (in == 4'b1000) ? 7'b1111111 : 
        (in == 4'b1001) ? 7'b1100111 : 
        (in == 4'b1010) ? 7'b1110111 : 
        (in == 4'b1011) ? 7'b1111100 : 
        (in == 4'b1100) ? 7'b0111001 : 
        (in == 4'b1101) ? 7'b1011110 : 
        (in == 4'b1110) ? 7'b1111001 : 
        (in == 4'b1111) ? 7'b1110001 : 
        7'b0000000) : 7'b0000000; 
endmodule

module ll_display (
    input logic clk,
    input logic rst,
    input logic land,
    input logic crash,
    input logic [3:0] disp_ctrl,
    input logic [15:0] alt, vel, fuel, thrust,
    output logic [7:0] ss7, ss6, ss5, ss3, ss2, ss1, ss0,
    output logic red,
    output logic green
);

    logic [3:0] display_mode;
    logic [15:0] display_val, abs_val;
    logic neg;

    localparam [23:0] ALT = 24'b01110111_00111000_01111000;
    localparam [23:0] VEL = 24'b00111110_01111001_00111000;
    localparam [23:0] GAS = 24'b01101111_01110111_01101101;
    localparam [23:0] THR = 24'b01111000_01110110_01010000;

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            display_mode <= 4'b1000;
        else
            display_mode <= (|disp_ctrl) ? disp_ctrl : display_mode;
    end

    always_comb begin
        case (display_mode)
            4'b1000: {ss7, ss6, ss5, display_val, neg} = {ALT, alt, 1'b0};
            4'b0100: {ss7, ss6, ss5, display_val, neg} = {VEL, vel, vel[15]};
            4'b0010: {ss7, ss6, ss5, display_val, neg} = {GAS, fuel, 1'b0};
            4'b0001: {ss7, ss6, ss5, display_val, neg} = {THR, thrust, 1'b0};
            default: {ss7, ss6, ss5, display_val, neg} = {ALT, alt, 1'b0};
        endcase
    end

    bcdaddsub4 u1 (
        .a(16'h0),
        .b(display_val),
        .op(neg),
        .s(abs_val)
    );
	logic ssd3;
	logic [6:0] temp_ssd3;
	ssdec d3 (
        .in(abs_val[15:12]),
        .enable(ssd3),
        .out(temp_ssd3)
    ); 
	always_comb begin
    	ssd3 = |abs_val[15:12];
    	ss3 = neg ? 8'b01000000 : {1'b0, temp_ssd3};
	end
    ssdec d2 (
        .in(abs_val[11:8]),
        .enable(abs_val[15:8] != 8'h00),
        .out(ss2[6:0])
    );
    ssdec d1 (
        .in(abs_val[7:4]),
        .enable(abs_val[15:4] != 12'h000),
        .out(ss1[6:0])
    );
    ssdec d0 (
        .in(abs_val[3:0]),
        .enable(1'b1),
        .out(ss0[6:0])
    );
	//assign ss3[7] = neg ? 1'b1 : 1'b0;
    assign {ss2[7], ss1[7], ss0[7]} = 3'b000;
    assign red = crash;
    assign green = land;

endmodule
