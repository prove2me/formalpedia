-- Prove2me | solution 1 for Helfgott.rankin_single_prime_factor_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:19:31.83983+00:00
-- url     : https://prove2.me/submissions/4b2634ea-f2db-40bc-ae01-53fe9cdf7ed0

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Helfgott

theorem rankin_single_euler_factor_upper (x y : ℝ) (hx : 0<x) (hxy : x≤y)
    (hy : y<1) (hysq : y^2≤x) :
    1+x*y/((1+x)*(1-y))≤(1-x^3)/((1-x*y)*(1-x*y^2)) := by
  have hy0 : 0≤y := hx.le.trans hxy
  have hx1 : x<1 := hxy.trans_lt hy
  have hxylt : x*y<x := by simpa only [mul_one] using mul_lt_mul_of_pos_left hy hx
  have hxy1 : x*y<1 := hxylt.trans hx1
  have hy2 : y^2<1 := by nlinarith
  have hxysq1 : x*y^2<1 := (show x*y^2<x by simpa only [mul_one] using mul_lt_mul_of_pos_left hy2 hx).trans hx1
  have hden1 : 0<(1+x)*(1-y) := mul_pos (by linarith) (by linarith)
  have hden2 : 0<(1-x*y)*(1-x*y^2) := mul_pos (by linarith) (by linarith)
  have hfactor : (1+x-y)*(1-x*y)*(1-x*y^2)-(1+x)*(1-y)*(1-x^3)=
      (x-y)*(y^2-x)*(x*y-x-1)*x := by ring
  have hneg : x*y-x-1≤0 := by nlinarith
  have hprod : (x-y)*(y^2-x)*(x*y-x-1)*x≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hneg) hx.le
  have he : 1+x*y/((1+x)*(1-y))=(1+x-y)/((1+x)*(1-y)) := by
    field_simp [ne_of_gt (by linarith : (0:ℝ)<1+x),ne_of_gt (by linarith : (0:ℝ)<1-y)] <;> ring
  rw [he]
  apply (div_le_div_iff₀ hden1 hden2).mpr
  nlinarith [hfactor,hprod]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Real
namespace Helfgott

theorem rankin_single_prime_factor_upper_complete (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := by
  have hp0 : 0<p := by linarith
  have hx : 0<p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ)≤p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2≤p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := rankin_single_euler_factor_upper (p^(-1:ℝ)) (p^(-s)) hx hxy hy hysq
  have he1 : p^(-1:ℝ)*p^(-s)=p^(-s-1) := by
    rw [←Real.rpow_add hp0]
    congr 1
    ring
  have he2 : p^(-1:ℝ)*(p^(-s))^2=p^(-2*s-1) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2,←Real.rpow_add hp0]
    congr 1
    ring
  have he3 : (p^(-1:ℝ))^3=p^(-3:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 3]
    norm_num
  simpa only [he1,he2,he3] using h

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := Helfgott.rankin_single_prime_factor_upper_complete p s hp hs0 hs1

#print axioms solution
