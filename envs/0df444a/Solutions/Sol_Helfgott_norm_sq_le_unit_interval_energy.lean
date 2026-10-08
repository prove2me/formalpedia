-- Prove2me | solution 1 for Helfgott.norm_sq_le_unit_interval_energy
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T00:39:55.995323+00:00
-- url     : https://prove2.me/submissions/e27ab3b6-a5b8-4861-86cd-cbddc2a2cf68

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Complex
open scoped ComplexInnerProductSpace

namespace Helfgott

theorem norm_sq_le_unit_interval_energy (f f' : ℝ → ℂ)
    (hf : ∀ u,HasDerivAt f (f' u) u) (hc' : Continuous f')
    (a x : ℝ) (hx : x ∈ Icc a (a+1)) :
    ‖f x‖^2≤2*(∫ u in a..a+1,‖f u‖^2)+(∫ u in a..a+1,‖f' u‖^2) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun u => (hf u).continuousAt)
  let G : ℝ → ℝ := fun u => ‖f u‖^2
  let D : ℝ → ℝ := fun u => 2*inner ℝ (f u) (f' u)
  let B : ℝ → ℝ := fun u => ‖f u‖^2+‖f' u‖^2
  have hcG : Continuous G := by dsimp [G]; fun_prop
  have hcD : Continuous D := by dsimp [D]; fun_prop
  have hcB : Continuous B := by dsimp [B]; fun_prop
  have hdG (u : ℝ) : HasDerivAt G (D u) u := (hf u).norm_sq
  have hDB (u : ℝ) : ‖D u‖≤B u := by
    dsimp [D,B]
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have hi := abs_real_inner_le_norm (f u) (f' u)
    change |(f' u*(starRingEnd ℂ) (f u)).re|≤‖f u‖*‖f' u‖ at hi
    nlinarith [sq_nonneg (‖f u‖-‖f' u‖)]
  have hBi : IntervalIntegrable B volume a (a+1) := hcB.intervalIntegrable a (a+1)
  have hB0 : ∀ u,0≤B u := by intro u; dsimp [B]; positivity
  have hpoint (y : ℝ) (hy : y ∈ Icc a (a+1)) :
      G x≤G y+(∫ u in a..a+1,B u) := by
    by_cases hxy : y≤x
    · have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hdG u) (hcD.intervalIntegrable y x)
      have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := D) hxy
      have hm := intervalIntegral.integral_mono_on (μ := volume) hxy
        ((hcD.norm).intervalIntegrable y x) (hcB.intervalIntegrable y x)
        (fun u hu => hDB u)
      have hs := intervalIntegral.integral_mono_interval hy.1 hxy hx.2
        (ae_of_all _ hB0) hBi
      rw [he,Real.norm_eq_abs] at hn
      have hh := le_abs_self (G x-G y)
      linarith
    · have hyx : x≤y := le_of_lt (lt_of_not_ge hxy)
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hdG u) (hcD.intervalIntegrable x y)
      have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := D) hyx
      have hm := intervalIntegral.integral_mono_on (μ := volume) hyx
        ((hcD.norm).intervalIntegrable x y) (hcB.intervalIntegrable x y)
        (fun u hu => hDB u)
      have hs := intervalIntegral.integral_mono_interval hx.1 hyx hy.2
        (ae_of_all _ hB0) hBi
      rw [he,Real.norm_eq_abs] at hn
      have hh := neg_le_abs (G y-G x)
      linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) (show a≤a+1 by linarith)
    (intervalIntegrable_const (c := G x))
    ((hcG.add continuous_const).intervalIntegrable a (a+1)) hpoint
  change (∫ _ in a..a+1,G x)≤
    (∫ u in a..a+1,G u+(∫ v in a..a+1,B v)) at hi
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    (hcG.intervalIntegrable a (a+1)) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [add_sub_cancel_left,one_smul] at hi
  have hBe : (∫ u in a..a+1,B u)=
      (∫ u in a..a+1,‖f u‖^2)+(∫ u in a..a+1,‖f' u‖^2) := by
    dsimp [B]
    exact intervalIntegral.integral_add
      ((hc.norm.pow 2).intervalIntegrable a (a+1))
      ((hc'.norm.pow 2).intervalIntegrable a (a+1))
  rw [hBe] at hi
  change ‖f x‖^2≤_ at hi
  linarith

end Helfgott
end

open Helfgott MeasureTheory Set Complex

theorem solution (f f' : ℝ → ℂ)
    (hf : ∀ u,HasDerivAt f (f' u) u) (hc' : Continuous f')
    (a x : ℝ) (hx : x ∈ Icc a (a+1)) :
    ‖f x‖^2≤2*(∫ u in a..a+1,‖f u‖^2)+(∫ u in a..a+1,‖f' u‖^2) := Helfgott.norm_sq_le_unit_interval_energy f f' hf hc' a x hx

#print axioms solution
