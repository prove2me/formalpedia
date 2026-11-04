-- Prove2me | solution 1 for Grothendieck.integral_sqrt_inv_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:24:11.007549+00:00
-- url     : https://prove2.me/submissions/44aa689f-7013-4414-ad2c-4d80812f48d6

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The one-dimensional substitution `s = u²/2` in density form.** For a measurable `f`,
`∫₀^∞ f(s)·(√(2s))⁻¹ ds = ∫₀^∞ f(u²/2) du`. -/
theorem integral_sqrt_inv_mul_eq_proof {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ s in Set.Ioi (0:ℝ), (Real.sqrt (2 * s))⁻¹ * f s)
      = ∫ u in Set.Ioi (0:ℝ), f (u ^ 2 / 2) := by
  have himg : (fun u : ℝ => u ^ 2 / 2) '' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : (0:ℝ) < u := hu
      show (0:ℝ) < u ^ 2 / 2
      positivity
    · intro hs
      have hs0 : (0:ℝ) < s := hs
      refine ⟨Real.sqrt (2 * s), ?_, ?_⟩
      · show (0:ℝ) < Real.sqrt (2 * s)
        positivity
      · show Real.sqrt (2 * s) ^ 2 / 2 = s
        rw [Real.sq_sqrt (by positivity)]
        ring
  have hinj : Set.InjOn (fun u : ℝ => u ^ 2 / 2) (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    simp only at hab
    have : a ^ 2 = b ^ 2 := by linarith
    nlinarith [ha0, hb0, this]
  conv_lhs => rw [← himg]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f := fun u : ℝ => u ^ 2 / 2) (f' := fun u : ℝ => u)
    (fun u _ => ?_) hinj]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have habs : |u| = u := abs_of_pos hu0
    have hsq : Real.sqrt (2 * (u ^ 2 / 2)) = u := by
      rw [show 2 * (u ^ 2 / 2) = u ^ 2 by ring, Real.sqrt_sq hu0.le]
    simp only [smul_eq_mul, habs, hsq]
    field_simp
  · -- derivative of `u ↦ u²/2` is `u`
    have hd : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
      have h := (hasDerivAt_pow 2 u).div_const 2
      refine HasDerivAt.congr_deriv h ?_
      ring
    exact hd.hasDerivWithinAt

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ s in Set.Ioi (0:ℝ), (Real.sqrt (2 * s))⁻¹ * f s)
      = ∫ u in Set.Ioi (0:ℝ), f (u ^ 2 / 2) :=
  integral_sqrt_inv_mul_eq_proof hf
