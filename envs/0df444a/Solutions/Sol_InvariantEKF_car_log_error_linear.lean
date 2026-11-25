-- Prove2me | solution 1 for InvariantEKF.car_log_error_linear
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:52:19.155653+00:00
-- url     : https://prove2.me/submissions/02247b9a-b781-49f4-9fa6-903a222d11da

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

open InvariantEKF in
theorem solution (u ω θ x1 x2 θbar xbar1 xbar2 : ℝ → ℝ)
    (hθ : ∀ t, 0 ≤ t → HasDerivWithinAt θ (ω t) (Set.Ici 0) t)
    (hx1 : ∀ t, 0 ≤ t → HasDerivWithinAt x1 (Real.cos (θ t) * u t) (Set.Ici 0) t)
    (hx2 : ∀ t, 0 ≤ t → HasDerivWithinAt x2 (Real.sin (θ t) * u t) (Set.Ici 0) t)
    (hθbar : ∀ t, 0 ≤ t → HasDerivWithinAt θbar (ω t) (Set.Ici 0) t)
    (hxbar1 : ∀ t, 0 ≤ t → HasDerivWithinAt xbar1 (Real.cos (θbar t) * u t) (Set.Ici 0) t)
    (hxbar2 : ∀ t, 0 ≤ t → HasDerivWithinAt xbar2 (Real.sin (θbar t) * u t) (Set.Ici 0) t)
    (hdef : θ 0 - θbar 0 = 0 ∨ Real.cos (θ 0 - θbar 0) ≠ 1) :
    ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun s => carLogError (θ s) (x1 s) (x2 s) (θbar s) (xbar1 s) (xbar2 s))
        (carErrorMatrix (u t) (ω t) *ᵥ carLogError (θ t) (x1 t) (x2 t) (θbar t) (xbar1 t) (xbar2 t))
        (Set.Ici 0) t := by
  set s0 := θ 0 - θbar 0 with hs0
  -- the angle difference is constant
  have hD : ∀ t, 0 ≤ t → HasDerivWithinAt (fun r => θ r - θbar r) 0 (Set.Ici 0) t := fun t ht => by
    convert (hθ t ht).sub (hθbar t ht) using 1 <;> first | rfl | simp
  have hconst : ∀ t, 0 ≤ t → θ t - θbar t = s0 := by
    intro t ht
    have hcont : ContinuousOn (fun r => θ r - θbar r) (Set.Icc 0 t) := fun x hx =>
      ((hD x hx.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
    have := constant_of_has_deriv_right_zero hcont (fun x hx =>
      (hD x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) t ⟨ht, le_rfl⟩
    simpa [hs0] using this
  set c := carCoef s0 with hc
  clear_value s0 c
  have hc1 : c * (Real.cos s0 - 1) + s0 / 2 * Real.sin s0 = 0 ∧
      c * Real.sin s0 + s0 / 2 * (1 - Real.cos s0) = s0 := by
    by_cases h0 : s0 = 0
    · simp [hc, carCoef, h0]
    · have hcos : Real.cos s0 ≠ 1 := hdef.resolve_left h0
      have h1 : 1 - Real.cos s0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hcos)
      simp only [hc, carCoef, h0, if_false]
      constructor
      · field_simp; ring
      · field_simp
        linear_combination Real.sin_sq_add_cos_sq s0
  intro t ht
  have hst := hconst t ht
  set P : ℝ → ℝ := fun r => Real.cos (θbar r) * (x1 r - xbar1 r) + Real.sin (θbar r) * (x2 r - xbar2 r) with hP
  set Qf : ℝ → ℝ := fun r => -Real.sin (θbar r) * (x1 r - xbar1 r) + Real.cos (θbar r) * (x2 r - xbar2 r) with hQ
  have hcs : Real.cos (θ t) * Real.cos (θbar t) + Real.sin (θ t) * Real.sin (θbar t) = Real.cos s0 := by
    rw [← hst, Real.cos_sub]
  have hsn : Real.sin (θ t) * Real.cos (θbar t) - Real.cos (θ t) * Real.sin (θbar t) = Real.sin s0 := by
    rw [← hst, Real.sin_sub]
  have hPd : HasDerivWithinAt P (ω t * Qf t + u t * (Real.cos s0 - 1)) (Set.Ici 0) t := by
    have := (((hθbar t ht).cos).mul ((hx1 t ht).sub (hxbar1 t ht))).add
      (((hθbar t ht).sin).mul ((hx2 t ht).sub (hxbar2 t ht)))
    refine this.congr_deriv ?_
    simp only [hQ, Pi.sub_apply]
    rw [← hcs]
    have : Real.sin (θbar t) ^ 2 + Real.cos (θbar t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    linear_combination (-u t) * this
  have hQd : HasDerivWithinAt Qf (-(ω t) * P t + u t * Real.sin s0) (Set.Ici 0) t := by
    have := ((((hθbar t ht).sin).neg).mul ((hx1 t ht).sub (hxbar1 t ht))).add
      (((hθbar t ht).cos).mul ((hx2 t ht).sub (hxbar2 t ht)))
    refine this.congr_deriv ?_
    simp only [hP, Pi.sub_apply, Pi.neg_apply]
    rw [← hsn]
    ring
  have heq : ∀ r ∈ Set.Ici (0 : ℝ),
      carLogError (θ r) (x1 r) (x2 r) (θbar r) (xbar1 r) (xbar2 r) =
        ![s0, c * P r + s0 / 2 * Qf r, c * Qf r - s0 / 2 * P r] := by
    intro r hr
    simp only [carLogError, hconst r hr, hc, hP, hQ]
  rw [hasDerivWithinAt_pi]
  intro i
  have hcongr : ∀ (j : Fin 3), ∀ r ∈ Set.Ici (0 : ℝ),
      carLogError (θ r) (x1 r) (x2 r) (θbar r) (xbar1 r) (xbar2 r) j =
        (![s0, c * P r + s0 / 2 * Qf r, c * Qf r - s0 / 2 * P r] : Fin 3 → ℝ) j :=
    fun j r hr => by rw [heq r hr]
  have hxi : carLogError (θ t) (x1 t) (x2 t) (θbar t) (xbar1 t) (xbar2 t) =
      ![s0, c * P t + s0 / 2 * Qf t, c * Qf t - s0 / 2 * P t] := heq t ht
  rw [hxi]
  fin_cases i
  · refine (hasDerivWithinAt_const t _ s0).congr (fun r hr => hcongr 0 r hr) (hcongr 0 t ht) |>.congr_deriv ?_
    simp [carErrorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · have := ((hPd.const_mul c).add (hQd.const_mul (s0 / 2)))
    refine (this.congr (fun r hr => hcongr 1 r hr) (hcongr 1 t ht)).congr_deriv ?_
    simp [carErrorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (u t) * hc1.1
  · have := ((hQd.const_mul c).sub (hPd.const_mul (s0 / 2)))
    refine (this.congr (fun r hr => hcongr 2 r hr) (hcongr 2 t ht)).congr_deriv ?_
    simp [carErrorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (u t) * hc1.2
