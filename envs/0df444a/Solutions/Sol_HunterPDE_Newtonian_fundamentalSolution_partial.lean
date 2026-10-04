-- Prove2me | solution 1 for HunterPDE.Newtonian.fundamentalSolution_partial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:28:36.369679+00:00
-- url     : https://prove2.me/submissions/76c61e43-7af1-4c99-9fb7-756d7e700e57

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv

set_option autoImplicit false

namespace P42aa9de9

/-- Derivative of the Euclidean norm away from `0`, as `D` with `D (single i 1) = x i / ‖x‖`. -/
theorem norm_hasFDerivAt {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    ∃ D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, HasFDerivAt (fun y => ‖y‖) D x ∧
      ∀ i : Fin n, D (EuclideanSpace.single i 1) = x i / ‖x‖ := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hne : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  refine ⟨(1 / (2 * √(‖x‖ ^ 2))) • (2 : ℕ) • innerSL ℝ x, ?_, ?_⟩
  · refine h2.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y => by simp [Real.sqrt_sq (norm_nonneg y)]
  · intro i
    simp [Real.sqrt_sq (norm_nonneg x), EuclideanSpace.inner_single_right]
    field_simp

end P42aa9de9

open HunterPDE.Newtonian ContDiff in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ContDiffOn ℝ ∞ (fundamentalSolution n) {0}ᶜ ∧
    ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → ∀ i : Fin n,
      partialDeriv (fundamentalSolution n) i x =
        -(1 / ((n : ℝ) * unitBallVolume n)) * (1 / ‖x‖ ^ (n - 1)) * (x i / ‖x‖) := by
  by_cases h2 : n = 2
  · subst h2
    have hF : fundamentalSolution 2 = fun y => -(1 / (2 * Real.pi)) * Real.log ‖y‖ := by
      funext y; simp [fundamentalSolution]
    have hV : unitBallVolume 2 = Real.pi := by
      simp [unitBallVolume, Real.pi_pos.le]
    rw [hF, hV]
    refine ⟨fun x hx => ?_, fun x hx i => ?_⟩
    · have hx' : x ≠ 0 := hx
      have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
      exact (contDiffAt_const.mul ((contDiffAt_norm ℝ hx').log hne)).contDiffWithinAt
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨D, hD, hDi⟩ := P42aa9de9.norm_hasFDerivAt x hx
      have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => -(1 / (2 * Real.pi)) * Real.log ‖y‖)
          ((-(1 / (2 * Real.pi))) • (‖x‖⁻¹ • D)) x :=
        ((Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt x hD).const_mul (-(1 / (2 * Real.pi)))
      unfold partialDeriv
      rw [hL.fderiv]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, hDi]
      push_cast
      field_simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have e1 : k + 3 - 2 = k + 1 := by omega
    have e2 : k + 3 - 1 = k + 2 := by omega
    have hF : fundamentalSolution (k + 3) = fun y =>
        1 / (((k + 3 : ℕ) : ℝ) * (((k + 3 : ℕ) : ℝ) - 2) * unitBallVolume (k + 3)) *
          (‖y‖ ^ (k + 1))⁻¹ := by
      funext y; simp [fundamentalSolution, e1]
    rw [hF, e2]
    refine ⟨fun x hx => ?_, fun x hx i => ?_⟩
    · have hx' : x ≠ 0 := hx
      have hne : ‖x‖ ^ (k + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx')
      exact (contDiffAt_const.mul (((contDiffAt_norm ℝ hx').pow (k + 1)).inv hne)).contDiffWithinAt
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨D, hD, hDi⟩ := P42aa9de9.norm_hasFDerivAt x hx
      have hg : HasDerivAt (fun t : ℝ => (t ^ (k + 1))⁻¹)
          (-(((k + 1 : ℕ) : ℝ) * ‖x‖ ^ (k + 1 - 1)) / (‖x‖ ^ (k + 1)) ^ 2) ‖x‖ := by
        exact (hasDerivAt_pow (k + 1) ‖x‖).inv (pow_ne_zero _ hpos.ne')
      have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (k + 3)) =>
          1 / (((k + 3 : ℕ) : ℝ) * (((k + 3 : ℕ) : ℝ) - 2) * unitBallVolume (k + 3)) *
            (‖y‖ ^ (k + 1))⁻¹)
          ((1 / (((k + 3 : ℕ) : ℝ) * (((k + 3 : ℕ) : ℝ) - 2) * unitBallVolume (k + 3))) •
            ((-(((k + 1 : ℕ) : ℝ) * ‖x‖ ^ (k + 1 - 1)) / (‖x‖ ^ (k + 1)) ^ 2) • D)) x :=
        (hg.comp_hasFDerivAt x hD).const_mul _
      unfold partialDeriv
      rw [hL.fderiv]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, hDi]
      push_cast
      by_cases hV : unitBallVolume (k + 3) = 0
      · simp [hV]
      have hk : (k : ℝ) + 3 - 2 = k + 1 := by ring
      rw [hk]
      field_simp
      ring
