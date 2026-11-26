-- Prove2me | solution 1 for LogLogJam.Supplement.fixed_angle_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:21:10.884801+00:00
-- url     : https://prove2.me/submissions/01624c3a-91a0-4b26-b562-a9ec4b64d527

import Theorems.Thm_LogLogJam_Supplement_canonical_phase_born_law
import Theorems.Thm_LogLogJam_Supplement_nonadaptive_transcript_product
import Theorems.Thm_LogLogJam_Supplement_phase_location_from_samples
open MeasureTheory BosonicLearn LogLogJam LogLogJam.Supplement
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

private theorem squeezedDet (l a b : ℝ) (hl : l ≠ 0) :
    (Vsq l a + Vsq l b).det = 4 + (l-l⁻¹)^2 * Real.sin (a-b)^2 := by
  simp [Vsq, rot, Matrix.det_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, Real.sin_sub]
  linear_combination
    (l*l⁻¹ * (Real.sin a^2 + 2*Real.sin b^2 + Real.cos a^2 + 2*Real.cos b^2 + 1)) *
      Real.sin_sq_add_cos_sq a +
    (l*l⁻¹ * (Real.sin b^2 + Real.cos b^2 + 3)) * Real.sin_sq_add_cos_sq b +
    4 * (mul_inv_cancel₀ hl)

private theorem trDist_bound (r a b : ℝ) (hr : 0 ≤ r) :
    trDist (Real.exp (2*r)) a b ≤ Real.sinh (2*r) * |Real.sin (a-b)| := by
  let s := Real.sinh (2*r) * |Real.sin (a-b)|
  have hs : 0 ≤ s := mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (abs_nonneg _)
  have hu : (Real.exp (2*r) - (Real.exp (2*r))⁻¹)^2 * Real.sin (a-b)^2 = 4*s^2 := by
    dsimp [s]
    rw [Real.sinh_eq, Real.exp_neg, mul_pow, sq_abs]; ring
  rw [trDist, squeezedDet _ _ _ (Real.exp_pos _).ne', hu]
  let z := Real.sqrt (4+4*s^2)
  have hz : z^2 = 4+4*s^2 := Real.sq_sqrt (by positivity)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : 2 ≤ z := by nlinarith [sq_nonneg s]
  have hzu : z ≤ 2+2*s^2 := by nlinarith [sq_nonneg (s^2),sq_nonneg s]
  apply (Real.sqrt_le_left hs).mpr
  change 1 - 2 / z ≤ s^2
  have hh : (1-s^2)*z ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_right hz2 (sq_nonneg s)]
  linarith [(le_div_iff₀ (show 0 < z by linarith)).mpr hh]

theorem solution :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∀ S : BosonicLearn.AdaptiveScheme 1 m ℝ, phaseCountReadouts S →
    ∃ angle : (Fin m → ℝ) → ℝ, Measurable angle ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
        BosonicLearn.transcriptLaw S ρ.coefficients
          {x | η < LogLogJam.trDist (Real.exp (2 * r)) θ (angle x)} ≤ ENNReal.ofReal δ := by
  obtain ⟨C,hC,h⟩ := phase_location_from_samples
  refine ⟨C,hC,?_⟩
  intro η δ hη hη' hδ hδ' m hm S hS
  obtain ⟨angle,ha,hdep,hprob⟩ := h η δ hη hη' hδ hδ' m hm
  refine ⟨angle,ha,hdep,?_⟩
  intro ρ r θ hρ
  let μ := fun i : Fin m => (S.povm i (fun _ => default)).law ρ.coefficients
  have hpr (i : Fin m) : IsProbabilityMeasure (μ i) := (S.povm i _).law_prob _ ρ.density
  have h := hprob r θ hρ.1 μ hpr (fun i hi B hB =>
    canonical_phase_born_law (S.povm i _) (hS.2.1 i hi _) ρ r θ hρ B hB)
  rw [nonadaptive_transcript_product S ρ hS.1]
  refine le_trans (measure_mono ?_) h
  intro x hx
  exact lt_of_lt_of_le hx (trDist_bound r θ (angle x) hρ.1)
