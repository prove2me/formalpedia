-- Prove2me | solution 1 for MinRankRecovery.RandomRIP.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:19:13.374858+00:00
-- url     : https://prove2.me/submissions/28b76895-98db-4eec-8d04-3054fa1006d9

import Mathlib
import Definitions.Def_MinRankRecovery_RandomRIP_SubspaceDist

open MinRankRecovery.RandomRIP in
theorem solution {ι : Type} [Fintype ι] {p d : ℕ}
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin p))
    (U₁ U₂ : Submodule ℝ (EuclideanSpace ℝ ι))
    (hU₁ : Module.finrank ℝ U₁ = d) (hU₂ : Module.finrank ℝ U₂ = d)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hiso : ∀ X ∈ U₁, (1 - δ) * ‖X‖ ≤ ‖A X‖ ∧ ‖A X‖ ≤ (1 + δ) * ‖X‖) :
    ∀ Y ∈ U₂,
      (1 - (δ + (1 + ‖A‖) * projDist U₁ U₂)) * ‖Y‖ ≤ ‖A Y‖ ∧
        ‖A Y‖ ≤ (1 + (δ + (1 + ‖A‖) * projDist U₁ U₂)) * ‖Y‖ := by
  intro Y hY
  have hε0 : 0 ≤ projDist U₁ U₂ := norm_nonneg _
  set ε := projDist U₁ U₂ with hε
  set X := U₁.starProjection Y with hXdef
  have hX : X ∈ U₁ := Submodule.starProjection_apply_mem U₁ Y
  have hXY : ‖X‖ ≤ ‖Y‖ := U₁.norm_starProjection_apply_le Y
  have hdiff : ‖Y - X‖ ≤ ε * ‖Y‖ := by
    have e : Y - X = -((U₁.starProjection - U₂.starProjection) Y) := by
      rw [ContinuousLinearMap.sub_apply, Submodule.starProjection_eq_self_iff.mpr hY]
      abel
    rw [e, norm_neg]
    exact ContinuousLinearMap.le_opNorm _ _
  have hAd : ‖A (Y - X)‖ ≤ ‖A‖ * (ε * ‖Y‖) :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _))
  have h1 : ‖A Y‖ ≤ ‖A X‖ + ‖A (Y - X)‖ := by
    have : A Y = A X + A (Y - X) := by rw [map_sub]; abel
    rw [this]; exact norm_add_le _ _
  have h2 : ‖A X‖ ≤ ‖A Y‖ + ‖A (Y - X)‖ := by
    have : A X = A Y - A (Y - X) := by rw [map_sub]; abel
    rw [this]; exact norm_sub_le _ _
  have h3 : ‖Y‖ ≤ ‖X‖ + ‖Y - X‖ := by
    have : Y = X + (Y - X) := by abel
    calc ‖Y‖ = ‖X + (Y - X)‖ := by rw [← this]
      _ ≤ _ := norm_add_le _ _
  obtain ⟨hlo, hhi⟩ := hiso X hX
  have hY0 := norm_nonneg Y
  have hA0 := norm_nonneg A
  have k1 : 0 ≤ (1 - δ) * (‖X‖ - ‖Y‖ + ε * ‖Y‖) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ δ * ε * ‖Y‖ := by positivity
  have k3 : (1 + δ) * ‖X‖ ≤ (1 + δ) * ‖Y‖ := mul_le_mul_of_nonneg_left hXY (by linarith)
  have k4 : 0 ≤ ε * ‖Y‖ := by positivity
  constructor
  · nlinarith
  · nlinarith
