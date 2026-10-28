-- Prove2me | solution 1 for IsCompact.exists_isMaxOn_not_mem_of_subset_interior
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:23.683365+00:00
-- url     : https://prove2.me/submissions/215a8e8d-85f9-431d-a38e-420d0b3db158

import Mathlib

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3927-3985

section
open MeasureTheory Matrix
open scoped ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {Kc : Set E} (hK : IsCompact Kc) (hne : Kc.Nonempty) {D : Set E}
    (hD : D ⊆ interior Kc) (ℓ : E →L[ℝ] ℝ) :
    ∃ x ∈ Kc, x ∉ D ∧ ∀ y ∈ Kc, ℓ y ≤ ℓ x := by
  classical
  obtain ⟨x₀, hx₀K, hmax⟩ := hK.exists_isMaxOn hne ℓ.continuous.continuousOn
  have hmax' : ∀ y ∈ Kc, ℓ y ≤ ℓ x₀ := fun y hy => hmax hy
  by_cases hx₀D : x₀ ∉ D
  · exact ⟨x₀, hx₀K, hx₀D, hmax'⟩
  push Not at hx₀D
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨d, hd, hℓd⟩ : ∃ d : E, d ≠ 0 ∧ 0 ≤ ℓ d := by
    by_cases h : 0 ≤ ℓ v
    · exact ⟨v, hv, h⟩
    · refine ⟨-v, neg_ne_zero.2 hv, ?_⟩
      rw [map_neg]; linarith
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  let T : Set ℝ := {t | 0 ≤ t ∧ x₀ + t • d ∈ Kc}
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hTsub : T ⊆ Set.Icc 0 ((R + ‖x₀‖) / ‖d‖) := by
    rintro t ⟨ht0, htK⟩
    refine ⟨ht0, ?_⟩
    rw [le_div_iff₀ hdpos]
    have h1 : ‖x₀ + t • d‖ ≤ R := by simpa using hR htK
    have h2 : ‖t • d‖ ≤ ‖x₀ + t • d‖ + ‖x₀‖ := by
      calc ‖t • d‖ = ‖(x₀ + t • d) - x₀‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x₀ + t • d‖ + ‖x₀‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg ht0] at h2
    linarith
  have hTclosed : IsClosed T := by
    refine isClosed_Ici.inter (hK.isClosed.preimage ?_)
    fun_prop
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have hTne : T.Nonempty := ⟨0, le_refl 0, by simpa using hx₀K⟩
  obtain ⟨t₁, ⟨ht₁0, ht₁K⟩, ht₁max⟩ := hTc.exists_isGreatest hTne
  refine ⟨x₀ + t₁ • d, ht₁K, fun hyD => ?_, fun y hy => ?_⟩
  · have hint := hD hyD
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨ε, hε, hball⟩ := hint
    have hδ : 0 < ε / (2 * ‖d‖) := by positivity
    have hmem : x₀ + (t₁ + ε / (2 * ‖d‖)) • d ∈ Kc := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_smul, ← add_assoc, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδ.le]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have := ht₁max ⟨by linarith, hmem⟩
    linarith
  · have := hmax' y hy
    rw [map_add, map_smul, smul_eq_mul]
    nlinarith

end
