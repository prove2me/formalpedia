-- Prove2me | solution 1 for GlobalTheory.posDef_quad_margin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:11.562797+00:00
-- url     : https://prove2.me/submissions/e56260a2-5b9e-49bb-be9b-eb18394f658e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosDefQuadMargin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma quad_smul {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (a : ℝ) (c : ι → ℝ) :
    ∑ i, ∑ j, (a • c) i * (a • c) j * M i j = a ^ 2 * ∑ i, ∑ j, c i * c j * M i j := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring
private lemma quad_err {ι : Type} [Fintype ι] (E : ι → ι → ℝ) (η : ℝ) (_hη : 0 ≤ η)
    (hE : ∀ i j, |E i j| ≤ η) (c : ι → ℝ) :
    |∑ i, ∑ j, c i * c j * E i j| ≤ (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
  have hc : ∀ i, |c i| ≤ ‖c‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm c i
  calc |∑ i, ∑ j, c i * c j * E i j|
      ≤ ∑ i, ∑ j, |c i * c j * E i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖c‖ ^ 2 * η := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, sq]
        have h1 := hc i; have h2 := hc j; have h3 := hE i j
        have := abs_nonneg (c i); have := abs_nonneg (c j); have := abs_nonneg (E i j)
        have := norm_nonneg c
        calc |c i| * |c j| * |E i j| ≤ ‖c‖ * ‖c‖ * |E i j| := by gcongr
          _ ≤ ‖c‖ * ‖c‖ * η := by gcongr
    _ = (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) →
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun E _ c hc => absurd (Subsingleton.elim c 0) hc⟩
  set q : (ι → ℝ) → ℝ := fun c => ∑ i, ∑ j, c i * c j * M i j with hq
  have hcont : Continuous q := by
    simp only [hq]; fun_prop
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).mpr zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl; simp at hc₀
  set μ := q c₀ with hμ
  have hμpos : 0 < μ := hM c₀ hc₀ne
  have hlow : ∀ c : ι → ℝ, c ≠ 0 → μ * ‖c‖ ^ 2 ≤ q c := by
    intro c hc
    have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
    have h1 : μ ≤ q (‖c‖⁻¹ • c) := hmin hmem
    have h2 : q (‖c‖⁻¹ • c) = (‖c‖⁻¹) ^ 2 * q c := quad_smul M _ c
    rw [h2] at h1
    have h3 : (‖c‖⁻¹) ^ 2 * ‖c‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    calc μ * ‖c‖ ^ 2 ≤ ((‖c‖⁻¹) ^ 2 * q c) * ‖c‖ ^ 2 := by gcongr
      _ = q c := by rw [mul_comm ((‖c‖⁻¹) ^ 2), mul_assoc, h3, mul_one]
  set K : ℝ := (Fintype.card ι : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  refine ⟨μ / (2 * K + 1), div_pos hμpos (by linarith), ?_⟩
  intro E hE c hc
  have hη0 : 0 ≤ μ / (2 * K + 1) := (div_pos hμpos (by linarith)).le
  have herr := quad_err E _ hη0 hE c
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsplit : ∑ i, ∑ j, c i * c j * (M i j + E i j)
      = q c + ∑ i, ∑ j, c i * c j * E i j := by
    simp only [hq, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have hKη : K * (μ / (2 * K + 1)) < μ := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  have hs2 : 0 < ‖c‖ ^ 2 := by positivity
  have := hlow c hc
  have hlow' := (abs_le.mp herr).1
  rw [← hK] at hlow'
  nlinarith [mul_lt_mul_of_pos_right hKη hs2]
end GlobalTheory
