-- Prove2me | solution 1 for GradSampling.Conv.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:29:48.931679+00:00
-- url     : https://prove2.me/submissions/4dd0ee2a-05d2-4e8e-b59d-c5ad10eff176

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open GradSampling.Conv in
theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) (hCcl : IsClosed C)
    (hCcv : Convex ℝ C) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ C) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ C)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (u ubar : EuclideanSpace ℝ (Fin n)) (hu : u ∈ C)
    (hubar : ubar ∈ C) (hηu : η ≤ ‖ubar‖) (hmin : ‖ubar‖ = Metric.infDist 0 C)
    (hle : ‖u‖ ≤ ‖ubar‖ + δ) :
    inner ℝ (v - u) (-(‖u‖⁻¹ • u)) ≤
      (‖v‖ * Real.sqrt (2 / η) + Real.sqrt (2 * ‖ubar‖ + δ)) * Real.sqrt δ := by
  -- minimal norm
  have hminc : ∀ c ∈ C, ‖ubar‖ ≤ ‖c‖ := by
    intro c hc
    have := Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin n))) hc
    rw [dist_zero_left] at this
    rw [hmin]; exact this
  -- projection inequality
  have hproj : ∀ c ∈ C, ‖ubar‖ ^ 2 ≤ inner ℝ c ubar := by
    have : Nonempty C := ⟨⟨ubar, hubar⟩⟩
    have heq : ‖(0 : EuclideanSpace ℝ (Fin n)) - ubar‖
        = ⨅ w : C, ‖(0 : EuclideanSpace ℝ (Fin n)) - w‖ := by
      apply le_antisymm
      · refine le_ciInf fun w => ?_
        rw [zero_sub, zero_sub, norm_neg, norm_neg]
        exact hminc w w.2
      · have hbdd : BddBelow (Set.range fun w : C => ‖(0 : EuclideanSpace ℝ (Fin n)) - w‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w, rfl⟩
          exact norm_nonneg _
        exact ciInf_le hbdd (⟨ubar, hubar⟩ : C)
    have hiff := (norm_eq_iInf_iff_real_inner_le_zero hCcv hubar).mp heq
    intro c hc
    have h1 := hiff c hc
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm] at h1
    linarith
  set N := ‖u‖ with hN
  set B := ‖ubar‖ with hB
  have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
  have hNpos : 0 < N := norm_pos_iff.mpr hu0
  have hBN : B ≤ N := hminc u hu
  have hBpos : 0 < B := lt_of_lt_of_le hη hηu
  set w := u - ubar with hw
  set a := N ^ 2 - B ^ 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have huu := hproj u hu
  have hvu := hproj v hv
  -- ‖w‖² ≤ a
  have hw2 : ‖w‖ ^ 2 ≤ a := by
    have e : ‖w‖ ^ 2 = N ^ 2 - 2 * inner ℝ u ubar + B ^ 2 := by
      rw [hw, @norm_sub_sq_real]
    rw [e, ha]; linarith
  -- ⟪v,u⟫ ≥ B² - ‖v‖‖w‖
  have hvw : -(‖v‖ * ‖w‖) ≤ inner ℝ v w := by
    have := abs_real_inner_le_norm v w
    linarith [neg_abs_le (inner ℝ v w)]
  have hvu' : B ^ 2 - ‖v‖ * ‖w‖ ≤ inner ℝ v u := by
    have e : inner ℝ v u = inner ℝ v ubar + inner ℝ v w := by
      rw [hw, inner_sub_right]; ring
    rw [e]
    linarith
  -- the inner product
  have hinner : inner ℝ (v - u) (-(N⁻¹ • u)) = N⁻¹ * (N ^ 2 - inner ℝ v u) := by
    rw [inner_neg_right, inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  rw [hinner]
  have hmain : N⁻¹ * (N ^ 2 - inner ℝ v u) ≤ a / N + ‖v‖ * (‖w‖ / N) := by
    rw [div_eq_inv_mul, mul_div_assoc', div_eq_inv_mul, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNpos.le)
    rw [ha]; linarith
  refine hmain.trans ?_
  -- bound a / N
  have hA : a / N ≤ Real.sqrt (2 * B + δ) * Real.sqrt δ := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * B + δ)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h1 : (a / N) ^ 2 ≤ a := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have : a ≤ N ^ 2 := by rw [ha]; nlinarith
      nlinarith
    have h2 : a ≤ (2 * B + δ) * δ := by
      rw [ha]; nlinarith
    linarith
  have hW : ‖w‖ / N ≤ Real.sqrt (2 / η) * Real.sqrt δ := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / η)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h1 : a ≤ 2 * δ * N := by rw [ha]; nlinarith
    have hηN : η ≤ N := hηu.trans hBN
    rw [div_pow, div_le_iff₀ (by positivity)]
    have h3 : 2 / η * δ * N ^ 2 ≥ 2 * δ * N := by
      have : 2 / η * δ * N ^ 2 = (2 * δ * N) * (N / η) := by field_simp
      rw [this]
      have : 1 ≤ N / η := by rw [le_div_iff₀ hη]; linarith
      nlinarith [hδ, hNpos]
    linarith
  have hv0 := norm_nonneg v
  calc a / N + ‖v‖ * (‖w‖ / N)
      ≤ Real.sqrt (2 * B + δ) * Real.sqrt δ + ‖v‖ * (Real.sqrt (2 / η) * Real.sqrt δ) :=
        add_le_add hA (mul_le_mul_of_nonneg_left hW hv0)
    _ = (‖v‖ * Real.sqrt (2 / η) + Real.sqrt (2 * B + δ)) * Real.sqrt δ := by ring
