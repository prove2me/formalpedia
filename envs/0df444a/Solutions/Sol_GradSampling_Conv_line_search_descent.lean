-- Prove2me | solution 1 for GradSampling.Conv.line_search_descent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:27:00.237995+00:00
-- url     : https://prove2.me/submissions/b0bf00b8-482d-4f70-b3ef-cdd1f901da6d

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open GradSampling.Conv in
theorem solution {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hC1 : ContDiffOn ℝ 1 f D) (β : ℝ) (hβ : β ∈ Set.Ioo 0 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) (pts : Fin m → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n))
    (hg : IsMinNormIn g (sampleHull f x pts)) (hg0 : g ≠ 0) :
    (∀ h ∈ sampleHull f x pts, inner ℝ h (-(‖g‖⁻¹ • g)) ≤ -‖g‖) ∧
      ∃ tbar > 0, ∀ s ∈ Set.Ioo 0 tbar,
        f (x + s • -(‖g‖⁻¹ • g)) ≤ f x + s * β * inner ℝ (gradient f x) (-(‖g‖⁻¹ • g)) ∧
          f x + s * β * inner ℝ (gradient f x) (-(‖g‖⁻¹ • g)) ≤ f x - s * β * ‖g‖ := by
  set K := sampleHull f x pts with hK
  have hKc : Convex ℝ K := convex_convexHull ℝ _
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  -- variational inequality
  have hvar : ∀ w ∈ K, ‖g‖ ^ 2 ≤ inner ℝ w g := by
    have : Nonempty K := ⟨⟨g, hg.1⟩⟩
    have heq : ‖(0 : EuclideanSpace ℝ (Fin n)) - g‖ = ⨅ w : K, ‖(0 : EuclideanSpace ℝ (Fin n)) - w‖ := by
      apply le_antisymm
      · refine le_ciInf fun w => ?_
        rw [zero_sub, zero_sub, norm_neg, norm_neg]
        exact hg.2 w w.2
      · have hbdd : BddBelow (Set.range fun w : K => ‖(0 : EuclideanSpace ℝ (Fin n)) - w‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w, rfl⟩
          exact norm_nonneg _
        exact ciInf_le hbdd (⟨g, hg.1⟩ : K)
    have hiff := (norm_eq_iInf_iff_real_inner_le_zero hKc hg.1).mp heq
    intro w hw
    have h1 := hiff w hw
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm] at h1
    linarith
  have part1 : ∀ h ∈ K, inner ℝ h (-(‖g‖⁻¹ • g)) ≤ -‖g‖ := by
    intro h hh
    rw [inner_neg_right, inner_smul_right]
    have := hvar h hh
    have e : ‖g‖⁻¹ * ‖g‖ ^ 2 = ‖g‖ := by field_simp
    have h2 : ‖g‖⁻¹ * ‖g‖ ^ 2 ≤ ‖g‖⁻¹ * inner ℝ h g :=
      mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (norm_nonneg _))
    rw [e] at h2
    linarith
  refine ⟨part1, ?_⟩
  set d : EuclideanSpace ℝ (Fin n) := -(‖g‖⁻¹ • g) with hd
  set L : ℝ := inner ℝ (gradient f x) d with hL
  have hgradK : gradient f x ∈ K := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hLle : L ≤ -‖g‖ := part1 _ hgradK
  have hLneg : L < 0 := by linarith
  have hdiff : DifferentiableAt ℝ f x :=
    (hC1.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hx)
  have hF : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (gradient f x)) x :=
    hdiff.hasGradientAt.hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    simpa using this
  have hφ : HasDerivAt (f ∘ fun s : ℝ => x + s • d) L 0 := by
    have := hF.comp_hasDerivAt_of_eq 0 hl (by simp)
    simpa [InnerProductSpace.toDual_apply_apply, hL] using this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hφ
  have hβL : L < β * L := by nlinarith [hβ.1, hβ.2]
  have hev := (tendsto_order.1 hslope).2 (β * L) hβL
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε, hε, fun s hs => ⟨?_, ?_⟩⟩
  · have hs0 : s ≠ 0 := ne_of_gt hs.1
    have hdist : dist s 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; exact hs.2
    have h := hball hdist hs0
    rw [slope_def_field] at h
    simp only [Function.comp, zero_smul, add_zero, sub_zero] at h
    rw [div_lt_iff₀ hs.1] at h
    linarith
  · have : s * β * L ≤ s * β * (-‖g‖) :=
      mul_le_mul_of_nonneg_left hLle (by nlinarith [hs.1, hβ.1])
    linarith
