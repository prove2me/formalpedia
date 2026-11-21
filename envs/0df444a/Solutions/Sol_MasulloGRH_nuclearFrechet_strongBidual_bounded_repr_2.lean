-- Prove2me | solution 2 for MasulloGRH.nuclearFrechet_strongBidual_bounded_repr
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:43:42.451705+00:00
-- url     : https://prove2.me/submissions/dd4c5cc2-52e1-414c-b862-ababb519dbb3

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact

set_option autoImplicit false

open MasulloGRH Filter Set Topology Bornology
open scoped Pointwise

private theorem compact_of_closed_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (hC : IsCompleteTVS E) (hN : IsNuclear E)
    (D : Set E) (hD : IsClosed D) (hb : IsVonNBounded ℂ D) : IsCompact D := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := by
    constructor
    intro f hf
    obtain ⟨hbot, hdiff⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).1 hf
    refine hC.2 f ⟨hbot, fun U hU => ?_⟩
    obtain ⟨A, hA, B, hB, hsub⟩ := mem_prod_iff.1 (hdiff hU)
    exact ⟨A ∩ B, inter_mem hA hB, fun x hx y hy => hsub (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩
  refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, hD.isComplete⟩
  apply totallyBounded_iff_subset_finite_iUnion_nhds_zero.2
  intro U hU
  obtain ⟨t, ht⟩ := nuclear_bounded_precompact E hN D hb U hU
  refine ⟨t, t.finite_toSet, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
  refine mem_iUnion₂.2 ⟨x, hx, ?_⟩
  have : y - x ∈ U := hyx
  exact ⟨y - x, this, by simp [vadd_eq_add, sub_eq_add_neg, add_left_comm]⟩

private theorem rotate_to_norm (z : ℂ) :
    ∃ a : ℂ, ‖a‖ ≤ 1 ∧ (a * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℂ := (starRingEnd ℂ) z / (‖z‖ : ℂ)
  refine ⟨a, ?_, ?_⟩
  · change ‖(starRingEnd ℂ) z / (‖z‖ : ℂ)‖ ≤ 1
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']
  · change (((starRingEnd ℂ) z / (‖z‖ : ℂ)) * z).re = ‖z‖
    have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_mul_eq_mul_div, RCLike.conj_mul]
    change (((‖z‖ : ℂ) ^ 2) / (‖z‖ : ℂ)).re = ‖z‖
    rw [sq, mul_div_cancel_right₀ _ hc]
    exact Complex.ofReal_re _

private theorem interpolate {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (D : Set E) (hD : IsCompact D) (hconv : Convex ℝ D) (hbal : Balanced ℂ D)
    (h0 : (0 : E) ∈ D) (F : StrongDual ℂ (StrongDual ℂ E))
    (hF : ∀ f : StrongDual ℂ E, (∀ x ∈ D, ‖f x‖ < 1) → ‖F f‖ < 1)
    (s : Finset (StrongDual ℂ E)) : ∃ y ∈ D, ∀ f ∈ s, F f = f y := by
  classical
  -- Prescribe the values on this finite family simultaneously.
  let e : E →L[ℂ] (s → ℂ) := ContinuousLinearMap.pi fun i : s => i.1
  let v : s → ℂ := fun i => F i.1
  suffices hv : v ∈ e '' D by
    obtain ⟨y, hy, he⟩ := hv
    exact ⟨y, hy, fun f hf => (congrFun he ⟨f, hf⟩).symm⟩
  by_contra hv
  have hcv : Convex ℝ (e '' D) := hconv.linear_image (e.toLinearMap.restrictScalars ℝ)
  have hclosed : IsClosed (e '' D) := (hD.image e.continuous).isClosed
  obtain ⟨l, c, hc, hlt⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hcv hclosed hv
  have hcpos : 0 < c := by simpa using hc (e 0) (mem_image_of_mem e h0)
  let g : StrongDual ℂ E := l.comp e
  have hg (y : E) (hy : y ∈ D) : ‖g y‖ < c := by
    obtain ⟨a, ha, hre⟩ := rotate_to_norm (g y)
    have hcut := hc (e (a • y)) (mem_image_of_mem e (hbal.smul_mem ha hy))
    change (g (a • y)).re < c at hcut
    rw [map_smul, smul_eq_mul, hre] at hcut
    exact hcut
  have hgF : ‖F g‖ < c := by
    have hn : ‖(↑c⁻¹ : ℂ)‖ = c⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hcpos.le)]
    have h := hF ((↑c⁻¹ : ℂ) • g) (fun y hy => by
      rw [smul_apply, norm_smul, hn, inv_mul_lt_iff₀ hcpos, mul_one]
      exact hg y hy)
    rw [map_smul, norm_smul, hn, inv_mul_lt_iff₀ hcpos, mul_one] at h
    exact h
  have hl (z : s → ℂ) : l z = ∑ i : s, l (Pi.single i (1 : ℂ)) * z i := by
    calc
      l z = l (∑ i : s, Pi.single i (z i)) := congrArg l (Finset.univ_sum_single z).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hsingle : Pi.single i (z i) = z i • Pi.single i (1 : ℂ) := by
          ext j
          by_cases h : j = i
          · subst j; simp
          · simp [Pi.single_eq_of_ne h]
        rw [hsingle, map_smul, smul_eq_mul, mul_comm]
  have hg_sum : g = ∑ i : s, l (Pi.single i (1 : ℂ)) • i.1 := by
    ext y
    rw [sum_apply]
    exact hl (e y)
  have heq : F g = l v := by
    rw [hg_sum, map_sum, hl]
    simp only [map_smul, smul_eq_mul, v]
  exact ((RCLike.re_le_norm (l v)).trans_lt (heq ▸ hgF)).not_gt hlt

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    ∃ D : Set E, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ E), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ E, F f = f y := by
  classical
  obtain ⟨ι, _, P, hP⟩ := hE.1
  let : IsTopologicalAddGroup E := hP.topologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  have hn : {f | q f < 1} ∈ 𝓝 (0 : StrongDual ℂ E) :=
    IsOpen.mem_nhds (isOpen_lt hq continuous_const) (by simp)
  obtain ⟨⟨B, r⟩, ⟨hB, hr⟩, hsub⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis (Metric.nhds_basis_ball :
      (𝓝 (0 : ℂ)).HasBasis (fun r : ℝ => 0 < r) (Metric.ball 0))).mem_iff.1 hn
  choose M hM hMB using (hP.isVonNBounded_iff_seminorm_bounded.1 hB)
  -- A closed bounded intersection of seminorm balls contains the scaled test set.
  let R (i : ι) : ℝ := r⁻¹ * M i
  have hR (i : ι) : 0 ≤ R i := mul_nonneg (inv_nonneg.mpr hr.le) (hM i).le
  let D : Set E := ⋂ i, (P i).closedBall 0 (R i)
  have hmem (y : E) : y ∈ D ↔ ∀ i, P i y ≤ R i := by
    simp [D, Seminorm.mem_closedBall, sub_zero]
  have h0 : (0 : E) ∈ D := (hmem 0).2 fun i => by simpa using hR i
  have hDclosed : IsClosed D := isClosed_iInter fun i => by
    simpa only [Seminorm.closedBall, sub_zero] using
      isClosed_le (hP.continuous_seminorm i) (continuous_const (y := R i))
  have hDbdd : IsVonNBounded ℂ D := hP.isVonNBounded_iff_seminorm_bounded.2 fun i =>
    ⟨R i + 1, add_pos_of_nonneg_of_pos (hR i) zero_lt_one, fun y hy =>
      ((hmem y).1 hy i).trans_lt (lt_add_one _)⟩
  have hDconv : Convex ℝ D := convex_iInter fun i => (P i).convex_closedBall 0 (R i)
  have hDbal : Balanced ℂ D := balanced_iff_smul_mem.2 fun a ha y hy => (hmem _).2 fun i => calc
    P i (a • y) = ‖a‖ * P i y := map_smul_eq_mul _ _ _
    _ ≤ P i y := mul_le_of_le_one_left (apply_nonneg (P i) y) ha
    _ ≤ R i := (hmem y).1 hy i
  have hDcomp := compact_of_closed_bounded hE.2.1 hN D hDclosed hDbdd
  refine ⟨D, hDbdd, fun F hF => ?_⟩
  have hsmall (f : StrongDual ℂ E) (hf : ∀ x ∈ D, ‖f x‖ < 1) : ‖F f‖ < 1 := by
    apply (hF f).trans_lt
    apply hsub
    intro x hx
    have hxD : (↑r⁻¹ : ℂ) • x ∈ D := (hmem _).2 fun i => by
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      exact mul_le_mul_of_nonneg_left (hMB i x hx).le (inv_nonneg.mpr hr.le)
    have hfx := hf _ hxD
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      inv_mul_lt_iff₀ hr, mul_one] at hfx
    simpa only [Metric.mem_ball, dist_zero_right] using hfx
  -- Compactness gives a point satisfying all of the finite interpolation conditions.
  let C (f : StrongDual ℂ E) : Set E := {y | F f = f y}
  have hCclosed (f : StrongDual ℂ E) : IsClosed (C f) :=
    isClosed_eq continuous_const f.continuous
  obtain ⟨y, hy, hyall⟩ := hDcomp.inter_iInter_nonempty C hCclosed (fun s => by
    obtain ⟨z, hz, hzs⟩ := interpolate D hDcomp hDconv hDbal h0 F hsmall s
    exact ⟨z, hz, mem_iInter₂.2 hzs⟩)
  exact ⟨y, hy, mem_iInter.1 hyall⟩
