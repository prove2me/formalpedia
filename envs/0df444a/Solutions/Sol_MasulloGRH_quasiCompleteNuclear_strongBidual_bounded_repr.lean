-- Prove2me | solution 1 for MasulloGRH.quasiCompleteNuclear_strongBidual_bounded_repr
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:54:42.624174+00:00
-- url     : https://prove2.me/submissions/091c595f-61ce-43cb-a8ab-ac7581d8a179

import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact
import Theorems.Thm_MasulloGRH_compact_disk_bidual_representation
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set
open scoped ComplexOrder Pointwise

private theorem bounded_hull {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {ι : Type*} (p : SeminormFamily ℂ E ι) (hp : WithSeminorms p)
    (S : Set E) (hS : Bornology.IsVonNBounded ℂ S) :
    Bornology.IsVonNBounded ℂ (closedAbsConvexHull ℂ S) := by
  apply hp.isVonNBounded_iff_seminorm_bounded.mpr
  intro i
  obtain ⟨r, hr, hb⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hS i
  refine ⟨r + 1, by linarith, ?_⟩
  have hsub : closedAbsConvexHull ℂ S ⊆ (p i).closedBall 0 r := by
    apply closedAbsConvexHull_min
    · intro x hx
      simpa [Seminorm.mem_closedBall_zero] using (hb x hx).le
    · exact ⟨(p i).balanced_closedBall_zero r,
        convex_RCLike_iff_convex_real.mpr ((p i).convex_closedBall 0 r)⟩
    · simpa [Seminorm.closedBall_zero_eq] using
        (isClosed_le (hp.continuous_seminorm i) continuous_const)
  intro x hx
  have h := hsub hx
  simp only [Seminorm.mem_closedBall_zero] at h
  linarith

private theorem nuclear_compact_closed_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsQuasiComplete E) (hN : IsNuclear E)
    (S : Set E) (hc : IsClosed S) (hb : Bornology.IsVonNBounded ℂ S) : IsCompact S := by
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hE.1
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcomplete : IsComplete S := by
    intro f hf hfs
    have hSf : S ∈ f := Filter.le_principal_iff.mp hfs
    have hcauchy : IsCauchyFilter f := by
      obtain ⟨hne, ht⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).mp hf
      refine ⟨hne, ?_⟩
      intro U hU
      obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp (ht hU)
      exact ⟨A ∩ B, inter_mem hA hB,
        fun x hx y hy => hAB (show (x,y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩
    obtain ⟨x, hx⟩ := hE.2 f hcauchy ⟨S, hSf, hb⟩
    have : f.NeBot := hf.1
    exact ⟨x, hc.mem_of_tendsto hx hSf, hx⟩
  apply TotallyBounded.isCompact_of_isComplete (hc := hcomplete)
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨t, ht⟩ := MasulloGRH.nuclear_bounded_precompact E hN S hb U hU
  refine ⟨t, t.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  apply Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  exact ⟨x - y, hxy, by simp⟩


theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsQuasiComplete E) (hN : IsNuclear E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    ∃ D : Set E, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ E), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ E, F f = f y := by
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hE.1
  obtain ⟨B, C, hB, hC, hqB⟩ :=
    MasulloGRH.strongDual_seminorm_le_polar E hN.1 q hq
  let a : ℝ := C + 1
  have ha : 0 < a := by dsimp [a]; linarith
  let S : Set E := insert 0 ((a : ℂ) • B)
  let D : Set E := closedAbsConvexHull ℂ S
  have hS : Bornology.IsVonNBounded ℂ S := by
    apply Bornology.IsVonNBounded.insert
    exact hB.image ((a : ℂ) • ContinuousLinearMap.id ℂ E)
  have hD : Bornology.IsVonNBounded ℂ D := bounded_hull p hp S hS
  refine ⟨D, hD, ?_⟩
  intro F hF
  have hc : IsCompact D := nuclear_compact_closed_bounded hE hN D
    isClosed_closedAbsConvexHull hD
  apply MasulloGRH.compact_disk_bidual_representation E D hc
    (convex_RCLike_iff_convex_real.mp (absConvex_convexClosedHull.2))
    (absConvex_convexClosedHull.1) (subset_closedAbsConvexHull (mem_insert 0 _)) F
  intro f r hr hbound
  apply (hF f).trans
  apply (hqB f (r / a) (div_nonneg hr ha.le) ?_).trans
  · have hratio : C / a ≤ 1 := (div_le_one ha).mpr (by dsimp [a]; linarith)
    calc C * (r / a) = (C / a) * r := by ring
         _ ≤ 1 * r := mul_le_mul_of_nonneg_right hratio hr
         _ = r := one_mul r
  · intro x hx
    have hax : (a : ℂ) • x ∈ D := subset_closedAbsConvexHull
      (mem_insert_of_mem 0 (Set.smul_mem_smul_set hx))
    have h := hbound _ hax
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha] at h
    exact (le_div_iff₀ ha).mpr (by nlinarith)
