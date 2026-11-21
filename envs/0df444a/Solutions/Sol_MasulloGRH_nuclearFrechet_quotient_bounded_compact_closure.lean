-- Prove2me | solution 1 for MasulloGRH.nuclearFrechet_quotient_bounded_compact_closure
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:53:48.235163+00:00
-- url     : https://prove2.me/submissions/afc56f62-9122-45ae-b628-34123ae6d5d0

import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact
import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded

open Filter Set Topology
open scoped Pointwise

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (hN : IsNuclear E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (B : Set (E ⧸ V)) (hB : Bornology.IsVonNBounded ℂ B) : IsCompact (closure B) := by
  obtain ⟨ι, hι, p, hp⟩ := hF.1
  let := hp.topologicalAddGroup
  let := hp.continuousSMul
  let := hF.2.1.1
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := by
    constructor
    intro f hf
    have hh := (IsUniformAddGroup.cauchy_iff_tendsto f).mp hf
    apply hF.2.1.2 f
    refine ⟨hh.1, ?_⟩
    intro U hU
    obtain ⟨S, hS, T, hT, hST⟩ := mem_prod_iff.mp (hh.2 hU)
    exact ⟨S ∩ T, inter_mem hS hT, fun x hx y hy => @hST (x, y) ⟨hx.1, hy.2⟩⟩
  obtain ⟨A, hA, hBA⟩ := nuclear_frechet_quotient_lifts_bounded E hF hN V hV B hB
  have htot : TotallyBounded A := by
    apply totallyBounded_iff_subset_finite_iUnion_nhds_zero.mpr
    intro U hU
    obtain ⟨t, ht⟩ := nuclear_bounded_precompact E hN A hA U hU
    refine ⟨t, t.finite_toSet, ?_⟩
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨a, ha, x - a, hxa, by simp⟩
  let : T2Space (E ⧸ V) := by
    let : IsClosed (V : Set E) := hV
    infer_instance
  have hK := (htot.closure.isCompact_of_isClosed isClosed_closure).image V.continuous_mkQ
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (hBA.trans (image_mono subset_closure)) hK.isClosed)
