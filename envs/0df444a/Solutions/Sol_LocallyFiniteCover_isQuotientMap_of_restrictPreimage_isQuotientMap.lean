-- Prove2me | solution 1 for LocallyFiniteCover.isQuotientMap_of_restrictPreimage_isQuotientMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:00:55.319581+00:00
-- url     : https://prove2.me/submissions/ed072dac-fc0f-4d80-929d-eeb4b66570ae

import Mathlib

open Topology

set_option autoImplicit false


theorem solution
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (A : ι → Set Y)
    (hA : LocallyFinite A) (hAc : ∀ i, IsClosed (A i)) (hAcov : ⋃ i, A i = Set.univ)
    (hq : ∀ i, IsQuotientMap ((A i).restrictPreimage f)) :
    IsQuotientMap f := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨?_, fun s => ⟨fun hs => hs.preimage hf, fun hs => ?_⟩⟩
  · intro y
    have hy : y ∈ ⋃ i, A i := hAcov ▸ Set.mem_univ y
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨⟨x, hx⟩, hxy⟩ := (hq i).surjective ⟨y, hi⟩
    exact ⟨x, congrArg Subtype.val hxy⟩
  · -- each piece `s ∩ A i` is closed
    have hpiece : ∀ i, IsClosed (s ∩ A i) := by
      intro i
      have ht : IsClosed (((↑) : A i → Y) ⁻¹' s) := by
        rw [(isQuotientMap_iff_isClosed.mp (hq i)).2]
        have hpre : (A i).restrictPreimage f ⁻¹' (((↑) : A i → Y) ⁻¹' s)
            = ((↑) : f ⁻¹' A i → X) ⁻¹' (f ⁻¹' s) := by
          ext x
          rfl
        rw [hpre]
        exact hs.preimage continuous_subtype_val
      have himg := (hAc i).isClosedMap_subtype_val _ ht
      rwa [Subtype.image_preimage_coe, Set.inter_comm] at himg
    have hlf : LocallyFinite fun i => s ∩ A i :=
      hA.subset fun i => Set.inter_subset_right
    have hU := hlf.isClosed_iUnion hpiece
    have heq : (⋃ i, s ∩ A i) = s := by
      rw [← Set.inter_iUnion, hAcov, Set.inter_univ]
    rwa [heq] at hU
