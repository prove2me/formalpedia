-- Prove2me | solution 1 for GlobalTheory.isIso_cubeLowerProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:37.006996+00:00
-- url     : https://prove2.me/submissions/8b5ef9b2-ac36-4f2f-927e-8747dce40140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
namespace GlobalTheory
theorem _root_.solution (he : Function.Surjective e) (A : Cube.{v} ι R) :
    IsIso (cubeLowerProj e A) := by
  have : ∀ p, IsIso ((cubeLowerProj e A).f p) := fun p => by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (Cube.termLower e A p)
    have hb : Function.Bijective (fun s : {s : Finset κ // s.card = p} =>
        (⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ : {t : Finset ι // t.card = p})) := by
      refine ⟨fun s s' h => Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h)), ?_⟩
      rintro ⟨t, ht⟩
      have h : (t.preimage e e.injective.injOn).map e.toEmbedding = t := by
        ext j
        obtain ⟨k, rfl⟩ := he j
        simp
      exact ⟨⟨t.preimage e e.injective.injOn, by rw [← ht, ← h, Finset.card_map, h]⟩,
        Subtype.ext h⟩
    exact (Equiv.piCongrLeft (fun t : {t : Finset ι // t.card = p} => A.obj t.1)
      (Equiv.ofBijective _ hb)).symm.bijective
  exact HomologicalComplex.Hom.isIso_of_components _
end GlobalTheory
