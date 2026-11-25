-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isAdmissible_genQuotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:48.331876+00:00
-- url     : https://prove2.me/submissions/3b1f581e-3fb8-4fd7-b91b-b8eae78551b9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_genSubrep
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_genQuotRep
import Theorems.Thm_GroundTheory_Automorphic_fixedMap_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
variable {N}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution
    (hfin : ∀ K' : Subgroup L, IsCompact (K' : Set L) → IsOpen (K' : Set L) →
      FiniteDimensional ℂ (fixedVectors (genSubrep σ N).toRepresentation K')) :
    IsAdmissible (genQuotRep hσ hKc hKo N) := by
  refine ⟨isSmooth_genQuotRep hσ hKc hKo N, fun K' hK'c hK'o => ?_⟩
  have := hfin K' hK'c hK'o
  have hsurj := fixedMap_surjective (isSmooth_genSubrep hσ N) (isSmooth_genQuotRep hσ hKc hKo N)
    hK'c hK'o (f := genQuotMap hσ hKc hKo N) (Submodule.mkQ_surjective _)
  exact Module.Finite.of_surjective _ hsurj
end GroundTheory.Automorphic.RestrictedTensor
