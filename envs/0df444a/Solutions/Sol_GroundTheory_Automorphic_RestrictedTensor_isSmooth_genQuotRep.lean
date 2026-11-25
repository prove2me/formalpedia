-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isSmooth_genQuotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:30.601113+00:00
-- url     : https://prove2.me/submissions/2eecb1fe-179f-47a6-9d29-504bfc46ba7e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genQuotRep_mk
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_genSubrep

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution : IsSmooth (genQuotRep hσ hKc hKo N) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (genSubrep σ N).toRepresentation u)
    (fun g hg => ?_) (isSmooth_genSubrep hσ N u)
  show genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [genQuotRep_mk, hg]
end GroundTheory.Automorphic.RestrictedTensor
