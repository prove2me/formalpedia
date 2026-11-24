-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.genQuotRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:41.754288+00:00
-- url     : https://prove2.me/submissions/37e79f44-2f0a-461b-a1af-80d6d98db3b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent

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
theorem _root_.solution (g : L) (u : (genSubrep σ N).toSubmodule) :
    genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((genSubrep σ N).toRepresentation g u) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
