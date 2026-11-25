-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.genQuotForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:24.361293+00:00
-- url     : https://prove2.me/submissions/04fc7bdd-621d-43e8-b796-e4d523a3c555

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
variable {N}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (l : Dual ℂ (fixedVectors σ K)) (hNK : N ≤ fixedVectors σ K) (g : L)
    (n : N) :
    genQuotForm hσ hKc hKo l (genQuotRep hσ hKc hKo N g (genQuotMk hσ hKc hKo N n)) =
      l (fixedProj σ hσ hKc hKo (σ g n)) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
