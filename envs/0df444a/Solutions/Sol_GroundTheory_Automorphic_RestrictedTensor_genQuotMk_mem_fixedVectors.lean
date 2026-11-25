-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.genQuotMk_mem_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:25.356799+00:00
-- url     : https://prove2.me/submissions/76c6832d-6409-4824-a56c-0993b83be982

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genQuotRep_mk

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
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
include hNK
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (n : N) :
    genQuotMk hσ hKc hKo N n ∈ fixedVectors (genQuotRep hσ hKc hKo N) K := by
  intro k hk
  show genQuotRep hσ hKc hKo N k (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [genQuotRep_mk]
  congr 1
  exact Subtype.ext (hNK n.2 k hk)
end GroundTheory.Automorphic.RestrictedTensor
