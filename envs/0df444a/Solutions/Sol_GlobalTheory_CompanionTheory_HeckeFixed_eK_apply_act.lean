-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.eK_apply_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:29.1325+00:00
-- url     : https://prove2.me/submissions/e56fbbca-1874-4eb6-9a6d-ef96a1157020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_eK_apply_of_mem_coK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFixed
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
  (hKc : IsCompact (K : Set G))
namespace GlobalTheory.CompanionTheory.HeckeFixed
theorem _root_.solution {k : G} (hk : k ∈ K) (v : V) : eK π hπ hKc (π k v) = eK π hπ hKc v := by
  rw [← sub_eq_zero, ← map_sub]
  exact eK_apply_of_mem_coK hπ hKc (sub_mem_coK (resK π K) ⟨k, hk⟩ v)
end GlobalTheory.CompanionTheory.HeckeFixed
