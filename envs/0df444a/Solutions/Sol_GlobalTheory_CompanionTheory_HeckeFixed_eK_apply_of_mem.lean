-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.eK_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:20.990844+00:00
-- url     : https://prove2.me/submissions/d22eae34-6a23-4f91-80f1-00801b8b6264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_coe_eK

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
theorem _root_.solution {v : V} (hv : v ∈ fixed π K) : (eK π hπ hKc v : V) = v := by
  have hv' : v ∈ Representation.invariants (resK π K) := by rwa [← fixed_eq_invariants]
  rw [coe_eK, Submodule.projectionOnto_apply_of_mem_left _ hv']
end GlobalTheory.CompanionTheory.HeckeFixed
