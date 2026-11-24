-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.existsUnique_isHeckeOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:28.311179+00:00
-- url     : https://prove2.me/submissions/918a59ef-55f7-428e-814e-c953dac70d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_isHeckeOn_heckeOn
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_IsHeckeOn_unique

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
include hπ hKc
namespace GlobalTheory.CompanionTheory.HeckeFixed
theorem _root_.solution (g : G) : ∃! T : Module.End ℂ (fixed π K), IsHeckeOn π K g T :=
  ⟨heckeOn π hπ hKc g, isHeckeOn_heckeOn hπ hKc g,
    fun _ hT => hT.unique hπ hKc (isHeckeOn_heckeOn hπ hKc g)⟩
end GlobalTheory.CompanionTheory.HeckeFixed
