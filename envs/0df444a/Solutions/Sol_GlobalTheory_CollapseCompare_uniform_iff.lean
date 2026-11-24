-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.uniform_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:36.265309+00:00
-- url     : https://prove2.me/submissions/7ebe0937-5413-47be-8c11-b6094fe79e12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_Core_collapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_core_of_collapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_hasTargetType_untwist
import Theorems.Thm_GlobalTheory_CollapseCompare_oneCoset_untwist
import Theorems.Thm_GlobalTheory_CollapseCompare_core_of_untwist
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
namespace GlobalTheory.CollapseCompare
theorem _root_.solution : CollapseUniform ↔ IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse := by
  refine ⟨fun H => ?_, fun H => ?_⟩ <;>
    intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas <;>
    obtain ⟨κ, hκ, H'⟩ := H k n c hc ν μX μG hν hX hG J ho hcp bas <;>
    refine ⟨κ, hκ, fun n' _ _ ψ hψ hψ1 μ lam Φ h1 h2 => ?_⟩
  · exact (H' n' ψ hψ hψ1 μ lam Φ h1 h2).collapsesWith
  · exact core_of_untwist (core_of_collapsesWith hc (by simp) ho (hasTargetType_untwist h1)
      (H' n' ψ hψ hψ1 1 _ Φ (hasTargetType_untwist h1) (oneCoset_untwist h2)))
end GlobalTheory.CollapseCompare
