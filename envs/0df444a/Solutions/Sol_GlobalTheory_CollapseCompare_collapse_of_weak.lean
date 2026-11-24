-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.collapse_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:35.227801+00:00
-- url     : https://prove2.me/submissions/834d598b-7c1b-4d96-9b13-c54a67576c40

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
import Theorems.Thm_GlobalTheory_CollapseCompare_core_of_collapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_hasTargetType_untwist
import Theorems.Thm_GlobalTheory_CollapseCompare_oneCoset_untwist
import Theorems.Thm_GlobalTheory_CollapseCompare_core_of_untwist
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_ne_one
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
theorem _root_.solution (H : CollapseWeak) : SymChain.Collapse := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c hc μ P Φ hΦ hJ h1 h2 bas m hm μG hG
  have := hν.1
  obtain ⟨κ, hκ, H'⟩ := H k n c hc ν m μG hν.1 hm hG P.J hJ.1 hJ.2 bas n' ψ hψ.continuous hψ.ne_one 1
    (untwist μ P.lam) ⟨Φ, hΦ⟩ (hasTargetType_untwist h1) (oneCoset_untwist h2)
  exact ⟨κ, hκ, core_of_untwist (core_of_collapsesWith (Φ := ⟨Φ, hΦ⟩) hc (by simp) hJ.1 (hasTargetType_untwist h1) H')⟩
end GlobalTheory.CollapseCompare
