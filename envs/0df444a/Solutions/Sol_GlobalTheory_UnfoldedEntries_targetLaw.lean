-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.targetLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:47.71646+00:00
-- url     : https://prove2.me/submissions/36c9b2dc-ba56-434f-b74c-899b2f04a88e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsParabolicDoubleCosetFunctionEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhdsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarCompactOpenRatioEqZpowOfTopNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParabolicHaarVolumeConjIntersectionEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralTranslateIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBoxStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SymmetricPositionLevelShapeOnParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Theorems.Thm_GlobalTheory_UnfoldedEntries_om_smul
import Theorems.Thm_GlobalTheory_UnfoldedEntries_target_law
import Theorems.Thm_GlobalTheory_UnfoldedEntries_exists_char
import Theorems.Thm_GlobalTheory_UnfoldedEntries_xi_eq_smul
import Theorems.Thm_GlobalTheory_RootEx_opE_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.UnfoldedEntries
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
namespace GlobalTheory.UnfoldedEntries
theorem _root_.solution : TargetLaw ψ ν := by
  intro n n' _ _ _ _ c hc μ P' P Φ hΦ _ hJ H h' h
  refine ⟨fun u hu => target_law hc hJ H h' h hu, fun h0 => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_char μ (prX (Cgrp P.J h)) h0 fun g ⟨u, hu, hm⟩ =>
    ⟨_, target_law hc hJ H h' h hu g (mem_Cgrp.1 hm).2⟩
  refine ⟨χ, fun g u hu hm => smul_left_injective ℂ h0 ((hχ g).symm.trans (target_law hc hJ H h' h hu g hm)),
    fun g => ⟨hχ g, fun b => ?_, fun V' V _ _ _ _ π' π θ hθ φ => ?_⟩⟩
  · rw [xi_eq_smul, om_smul, hχ, smul_comm]
  · rw [← hθ 1 g φ (flat ψ ν μ Φ h' h) (opE_mem_SB 1 ψ ν (om_mem_SB μ h' h hΦ)), map_one, Module.End.one_apply]
    exact (congrArg _ (hχ g)).trans (map_smul _ _ _)
end GlobalTheory.UnfoldedEntries
