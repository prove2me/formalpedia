-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.chainFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:52.03337+00:00
-- url     : https://prove2.me/submissions/35c6200d-bebf-4d03-aadb-0dccb49efa39

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
import Theorems.Thm_GlobalTheory_UnfoldedEntries_stepWellDefined
import Theorems.Thm_GlobalTheory_UnfoldedEntries_isCO_lev
import Theorems.Thm_GlobalTheory_UnfoldedEntries_reps_finite
import Theorems.Thm_GlobalTheory_UnfoldedEntries_reps_image
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_T_exists_adapted_exponent_schwartzBruhat_lastColumn
import Theorems.Thm_GlobalTheory_T_finite_quotient_cosets_scaledStandardLatticeBox


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
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
namespace GlobalTheory.UnfoldedEntries
theorem _root_.solution (hψ : HasConductor ψ 1) : ChainFinite ψ ν := by
  intro s X _ _ Z _ _ T hT hL
  refine ⟨fun j c h g g' => ?_, fun A hA => ⟨reps_finite hψ hT hA, fun A' hA' => reps_image hL hA hA',
    fun ϖ hϖ => ?_, fun c₁ c₂ => (GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox k _ c₁ c₂).subset fun yb ⟨y, hy, e, _⟩ => ⟨y, hy, e⟩⟩⟩
  · exact (stepWellDefined hψ _ _ (c + 1) (by omega) _ _ _ _ (hT.1 _ _ _) (isCO_lev hT _ _ _) (isCO_lev hT _ _ _)
      (hL.1 j (c + 1) (by omega))).2.2.2.2.2.2 _ g g'
  · obtain ⟨e, he, H⟩ := GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn k _ _ _ ((reps_finite hψ hT hA s 0 rfl).image
      fun g => om (T.mu (s + 1)) g 1 (T.Phi s 0 rfl)) (by
        rintro _ ⟨g, -, rfl⟩; exact om_mem_SB _ _ _ (hT.1 _ _ _)) ϖ hϖ
    exact ⟨e, he, fun g hg => H _ ⟨g, hg, rfl⟩⟩
end GlobalTheory.UnfoldedEntries
