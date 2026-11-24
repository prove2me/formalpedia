-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.reps_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:47.964254+00:00
-- url     : https://prove2.me/submissions/c59dd363-693d-416a-aa4b-135dd3a860c2

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
import Theorems.Thm_GlobalTheory_UnfoldedEntries_flat_ne_zero_congr

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
theorem _root_.solution {T : Chain k s X Z} (hL : T.Laws) {A A' : RepFam k s X}
    (hA : T.IsRepSystem A ψ ν) (hA' : T.IsRepSystem A' ψ ν) (j : ℕ) : ∀ c (h : j + c = s),
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A j c h =
      DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A' j c h := by
  induction j with
  | zero => intro c h; rw [hA.zero, hA'.zero]
  | succ j ih =>
    intro c h
    rw [(hA.bij j c h).image_eq, (hA'.bij j c h).image_eq]
    have key : ∀ {B B' : Set (GL (X j ⊕ Fin (c + 1 + 1)) k)},
        DoubleCoset.mk (R k (X j) (c + 1 + 1) 1) (T.lev j (c + 1 + 1) (by omega)).J '' B =
          DoubleCoset.mk (R k (X j) (c + 1 + 1) 1) (T.lev j (c + 1 + 1) (by omega)).J '' B' →
        ⋃ g ∈ B, T.idx ψ ν j c h g ⊆ ⋃ g ∈ B', T.idx ψ ν j c h g := by
      intro B B' e β hβ
      obtain ⟨g, hg, x, rfl, hx⟩ := Set.mem_iUnion₂.1 hβ
      obtain ⟨g', hg', e'⟩ := e ▸ Set.mem_image_of_mem _ hg
      exact Set.mem_iUnion₂.2 ⟨g', hg', x, rfl,
        (flat_ne_zero_congr (by omega) (hL.1 j (c + 1) (by omega)) e' rfl).2 hx⟩
    exact (key (ih _ _)).antisymm (key (ih _ _).symm)
end GlobalTheory.UnfoldedEntries
