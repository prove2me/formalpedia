-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.firstVertex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:19.022459+00:00
-- url     : https://prove2.me/submissions/19eca6a1-a442-4c47-87b5-39f90f61bbdb

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
import Theorems.Thm_GlobalTheory_UnfoldedEntries_source_law
import Theorems.Thm_GlobalTheory_UnfoldedEntries_isCO_lev
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_eq_zero


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
theorem _root_.solution {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z]
    [DecidableEq Z] {C : Chain k s X Z} (hT : C.Regular) (hL : C.Laws) {K₀ : Set (GL (X 0) k)}
    {lam : GL (X 0) k → ℂ} (H : ∀ c (H : 0 + c = s + 1), (prX (Cgrp (C.lev 0 c H).J 1) : Set (GL (X 0) k)) = K₀ ∧
      (∀ γ ∈ K₀, ∃ hm : embX c γ ∈ (C.lev 0 c H).J, ((C.lev 0 c H).lam ⟨_, hm⟩ : ℂ) = lam γ) ∧
      ∀ u ∈ N k (X 0) c 1, ∀ hm : u ∈ (C.lev 0 c H).J, ((C.lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u)) :
    FirstVertex ψ ν C K₀ lam := by
  refine ⟨fun c hc => ?_, fun c hc h γ hγ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := H c hc
    refine ⟨h1, h2, ?_⟩
    choose hm hlam using h2
    have hK : ∀ γ : prX (Cgrp (C.lev 0 c hc).J 1), (γ : GL (X 0) k) ∈ K₀ := fun γ => h1 ▸ γ.2
    let ι : prX (Cgrp (C.lev 0 c hc).J 1) →* (C.lev 0 c hc).J :=
      ((embX c).comp (Subgroup.subtype _)).codRestrict _ fun γ => hm γ (hK γ)
    refine ⟨((C.lev 0 c hc).lam.comp ι)⁻¹, fun γ u hu hu' => ?_, fun γ => ?_⟩
    · have hu'' : u ∈ (C.lev 0 c hc).J := by simpa using mul_mem hu' (inv_mem (hm γ (hK γ)))
      rw [← h3 u hu hu'', show (⟨_, hu'⟩ : (C.lev 0 c hc).J) = ⟨u, hu''⟩ * ι γ from Subtype.ext (by simp; rfl),
        map_mul]
      simp
      field_simp
    · rw [← hlam γ (hK γ)]
      exact Units.inv_mul _
  · obtain ⟨hm, e⟩ := (H (c + 1 + 1) (by omega)).2.1 γ hγ
    rw [source_law (by omega) (isCO_lev hT _ _ _) (hL.1 0 (c + 1) hc) 1 h (one_mem _) γ (by simpa using hm),
      Radical.simpleSum_eq_zero (by simp [Matrix.one_apply]), ← e]
    simp
end GlobalTheory.UnfoldedEntries
