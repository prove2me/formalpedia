-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.idxAt_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:27.872001+00:00
-- url     : https://prove2.me/submissions/460b5366-a1eb-4044-a07b-105aef5cb1f3

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
import Theorems.Thm_GlobalTheory_QuotInt_finite_quot
import Theorems.Thm_GlobalTheory_RootEx_opE_support_compact_mod_R
import Theorems.Thm_GlobalTheory_RootEx_sb_matrix_exists_isOpen_addSubgroup
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul


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
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {μ : kˣ →* ℂˣ} {P' : Level (GL (n' ⊕ Fin (c + 1)) k)} {P : Level (GL (n ⊕ Fin c) k)}
  {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
variable [ν.IsAddHaarMeasure]
namespace GlobalTheory.UnfoldedEntries
theorem _root_.solution (hψ : HasConductor ψ 1) (hc : 1 ≤ c) (hΦ : Φ ∈ SB _) {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (h' : GL (n' ⊕ Fin (c + 1)) k) : (idxAt ψ ν μ Φ J h').Finite := by
  have hΨ := om_mem_SB μ h' 1 hΦ
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ _ hΨ
  obtain ⟨Ω, hΩ, hs⟩ := opE_support_compact_mod_R k n n' c 1 le_rfl hc ψ hψ.continuous hψ.ne_one ν _ hΨ.2 Λ hΛ
  obtain ⟨S, hS⟩ := QuotInt.finite_quot J hJ hΩ
  refine (S.finite_toSet.image fun q => DoubleCoset.mk (R k n c 1) J q.out).subset ?_
  rintro _ ⟨h, rfl, h0⟩
  obtain ⟨x₀, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨r, hr, w, hw, rfl⟩ := hs μ _ (subset_tsupport _) hinv (fun _ => 1) (IsLocallyConstant.const 1) h x₀ (by
    simp only [one_mul]
    rw [show (fun x => om μ 1 h (om μ h' 1 Φ) x) = om μ h' h Φ by rw [← om_mul]; simp]
    exact hx)
  refine ⟨(w : _ ⧸ J), hS w hw, (DoubleCoset.eq _ _ _ _).2 ⟨r, hr, ((w : _ ⧸ J).out)⁻¹ * w, ?_, by simp [mul_assoc]⟩⟩
  exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
end GlobalTheory.UnfoldedEntries
