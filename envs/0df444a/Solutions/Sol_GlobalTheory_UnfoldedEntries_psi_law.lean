-- Prove2me | solution 1 for GlobalTheory.UnfoldedEntries.psi_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:13.802804+00:00
-- url     : https://prove2.me/submissions/dd06185a-56cf-412c-93bc-5f223c87d5b6

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
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_embX_val
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_one
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_eq_zero
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
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
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.UnfoldedEntries
theorem _root_.solution (ψ : AddChar k Circle) {T : Chain k s X Z} (hL : T.Laws) (h) {u} (hu : u ∈ N k (X s) (0 + 1) 1)
    (g : GL (X s) k) (hm : h⁻¹ * (u * embX (0 + 1) g) * h ∈ (T.lev s (0 + 1) rfl).J) (y : X (s + 1) → k) :
    om (T.mu (s + 1)) g 1 (fun x₀ => T.Psi h x₀ y) =
      ((ψ (simpleSum u) : ℂ)⁻¹ * ((T.lev s (0 + 1) rfl).lam ⟨_, hm⟩ : ℂ)) • fun x₀ => T.Psi h x₀ y := by
  obtain rfl : u = 1 := Units.ext (Matrix.ext fun r t => Model.mem_N_iff.1 hu r t (by
    rcases r with r | r <;> rcases t with t | t <;> simp [lev]))
  have e : om (T.mu (s + 1)) (embX (0 + 1) g) 1 (om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl)) =
      ((T.lev s (0 + 1) rfl).lam ⟨_, hm⟩ : ℂ) • om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl) := by
    rw [← om_smul, ← (hL.1 s 0 rfl).1 ⟨_, hm⟩, ← om_mul, ← om_mul]; simp [mul_assoc]
  have d : Matrix.GeneralLinearGroup.det (embX (0 + 1) g) = Matrix.GeneralLinearGroup.det g :=
    Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Radical.embX_val])
  funext x
  have w : withCol x y * (embX (0 + 1) g).val = withCol (x * g.val) y := by
    simp [withCol, Radical.embX_val, fromBlocks_multiply]
  have := congrFun e (withCol x y)
  rw [om, d] at this
  simp only [inv_one, Units.val_one, Matrix.one_mul, w] at this
  rw [om, Radical.simpleSum_eq_zero (by simp [Matrix.one_apply])]
  simpa [Chain.Psi, nabs_one] using this
end GlobalTheory.UnfoldedEntries
