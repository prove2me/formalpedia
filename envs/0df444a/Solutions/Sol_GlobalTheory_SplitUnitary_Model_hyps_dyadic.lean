-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.Model.hyps_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:12:41.961038+00:00
-- url     : https://prove2.me/submissions/cfbee2c0-5e52-43cb-b5db-803be87f69b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
import Theorems.Thm_GlobalTheory_SplitUnitary_Model_isQuad_isHerm_continuous_resEtaPow
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_localField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)
namespace GlobalTheory.SplitUnitary.Model
theorem _root_.solution : ∃ (_ : IsNonarchimedeanLocalField ℚ_[2]) (_ : TopologicalSpace (QuadraticAlgebra ℚ_[2] 2 0))
      (_ : IsModuleTopology ℚ_[2] (QuadraticAlgebra ℚ_[2] 2 0))
      (c : QuadraticAlgebra ℚ_[2] 2 0 →ₐ[ℚ_[2]] QuadraticAlgebra ℚ_[2] 2 0) (δ : QuadraticAlgebra ℚ_[2] 2 0)
      (Q : Matrix (Fin (2 * 1)) (Fin (2 * 1)) (QuadraticAlgebra ℚ_[2] 2 0)) (ψ : AddChar ℚ_[2] ℂ)
      (χ : (QuadraticAlgebra ℚ_[2] 2 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := ℚ_[2]) ⊥ χ (Fintype.card (Fin (2 * 1))) :=
  ⟨GlobalTheory.SplitWeil.Model.padic_localField 2, @isQuad_isHerm_continuous_resEtaPow ℚ_[2] _ _ _ _ (GlobalTheory.SplitWeil.Model.padic_localField 2) 2 _ 1⟩
end GlobalTheory.SplitUnitary.Model
