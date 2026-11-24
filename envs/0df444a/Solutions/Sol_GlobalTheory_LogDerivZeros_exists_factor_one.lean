-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.exists_factor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:14.037355+00:00
-- url     : https://prove2.me/submissions/1b7d07f1-c9f2-40e9-bab2-7c9d5f1d6897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Theorems.Thm_GlobalTheory_FactorOrderExistence_exists_factor_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ} (hw : w ∈ U)
    (ho : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ z, g z = (z - w) ^ (analyticOrderNatAt g w) * h z) ∧
      h w ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order
  | exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order
  | (apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order ..)
end GlobalTheory.LogDerivZeros
