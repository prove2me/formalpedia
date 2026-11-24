-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:29.66336+00:00
-- url     : https://prove2.me/submissions/8afb76d5-9c49-4da3-81e4-40bb3fa48f60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZeroStatement
import Theorems.Thm_GlobalTheory_KSp_exists_integral_cball_char_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  first | exact @GlobalTheory.KSp.exists_integral_cball_char_eq_zero | exact GlobalTheory.KSp.exists_integral_cball_char_eq_zero | (intros; apply GlobalTheory.KSp.exists_integral_cball_char_eq_zero <;> assumption)
end _root_.GlobalTheory.T
