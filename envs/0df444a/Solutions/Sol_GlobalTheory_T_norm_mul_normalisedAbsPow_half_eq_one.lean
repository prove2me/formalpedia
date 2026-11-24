-- Prove2me | solution 1 for GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:57.516487+00:00
-- url     : https://prove2.me/submissions/3b65fe27-8ece-44ae-829a-c26508c5b500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOneStatement
import Theorems.Thm_GlobalTheory_CharNormHalf_norm_mul_apow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
end _root_.GlobalTheory.T
