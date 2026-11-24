-- Prove2me | solution 1 for GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:44.011984+00:00
-- url     : https://prove2.me/submissions/205fd615-c879-46e5-a01e-d38b0a633b87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussIntegralQuadraticCharEventuallyConst
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussIntegralQuadraticCharEventuallyConstStatement
import Theorems.Thm_GlobalTheory_KSp_gauss_integral_eventually_const


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) → ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) → K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  first | exact @GlobalTheory.KSp.gauss_integral_eventually_const | exact GlobalTheory.KSp.gauss_integral_eventually_const | (intros; apply GlobalTheory.KSp.gauss_integral_eventually_const <;> assumption)
end _root_.GlobalTheory.T
