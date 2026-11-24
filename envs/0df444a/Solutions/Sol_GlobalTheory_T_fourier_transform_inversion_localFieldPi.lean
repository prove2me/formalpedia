-- Prove2me | solution 1 for GlobalTheory.T.fourier_transform_inversion_localFieldPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:43.047171+00:00
-- url     : https://prove2.me/submissions/7ba903d1-3c63-4388-9a07-b525bab920e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPiStatement
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.fourier_pi | exact GlobalTheory.SplitWeil.FourierPi.fourier_pi | (intros; apply GlobalTheory.SplitWeil.FourierPi.fourier_pi <;> assumption)
end _root_.GlobalTheory.T
