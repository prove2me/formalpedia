-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:34.25718+00:00
-- url     : https://prove2.me/submissions/75770e81-ffb4-408d-aba6-2328034a3ea2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_pi_of_conductor
import Theorems.Thm_GlobalTheory_SplitWeil_conductor_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν f hf
  obtain ⟨c, h⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hc h1
  exact fourier_pi_of_conductor h hν hf
end GlobalTheory.SplitWeil.FourierPi
