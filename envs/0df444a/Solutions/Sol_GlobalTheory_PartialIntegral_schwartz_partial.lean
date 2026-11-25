-- Prove2me | solution 1 for GlobalTheory.PartialIntegral.schwartz_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:36.088924+00:00
-- url     : https://prove2.me/submissions/5ac110b2-2ea7-4bbf-87e5-2fae2d01843a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocallyConstantPartial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.PartialIntegral
variable {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] (μ : Measure X) [μ.IsAddHaarMeasure]
namespace GlobalTheory.PartialIntegral
theorem _root_.solution [FiniteDimensional ℝ A] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ))
    (L₁ : X →ₗ[ℝ] V) (L₂ : A →ₗ[ℝ] V) (hL : ∀ x a, L₁ x + L₂ a = 0 → x = 0 ∧ a = 0) :
    (∀ a, Integrable (fun x => f (L₁ x + L₂ a)) μ) ∧ ∃ h : 𝓢(A, ℂ), ∀ a, h a = ∫ x, f (L₁ x + L₂ a) ∂μ := by
  let L : (X × A) →L[ℝ] V := LinearMap.toContinuousLinearMap (L₁.coprod L₂)
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (L₁.coprod L₂)
    (LinearMap.ker_eq_bot'.2 fun z hz => Prod.ext (hL z.1 z.2 hz).1 (hL z.1 z.2 hz).2)
  let F : 𝓢(X × A, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ (g := L) L.hasTemperateGrowth hK f
  exact ⟨fun a => integrable_slice μ F a, intFst μ F, fun a => rfl⟩
end GlobalTheory.PartialIntegral
