-- Prove2me | solution 1 for GlobalTheory.averageCore_inner_map_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:19.202907+00:00
-- url     : https://prove2.me/submissions/7c76b597-32cc-4ca9-b2dd-d1fb5f10a1de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
namespace GlobalTheory
theorem _root_.solution [MeasurableSpace K] [BorelSpace K] {V E : Type*}
    [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ρ : Representation 𝕜 K V) (e : V →ₗ[𝕜] E) (he : Function.Injective e)
    (hc : ∀ v, Continuous fun k => e (ρ k v)) (g : K) (u v : V) :
    (averageCore ρ e he hc).inner (ρ g u) (ρ g v) = (averageCore ρ e he hc).inner u v := by
  have h := integral_mul_right_eq_self (μ := haarProb K) (fun k => ⟪e (ρ k u), e (ρ k v)⟫_𝕜) g
  simp only [map_mul, Module.End.mul_apply] at h
  exact h
end GlobalTheory
