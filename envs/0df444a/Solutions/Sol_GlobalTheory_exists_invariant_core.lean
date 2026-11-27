-- Prove2me | solution 1 for GlobalTheory.exists_invariant_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:50.806814+00:00
-- url     : https://prove2.me/submissions/94e493a3-b1bf-4e2b-905a-727b69018cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_exists_invariant_core_of_continuous_coeff

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
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (ρ : Representation 𝕜 K V) (hρc : ∀ v, Continuous fun k => ρ k v) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v :=
  exists_invariant_core_of_continuous_coeff ρ fun l v =>
    (LinearMap.continuous_of_finiteDimensional l).comp (hρc v)
end GlobalTheory
