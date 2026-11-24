-- Prove2me | solution 1 for GlobalTheory.exists_invariant_core_of_continuous_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:01.541566+00:00
-- url     : https://prove2.me/submissions/8981f481-130f-4e97-a493-d6e0f6abe233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_averageCore_inner_map_map

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 K V)
    (hρc : ∀ (l : Module.Dual 𝕜 V) (v : V), Continuous fun k => l (ρ k v)) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v := by
  borelize K
  let b := Module.finBasis 𝕜 V
  let e : V ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V)) :=
    b.equivFun.trans (WithLp.linearEquiv 2 𝕜 _).symm
  have hc : ∀ v, Continuous fun k => e.toLinearMap (ρ k v) := fun v =>
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => hρc (b.coord i) v)
  exact ⟨averageCore ρ e.toLinearMap e.injective hc, averageCore_inner_map_map ρ _ _ hc⟩
end GlobalTheory
