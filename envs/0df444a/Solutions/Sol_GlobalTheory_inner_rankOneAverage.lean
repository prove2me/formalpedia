-- Prove2me | solution 1 for GlobalTheory.inner_rankOneAverage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:02.212413+00:00
-- url     : https://prove2.me/submissions/559f57ea-3eeb-4489-b2e3-fe84abfd17f6

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
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
omit [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (hσc : ∀ w, Continuous fun k => σ k w) (u v : V) (u' w : W) :
    ⟪u', rankOneAverage μ ρ σ hρc hρu hσc v w u⟫_ℂ =
      ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', σ k w⟫_ℂ ∂μ := by
  have := FiniteDimensional.complete ℂ W
  have h := integral_inner (𝕜 := ℂ) (integrable_of_continuous_of_compactSpace μ
        (((hρc v).inner (𝕜 := ℂ) (continuous_const (y := u))).smul (hσc w))) u'
  refine Eq.trans h.symm ?_
  simp [inner_smul_right]
end GlobalTheory
