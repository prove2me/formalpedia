-- Prove2me | solution 1 for GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:02.167723+00:00
-- url     : https://prove2.me/submissions/46841d64-a899-4329-8a28-d43398319416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Published
theorem _root_.solution (hp : 0 < p) {x : K} (hx : x ^ 2 = -(p : K)) :
    IsTotallyComplex K := by
  refine ⟨fun v => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h1
  have h2 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]
end GlobalTheory.Published
