-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:20.148163+00:00
-- url     : https://prove2.me/submissions/71082af8-7c4f-4df1-8b6d-44322e7438b4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_sum_sq_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
theorem _root_.solution (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c t : k}
    (hc : c ≠ 0) (ht : t ≠ 0) :
    ∑ y : k, ψ ((t * c) * (y * y)) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (c * (y * y)) := by
  rw [sum_sq_eq hchar ψ hψ (mul_ne_zero ht hc), sum_sq_eq hchar ψ hψ hc, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ fun z => ?_
  have h1 : (quadraticChar k t : ℂ) * (quadraticChar k t : ℂ) = 1 := by
    have := quadraticChar_sq_one ht
    have h2 : (quadraticChar k t) * (quadraticChar k t) = 1 := by rw [← pow_two]; exact this
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h2
  have e : (Equiv.mulLeft₀ t ht) z = t * z := rfl
  rw [e, map_mul (quadraticChar k) t z, Int.cast_mul, show t * c * z = c * (t * z) by ring]
  linear_combination (-(quadraticChar k z : ℂ) * ψ (c * (t * z))) * h1
end GlobalTheory.CompanionTheory.SW.QuadricUnit
