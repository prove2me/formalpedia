-- Prove2me | solution 1 for GlobalTheory.eq_I_mul_sqrt_or_of_sq_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:24.987076+00:00
-- url     : https://prove2.me/submissions/48b14198-bddf-4612-b60e-95d03e7a8315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution {d : ℕ} {z : ℂ} (hz : z ^ 2 = -d) :
    z = Complex.I * √d ∨ z = -(Complex.I * √d) := by
  have h : (Complex.I * √d) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans h.symm)
end GlobalTheory
