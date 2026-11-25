-- Prove2me | solution 1 for GroundTheory.ProfCoh.eq_of_forall_le_exp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:41.587734+00:00
-- url     : https://prove2.me/submissions/5ccdc09e-4554-4a5a-8a24-5cedeaa471e3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
namespace GroundTheory.ProfCoh
theorem _root_.solution {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
      (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) → b ≤ WithZero.exp (-(n : ℤ))) → b ≤ a := by
    intro a b ha0 ha1 h
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log ha0, WithZero.exp_zero]
      exact ha1
    have hn : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
    have := h (-WithZero.log a).toNat (by rw [hn, neg_neg, WithZero.exp_log ha0])
    rwa [hn, neg_neg, WithZero.exp_log ha0] at this
  exact le_antisymm (key hb0 hb1 fun n => (h n).2) (key ha0 ha1 fun n => (h n).1)
end GroundTheory.ProfCoh
