-- Prove2me | solution 1 for GlobalTheory.orderOf_transvectionUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:40.734926+00:00
-- url     : https://prove2.me/submissions/52e4fb18-a9c5-4825-8759-b8802ad8d4ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Theorems.Thm_GlobalTheory_transvectionUnit_pow_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (q : ℕ) [CharP R q] {r : ℕ}
    {i j : Fin r} (h : i ≠ j) : orderOf (transvectionUnit (R := R) h) = q := by
  have key : ∀ n : ℕ, orderOf (transvectionUnit (R := R) h) ∣ n ↔ q ∣ n := by
    intro n
    rw [orderOf_dvd_iff_pow_eq_one, ← CharP.cast_eq_zero_iff R q n, Units.ext_iff,
      transvectionUnit_pow_val, Units.val_one]
    constructor
    · intro hn
      have := congrFun (congrFun hn i) j
      simpa [transvection, one_apply_ne h] using this
    · intro hn
      rw [hn, transvection_zero]
  exact Nat.dvd_antisymm ((key q).2 dvd_rfl) ((key _).1 dvd_rfl)
end GlobalTheory
