-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.val_other_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:56.197042+00:00
-- url     : https://prove2.me/submissions/6997a770-221b-4c1a-b010-89e06eb40a0b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Theorems.Thm_GlobalTheory_RadiiIdentities_val_natCast_nonneg
import Theorems.Thm_GlobalTheory_RadiiIdentities_val_intCast_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution : ValOther := by
  intro C _ v l hl hvl p hp hpl
  refine le_antisymm ?_ (val_natCast_nonneg v p)
  by_contra hlt
  rw [not_le] at hlt
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 (Ne.symm hpl)
  have hbez : ((1 : ℤ) : C) = ((l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p : ℤ) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    simp
  push_cast at hbez
  have hA : (0 : WithTop ℝ) < v ((l : C) * (Nat.gcdA l p : C)) := by
    rw [AddValuation.map_mul, hvl]
    exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1))
      (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hB : (0 : WithTop ℝ) < v ((p : C) * (Nat.gcdB l p : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hsum := AddValuation.map_add v ((l : C) * (Nat.gcdA l p : C)) ((p : C) * (Nat.gcdB l p : C))
  rw [← hbez, AddValuation.map_one] at hsum
  exact absurd (lt_of_lt_of_le (lt_min hA hB) hsum) (lt_irrefl 0)
end GlobalTheory.RadiiIdentities
