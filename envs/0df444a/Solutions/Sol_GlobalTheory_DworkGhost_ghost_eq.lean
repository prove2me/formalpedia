-- Prove2me | solution 1 for GlobalTheory.DworkGhost.ghost_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:31.14885+00:00
-- url     : https://prove2.me/submissions/f2240812-e9a1-4eee-a8a0-e8c0d36c764b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate
import Theorems.Thm_GlobalTheory_DworkGhost_coeff_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Finset
open GlobalTheory GlobalTheory.DworkGhost
namespace GlobalTheory.DworkGhost
theorem _root_.solution {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec
    rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))
end GlobalTheory.DworkGhost
