-- Prove2me | solution 1 for GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:52.819899+00:00
-- url     : https://prove2.me/submissions/45ce0b3c-de74-470a-be38-66004ce65d43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GhostComponentInjectiveOfNoTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
namespace WittVector
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn
    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]
end WittVector
end GlobalTheory
