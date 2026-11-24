-- Prove2me | solution 1 for GlobalTheory.phiEq_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:06.20752+00:00
-- url     : https://prove2.me/submissions/ac29ee04-70a2-4ff5-a485-53efe5c76913

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPow

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [ExpChar R l] (u : R)
    (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ)
    (hD : ∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) (k : ℕ) :
    ∃ a : ℕ, a + h ≤ h * l ^ k ∧ ∃ e : κ → κ → R,
      ∀ j, u ^ a * D j = ∑ i, D i ^ (l ^ k) * e i j := by
  classical
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  induction k with
  | zero =>
    refine ⟨0, by simp, fun i j => if i = j then 1 else 0, fun j => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨a, ha, e, he⟩ := ih
    refine ⟨h + l * a, ?_, fun i' j => ∑ i, e i' i ^ l * c i j, fun j => ?_⟩
    · have h1 : l * (a + h) ≤ l * (h * l ^ k) := Nat.mul_le_mul_left _ ha
      have h2 : 2 * h ≤ l * h := Nat.mul_le_mul_right _ hl2
      calc h + l * a + h = 2 * h + l * a := by ring
        _ ≤ l * h + l * a := by omega
        _ = l * (a + h) := by ring
        _ ≤ l * (h * l ^ k) := h1
        _ = h * l ^ (k + 1) := by ring
    · calc u ^ (h + l * a) * D j = ∑ i, (u ^ a * D i) ^ l * c i j := by
            rw [pow_add, mul_comm (u ^ h) (u ^ (l * a)), mul_assoc, hD j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, ← pow_mul, mul_comm a l]; ring
        _ = ∑ i, (∑ i', D i' ^ (l ^ k) * e i' i) ^ l * c i j := by
            simp only [he]
        _ = ∑ i, ∑ i', D i' ^ (l ^ (k + 1)) * (e i' i ^ l * c i j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sum_pow_char, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [mul_pow, ← pow_mul, pow_succ]; ring
        _ = ∑ i', D i' ^ (l ^ (k + 1)) * ∑ i, e i' i ^ l * c i j := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
end GlobalTheory
