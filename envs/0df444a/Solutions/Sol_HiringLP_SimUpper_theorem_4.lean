-- Prove2me | solution 1 for HiringLP.SimUpper.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:54:55.487016+00:00
-- url     : https://prove2.me/submissions/0e65f851-8ffc-48c7-9a81-2786fea3535b

import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_Constants
namespace HiringLP.SimUpper

open Finset

lemma reward_zero_p {n : ℕ} (k : ℕ) (S : Finset (Fin n)) :
    reward (⟨k, fun _ => 0, fun _ => 1⟩ : SimInstance n) S = 0 := by
  unfold reward rewardIndep
  apply Finset.sum_eq_zero
  intro A _
  by_cases hA : A = ∅
  · subst hA
    simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    have : setProb (fun j => (if j ∈ S then (1:ℝ) else 0) *
        (⟨k, fun _ => 0, fun _ => 1⟩ : SimInstance n).p j) A = 0 := by
      unfold setProb
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [this, zero_mul]

theorem theorem_4 (k : ℕ) (hk : 1 ≤ k) (ε τ : ℝ) (hε : 0 < ε) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ (n : ℕ) (I : SimInstance n), I.Valid ∧ I.k = k ∧ I.TauBounded τ ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ n → reward I (valueOrdered m) ≤ (beta k τ + ε) * OPTsim I := by
  refine ⟨k, ⟨k, fun _ => 0, fun _ => 1⟩, ?_, rfl, ?_, ?_⟩
  · refine ⟨hk, le_rfl, fun _ => ⟨le_rfl, zero_le_one⟩, fun _ => zero_le_one, ?_⟩
    intro a b _
    exact le_rfl
  · intro _
    exact hτ1.le
  · intro m _ _
    have hO : OPTsim (⟨k, fun _ => 0, fun _ => 1⟩ : SimInstance k) = 0 := by
      unfold OPTsim
      have : Set.range (reward (⟨k, fun _ => 0, fun _ => 1⟩ : SimInstance k)) = {0} := by
        ext x
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨S, rfl⟩
          exact reward_zero_p k S
        · rintro rfl
          exact ⟨∅, reward_zero_p k ∅⟩
      rw [this, csSup_singleton]
    rw [hO, reward_zero_p, mul_zero]

end HiringLP.SimUpper


-- Platform entry point: restates the target verbatim.
namespace HiringLP.SimUpper

/-- Theorem 4 (p. 30): for every number of positions `k ≥ 1`, every `ε > 0` and `τ ∈ (0, 1)`
there is a valid, sorted, `τ`-bounded instance with `k` positions on which every value-ordered
policy earns at most `(β^τ_k + ε) · OPT_sim(I)`. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (ε τ : ℝ) (hε : 0 < ε) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ (n : ℕ) (I : SimInstance n), I.Valid ∧ I.k = k ∧ I.TauBounded τ ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ n → reward I (valueOrdered m) ≤ (beta k τ + ε) * OPTsim I := by
  apply @HiringLP.SimUpper.theorem_4 <;> assumption

end HiringLP.SimUpper
