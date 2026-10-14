-- Prove2me | solution 1 for ManneLP.Equilibrium.terminal_law_eq_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:46:31.489369+00:00
-- url     : https://prove2.me/submissions/0da495e6-f6ed-4398-b402-2ce7578625b3

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP



namespace ManneLP.Equilibrium

open Classical in
lemma sum_states_actions (M : Model) (f : ℕ × ℕ → ℝ) :
    ∑ i ∈ states M, ∑ j ∈ actions M i, f (i, j) = ∑ a ∈ M.A, f a := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun s _ => (s.1, s.2)) (fun a _ => ⟨a.1, a.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_sigma, actions, states, Finset.mem_filter, Finset.mem_range] at hs
    exact hs.2.2
  · intro a ha
    have := M.A_le a ha
    simp only [Finset.mem_sigma, actions, states, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ha⟩
  · intro s _; rfl
  · intro a _; rfl
  · intro s _; rfl

lemma termProb_summable (M : Model) (k t : ℕ) :
    Summable (fun n : ℕ => if k - n = t then M.p n else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) M.p_hasSum.summable
  · split_ifs
    · exact M.p_nonneg n
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact M.p_nonneg n

lemma lhs_eq (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ states M, y i * trans M q i t =
      ∑ a ∈ M.A, ∑' n : ℕ, if a.1 + a.2 - n = t then M.p n * (y a.1 * q a.1 a.2) else 0 := by
  have h1 : ∑ i ∈ states M, y i * trans M q i t =
      ∑ i ∈ states M, ∑ j ∈ actions M i, y i * q i j * termProb M (i + j) t := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold trans
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h1, sum_states_actions M (fun a => y a.1 * q a.1 a.2 * termProb M (a.1 + a.2) t)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  unfold termProb
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  split_ifs <;> ring

theorem terminal_law_core (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    ∑ i ∈ states M, y i * trans M q i 0 = rhsZero M (jointLaw y q) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ M.T →
      ∑ i ∈ states M, y i * trans M q i t = rhsPos M (jointLaw y q) t := by
  refine ⟨?_, fun t ht _ => ?_⟩
  · rw [lhs_eq]
    unfold rhsZero jointLaw
    refine Finset.sum_congr rfl (fun a _ => tsum_congr (fun n => ?_))
    have : (a.1 + a.2 - n = 0) ↔ ((a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) ≤ 0) := by omega
    by_cases h : a.1 + a.2 - n = 0
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  · rw [lhs_eq]
    unfold rhsPos jointLaw
    refine Finset.sum_congr rfl (fun a _ => tsum_congr (fun n => ?_))
    have : (a.1 + a.2 - n = t) ↔ ((a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ)) := by omega
    by_cases h : a.1 + a.2 - n = t
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

theorem equil_core (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ)
    (hq : IsRule M q) (hy : IsEquilibrium M q y) :
    (∀ a ∈ M.A, 0 ≤ jointLaw y q a) ∧ ∑ a ∈ M.A, jointLaw y q a = 1 ∧
      Eq80 M (jointLaw y q) ∧ ∀ t : ℕ, 1 ≤ t → t ≤ M.T → Eq8t M (jointLaw y q) t := by
  obtain ⟨hq0, hqA, hq1⟩ := hq
  obtain ⟨hy0, hy1, hyt⟩ := hy
  have hT := terminal_law_core M q y
  have hmarg : ∀ t, t ≤ M.T → marginal M (jointLaw y q) t = y t := by
    intro t ht
    unfold marginal jointLaw
    simp only
    rw [← Finset.mul_sum, hq1 t ht, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have := M.A_le a ha
    exact mul_nonneg (hy0 _ (by omega)) (hq0 _ _)
  · rw [← sum_states_actions M (jointLaw y q)]
    have : ∀ i ∈ states M, ∑ j ∈ actions M i, jointLaw y q (i, j) = y i := by
      intro i hi
      have := hmarg i (by simp [states] at hi; omega)
      exact this
    rw [Finset.sum_congr rfl this]
    exact hy1
  · unfold Eq80
    rw [hmarg 0 M.T_pos.le, ← hT.1]
    exact hyt 0 M.T_pos.le
  · intro t ht1 ht2
    unfold Eq8t
    rw [hmarg t ht2, ← hT.2 t ht1 ht2]
    exact hyt t ht2

end ManneLP.Equilibrium

open ManneLP.Equilibrium


theorem solution (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    ∑ i ∈ states M, y i * trans M q i 0 = rhsZero M (jointLaw y q) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ M.T →
      ∑ i ∈ states M, y i * trans M q i t = rhsPos M (jointLaw y q) t := by
  exact terminal_law_core M q y
