-- Prove2me | solution 1 for LLLFactor.Reduction.case2_count_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:22:45.08603+00:00
-- url     : https://prove2.me/submissions/b3137581-a7c3-4dbe-8fa3-db3fe4955b0c

import Definitions.Def_LLLFactor_Reduction_Algorithm
open LLLFactor.Reduction

open Classical in
private lemma count_invariant {n : ℕ} (hn : 0 < n)
    (b : Fin n → LLLFactor.RedBasis.Vec n) (s : ℕ → State n)
    (hs0 : s 0 = (b, 2)) (T : ℕ) (hrun : ∀ t < T, Step (s t) (s (t + 1))) :
    ((Finset.range T).filter (fun t => Case2 (s t) (s (t + 1)))).card + 2 =
      ((Finset.range T).filter (fun t => Case1 (s t) (s (t + 1)))).card + (s T).2 ∧
      (s T).2 ≤ n + 1 := by
  classical
  induction T with
  | zero => simp [hs0]; omega
  | succ T ih =>
    obtain ⟨hi, hb⟩ := ih (fun t ht => hrun t (by omega))
    have hstep := hrun T (by omega)
    have hn1 : T ∉ (Finset.range T).filter (fun t => Case1 (s t) (s (t+1))) := by simp
    have hn2 : T ∉ (Finset.range T).filter (fun t => Case2 (s t) (s (t+1))) := by simp
    rcases hstep with h1 | h2
    · have hk := h1
      obtain ⟨h, c, ha, hc, he, hk⟩ := hk
      have hnot : ¬ Case2 (s T) (s (T+1)) := by
        rintro ⟨h', c', ha', hc', hl', hr', hk'⟩
        omega
      simp only [Finset.range_add_one, Finset.filter_insert, h1, hnot,
        if_true, if_false, Finset.card_insert_of_notMem hn1]
      constructor <;> omega
    · have hk := h2
      obtain ⟨h, c, ha, hc, hl, hr, hk⟩ := hk
      have hnot : ¬ Case1 (s T) (s (T+1)) := by
        rintro ⟨h', c', ha', hc', he', hk'⟩
        omega
      simp only [Finset.range_add_one, Finset.filter_insert, h2, hnot,
        if_true, if_false, Finset.card_insert_of_notMem hn2]
      constructor <;> omega

open Classical in
theorem solution {n : ℕ} (hn : 0 < n) (b : Fin n → LLLFactor.RedBasis.Vec n)
    (s : ℕ → State n) (T : ℕ) (hs0 : s 0 = (b, 2))
    (hrun : ∀ t < T, Step (s t) (s (t + 1))) :
    ((Finset.range T).filter (fun t => Case2 (s t) (s (t + 1)))).card ≤
      ((Finset.range T).filter (fun t => Case1 (s t) (s (t + 1)))).card + (n - 1) := by
  obtain ⟨hi, hb⟩ := count_invariant hn b s hs0 T hrun
  omega

#print axioms solution
