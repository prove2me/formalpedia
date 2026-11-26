-- Prove2me | solution 1 for LayeredTransitionAudit.equality_midpoint_width
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:58:52.435539+00:00
-- url     : https://prove2.me/submissions/8e9c1aac-fec6-4251-b679-4c05ae29b76f

import Definitions.Def_LayeredTransitionAudit

set_option autoImplicit false

namespace LayeredTransitionAudit

variable {Q A : Type*} [DecidableEq Q]

omit [DecidableEq Q] in
theorem run_append (step : ℕ → Q → A → Q) (i : ℕ) (q : Q) (u v : List A) :
    run step i q (u ++ v) = run step (i + u.length) (run step i q u) v := by
  induction u generalizing i q with
  | nil => simp [run]
  | cons a u ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    rw [show i + (u.length + 1) = i + 1 + u.length by omega]

omit [DecidableEq Q] in
theorem acceptsWord_append (allowed : ℕ → Finset A) (i : ℕ) (u v : List A) :
    acceptsWord allowed i (u ++ v) ↔
      acceptsWord allowed i u ∧ acceptsWord allowed (i + u.length) v := by
  induction u generalizing i with
  | nil => simp [acceptsWord]
  | cons a u ih =>
    simp only [List.cons_append, acceptsWord, ih, List.length_cons]
    rw [show i + (u.length + 1) = i + 1 + u.length by omega, and_assoc]

theorem mem_reachable_iff (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q)
    (root : Q) (i : ℕ) (q : Q) :
    q ∈ reachable allowed step root i ↔
      ∃ word : List A, word.length = i ∧ acceptsWord allowed 0 word ∧
        run step 0 root word = q := by
  induction i generalizing q with
  | zero => simp [reachable, run, acceptsWord, eq_comm]
  | succ i ih =>
    simp only [reachable, successor, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, a, ha, rfl⟩
      obtain ⟨word, width, good, finish⟩ := (ih p).mp hp
      refine ⟨word ++ [a], by simp [width], ?_, ?_⟩
      · rw [acceptsWord_append]
        exact ⟨good, by simpa [acceptsWord, width] using ha⟩
      · simp [run_append, width, finish, run]
    · rintro ⟨word, width, good, finish⟩
      have nonempty : word ≠ [] := by
        intro h
        simp [h] at width
      obtain ⟨earlier, a, rfl⟩ := List.eq_nil_or_concat' word |>.resolve_left nonempty
      have prefixWidth : earlier.length = i := by simpa using width
      obtain ⟨prefixGood, lastGood⟩ := (acceptsWord_append allowed 0 earlier [a]).mp good
      refine ⟨run step 0 root earlier,
        (ih _).mpr ⟨earlier, prefixWidth, prefixGood, rfl⟩, a, ?_, ?_⟩
      · simpa [acceptsWord, prefixWidth] using lastGood
      · simpa [run_append, run, prefixWidth] using finish

end LayeredTransitionAudit

open LayeredTransitionAudit

theorem solution {Q : Type*} [DecidableEq Q]
    (width : ℕ) (step : ℕ → Q → Bool → Q) (root : Q) (output : Q → Bool)
    (correct : ∀ x y : Fin width → Bool,
      output (run step 0 root (List.ofFn x ++ List.ofFn y)) = decide (x = y)) :
    2^width ≤ (reachable (fun _ => Finset.univ) step root width).card := by
  let midpoint (x : Fin width → Bool) := run step 0 root (List.ofFn x)
  have different : Function.Injective midpoint := by
    intro x y equalState
    have sameWithX := correct x x
    have tryWithX := correct y x
    simp only [run_append, List.length_ofFn, Nat.zero_add, decide_true] at sameWithX
    simp only [run_append, List.length_ofFn, Nat.zero_add] at tryWithX
    change output (run step width (midpoint x) (List.ofFn x)) = true at sameWithX
    change output (run step width (midpoint y) (List.ofFn x)) = decide (y = x) at tryWithX
    rw [← equalState, sameWithX] at tryWithX
    exact (of_decide_eq_true tryWithX.symm).symm
  have unrestricted (i : ℕ) (w : List Bool) : acceptsWord (fun _ => Finset.univ) i w := by
    induction w generalizing i with
    | nil => trivial
    | cons a w ih => exact ⟨Finset.mem_univ a, ih _⟩
  have included : Finset.univ.image midpoint ⊆ reachable (fun _ => Finset.univ) step root width := by
    intro q present
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp present
    exact (mem_reachable_iff _ _ _ _ _).mpr
      ⟨List.ofFn x, List.length_ofFn, unrestricted 0 _, rfl⟩
  have many : (Finset.univ.image midpoint).card = 2^width := by
    rw [Finset.card_image_of_injective _ different]
    simp
  exact many ▸ Finset.card_le_card included

#print axioms solution
