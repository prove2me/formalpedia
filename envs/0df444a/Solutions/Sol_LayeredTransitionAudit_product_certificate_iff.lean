-- Prove2me | solution 1 for LayeredTransitionAudit.product_certificate_iff
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:54:18.096301+00:00
-- url     : https://prove2.me/submissions/7e9b5ab5-007d-4712-b26d-778020618c09

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

theorem reachable_le_layers (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q)
    (root : Q) (width : ℕ) (layers : ℕ → Finset Q)
    (root_mem : root ∈ layers 0)
    (closed : ∀ i < width, successor allowed step i (layers i) ⊆ layers (i + 1))
    (i : ℕ) (within : i ≤ width) : reachable allowed step root i ⊆ layers i := by
  induction i with
  | zero => simpa [reachable]
  | succ i ih =>
    intro q h
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hap
    have pListed := ih (by omega) hp
    apply closed i (by omega)
    exact Finset.mem_biUnion.mpr ⟨p,pListed,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩

theorem closed_iff_every_admissible_word (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q)
    (root : Q) (width : ℕ) (valid : Q → Prop) :
    (∃ layers : ℕ → Finset Q, ClosedLayers allowed step root width layers valid) ↔
    (∀ word : List A, word.length = width → acceptsWord allowed 0 word →
      valid (run step 0 root word)) := by
  constructor
  · rintro ⟨layers, init, closed, ending⟩ word len permitted
    apply ending _ (reachable_le_layers allowed step root width layers init closed width le_rfl _)
    exact (mem_reachable_iff allowed step root width _).mpr ⟨word,len,permitted,rfl⟩
  · intro validWords
    refine ⟨reachable allowed step root, by simp [reachable], fun _ _ => Finset.Subset.rfl, ?_⟩
    intro q reached
    obtain ⟨w,length,good,rfl⟩ := (mem_reachable_iff allowed step root width q).mp reached
    exact validWords w length good

/-- A layered audit never needs more state mentions than one copy of the
finite state space per layer. -/
theorem bounded_closed_iff_every_admissible_word [Fintype Q] (allowed : ℕ → Finset A)
    (step : ℕ → Q → A → Q) (root : Q) (width : ℕ) (valid : Q → Prop) :
    (∃ layers : ℕ → Finset Q, ClosedLayers allowed step root width layers valid ∧
      (∑ i ∈ Finset.range (width + 1), (layers i).card) ≤ (width + 1) * Fintype.card Q) ↔
    (∀ word : List A, word.length = width → acceptsWord allowed 0 word →
      valid (run step 0 root word)) := by
  rw [← closed_iff_every_admissible_word]
  constructor
  · rintro ⟨layers, closed, _⟩
    exact ⟨layers, closed⟩
  · rintro ⟨layers, closed⟩
    refine ⟨layers, closed, ?_⟩
    calc
      _ ≤ ∑ _i ∈ Finset.range (width + 1), Fintype.card Q :=
        Finset.sum_le_sum (fun _ _ => Finset.card_le_univ _)
      _ = _ := by simp

theorem verify_iff [DecidableEq A] (allowed : ℕ → List A) (step : ℕ → Q → A → Q)
    (root : Q) (width : ℕ) (layers : ℕ → List Q) (valid : Q → Bool) :
    verify allowed step root width layers valid = true ↔
      ClosedLayers (fun i => (allowed i).toFinset) step root width
        (fun i => (layers i).toFinset) (fun q => valid q = true) := by
  unfold verify ClosedLayers successor
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_toFinset, and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro check i hi state present
    obtain ⟨fromState, beforeState, member⟩ := Finset.mem_biUnion.mp present
    obtain ⟨symbol, allowedSymbol, rfl⟩ := Finset.mem_image.mp member
    exact List.mem_toFinset.mpr (check i hi fromState (List.mem_toFinset.mp beforeState) symbol
      (List.mem_toFinset.mp allowedSymbol))
  · intro closed i hi state beforeState symbol allowedSymbol
    exact List.mem_toFinset.mp (closed i hi (Finset.mem_biUnion.mpr
      ⟨state, List.mem_toFinset.mpr beforeState,
        Finset.mem_image.mpr ⟨symbol, List.mem_toFinset.mpr allowedSymbol, rfl⟩⟩))

section Product

variable {Left Right : Type*}

omit [DecidableEq Q] in
theorem run_product (left : ℕ → Left → A → Left) (right : ℕ → Right → A → Right)
    (i : ℕ) (p : Left) (q : Right) (word : List A) :
    run (productStep left right) i (p,q) word = (run left i p word, run right i q word) := by
  induction word generalizing i p q with
  | nil => rfl
  | cons a tail ih => exact ih _ _ _

end Product

end LayeredTransitionAudit

open LayeredTransitionAudit

theorem solution {A Left Right Value : Type*}
    [DecidableEq Left] [Fintype Left] [DecidableEq Right] [Fintype Right]
    (allowed : ℕ → Finset A) (left : ℕ → Left → A → Left)
    (right : ℕ → Right → A → Right) (p : Left) (q : Right) (width : ℕ)
    (readLeft : Left → Value) (readRight : Right → Value) :
    (∃ layers : ℕ → Finset (Left × Right),
      ClosedLayers allowed (productStep left right) (p,q) width layers
        (fun s => readLeft s.1 = readRight s.2) ∧
      (∑ i ∈ Finset.range (width + 1), (layers i).card) ≤
        (width + 1) * (Fintype.card Left * Fintype.card Right)) ↔
    (∀ word : List A, word.length = width → acceptsWord allowed 0 word →
      readLeft (run left 0 p word) = readRight (run right 0 q word)) := by
  simpa only [Fintype.card_prod, LayeredTransitionAudit.run_product] using
    LayeredTransitionAudit.bounded_closed_iff_every_admissible_word allowed (productStep left right) (p,q) width
      (fun s => readLeft s.1 = readRight s.2)


#print axioms solution
