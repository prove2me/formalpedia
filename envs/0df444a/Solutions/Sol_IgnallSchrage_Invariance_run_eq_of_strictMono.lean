-- Prove2me | solution 1 for IgnallSchrage.Invariance.run_eq_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:05:30.457962+00:00
-- url     : https://prove2.me/submissions/3bdf07cd-142d-46f7-84cd-811ba031028b

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Procedure
open IgnallSchrage.Makespan

private def Good {n : ℕ} (P : List (Fin n)) : Prop :=
  P.Nodup ∧ 1 ≤ P.length ∧ P.length+1 ≤ n

private lemma insert_good {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n))
    (hx : Good x) (L : List (List (Fin n))) (hL : ∀ y ∈ L, Good y) :
    ∀ y ∈ insertNode LB x L, Good y := by
  induction L with
  | nil => simpa [insertNode] using hx
  | cons y ys ih =>
    have hy := hL y (by simp)
    have hys : ∀ z ∈ ys, Good z := fun z hz => hL z (by simp [hz])
    simp only [insertNode]
    split_ifs
    · simpa using (show ∀ z ∈ x::y::ys, Good z from by simpa using ⟨hx, hy, hys⟩)
    · simpa using (show Good y ∧ (∀ z ∈ insertNode LB x ys, Good z) from ⟨hy, ih hys⟩)

private lemma insert_eq {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ) (h : ∀ P, Good P → LB' P = φ (LB P))
    (x : List (Fin n)) (hx : Good x) (L : List (List (Fin n))) (hL : ∀ y ∈ L, Good y) :
    insertNode LB' x L = insertNode LB x L := by
  induction L with
  | nil => rfl
  | cons y ys ih =>
    have hy := hL y (by simp)
    have hys : ∀ z ∈ ys, Good z := fun z hz => hL z (by simp [hz])
    simp only [insertNode, h x hx, h y hy, hφ.le_iff_le]
    split_ifs <;> simp [ih hys]

private lemma fold_eq {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ) (h : ∀ P, Good P → LB' P = φ (LB P))
    (C L : List (List (Fin n))) (hC : ∀ x ∈ C, Good x) (hL : ∀ y ∈ L, Good y) :
    C.foldl (fun L x => insertNode LB' x L) L = C.foldl (fun L x => insertNode LB x L) L ∧
    (∀ y ∈ C.foldl (fun L x => insertNode LB x L) L, Good y) := by
  induction C generalizing L with
  | nil => exact ⟨rfl, hL⟩
  | cons x xs ih =>
    have hx := hC x (by simp)
    have hxs : ∀ y ∈ xs, Good y := fun y hy => hC y (by simp [hy])
    simp only [List.foldl_cons]
    rw [insert_eq LB LB' φ hφ h x hx L hL]
    exact ih _ hxs (insert_good LB x hx L hL)

private lemma children_good {n : ℕ} (P : List (Fin n)) (hp : P.Nodup)
    (hlen : P.length+2 ≤ n) : ∀ x ∈ children P, Good x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hnot : j ∉ P := by simpa using (List.mem_filter.mp hj).2
  refine ⟨?_, ?_, ?_⟩
  · simpa using hp.concat hnot
  · simp
  · simp only [List.length_append, List.length_singleton]; omega

private lemma step_eq {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ) (h : ∀ P, Good P → LB' P = φ (LB P))
    (L : List (List (Fin n))) (hL : L = [[]] ∨ ∀ y ∈ L, Good y) :
    step LB' L = step LB L ∧ (step LB L = [[]] ∨ ∀ y ∈ step LB L, Good y) := by
  rcases hL with rfl | hL
  · by_cases hn : n = 1
    · simp [step, IsTerminal, hn]
    · have hroot : ¬ IsTerminal ([] : List (Fin n)) := by simpa [IsTerminal, eq_comm] using hn
      rw [step, step, if_neg hroot, if_neg hroot]
      by_cases hn0 : n = 0
      · subst n
        simp [children]
      · have hc := children_good ([] : List (Fin n)) (by simp) (by simp; omega)
        obtain ⟨he, hg⟩ := fold_eq LB LB' φ hφ h (children []) [] hc (by simp)
        exact ⟨he, Or.inr hg⟩
  · cases L with
    | nil => simp [step]
    | cons P rest =>
      have hp := hL P (by simp)
      have hr : ∀ y ∈ rest, Good y := fun y hy => hL y (by simp [hy])
      by_cases ht : IsTerminal P
      · simp only [step, if_pos ht]
        exact ⟨trivial, Or.inr hL⟩
      · have hlen : P.length+2 ≤ n := by have := hp.2.2; unfold IsTerminal at ht; omega
        have hc := children_good P hp.1 hlen
        obtain ⟨he,hg⟩ := fold_eq LB LB' φ hφ h (children P) rest hc hr
        simp only [step, if_neg ht]
        exact ⟨he, Or.inr hg⟩

theorem solution {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ)
    (h : ∀ J : List (Fin n), J.Nodup → 1 ≤ J.length → J.length + 1 ≤ n → LB' J = φ (LB J)) :
    ∀ k : ℕ, IgnallSchrage.Makespan.run LB' k = IgnallSchrage.Makespan.run LB k := by
  have hh : ∀ P, Good P → LB' P = φ (LB P) := fun P hp => h P hp.1 hp.2.1 hp.2.2
  have hi : ∀ k, run LB' k = run LB k ∧ (run LB k = [[]] ∨ ∀ y ∈ run LB k, Good y) := by
    intro k
    induction k with
    | zero => simp [run]
    | succ k ih =>
      simp only [run, Function.iterate_succ_apply'] at ih ⊢
      rw [ih.1]
      exact step_eq LB LB' φ hφ hh _ ih.2
  exact fun k => (hi k).1

#print axioms solution
