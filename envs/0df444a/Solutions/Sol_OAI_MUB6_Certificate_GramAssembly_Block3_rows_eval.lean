-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T18:45:38.382656+00:00
-- url     : https://prove2.me/submissions/1f4759e9-0b04-40fa-88c8-0a3123e0dfcb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D142

inductive SolBT where
  | nil : SolBT
  | leaf (z : ℤ) : SolBT
  | node (l r : SolBT) : SolBT

def SolBT.get : ℕ → ℕ → SolBT → ℤ
  | 0, _, .leaf z => z
  | d+1, k, .node l r => if k % 2 = 0 then SolBT.get d (k / 2) l else SolBT.get d (k / 2) r
  | _, _, _ => 0

def SolBT.ins : ℕ → ℕ → ℤ → SolBT → SolBT
  | 0, _, z, .leaf a => .leaf (a + z)
  | 0, _, z, _ => .leaf z
  | d+1, k, z, .node l r =>
      if k % 2 = 0 then .node (SolBT.ins d (k / 2) z l) r else .node l (SolBT.ins d (k / 2) z r)
  | d+1, k, z, _ =>
      if k % 2 = 0 then .node (SolBT.ins d (k / 2) z .nil) .nil else .node .nil (SolBT.ins d (k / 2) z .nil)

def SolBT.allZ : SolBT → Bool
  | .nil => true
  | .leaf z => z == 0
  | .node l r => SolBT.allZ l && SolBT.allZ r

theorem SolBT.get_nil (d k : ℕ) : SolBT.get d k .nil = 0 := by
  cases d <;> rfl

theorem SolBT.get_ins (d : ℕ) : ∀ (k k' : ℕ) (z : ℤ) (t : SolBT), k < 2 ^ d → k' < 2 ^ d →
    SolBT.get d k' (SolBT.ins d k z t) = SolBT.get d k' t + (if k' = k then z else 0) := by
  induction d with
  | zero =>
    intro k k' z t hk hk'
    have h1 : k = 0 := by simpa using hk
    have h2 : k' = 0 := by simpa using hk'
    subst h1; subst h2
    cases t <;> simp [SolBT.ins, SolBT.get]
  | succ d ih =>
    intro k k' z t hk hk'
    have hk2 : k / 2 < 2 ^ d := by rw [pow_succ] at hk; omega
    have hk2' : k' / 2 < 2 ^ d := by rw [pow_succ] at hk'; omega
    have key : (k' = k) ↔ (k' % 2 = k % 2 ∧ k' / 2 = k / 2) := by omega
    have hn : ∀ l r : SolBT, SolBT.get (d+1) k' (.node l r) =
        if k' % 2 = 0 then SolBT.get d (k' / 2) l else SolBT.get d (k' / 2) r := fun _ _ => rfl
    have h0 : ∀ u : SolBT, (∀ l r, u ≠ .node l r) → SolBT.get (d+1) k' u = 0 := by
      intro u hu; cases u with
      | nil => rfl
      | leaf _ => rfl
      | node l r => exact absurd rfl (hu l r)
    have hins : SolBT.ins (d+1) k z t = (match t with
        | .node l r => if k % 2 = 0 then .node (SolBT.ins d (k / 2) z l) r else .node l (SolBT.ins d (k / 2) z r)
        | _ => if k % 2 = 0 then .node (SolBT.ins d (k / 2) z .nil) .nil else .node .nil (SolBT.ins d (k / 2) z .nil)) := by
      cases t <;> rfl
    rw [hins]
    cases t with
    | node l r =>
      simp only [hn]
      by_cases hk0 : k % 2 = 0 <;> by_cases hk0' : k' % 2 = 0 <;> simp only [hk0, hk0', if_true, if_false, hn, ih _ _ _ _ hk2 hk2', key] <;> split_ifs <;> first | rfl | omega | simp_all
    | nil =>
      rw [h0 .nil (by intros; simp)]
      by_cases hk0 : k % 2 = 0 <;> by_cases hk0' : k' % 2 = 0 <;> simp only [hk0, hk0', if_true, if_false, hn, ih _ _ _ _ hk2 hk2', SolBT.get_nil, key] <;> split_ifs <;> first | rfl | omega | simp_all
    | leaf a =>
      rw [h0 (.leaf a) (by intros; simp)]
      by_cases hk0 : k % 2 = 0 <;> by_cases hk0' : k' % 2 = 0 <;> simp only [hk0, hk0', if_true, if_false, hn, ih _ _ _ _ hk2 hk2', SolBT.get_nil, key] <;> split_ifs <;> first | rfl | omega | simp_all

theorem SolBT.get_allZ : ∀ (d k : ℕ) (t : SolBT), SolBT.allZ t = true → SolBT.get d k t = 0 := by
  intro d; induction d with
  | zero => intro k t h; cases t <;> simp_all [SolBT.allZ, SolBT.get]
  | succ d ih =>
    intro k t h; cases t with
    | nil => rfl
    | leaf _ => rfl
    | node l r =>
      simp only [SolBT.allZ, Bool.and_eq_true] at h
      show (if k % 2 = 0 then SolBT.get d (k / 2) l else SolBT.get d (k / 2) r) = 0
      split_ifs
      · exact ih _ _ h.1
      · exact ih _ _ h.2

namespace OAI.MUB6.Certificate

open scoped BigOperators

def solBuild {n : ℕ} (L : Integer.Sparse (Fin n)) : SolBT :=
  L.foldr (fun p t => SolBT.ins 12 p.1.val p.2 t) .nil

theorem solBuild_get {n : ℕ} (hn : n ≤ 4096) (L : Integer.Sparse (Fin n)) (i : Fin n) :
    SolBT.get 12 i.val (solBuild L) = Integer.Sparse.coeff L i := by
  induction L with
  | nil => simp [solBuild, SolBT.get_nil]
  | cons p L ih =>
    have h1 : p.1.val < 2 ^ 12 := by have := p.1.isLt; norm_num; omega
    have h2 : i.val < 2 ^ 12 := by have := i.isLt; norm_num; omega
    have : solBuild (p :: L) = SolBT.ins 12 p.1.val p.2 (solBuild L) := rfl
    rw [this, SolBT.get_ins _ _ _ _ _ h1 h2, ih, Integer.Sparse.coeff_cons, add_comm]
    congr 1
    by_cases h : p.1 = i
    · subst h; simp
    · have : i.val ≠ p.1.val := fun e => h (Fin.ext e.symm)
      simp [h, this]

theorem sol_eval_sum {n : ℕ} (v : Integer.Sparse (Fin n)) (x : Fin n → ℝ) :
    Integer.Sparse.eval v x = ∑ i, (Integer.Sparse.coeff v i : ℝ) * x i := by
  induction v with
  | nil => simp
  | cons p v ih =>
    rw [Integer.Sparse.eval_cons, ih]
    simp only [Integer.Sparse.coeff_cons, Int.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    simp [apply_ite (fun z : ℤ => (z : ℝ)), ite_mul]

theorem sol_eval_zero {n : ℕ} (hn : n ≤ 4096) (L : Integer.Sparse (Fin n))
    (h : SolBT.allZ (solBuild L) = true) (x : Fin n → ℝ) : Integer.Sparse.eval L x = 0 := by
  rw [sol_eval_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← solBuild_get hn, SolBT.get_allZ _ _ _ h]
  simp

theorem sol_eval_flatMap {n m : ℕ} (l : List (Fin m)) (f : Fin m → Integer.Sparse (Fin n))
    (x : Fin n → ℝ) :
    Integer.Sparse.eval (l.flatMap f) x = (l.map fun j => Integer.Sparse.eval (f j) x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sol_row {n m : ℕ} (hn : n ≤ 4096) (a : Integer.Sparse (Fin n)) (w : Fin m → ℤ)
    (e : Fin m → Integer.Sparse (Fin n))
    (h : SolBT.allZ (solBuild (a ++ (List.finRange m).flatMap
      (fun j => Integer.Sparse.scale (-w j) (e j)))) = true) (x : Fin n → ℝ) :
    Integer.Sparse.eval a x = ∑ j, (w j : ℝ) * Integer.Sparse.eval (e j) x := by
  have := sol_eval_zero hn _ h x
  rw [Integer.Sparse.eval_append, sol_eval_flatMap] at this
  rw [Fin.sum_univ_def]
  have hs : ((List.finRange m).map fun j => Integer.Sparse.eval (Integer.Sparse.scale (-w j) (e j)) x).sum
      = -((List.finRange m).map fun j => (w j : ℝ) * Integer.Sparse.eval (e j) x).sum := by
    induction (List.finRange m) with
    | nil => simp
    | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Integer.Sparse.eval_scale]; push_cast; ring
  rw [hs] at this
  linarith

end OAI.MUB6.Certificate

open OAI OAI.MUB6.Certificate OAI.MUB6.Certificate.GramAssembly.Block3 in
theorem solution (i : Fin 27) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 27, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  revert x
  fin_cases i <;> exact sol_row (by norm_num) _ _ _ (by decide +kernel)
