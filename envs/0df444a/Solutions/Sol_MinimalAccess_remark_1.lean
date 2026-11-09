-- Prove2me | solution 1 for MinimalAccess.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:39:19.168625+00:00
-- url     : https://prove2.me/submissions/16ffe298-e03a-44d5-ab7e-91d62047545b

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities

open GaleShapley1962.Admissions

open MinimalAccess in
theorem solution {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) :
    (∀ (μ : Assignment n m) (i : Fin n),
      HasJustifiedMaxEnvy P pri r μ i ↔ HasClassicalEnvy P (adjKey pri r) μ i) ∧
    (∀ μ : Assignment n m, IsStable q P pri r μ ↔ IsClassicallyStable q P (adjKey pri r) μ) := by
  have key_iff : ∀ (s : Fin m) (i j : Fin n),
      ((s ∉ r i ∧ s ∉ r j ∧ pri s i < pri s j) ∨ (s ∈ r i ∧ s ∈ r j ∧ pri s i < pri s j) ∨
        (s ∈ r i ∧ s ∉ r j)) ↔ adjKey pri r s i < adjKey pri r s j := by
    intro s i j
    unfold adjKey
    simp only [Fin.lt_iff_val_lt_val]
    have hi := (pri s i).isLt
    have hj := (pri s j).isLt
    by_cases hsi : s ∈ r i <;> by_cases hsj : s ∈ r j <;> simp [hsi, hsj] <;> omega
  have h1 : ∀ (μ : Assignment n m) (i : Fin n),
      HasJustifiedMaxEnvy P pri r μ i ↔ HasClassicalEnvy P (adjKey pri r) μ i := by
    intro μ i
    unfold HasJustifiedMaxEnvy HasClassicalEnvy MaxEnvyAt
    exact exists_congr fun j => exists_congr fun s =>
      and_congr Iff.rfl (and_congr Iff.rfl (key_iff s i j))
  refine ⟨h1, fun μ => ?_⟩
  unfold MinimalAccess.IsStable MinimalAccess.IsClassicallyStable
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => not_congr (h1 μ i)))
