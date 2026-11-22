-- Prove2me | solution 1 for LatinQuarter.corner_forcing_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:08.115871+00:00
-- url     : https://prove2.me/submissions/f0028313-a82e-43cb-8c7d-88e642bf871b

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
public import Theorems.Thm_LatinQuarter_cyclic_isLatin
public import Theorems.Thm_LatinQuarter_mem_cornerSet
public import Theorems.Thm_LatinQuarter_fillingOrder_row
public import Theorems.Thm_LatinQuarter_fillingOrder_column
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions


attribute [local simp] LatinQuarter.mem_cornerSet

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (hn : 0 < n) (M : Square n)
    (hM : IsLatin M) (ha : Agrees (cornerSet n) (cyclic n) M)
    (r c : Fin n)
    (hprev : ∀ i j, fillingOrder i j < fillingOrder r c → M i j = cyclic n i j) :
    M r c = cyclic n r c := by
  classical
  by_cases hrc : (r, c) ∈ cornerSet n
  · exact ha (r, c) hrc
  have hL := cyclic_isLatin n hn
  obtain ⟨j, hj⟩ := (hL.1 r).surjective (M r c)
  by_cases hjc : j = c
  · simpa [hjc] using hj.symm
  have hrow : M r j ≠ M r c := fun he => hjc ((hM.1 r).injective he)
  by_cases hjright : c < j
  · have he := hprev r j (fillingOrder_column r c j hjright)
    exact (hrow (he.trans hj)).elim
  by_cases hrj : (r, j) ∈ cornerSet n
  · exact (hrow ((ha (r, j) hrj).trans hj)).elim
  have hjlt : j.val < c.val := by
    have hne : j.val ≠ c.val := fun he => hjc (Fin.ext he)
    change ¬c.val < j.val at hjright
    omega
  have hband : n / 2 ≤ r.val + j.val ∧ r.val + j.val < n + n / 2 := by
    simpa only [mem_cornerSet, not_or, not_lt, not_le] using hrj
  let u := r.val + j.val
  by_cases huc : c.val ≤ u
  · let i : Fin n := ⟨u - c.val, by have := r.isLt; dsimp [u]; omega⟩
    have hir : i < r := by change u - c.val < r.val; dsimp [u]; omega
    have hiadd : cyclic n i c = cyclic n r j := by
      apply Fin.ext
      change (i.val + c.val) % n = (r.val + j.val) % n
      have he : i.val + c.val = r.val + j.val := by dsimp [i, u]; omega
      rw [he]
    have he := hprev i c (fillingOrder_row r i c c hir)
    have hirEq := (hM.2 c).injective (he.trans (hiadd.trans hj))
    exact (ne_of_lt hir hirEq).elim
  · let i : Fin n := ⟨u + n - c.val, by have := c.isLt; omega⟩
    have hiadd : cyclic n i c = cyclic n r j := by
      apply Fin.ext
      change (i.val + c.val) % n = (r.val + j.val) % n
      have he : i.val + c.val = u + n := by have := c.isLt; dsimp [i]; omega
      rw [he, Nat.add_mod_right]
    have hic : (i, c) ∈ cornerSet n := by
      apply (mem_cornerSet i c).mpr
      right
      have := c.isLt
      dsimp [i, u]
      omega
    have hirEq := (hM.2 c).injective ((ha (i, c) hic).trans (hiadd.trans hj))
    have he : cyclic n r c = cyclic n r j := by
      change i = r at hirEq
      rw [hirEq] at hiadd
      exact hiadd
    exact (hjc ((hL.1 r).injective he).symm).elim
end LatinQuarter
