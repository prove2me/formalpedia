-- Prove2me | solution 1 for Kac.lt_returnTime_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:25.670201+00:00
-- url     : https://prove2.me/submissions/c003e229-066e-4412-ac8f-2b9206eff8cd

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_mem_notYet_iff
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (n : ℕ) (x : α) :
    (n : ℕ∞) < returnTime f A x ↔ f x ∈ notYet f A n := by
  classical
  rw [mem_notYet_iff]
  simp only [returnTime]
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    constructor
    · intro hlt k hk
      have h2 := hlt (k + 1) (by omega)
      rw [not_and] at h2
      have h3 := h2 (by omega)
      rwa [Function.iterate_succ_apply] at h3
    · intro hall m hm
      rw [not_and]
      intro _
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact hall m' (by omega)
  · push Not at h
    constructor
    · intro _ k hk
      have h2 := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h2
    · intro _
      simp
end Kac
