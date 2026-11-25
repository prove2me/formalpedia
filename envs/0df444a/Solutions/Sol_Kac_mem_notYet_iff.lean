-- Prove2me | solution 1 for Kac.mem_notYet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:08:07.528802+00:00
-- url     : https://prove2.me/submissions/e7077af0-9a77-417c-9ff4-17c33f0ea1be

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
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
theorem _root_.solution (n : ℕ) (x : α) : x ∈ notYet f A n ↔ ∀ k < n, f^[k] x ∉ A := by
  induction n generalizing x with
  | zero => simp
  | succ j ih =>
    simp only [notYet_succ, mem_inter_iff, mem_compl_iff, mem_preimage]
    constructor
    · rintro ⟨hx0, hxs⟩ k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hx0
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Function.iterate_succ_apply]
        exact (ih (f x)).mp hxs k' (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), (ih (f x)).mpr (fun k hk => ?_)⟩
      have := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
end Kac
