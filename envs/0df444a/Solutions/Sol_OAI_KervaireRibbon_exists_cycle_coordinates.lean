-- Prove2me | solution 1 for OAI.KervaireRibbon.exists_cycle_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:58:42.685526+00:00
-- url     : https://prove2.me/submissions/278dbf0f-6970-4c24-ae91-49cdc12f25ee

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]
theorem kr_cyc (σ : Equiv.Perm D) (x : D) (j : ℕ) (hj : j < (cycleList σ x).length) :
    σ ((cycleList σ x)[j]) = (cycleList σ x)[(j + 1) % (cycleList σ x).length]'(Nat.mod_lt _ (by omega)) := by
  by_cases hx : σ x = x
  · have hl : cycleList σ x = [x] := by simp [cycleList, hx]
    have h1 : (cycleList σ x).length = 1 := by rw [hl]; rfl
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [hl, List.getElem_cons_zero, List.length_singleton, zero_add, Nat.mod_self]
    exact hx
  · have hl : cycleList σ x = σ.toList x := by simp [cycleList, hx]
    have hmem : (cycleList σ x)[j] ∈ cycleList σ x := List.getElem_mem _
    have hsc := (mem_cycleList σ x _).1 hmem
    rw [← hsc.cycleOf_apply, ← Equiv.Perm.formPerm_toList]
    simp only [hl]
    exact List.formPerm_apply_getElem _ (σ.nodup_toList x) j _

theorem solution (σ : Equiv.Perm D) :
    ∃ (n : Cycles σ → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D),
      ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩ := by
  have hpos : ∀ z : Cycles σ, 0 < (cycleList σ z.out).length := fun z =>
    List.length_pos_of_mem ((mem_cycleList σ _ _).2 SameCycle.rfl)
  refine ⟨fun z => (cycleList σ z.out).length - 1,
    (Equiv.sigmaCongrRight (fun z => finCongr (Nat.sub_add_cancel (hpos z)))).trans (cycleEquiv σ), ?_⟩
  intro z i
  have hce : ∀ p, cycleEquiv σ p = (cycleList σ p.1.out)[p.2.val] := fun p => rfl
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, finCongr_apply, hce, Fin.val_cast]
  rw [kr_cyc]
  congr 1
  have h := Nat.sub_add_cancel (hpos z)
  rw [finRotate_apply, Fin.val_add_one]
  split_ifs with hi
  · rw [hi, Fin.val_last, h, Nat.mod_self]
  · have hlt : i.val + 1 < (cycleList σ z.out).length - 1 + 1 := by
      have := Fin.val_lt_last hi; simp only [Fin.val_last] at this; omega
    rw [Nat.mod_eq_of_lt (by omega)]

