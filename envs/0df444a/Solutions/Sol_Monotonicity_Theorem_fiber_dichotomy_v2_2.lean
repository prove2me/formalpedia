-- Prove2me | solution 2 for Monotonicity_Theorem.fiber_dichotomy_v2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T20:09:55.200481+00:00
-- url     : https://prove2.me/submissions/531183a7-8279-4bdd-8523-4fb20d541c0b

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_definable_value_fiber

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    (∃ z : Power R 1,
      (M.S 1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) ∧
       IsInfinite1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)))) ∨
    ∀ z : Power R 1, IsFinite1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
      (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) := by
  classical
  by_cases h : ∃ z : Power R 1,
      IsInfinite1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0))
  · rcases h with ⟨z, hz⟩
    left
    exact ⟨z, Monotonicity_Theorem.definable_value_fiber D M f z, hz⟩
  · right
    intro z
    by_contra hz
    apply h
    exact ⟨z, hz⟩
