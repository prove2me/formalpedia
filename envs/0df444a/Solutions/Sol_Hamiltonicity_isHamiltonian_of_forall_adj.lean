-- Prove2me | solution 1 for Hamiltonicity.isHamiltonian_of_forall_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:30.727835+00:00
-- url     : https://prove2.me/submissions/4b3c3543-f122-426d-a591-a2e285213604

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_lt
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_eq
public import Theorems.Thm_Hamiltonicity_CycArr_isHamiltonian
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hn : 3 ≤ Fintype.card V) (hadj : ∀ u v, u ≠ v → G.Adj u v) : G.IsHamiltonian := by
  set n := Fintype.card V
  have hn0 : 0 < n := by omega
  let e := Fintype.equivFin V
  let h : ℕ → V := fun i => e.symm ⟨i % n, Nat.mod_lt _ hn0⟩
  have hinj : ∀ i j, h i = h j → i % n = j % n := by
    intro i j hij
    have := e.symm.injective hij
    simpa using this
  refine CycArr.isHamiltonian (m := n) (f := h) ⟨hn, ?_, ?_, ?_⟩ rfl
  · intro i
    simp [h]
  · intro i j hi hj hij
    have := hinj i j hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · intro i
    apply hadj
    intro hij
    have := hinj i (i + 1) hij
    have hlt : i % n < n := Nat.mod_lt _ hn0
    by_cases hc : i % n + 1 < n
    · rw [CycArr.succ_mod_of_lt hc] at this
      omega
    · rw [CycArr.succ_mod_of_eq (by omega)] at this
      omega
end Hamiltonicity
