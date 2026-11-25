-- Prove2me | solution 1 for Hamiltonicity.CycArr.of_fun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:28:08.804968+00:00
-- url     : https://prove2.me/submissions/a70ed385-0d15-4297-872a-524a9dafafde

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_lt
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution {h : ℕ → V} (hm : 3 ≤ m) (hinj : ∀ i j, i < m → j < m → h i = h j → i = j)
    (hadj : ∀ i < m, G.Adj (h i) (h (i + 1))) (hend : h m = h 0) :
    CycArr G m (fun i => h (i % m)) where
  three_le := hm
  periodic i := by simp
  inj i j hi hj hij := by
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
    exact hinj i j hi hj hij
  adj i := by
    have hm0 : 0 < m := by omega
    have hlt : i % m < m := Nat.mod_lt _ hm0
    by_cases hc : i % m + 1 < m
    · rw [succ_mod_of_lt hc]
      exact hadj _ hlt
    · have hc' : i % m + 1 = m := by omega
      rw [succ_mod_of_eq hc', ← hend]
      have := hadj _ hlt
      rwa [hc'] at this
end Hamiltonicity.CycArr
