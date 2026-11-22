-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_eq_card_antiSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:49.962401+00:00
-- url     : https://prove2.me/submissions/964353f8-222e-4084-9357-674d63c0454d

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_sum

section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
private lemma site_symp (a b : ZMod 2 × ZMod 2) :
    a.1 * b.2 + a.2 * b.1 = if a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b then 1 else 0 := by
  revert a b; decide
variable {kh : ℕ}
end PauliString
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (G s : PauliString n) :
    sympForm G s = ((antiSites G s).card : ZMod 2) := by
  rw [sympForm_eq_sum]
  have : ∀ i : Fin n, G.x i * s.z i + G.z i * s.x i
      = if site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i then (1 : ZMod 2) else 0 :=
    fun i => site_symp (site G i) (site s i)
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_boole]
  rfl
end Lean4LPD.PauliString
