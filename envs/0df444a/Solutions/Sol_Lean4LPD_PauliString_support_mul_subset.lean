-- Prove2me | solution 1 for Lean4LPD.PauliString.support_mul_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:50.386071+00:00
-- url     : https://prove2.me/submissions/6dda6371-2435-4d28-ae2e-1f08ebe90265

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.site_mul



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    support (s * t) ⊆ support s ∪ support t := by
  intro i hi
  rw [mem_support, site_mul] at hi
  rw [Finset.mem_union, mem_support, mem_support]
  by_contra hc
  have h1 : site s i = 0 := by by_contra h; exact hc (Or.inl h)
  have h2 : site t i = 0 := by by_contra h; exact hc (Or.inr h)
  exact hi (by rw [h1, h2, add_zero])
end Lean4LPD.PauliString
