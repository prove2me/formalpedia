-- Prove2me | solution 1 for Lean4LPD.PauliString.card_cancelSites_add_card_antiSites_add_card_createSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:46.726275+00:00
-- url     : https://prove2.me/submissions/819a0e2a-c100-4fea-9b1c-31750a8673e1

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_mem_cancelSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_createSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_support_eq_union
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self


attribute [local simp] Lean4LPD.PauliString.mem_antiSites
section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
private lemma disjoint_cancel_anti (G s : PauliString n) :
    Disjoint (cancelSites G s) (antiSites G s) := by
  rw [Finset.disjoint_left]
  intro i hc ha
  rw [mem_cancelSites] at hc
  rw [mem_antiSites] at ha
  exact ha.2.2 hc.2
private lemma disjoint_union_create (G s : PauliString n) :
    Disjoint (cancelSites G s ∪ antiSites G s) (createSites G s) := by
  rw [Finset.disjoint_left]
  intro i h hcr
  rw [mem_createSites] at hcr
  rcases Finset.mem_union.1 h with hc | ha
  · exact (mem_cancelSites.1 hc).1 hcr.2
  · exact (mem_antiSites.1 ha).2.1 hcr.2
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
    (cancelSites G s).card + (antiSites G s).card + (createSites G s).card = weight G := by
  rw [weight, support_eq_union G s,
    Finset.card_union_of_disjoint (disjoint_union_create G s),
    Finset.card_union_of_disjoint (disjoint_cancel_anti G s)]
end Lean4LPD.PauliString
