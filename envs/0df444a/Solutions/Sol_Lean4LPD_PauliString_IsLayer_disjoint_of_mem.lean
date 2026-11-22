-- Prove2me | solution 1 for Lean4LPD.PauliString.IsLayer.disjoint_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:15.047768+00:00
-- url     : https://prove2.me/submissions/acb1eaf2-7858-4330-b110-18221605529b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul


attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.reachable_cons
section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
private theorem pairwise_disjoint_of_mem : ∀ {M : List (PauliString n)},
    (M.Pairwise fun G H => Disjoint (support G) (support H)) →
    ∀ {G H : PauliString n}, G ∈ M → H ∈ M → G ≠ H → Disjoint (support G) (support H) := by
  intro M
  induction M with
  | nil => intro _ _ _ hG _ _; exact absurd hG (by simp)
  | cons a t ih =>
    intro hpw G H hG hH hne
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.1 hG with rfl | hG'
    · rcases List.mem_cons.1 hH with rfl | hH'
      · exact absurd rfl hne
      · exact hpw.1 _ hH'
    · rcases List.mem_cons.1 hH with rfl | hH'
      · exact (hpw.1 _ hG').symm
      · exact ih hpw.2 hG' hH' hne
end PauliString
namespace LayerWitness
open PauliString
end LayerWitness
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
namespace IsLayer
theorem _root_.solution (hL : IsLayer kh L) (hG : G ∈ L) (hH : H ∈ L) (hne : G ≠ H) :
    Disjoint (support G) (support H) :=
  pairwise_disjoint_of_mem hL.disjoint hG hH hne
end IsLayer
end Lean4LPD.PauliString
