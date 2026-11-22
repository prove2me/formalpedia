-- Prove2me | solution 1 for Lean4LPD.PauliString.layer_sympForm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:19.248841+00:00
-- url     : https://prove2.me/submissions/264ac6b2-e274-4a28-bb6f-c96cb7e03856

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_IsLayer_disjoint_of_mem
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_of_disjoint_support
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
attribute [local simp] Lean4LPD.PauliString.sympForm_self



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) :
    ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 := by
  intro g hg h hh
  by_cases hgh : g.1 = h.1
  · rw [hgh, sympForm_self]
  · exact sympForm_eq_zero_of_disjoint_support
      (hL.disjoint_of_mem (List.mem_map_of_mem hg) (List.mem_map_of_mem hh) hgh)
end Lean4LPD.PauliString
