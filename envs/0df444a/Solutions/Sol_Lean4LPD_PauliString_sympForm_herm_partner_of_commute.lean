-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_herm_partner_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:14.39677+00:00
-- url     : https://prove2.me/submissions/95af687c-a60e-449d-b097-76df5191fd77

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_right


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (G H : PauliString n)
    (hGH : sympForm G H = 0) (p : PauliIndex n) :
    sympForm G (herm (partner H p)) = sympForm G (herm p) := by
  change sympForm G (H * herm p) = _
  rw [sympForm_mul_right, hGH, zero_add]
end Lean4LPD.PauliString
