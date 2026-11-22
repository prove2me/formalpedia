-- Prove2me | solution 1 for Lean4LPD.PauliString.wt_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:10.208157+00:00
-- url     : https://prove2.me/submissions/ef0a4a11-666c-453c-9b33-14145682f612

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_weight_congr

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (s : PauliString n) : wt (cls s) = weight s := weight_congr rfl rfl
end Lean4LPD.PauliString
