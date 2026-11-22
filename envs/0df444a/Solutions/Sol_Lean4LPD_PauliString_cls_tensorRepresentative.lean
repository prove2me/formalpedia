-- Prove2me | solution 1 for Lean4LPD.PauliString.cls_tensorRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:10.138777+00:00
-- url     : https://prove2.me/submissions/c58423c8-4441-474c-8c51-f42a1d4b0e18

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution {n : ℕ} (p : PauliIndex n) :
    cls (tensorRepresentative p) = p := rfl
end Lean4LPD.PauliString
