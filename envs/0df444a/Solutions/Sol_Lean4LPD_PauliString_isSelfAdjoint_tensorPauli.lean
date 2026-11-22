-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_tensorPauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:08.426085+00:00
-- url     : https://prove2.me/submissions/eac15851-4397-4cd1-aef3-946e5f7ae036

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_tensorRepresentative
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_tensorRepresentative
public import Theorems.Thm_Lean4LPD_PauliString_star_toMatrix_of_isSelfAdjoint


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorPauli n p.1 p.2) := by
  rw [← toMatrix_tensorRepresentative]
  exact star_toMatrix_of_isSelfAdjoint (isSelfAdjoint_tensorRepresentative p)
end Lean4LPD.PauliString
