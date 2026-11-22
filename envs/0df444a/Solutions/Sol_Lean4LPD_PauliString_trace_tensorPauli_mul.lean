-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_tensorPauli_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:28.342517+00:00
-- url     : https://prove2.me/submissions/28fef2c1-726b-4171-a5dc-112ae6cd0af2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_tensorPauli
public import Theorems.Thm_Lean4LPD_PauliString_trace_star_tensorPauli_mul

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution {n : ℕ} (p q : PauliIndex n) :
    (tensorPauli n p.1 p.2 * tensorPauli n q.1 q.2).trace =
      if p = q then (2 : ℂ) ^ n else 0 := by
  have h := trace_star_tensorPauli_mul p q
  rw [show star (tensorPauli n p.1 p.2) = tensorPauli n p.1 p.2 from
    isSelfAdjoint_tensorPauli p] at h
  exact h
end Lean4LPD.PauliString
