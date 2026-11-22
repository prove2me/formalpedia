-- Prove2me | solution 1 for Lean4LPD.PauliString.sum_norm_stayAct_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:59.018569+00:00
-- url     : https://prove2.me/submissions/93e1db92-0cce-45f6-8dc8-8613c1117e92

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_norm_stayAct_apply_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ p, ‖(stayAct G θ y).ofLp p‖ ≤ ∑ p, ‖y.ofLp p‖ :=
  Finset.sum_le_sum fun p _ => norm_stayAct_apply_le G θ y p
end Lean4LPD.PauliString
