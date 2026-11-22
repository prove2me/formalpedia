-- Prove2me | solution 1 for Lean4LPD.PauliString.stayAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:22.735013+00:00
-- url     : https://prove2.me/submissions/975b81f3-4c66-44c4-b287-71ef37d0aa56

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (stayAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then y.ofLp p else (Real.cos θ : ℂ) * y.ofLp p := rfl
end Lean4LPD.PauliString
