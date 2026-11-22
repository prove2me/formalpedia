-- Prove2me | solution 1 for Lean4LPD.PauliString.jumpAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:33.980855+00:00
-- url     : https://prove2.me/submissions/e7302984-718c-4d65-9399-bc469054695b

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
    (jumpAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then 0
      else -(Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p)) := rfl
end Lean4LPD.PauliString
