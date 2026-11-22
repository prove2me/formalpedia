-- Prove2me | solution 1 for Lean4LPD.PauliString.rot_toMatrix_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:29.378844+00:00
-- url     : https://prove2.me/submissions/888e8777-3929-4556-8e0f-b1abac9f0a60

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
public import Theorems.Thm_Lean4LPD_rot_eq_exp
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_self_of_isSelfAdjoint


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
open Lean4LPD.PauliString
variable {n : ℕ} {G : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) θ =
      NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix G) :=
  rot_eq_exp (toMatrix_mul_self_of_isSelfAdjoint hG) θ
end Lean4LPD.PauliString
