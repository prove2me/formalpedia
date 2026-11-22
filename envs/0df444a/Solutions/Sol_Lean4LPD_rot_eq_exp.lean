-- Prove2me | solution 1 for Lean4LPD.rot_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:11.712789+00:00
-- url     : https://prove2.me/submissions/1d4195ca-270d-4315-b8dd-55acdcca6861

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
public import Theorems.Thm_Lean4LPD_exp_smul_I_of_involution

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (θ : ℝ) :
    rot G θ = NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) := by
  rw [exp_smul_I_of_involution hG, rot, Complex.ofReal_cos, Complex.ofReal_sin]
end Lean4LPD
