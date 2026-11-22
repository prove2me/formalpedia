-- Prove2me | solution 1 for Lean4LPD.exp_conj_of_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:49.589492+00:00
-- url     : https://prove2.me/submissions/968591f7-7cac-4a72-9c4b-177e6be7721e

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
public import Theorems.Thm_Lean4LPD_rot_eq_exp
public import Theorems.Thm_Lean4LPD_rot_neg_eq_exp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (h : G * P = -(P * G)) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) =
      (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) := by
  rw [← rot_eq_exp hG θ, ← rot_neg_eq_exp hG θ]
  exact rot_conj_of_anticommute hG h
end Lean4LPD
