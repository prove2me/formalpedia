-- Prove2me | solution 1 for Lean4LPD.exp_conj_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:48.897401+00:00
-- url     : https://prove2.me/submissions/dc84e490-4ffd-426b-8171-1aade9407f45

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
public import Theorems.Thm_Lean4LPD_rot_eq_exp
public import Theorems.Thm_Lean4LPD_rot_neg_eq_exp
public import Theorems.Thm_Lean4LPD_rot_conj_of_commute


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (h : Commute G P) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) = P := by
  rw [← rot_eq_exp hG θ, ← rot_neg_eq_exp hG θ]
  exact rot_conj_of_commute hG h
end Lean4LPD
