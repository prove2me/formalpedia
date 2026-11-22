-- Prove2me | solution 1 for Lean4LPD.exp_term_even_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:19.717146+00:00
-- url     : https://prove2.me/submissions/775d6d42-6676-4f72-bfea-d4f88fa9b027

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (z : ℂ) (n : ℕ) :
    ((2 * n)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n) =
      ((z * Complex.I) ^ (2 * n) / (2 * n)!) • (1 : A) := by
  have hp : G ^ (2 * n) = 1 := by rw [pow_mul, pow_two, hG, one_pow]
  rw [smul_pow, hp, smul_smul]
  congr 1
  ring
end Lean4LPD
