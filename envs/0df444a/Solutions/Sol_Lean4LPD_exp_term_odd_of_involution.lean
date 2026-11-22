-- Prove2me | solution 1 for Lean4LPD.exp_term_odd_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:33.907138+00:00
-- url     : https://prove2.me/submissions/d66417f5-c730-4c18-b726-e3564f24f269

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
    ((2 * n + 1)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n + 1) =
      (((z * Complex.I) ^ (2 * n + 1) / (2 * n + 1)! / Complex.I) * Complex.I) • G := by
  have hp : G ^ (2 * n + 1) = G := by
    rw [pow_succ, pow_mul, pow_two, hG, one_pow, one_mul]
  rw [smul_pow, hp, smul_smul, div_mul_cancel₀ _ Complex.I_ne_zero]
  congr 1
  ring
end Lean4LPD
