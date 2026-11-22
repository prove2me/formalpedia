-- Prove2me | solution 1 for Lean4LPD.exp_smul_I_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:24.440833+00:00
-- url     : https://prove2.me/submissions/905f57f5-b52d-420f-aff4-5350809d992f

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
public import Theorems.Thm_Lean4LPD_exp_term_even_of_involution
public import Theorems.Thm_Lean4LPD_exp_term_odd_of_involution

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (z : ℂ) :
    NormedSpace.exp ((Complex.I * z) • G) =
      Complex.cos z • (1 : A) + (Complex.I * Complex.sin z) • G := by
  have hc := (Complex.hasSum_cos' z).smul_const (1 : A)
  have hs := ((Complex.hasSum_sin' z).mul_right Complex.I).smul_const G
  have hsum : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • ((z * Complex.I) • G) ^ n)
      (Complex.cos z • (1 : A) + (Complex.sin z * Complex.I) • G) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert hc using 1
      ext n
      exact exp_term_even_of_involution hG z n
    · convert hs using 1
      ext n
      exact exp_term_odd_of_involution hG z n
  rw [mul_comm Complex.I z, NormedSpace.exp_eq_tsum ℂ, mul_comm Complex.I (Complex.sin z)]
  exact hsum.tsum_eq
end Lean4LPD
