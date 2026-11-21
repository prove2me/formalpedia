-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.butterfly_eq_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:13.197332+00:00
-- url     : https://prove2.me/submissions/c53fe704-83a4-40cf-b565-1190a716f197

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd
attribute [local simp] MiLAC.parallel_natAdd_natAdd



set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution (L : ℕ) (i : Fin (2 ^ L)) :
    butterfly L i = block 0 (-2 * Real.pi * (i : ℕ) / 2 ^ (L + 1)) 0 := by
  ext a b
  have h01 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) =
      Complex.exp (-(2 * (Real.pi : ℂ) * ((i : ℕ) : ℂ)) / 2 ^ (L + 1) * Complex.I) := by
    congr 1
    ring
  have h11 : Complex.exp (((Real.pi : ℂ) + -(2 * (Real.pi : ℂ) * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) *
      Complex.I) =
      -Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((i : ℕ) : ℂ)) / 2 ^ (L + 1)) := by
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring_nf
  fin_cases a <;> fin_cases b <;> simp [butterfly, block, h01, h11]
end MiLAC.HybridCouplersPhaseShifters
