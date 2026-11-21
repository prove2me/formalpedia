-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.dft_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:21.479053+00:00
-- url     : https://prove2.me/submissions/dd85f852-964c-44b8-ad08-d46fd61ab214

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
theorem _root_.solution (L a b i k : ℕ) :
    Complex.exp (-2 * Real.pi * Complex.I * ((i : ℂ) + 2 ^ L * a) * ((b : ℂ) + 2 * k) /
        2 ^ (L + 1)) =
      (-1) ^ (a * b) *
        Complex.exp (-2 * Real.pi * Complex.I * i * b / 2 ^ (L + 1)) *
        Complex.exp (-2 * Real.pi * Complex.I * i * k / 2 ^ L) := by
  have harg : -2 * Real.pi * Complex.I * ((i : ℂ) + 2 ^ L * a) * ((b : ℂ) + 2 * k) /
        2 ^ (L + 1) =
      -2 * Real.pi * Complex.I * i * b / 2 ^ (L + 1) +
        -2 * Real.pi * Complex.I * i * k / 2 ^ L +
        ((-(a * k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) +
        ((a * b : ℕ) : ℂ) * (-(Real.pi * Complex.I)) := by
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_nat_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp
  ring
end MiLAC.HybridCouplersPhaseShifters
