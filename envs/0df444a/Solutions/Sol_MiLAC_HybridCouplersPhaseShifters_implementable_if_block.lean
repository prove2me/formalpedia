-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_if_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:30.086249+00:00
-- url     : https://prove2.me/submissions/f9efbb6c-d908-4a85-a989-c92ea870f9fb

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
theorem _root_.solution (θ₁₁ θ₁₂ θ₂₁ : ℝ) :
    Implementable (block θ₁₁ θ₁₂ θ₂₁) := by
  have hdecomp : block θ₁₁ θ₁₂ θ₂₁ =
      parallel (phaseShifter θ₁₂) (phaseShifter (Real.pi / 2 - θ₁₁ + θ₁₂ + θ₂₁)) *
        hybridCoupler * parallel (phaseShifter (θ₁₁ - θ₁₂ - Real.pi / 2)) interconnection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block, hybridCoupler, parallel, Matrix.reindex_apply, Matrix.mul_apply,
        Fin.sum_univ_two, phaseShifter, interconnection, finSumFinEquiv, Fin.addCases,
        add_mul, sub_mul, Complex.exp_add, Complex.exp_sub] <;>
      field_simp <;> simp [Complex.I_sq]
  rw [hdecomp]
  exact Implementable.series (Implementable.parallel (Implementable.ps _) Implementable.ic)
    (Implementable.series Implementable.hc
      (Implementable.parallel (Implementable.ps _) (Implementable.ps _)))
end MiLAC.HybridCouplersPhaseShifters
