-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.phaseDiagonal_parallel_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:11.114868+00:00
-- url     : https://prove2.me/submissions/c61abaf5-fbb2-44a7-a078-4b2d2479de15

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
theorem _root_.solution {n : ℕ} (φ : Fin n → ℝ) (m : ℕ) :
    parallel (phaseDiagonal φ) (1 : Network m) = phaseDiagonal (Fin.append φ 0) := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [phaseDiagonal, Matrix.diagonal_apply, Matrix.one_apply]
end MiLAC.HybridCouplersPhaseShifters
