-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_phaseShifter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:30.167179+00:00
-- url     : https://prove2.me/submissions/a6541d27-aed2-41d7-873c-c33400d5ef5b

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_blockDiagonal
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_parallel
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
theorem _root_.solution (φ : ℝ) : IsLayered (phaseShifter φ) := by
  have h : phaseShifter φ = blockDiagonal (C := 0) Fin.elim0 Fin.elim0 Fin.elim0 ![φ] := by
    ext i j
    fin_cases i
    fin_cases j
    change _ = parallel _ (phaseDiagonal ![φ]) (Fin.natAdd (2 * 0) 0) (Fin.natAdd (2 * 0) 0)
    rw [parallel_natAdd_natAdd]
    simp [phaseDiagonal, phaseShifter]
  rw [h]
  exact isLayered_blockDiagonal _ _ _ _
end MiLAC.HybridCouplersPhaseShifters
