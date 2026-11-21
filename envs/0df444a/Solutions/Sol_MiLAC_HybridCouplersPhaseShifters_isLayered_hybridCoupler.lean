-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_hybridCoupler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:30.643188+00:00
-- url     : https://prove2.me/submissions/08bc3ddc-23cb-4886-b93c-e066bafa9819

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
theorem _root_.solution : IsLayered hybridCoupler := by
  have h : hybridCoupler = blockDiagonal ![Real.pi / 2] ![0] ![0] (S := 0) Fin.elim0 := by
    have hI : Complex.exp (((Real.pi : ℂ) - Real.pi / 2) * Complex.I) = Complex.I := by
      rw [show ((Real.pi : ℂ) - Real.pi / 2) = Real.pi / 2 by ring,
        Complex.exp_pi_div_two_mul_I]
    ext i j
    change hybridCoupler i j = parallel _ _ (Fin.castAdd 0 i) (Fin.castAdd 0 j)
    rw [parallel_castAdd_castAdd]
    fin_cases i <;> fin_cases j <;>
      simp [hybridCoupler, block, hI, Matrix.reindex_apply, Matrix.blockDiagonal_apply,
        finProdFinEquiv, Fin.divNat, Fin.modNat]
  rw [h]
  exact isLayered_blockDiagonal _ _ _ _
end MiLAC.HybridCouplersPhaseShifters
