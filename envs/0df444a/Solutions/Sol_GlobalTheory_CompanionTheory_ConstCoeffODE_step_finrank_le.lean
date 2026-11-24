-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConstCoeffODE.step_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:00.97012+00:00
-- url     : https://prove2.me/submissions/3da226a5-5eb4-412c-aa8d-00c1a09a89fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpace
import Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_stepMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConstCoeffODE
namespace GlobalTheory.CompanionTheory.ConstCoeffODE
theorem _root_.solution (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    Module.finrank ℂ (step c S) ≤ Module.finrank ℂ S + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (stepMap_injective c S)
  rw [Module.finrank_prod, Module.finrank_self] at h
  exact h
end GlobalTheory.CompanionTheory.ConstCoeffODE
