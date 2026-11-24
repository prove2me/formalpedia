-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:27.232155+00:00
-- url     : https://prove2.me/submissions/7e9bbd8d-4cf7-4525-87d5-cd5d13885e4a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerMulOfKerBasicOfCvTest
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelComposition_integral_ker_mul_eq_unfolded
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelComposition_integral_shifted_eq_ker_cv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelComposition
namespace GlobalTheory.CompanionTheory.KernelComposition
theorem _root_.solution : KerBasic → CvTest → KerMul := by
  intro hk hc X φ ψ hφ hψ x y
  rw [integral_ker_mul_eq_unfolded hk X φ ψ hφ hψ x y,
    ← integral_shifted_eq_ker_cv hc X φ ψ hφ hψ x y,
    ← integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y) x]
  simp
end GlobalTheory.CompanionTheory.KernelComposition
