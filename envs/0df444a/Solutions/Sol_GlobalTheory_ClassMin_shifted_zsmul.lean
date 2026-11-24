-- Prove2me | solution 1 for GlobalTheory.ClassMin.shifted_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.730089+00:00
-- url     : https://prove2.me/submissions/df7f2a60-8e36-4d45-ac35-f24bbb1bb24c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hN : N ≠ 0) (ν : X →+ ℝ) (μ : X) :
    Q (N • μ) / N + ν (N • μ) = N * (Q μ + ν μ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [QuadraticMap.map_smul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  field_simp
end GlobalTheory.ClassMin
