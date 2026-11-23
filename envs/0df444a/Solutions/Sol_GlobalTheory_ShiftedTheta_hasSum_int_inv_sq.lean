-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.hasSum_int_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:54.204811+00:00
-- url     : https://prove2.me/submissions/9cf5fb20-8cfd-4062-8551-616e340e6cd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta
namespace GlobalTheory.ShiftedTheta
theorem _root_.solution :
    HasSum (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have h := HasSum.of_nat_of_neg (f := fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
  have e : Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 - 1 / ((0 : ℤ) : ℝ) ^ 2 = Real.pi ^ 2 / 3 := by
    simp
    ring
  exact e ▸ h
end GlobalTheory.ShiftedTheta
