-- Prove2me | solution 1 for OAI.Erdos3.scalarMesh_movement_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:07:15.75123+00:00
-- url     : https://prove2.me/submissions/4da811eb-6578-406b-ac73-f5d608248fb7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009
import Theorems.Thm_OAI_Erdos3_scalarMeshLog_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

theorem scalarMesh_movement_bound {d C B G P T : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdP : d ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hBP : B ≤ Real.exp P) :
    1 + d * (C + B) ≤ Real.exp (scalarMeshLog G P T) := by
  have hmul : d * (C + B) ≤ Real.exp P * (Real.exp P + Real.exp P) := by gcongr
  have h1 : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have heq : Real.exp P * (Real.exp P + Real.exp P) = 2 * Real.exp (2 * P) := by
    rw [show 2 * P = P + P by ring, Real.exp_add]; ring
  rw [heq] at hmul
  calc
    _ ≤ 3 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 3 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.2

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.scalarMesh_movement_bound := @OAI.Erdos3.scalarMesh_movement_bound
