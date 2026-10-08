-- Prove2me | solution 1 for OAI.Erdos3.scalarMeshLog_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:07:15.668985+00:00
-- url     : https://prove2.me/submissions/8e35a055-4c2b-4f3c-a48a-4ab0dcbb9872

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

theorem scalarMeshLog_bounds {G P T : ℝ} (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    0 ≤ scalarMeshLog G P T ∧ P ≤ scalarMeshLog G P T ∧ T ≤ scalarMeshLog G P T ∧
      G + 3 * P + 40 ≤ scalarMeshLog G P T ∧ 2 * P + 3 ≤ scalarMeshLog G P T := by
  unfold scalarMeshLog
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.scalarMeshLog_bounds := @OAI.Erdos3.scalarMeshLog_bounds
