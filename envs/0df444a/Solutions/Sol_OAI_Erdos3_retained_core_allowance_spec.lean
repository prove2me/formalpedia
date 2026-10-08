-- Prove2me | solution 1 for OAI.Erdos3.retained_core_allowance_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:23:17.177314+00:00
-- url     : https://prove2.me/submissions/1c4b8f95-5d18-48fb-87af-83f9af3bb1ad

import Mathlib

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
namespace OAI

section

namespace Erdos3

theorem retained_core_allowance_spec {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 + ε) ∧ ε / (2 + ε) ≤ 1 ∧ (ε / (2 + ε)) * (2 + ε) ≤ ε := by
  have hd : 0 < 2 + ε := by linarith
  refine ⟨div_pos hε hd, (div_le_one hd).mpr (by linarith), ?_⟩
  exact le_of_eq (div_mul_cancel₀ ε hd.ne')

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.retained_core_allowance_spec := @OAI.Erdos3.retained_core_allowance_spec
