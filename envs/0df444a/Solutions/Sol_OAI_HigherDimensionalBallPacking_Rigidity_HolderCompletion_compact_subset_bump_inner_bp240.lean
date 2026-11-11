-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:52:27.827961+00:00
-- url     : https://prove2.me/submissions/61b24739-99cd-4cf4-87cb-9855c688fb79

import Mathlib

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma compact_subset_bump_inner_bp240_oai {K : Set ℂ} (hK : IsCompact K) :
    ∃ b : ContDiffBump (0:ℂ), K ⊆ Metric.closedBall (0:ℂ) b.rIn := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0:ℂ) := ⟨R,R+1,hR,by linarith⟩
  refine ⟨b,?_⟩
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using hKR z hz

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner_bp240_oai
