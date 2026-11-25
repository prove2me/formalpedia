-- Prove2me | solution 1 for GlobalTheory.InnerAutomorphism.EntriesBounded.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:26.999222+00:00
-- url     : https://prove2.me/submissions/487d9628-8340-429a-a953-841a2c3f8f20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InnerAutomorphism
variable {K n : Type*} [NormedField K]
namespace GlobalTheory.InnerAutomorphism
namespace EntriesBounded
theorem _root_.solution [IsUltrametricDist K] [Fintype n] {M N : Matrix n n K} {c d : ℝ}
    (hM : EntriesBounded M c) (hN : EntriesBounded N d) :
    EntriesBounded (M * N) (c * d) := by
  intro i j
  have hc : 0 ≤ c := (norm_nonneg _).trans (hM i j)
  have hd : 0 ≤ d := (norm_nonneg _).trans (hN i j)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hM i k) (hN k j) (norm_nonneg _) hc
end EntriesBounded
end GlobalTheory.InnerAutomorphism
