-- Prove2me | solution 1 for GlobalTheory.det_gram_real_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:55.705627+00:00
-- url     : https://prove2.me/submissions/c6208b03-bb5a-4f0a-98bd-2abf76d1afd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_sum_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory
theorem _root_.solution (e : ι → E) (m : Matrix ι ι ℝ) :
    (gram ℝ (fun j => ∑ i, m i j • e i)).det = m.det ^ 2 * (gram ℝ e).det := by
  simpa using Hadamard.re_det_gram_sum_smul (𝕜 := ℝ) e m
end GlobalTheory
