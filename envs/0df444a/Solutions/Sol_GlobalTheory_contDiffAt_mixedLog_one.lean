-- Prove2me | solution 1 for GlobalTheory.contDiffAt_mixedLog_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:52.475376+00:00
-- url     : https://prove2.me/submissions/fc7e992b-590b-4800-a70a-2de4cc0857f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    ContDiffAt ℝ ∞ (mixedLog K) 1 := by
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.1 w) :=
      (contDiff_apply ℝ ℝ w).comp contDiff_fst
    exact h1.contDiffAt.log (by simp)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.2 w) :=
      (contDiff_apply ℝ ℂ w).comp contDiff_snd
    have h2 : ContDiffAt ℝ ∞ Complex.log ((1 : mixedSpace K).2 w) :=
      (Complex.contDiffAt_log (by simp)).restrict_scalars ℝ
    exact h2.comp 1 h1.contDiffAt
end GlobalTheory
