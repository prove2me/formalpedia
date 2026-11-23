-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.contDiff_phaseLine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:33.580567+00:00
-- url     : https://prove2.me/submissions/9bfa415d-39b1-4974-a63a-c41d17d436e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm
namespace GlobalTheory.LinPhaseSeminorm
theorem _root_.solution (c t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phaseLine c t) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold phaseLine; fun_prop
end GlobalTheory.LinPhaseSeminorm
