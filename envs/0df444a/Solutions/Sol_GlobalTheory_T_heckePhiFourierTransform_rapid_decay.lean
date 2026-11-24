-- Prove2me | solution 1 for GlobalTheory.T.heckePhiFourierTransform_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:16.155474+00:00
-- url     : https://prove2.me/submissions/1df1a5ae-36d3-47e0-b59d-b4113ec6025c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecayStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_hTrans_rapid_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_rapid_decay | exact GlobalTheory.HeckeTwo.hTrans_rapid_decay | (intros; apply GlobalTheory.HeckeTwo.hTrans_rapid_decay <;> assumption)
end _root_.GlobalTheory.T
