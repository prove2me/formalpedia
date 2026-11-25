-- Prove2me | solution 1 for GlobalTheory.T.fibre_cosine_pushforward_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:01.872325+00:00
-- url     : https://prove2.me/submissions/1634dd2f-dc64-4095-b1df-9795e49218e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreCosinePushforwardUniform
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreCosinePushforwardUniformStatement
import Theorems.Thm_GlobalTheory_FibCos_lintegral_indicator_cos_mul_fs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ J : Set ℝ, MeasurableSet J →
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos G x) * ENNReal.ofReal (GlobalTheory.FibCos.fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs | exact GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs | (intros; apply GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs <;> assumption)
end _root_.GlobalTheory.T
