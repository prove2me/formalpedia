-- Prove2me | solution 1 for GlobalTheory.T.cosine_square_pushforward_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:32.355026+00:00
-- url     : https://prove2.me/submissions/532f5c7a-5bf7-4200-b1c0-4468538aadc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_map_cosSq_fs


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
theorem _root_.solution : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool), G.PosDef →
    Measure.map (GlobalTheory.LineCos.cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (GlobalTheory.LineCos.hform G (GlobalTheory.LineCos.lineVec s x) (GlobalTheory.LineCos.lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.FsLaw.map_cosSq_fs | exact GlobalTheory.LineCos.FsLaw.map_cosSq_fs | (intros; apply GlobalTheory.LineCos.FsLaw.map_cosSq_fs <;> assumption)
end _root_.GlobalTheory.T
