-- Prove2me | solution 1 for GlobalTheory.LineCos.fsDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:00.007977+00:00
-- url     : https://prove2.me/submissions/ab0ab92e-d642-44a1-8bfa-a72be4f3ae4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Theorems.Thm_GlobalTheory_LineCos_lineVec_ne_zero
import Theorems.Thm_GlobalTheory_LineCos_re_hform_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < fsDensity s G x :=
  div_pos (Complex.pos_iff.1 hG.det_pos).1
    (mul_pos Real.pi_pos (pow_pos (re_hform_pos hG (lineVec_ne_zero s x)) 2))
end GlobalTheory.LineCos
