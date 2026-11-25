-- Prove2me | solution 1 for GlobalTheory.Phase.Calc.ph_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:17.039168+00:00
-- url     : https://prove2.me/submissions/91c9e5a3-b06f-4153-b09d-738b83d532ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnity
import Theorems.Thm_GlobalTheory_Phase_Calc_ph_mul
import Theorems.Thm_GlobalTheory_Phase_Calc_ph_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Calc
namespace GlobalTheory.Phase.Calc
theorem _root_.solution {a b : ℂ} (hb0 : b ≠ 0) (hb : Ph b) (hab : Ph (a * b)) : Ph a := by
  have h := ph_mul hab (ph_inv hb)
  rwa [mul_assoc, mul_inv_cancel₀ hb0, mul_one] at h
end GlobalTheory.Phase.Calc
