-- Prove2me | solution 1 for GlobalTheory.CoordScale.measurePreserving_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:50.325783+00:00
-- url     : https://prove2.me/submissions/37d5658f-145f-47b1-bf67-2eac41ee9c78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory
namespace GlobalTheory.CoordScale
theorem _root_.solution (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by
  refine ⟨measurable_id.const_mul _, ?_⟩
  have hfun : (fun z : ℂ => ((r : ℂ))⁻¹ * z) = fun z => (r⁻¹ : ℝ) • z := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_pos (by positivity)]
end GlobalTheory.CoordScale
