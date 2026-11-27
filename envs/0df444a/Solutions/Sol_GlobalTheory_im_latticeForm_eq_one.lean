-- Prove2me | solution 1 for GlobalTheory.im_latticeForm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:42.778264+00:00
-- url     : https://prove2.me/submissions/b3a7916d-5e6c-4029-8f71-32b6306b24f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_abs_im_latticeForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution (h : 0 < (L.ω₂ / L.ω₁).im) : (latticeForm L L.ω₂ L.ω₁).im = 1 := by
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  rw [← abs_im_latticeForm L, abs_of_pos]
  rw [latticeForm, div_ofReal_im]
  refine div_pos ?_ (latticeArea_pos L)
  rw [div_im, ← sub_div, div_pos_iff_of_pos_right (normSq_pos.2 h1)] at h
  simp only [mul_im, conj_re, conj_im]
  linarith
end GlobalTheory
