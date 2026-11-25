-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.latticeForm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:53:56.058528+00:00
-- url     : https://prove2.me/submissions/552387b2-a101-4c3f-af8a-19f81f7af1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

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
namespace IsHomothetic
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (u v : ℂ) : latticeForm L' (c * u) (c * v) = latticeForm L u v := by
  have hc := h.ne_zero
  have hc' : conj c ≠ 0 := by simpa using hc
  rw [latticeForm, latticeForm, h.latticeArea_eq, map_mul]
  push_cast
  rw [← mul_conj']
  field_simp
end IsHomothetic
end GlobalTheory
