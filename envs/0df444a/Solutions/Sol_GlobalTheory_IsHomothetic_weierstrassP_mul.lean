-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.weierstrassP_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:27.272262+00:00
-- url     : https://prove2.me/submissions/771087ea-8b40-4cd9-afaf-18cbdb5c3fa4

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
open GlobalTheory.IsHomothetic
variable {L} {L' : PeriodPair} {c : ℂ}
namespace GlobalTheory.IsHomothetic
theorem _root_.solution (h : IsHomothetic c L L') (z : ℂ) :
    ℘[L'] (c * z) = (c ^ 2)⁻¹ * ℘[L] z := by
  simp only [weierstrassP]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, one_div, mul_inv]
end GlobalTheory.IsHomothetic
