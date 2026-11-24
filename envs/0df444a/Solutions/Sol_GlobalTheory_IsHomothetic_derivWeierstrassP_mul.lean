-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.derivWeierstrassP_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:28.417641+00:00
-- url     : https://prove2.me/submissions/379beb0b-4b45-4035-ac74-80a927432172

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
    ℘'[L'] (c * z) = (c ^ 3)⁻¹ * ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← h.equiv.tsum_eq, mul_neg, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, div_eq_mul_inv, mul_inv]
  ring
end GlobalTheory.IsHomothetic
