-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.G_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:40.170304+00:00
-- url     : https://prove2.me/submissions/ddeb6bbe-6507-4b42-b475-24a142172d1c

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
theorem _root_.solution (h : IsHomothetic c L L') (n : ℕ) : L'.G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  simp only [coe_equiv, mul_pow, mul_inv]
end GlobalTheory.IsHomothetic
