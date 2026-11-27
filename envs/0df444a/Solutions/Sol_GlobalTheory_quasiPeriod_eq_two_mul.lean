-- Prove2me | solution 1 for GlobalTheory.quasiPeriod_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:27.480028+00:00
-- url     : https://prove2.me/submissions/0c804ec4-b98e-4ae1-ab44-fba6d0328ffb

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
theorem _root_.solution {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice) :
    quasiPeriod L w = 2 * weierstrassZeta L (w / 2) := by
  have h1 := weierstrassZeta_add L hw hw2
  rw [weierstrassZeta_add_of_half_notMem L hw hw2 hw2] at h1
  linear_combination -h1
end GlobalTheory
