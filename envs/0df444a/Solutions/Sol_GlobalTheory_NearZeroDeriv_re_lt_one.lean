-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.re_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:47.427532+00:00
-- url     : https://prove2.me/submissions/295dbcfd-5d88-42d2-b44c-f0caead0f630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv
namespace GlobalTheory.NearZeroDeriv
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ} {R : ℝ}
    (hw : w ∈ zerosDisc χ c R) : w.re < 1 := by
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ hw.2.1 (not_lt.1 h) hw.2.2
end GlobalTheory.NearZeroDeriv
