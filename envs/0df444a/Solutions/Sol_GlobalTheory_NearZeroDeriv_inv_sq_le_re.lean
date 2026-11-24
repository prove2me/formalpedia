-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.inv_sq_le_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:40.911932+00:00
-- url     : https://prove2.me/submissions/8ce910ef-87df-4396-9944-bd8d18131f0d

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
theorem _root_.solution {s w : ℂ} {r : ℝ} (m : ℕ) (h : r ≤ (s - w).re) :
    r * ((m : ℝ) / ‖s - w‖ ^ 2) ≤ ((m : ℂ) / (s - w)).re := by
  rw [div_eq_mul_inv (m : ℂ), ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re,
    Complex.normSq_eq_norm_sq, mul_div_assoc', mul_div_assoc', mul_comm]
  gcongr
end GlobalTheory.NearZeroDeriv
