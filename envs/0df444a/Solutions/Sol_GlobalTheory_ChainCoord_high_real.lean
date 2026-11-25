-- Prove2me | solution 1 for GlobalTheory.ChainCoord.high_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:55.228871+00:00
-- url     : https://prove2.me/submissions/0b148bda-7faf-4175-b4e6-2688495126bd

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
namespace GlobalTheory.ChainCoord
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) (k : ℕ) :
    1 + 1 / ((l : ℝ) ^ 2 - 1) ≤
      (1 - ((k + 3 : ℕ) : ℝ)) + ((l ^ (k + 3) : ℕ) : ℝ) * (1 / ((l : ℝ) ^ 2 - 1)) := by
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have h1 : k + 3 ≤ l ^ (k + 1) := by
    have : k < l ^ k := Nat.lt_pow_self (by omega)
    rw [pow_succ]; nlinarith
  have h2 : ((k : ℝ) + 3) ≤ (l : ℝ) ^ (k + 1) := by exact_mod_cast h1
  have h4 : ((k : ℝ) + 3) ≤ ((l : ℝ) ^ (k + 3) - 1) * (1 / ((l : ℝ) ^ 2 - 1)) := by
    rw [mul_one_div, le_div_iff₀ h, show (l : ℝ) ^ (k + 3) = (l : ℝ) ^ (k + 1) * l ^ 2 by ring]
    have : (0 : ℝ) ≤ k := by positivity
    nlinarith
  push_cast
  linarith
end GlobalTheory.ChainCoord
