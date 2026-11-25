-- Prove2me | solution 1 for GlobalTheory.ChainCoord.geom_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:55.218364+00:00
-- url     : https://prove2.me/submissions/16e182b7-ee5d-407a-b12c-aee85a3fc2be

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
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) (s : ℕ) :
    ((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) =
      (((l : ℝ) ^ 2) ^ s - 1) * (1 / ((l : ℝ) ^ 2 - 1)) := by
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  push_cast
  rw [← geom_sum_mul]
  field_simp
end GlobalTheory.ChainCoord
