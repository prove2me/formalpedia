-- Prove2me | solution 1 for GlobalTheory.ChainCoord.v_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:13.647629+00:00
-- url     : https://prove2.me/submissions/906b1111-bcf9-4944-b098-063457010686

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_v_inv_pow

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
variable {C : Type} [Field C]
namespace GlobalTheory.ChainCoord
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hv : v (l : C) = 1) (s : ℕ) :
    ((-((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v (kap C l s) := by
  have : v ((-1 : C) ^ s) = 0 := by rw [v.map_pow, v.map_neg, v.map_one, smul_zero]
  rw [kap, v.map_mul, this, zero_add]
  exact v_inv_pow hv _
end GlobalTheory.ChainCoord
