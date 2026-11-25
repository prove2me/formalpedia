-- Prove2me | solution 1 for GlobalTheory.ChainCoord.kap_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:56.250844+00:00
-- url     : https://prove2.me/submissions/737b18b4-022e-4950-87a1-1632c05fdede

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
variable {C : Type} [Field C]
namespace GlobalTheory.ChainCoord
theorem _root_.solution {l : ℕ} (ho : Odd l) (s : ℕ) :
    kap C l (s + 1) = -((l : C)⁻¹ * kap C l s ^ (l ^ 2)) := by
  have h1 : ((-1 : C) ^ s) ^ (l ^ 2) = (-1) ^ s := by
    rw [← pow_mul, mul_comm, pow_mul, (ho.pow (n := 2)).neg_one_pow]
  have h2 : ∑ u ∈ Finset.range (s + 1), (l ^ 2) ^ u =
      (∑ u ∈ Finset.range s, (l ^ 2) ^ u) * l ^ 2 + 1 := by
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp [pow_succ (l ^ 2)]
  rw [kap, kap, mul_pow, h1, h2, inv_pow, ← pow_mul, pow_succ (l : C), mul_inv]
  ring
end GlobalTheory.ChainCoord
