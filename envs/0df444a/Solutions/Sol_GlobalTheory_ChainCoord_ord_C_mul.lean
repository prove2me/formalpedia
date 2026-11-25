-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:59.325097+00:00
-- url     : https://prove2.me/submissions/79f1f4a0-bacc-49b5-be5f-c415f19c7030

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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}
namespace GlobalTheory.ChainCoord
theorem _root_.solution {g : MvPowerSeries (Fin M) C} {w a : ℝ} {x : C} (hx : (a : WithTop ℝ) ≤ v x)
    (h : OrdGe v ρ g w) : OrdGe v ρ (MvPowerSeries.C (R := C) x * g) (a + w) := fun α => by
  rw [coeff_C_mul, v.map_mul, add_sub_assoc, WithTop.coe_add]
  exact add_le_add hx (h α)
end GlobalTheory.ChainCoord
