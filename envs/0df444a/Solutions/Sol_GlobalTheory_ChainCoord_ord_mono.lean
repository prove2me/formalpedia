-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:11.492482+00:00
-- url     : https://prove2.me/submissions/f3eb101a-6104-499b-9cdc-bf4da37eceb9

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
theorem _root_.solution {g : MvPowerSeries (Fin M) C} {w w' : ℝ} (h : OrdGe v ρ g w) (hw : w' ≤ w) :
    OrdGe v ρ g w' := fun α =>
  le_trans (WithTop.coe_le_coe.2 (by linarith)) (h α)
end GlobalTheory.ChainCoord
