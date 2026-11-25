-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:10.682617+00:00
-- url     : https://prove2.me/submissions/86a68cce-3273-4cc3-b4a9-b98b191adfae

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
theorem _root_.solution {g g' : MvPowerSeries (Fin M) C} {w : ℝ} (h : OrdGe v ρ g w)
    (h' : OrdGe v ρ g' w) : OrdGe v ρ (g + g') w := fun α => by
  rw [map_add]
  exact le_trans (le_min (h α) (h' α)) (v.map_add _ _)
end GlobalTheory.ChainCoord
