-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:14.272861+00:00
-- url     : https://prove2.me/submissions/685ba14c-f213-4d89-9930-7999b62a5d2a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_ord_zero
import Theorems.Thm_GlobalTheory_ChainCoord_ord_add

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {g : ι → MvPowerSeries (Fin M) C} {w : ℝ}
    (h : ∀ i ∈ s, OrdGe v ρ (g i) w) : OrdGe v ρ (∑ i ∈ s, g i) w :=
  Finset.sum_induction g (fun x => OrdGe v ρ x w) (fun _ _ => ord_add) (ord_zero w) h
end GlobalTheory.ChainCoord
