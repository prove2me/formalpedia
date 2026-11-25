-- Prove2me | solution 1 for GlobalTheory.ChainCoord.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:54.317864+00:00
-- url     : https://prove2.me/submissions/0cf2aec2-977c-4235-9904-27c0d5aa251b

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
theorem _root_.solution {f : MvPowerSeries (Fin M) C} (hf : constantCoeff f = 0) {m : ℕ}
    (α : Fin M →₀ ℕ) (hα : Finsupp.degree α < m) : coeff α (f ^ m) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero m hf)
  exact_mod_cast hα
end GlobalTheory.ChainCoord
