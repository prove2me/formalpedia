-- Prove2me | solution 1 for GlobalTheory.zetaSeries_coeff_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:25.550129+00:00
-- url     : https://prove2.me/submissions/591dc135-3247-4245-b13d-f252c6a8a6d8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
open MvPowerSeries
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)
namespace GlobalTheory
theorem _root_.solution {c : C} {L : ℝ} (hc : ((L : ℝ) : WithTop ℝ) ≤ v c)
    {g : MvPowerSeries (Fin M) C} {s : ℝ} (hg : OrdGe v ρ g s) (α : Fin M →₀ ℕ) :
    (((L + s - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (c * coeff α g) := by
  rw [v.map_mul, show L + s - ∑ m, ρ m * (α m : ℝ) = L + (s - ∑ m, ρ m * (α m : ℝ)) by ring,
    WithTop.coe_add]
  exact add_le_add hc (hg α)
end GlobalTheory
