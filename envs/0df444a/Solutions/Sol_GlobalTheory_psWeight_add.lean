-- Prove2me | solution 1 for GlobalTheory.psWeight_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:52.908667+00:00
-- url     : https://prove2.me/submissions/6d19949c-03d5-4789-90db-86b5a88a4de1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus

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
namespace GlobalTheory
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g + g')) := by
  intro α
  have hc : MvPowerSeries.coeff α (g + g') =
      MvPowerSeries.coeff α g + MvPowerSeries.coeff α g' := map_add _ _ _
  rw [hc]
  refine AddValuation.map_le_add v ?_ ?_
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_left r r') _)) (h α)
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_right r r') _)) (h' α)
end GlobalTheory
