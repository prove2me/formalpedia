-- Prove2me | solution 1 for GlobalTheory.WeightSubst.wtNonneg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:28.995833+00:00
-- url     : https://prove2.me/submissions/14be81e3-8e5d-45f0-ac20-855602ffcc21

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightSubstNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.WeightSubst
open MvPowerSeries
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)
omit [Fintype σ]
namespace GlobalTheory.WeightSubst
theorem _root_.solution : WtNonneg v ρ (1 : MvPowerSeries σ C) := by
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp
end GlobalTheory.WeightSubst
