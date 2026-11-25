-- Prove2me | solution 1 for GlobalTheory.WeightSubst.wtNonneg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:28.354822+00:00
-- url     : https://prove2.me/submissions/0320aefa-ffe1-4de4-80dd-33e913742e18

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
theorem _root_.solution {f g : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (hg : WtNonneg v ρ g) :
    WtNonneg v ρ (f * g) := by
  intro α
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have e : ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) =
      ((0 - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) +
        ((0 - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← hp, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
    congr 1
    ring
  rw [e]
  exact add_le_add (hf p.1) (hg p.2)
end GlobalTheory.WeightSubst
