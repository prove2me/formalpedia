-- Prove2me | solution 1 for GlobalTheory.WeightSubst.wtNonneg_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:44.862321+00:00
-- url     : https://prove2.me/submissions/9661c7c3-383e-4a3e-aab3-6c4966baee09

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightSubstNonneg
import Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_one
import Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_mul

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, WtNonneg v ρ (f i)) : WtNonneg v ρ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wtNonneg_one v ρ
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact wtNonneg_mul v ρ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end GlobalTheory.WeightSubst
