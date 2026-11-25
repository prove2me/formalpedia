-- Prove2me | solution 1 for GlobalTheory.WeightSubst.wtNonneg_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:37.072369+00:00
-- url     : https://prove2.me/submissions/7365995b-93bb-4dc1-a224-866e7a3679c2

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
theorem _root_.solution {f : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (n : ℕ) :
    WtNonneg v ρ (f ^ n) := by
  induction n with
  | zero => simpa using wtNonneg_one v ρ
  | succ k ih =>
    rw [pow_succ]
    exact wtNonneg_mul v ρ ih hf
end GlobalTheory.WeightSubst
