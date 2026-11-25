-- Prove2me | solution 1 for GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:33.28354+00:00
-- url     : https://prove2.me/submissions/37a8e241-035a-42b0-8513-3cb7db8b6de1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOne
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Theorems.Thm_GlobalTheory_ExpWeight_weight_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  first | exact @GlobalTheory.ExpWeight.weight_exp | exact GlobalTheory.ExpWeight.weight_exp | (intros; apply GlobalTheory.ExpWeight.weight_exp <;> assumption)
end _root_.GlobalTheory.T
