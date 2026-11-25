-- Prove2me | solution 1 for GlobalTheory.psWeight_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:01.932218+00:00
-- url     : https://prove2.me/submissions/6e8dd6ac-dd0b-438a-9fe2-49be363792c2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Theorems.Thm_GlobalTheory_psWeight_mul

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
    [DecidableEq σ] (ρ : σ → ℝ) (g : MvPowerSeries σ C) (r : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g)) (N : ℕ) :
    ∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g ^ N)) := by
  induction N with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs with hα
    · subst hα
      simp
    · rw [AddValuation.map_zero]
      exact le_top
  | succ n ih =>
    intro α
    rw [pow_succ]
    have e : ((n + 1 : ℕ) : ℝ) * r = n * r + r := by push_cast; ring
    rw [e]
    exact psWeight_mul v ρ (g ^ n) g (n * r) r ih h α
end GlobalTheory
