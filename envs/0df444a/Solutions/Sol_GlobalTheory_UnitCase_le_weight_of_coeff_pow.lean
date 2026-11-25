-- Prove2me | solution 1 for GlobalTheory.UnitCase.le_weight_of_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:58.475572+00:00
-- url     : https://prove2.me/submissions/327dea1e-3235-4192-bcf4-b57e64eea1e9

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution (w : (σ →₀ ℕ) → ℕ) (hw : ∀ a b, w (a + b) = w a + w b)
    {h : MvPowerSeries σ C} (hh : ∀ p, MvPowerSeries.coeff p h ≠ 0 → 1 ≤ w p) (k : ℕ) :
    ∀ p, MvPowerSeries.coeff p (h ^ k) ≠ 0 → k ≤ w p := by
  classical
  induction k with
  | zero => exact fun _ _ => Nat.zero_le _
  | succ k ih =>
    intro p hp
    rw [pow_succ, MvPowerSeries.coeff_mul] at hp
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [← hx, hw]
    exact add_le_add (ih _ (left_ne_zero_of_mul hne)) (hh _ (right_ne_zero_of_mul hne))
end GlobalTheory.UnitCase
