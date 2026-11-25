-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_mul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:59.372864+00:00
-- url     : https://prove2.me/submissions/840f1104-a649-423f-8267-e975f8681423

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
theorem _root_.solution {a b : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (j k : ℕ) (m : σ →₀ ℕ) (h : m.degree < j + k) :
    MvPowerSeries.coeff m (a ^ j * b ^ k) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ MvPowerSeries.le_order_mul
  refine lt_of_lt_of_le ?_ (add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero j ha)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hb))
  exact_mod_cast h
end GlobalTheory.UnitCase
