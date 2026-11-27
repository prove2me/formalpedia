-- Prove2me | solution 1 for GlobalTheory.ActionLimit.coeff_prod_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:46.572829+00:00
-- url     : https://prove2.me/submissions/545d96ce-d4f8-4954-ad49-1cb82a69d2bf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
variable {C : Type} [Field C] {V : VF C} {σ τ : Type}
namespace GlobalTheory.ActionLimit
theorem _root_.solution {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (e : σ →₀ ℕ) (μ : τ →₀ ℕ) (h : μ.degree < e.degree) :
    coeff μ (e.prod fun s n => a s ^ n) = 0 := by
  classical
  apply coeff_of_lt_order
  have key : ∀ S : Finset σ, ((∑ s ∈ S, e s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, a s ^ e s).order := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert s S hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs, Nat.cast_add]
      exact le_trans (add_le_add (le_order_pow_of_constantCoeff_eq_zero _ (ha s)) ih) le_order_mul
  refine lt_of_lt_of_le ?_ (key e.support)
  exact_mod_cast h
end GlobalTheory.ActionLimit
