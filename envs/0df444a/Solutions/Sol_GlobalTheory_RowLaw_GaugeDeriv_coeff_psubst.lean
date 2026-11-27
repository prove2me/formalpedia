-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.coeff_psubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:22:45.237826+00:00
-- url     : https://prove2.me/submissions/72d7105f-5e10-4746-bbf1-c27233f31602

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution {a : MvPowerSeries τ C} (ha : constantCoeff a = 0) (f : PowerSeries C) (μ : τ →₀ ℕ) :
    coeff μ (subst (fun _ : Unit => a) f) =
      ∑ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n f * coeff μ (a ^ n) := by
  rw [← PowerSeries.subst_def, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
  · simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hn
    rw [coeff_of_lt_order, smul_zero]
    refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero n ha)
    exact_mod_cast (by omega : μ.degree < n)
end GlobalTheory.RowLaw.GaugeDeriv
