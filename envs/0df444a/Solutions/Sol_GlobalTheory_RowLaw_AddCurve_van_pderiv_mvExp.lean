-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.van_pderiv_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:47.417511+00:00
-- url     : https://prove2.me/submissions/02547487-2b3f-4ca9-997a-c4f318e16aff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_coeff_mul_van
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right
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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} (hH : Van T H) (t : τ) :
    Van T (pderiv C t (mvExp H) - pderiv C t H) := by
  intro ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul]
  have : coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
    show ∑ k ∈ Finset.range ((ν + Finsupp.single t 1).degree + 1),
      coeff (ν + Finsupp.single t 1) (H ^ k) / (k.factorial : C) = _
    rw [Finset.sum_eq_single 1]
    · simp
    · intro k _ hk
      rcases k with _ | _ | k
      · rw [pow_zero, coeff_one, if_neg, zero_div]
        intro h
        have := DFunLike.congr_fun h t
        simp at this
      · exact absurd rfl hk
      · rw [pow_succ', pow_succ', coeff_mul_van hH (hH.mul_right _) ν hν t, zero_div]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range, map_add, Finsupp.degree_single]
      omega
  rw [this, sub_self, zero_mul]
end GlobalTheory.RowLaw.AddCurve
