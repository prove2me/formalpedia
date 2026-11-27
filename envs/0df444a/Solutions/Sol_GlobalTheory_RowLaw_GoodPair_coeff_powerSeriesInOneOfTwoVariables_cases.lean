-- Prove2me | solution 1 for GlobalTheory.RowLaw.GoodPair.coeff_powerSeriesInOneOfTwoVariables_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:21:37.905368+00:00
-- url     : https://prove2.me/submissions/5a0ab2bb-9749-4659-a7b9-e4efdd62296b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_zero
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_one
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_coeff_single_powerSeriesInOneOfTwoVariables
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_coeff_powerSeriesInOneOfTwoVariables_other_ne
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


attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_zero
attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_one

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C}
namespace GlobalTheory.RowLaw.GoodPair
theorem _root_.solution (k : Fin 2) (f : PowerSeries C) (e : Fin 2 →₀ ℕ) :
    coeff e (em1 k f) = 0 ∨ coeff e (em1 k f) = PowerSeries.coeff (e k) f := by
  by_cases h : ∃ j, j ≠ k ∧ e j ≠ 0
  · obtain ⟨j, hj, he⟩ := h
    exact Or.inl (coeff_powerSeriesInOneOfTwoVariables_other_ne hj f e he)
  · right
    push Not at h
    have : e = Finsupp.single k (e k) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp
      · rw [h j hj, Finsupp.single_eq_of_ne hj]
    conv_lhs => rw [this]
    exact coeff_single_powerSeriesInOneOfTwoVariables k f _
end GlobalTheory.RowLaw.GoodPair
