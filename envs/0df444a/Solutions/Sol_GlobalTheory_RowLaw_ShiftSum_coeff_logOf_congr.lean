-- Prove2me | solution 1 for GlobalTheory.RowLaw.ShiftSum.coeff_logOf_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:04:15.564797+00:00
-- url     : https://prove2.me/submissions/5f8ad245-b3d0-49c8-880c-ab74c1e5b7ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ShiftedSumMemTypicalCurveSet
import Theorems.Thm_GlobalTheory_RowLaw_ShiftSum_coeff_tyS_congr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.ShiftSum
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.ShiftSum
theorem _root_.solution (X : RawChart C d I κ) (V : VF C) (g : Fin 2) {x x' : ℕ → I g ⊕ JJ I g → C} (m : ℕ)
    (h : ∀ s ≤ m, ∀ n, x s n = x' s n) :
    (∀ i, PowerSeries.coeff m ((logOf X V g x).1 i) = PowerSeries.coeff m ((logOf X V g x').1 i)) ∧
      ∀ q, PowerSeries.coeff m ((logOf X V g x).2 q) = PowerSeries.coeff m ((logOf X V g x').2 q) := by
  have key : ∀ n, PowerSeries.coeff m (tyS V.l (fun s => x s n)) = PowerSeries.coeff m (tyS V.l (fun s => x' s n)) :=
    fun n => coeff_tyS_congr V.l m fun s hs => h s hs n
  constructor
  · intro i
    simp only [logOf, map_sum, PowerSeries.coeff_smul, key]
  · intro q
    simp only [logOf, map_sub, map_sum, key]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · simp only [PowerSeries.coeff_smul, key]
    · rfl
end GlobalTheory.RowLaw.ShiftSum
