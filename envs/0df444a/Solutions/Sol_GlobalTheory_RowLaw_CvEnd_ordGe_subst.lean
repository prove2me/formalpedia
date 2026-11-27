-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.ordGe_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:34:11.185278+00:00
-- url     : https://prove2.me/submissions/e2761b3c-a4b7-4a3a-a805-2a4863bf205f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_mem_ordGe
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum
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
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {σ τ : Type}
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution {w : τ → ℕ} {w' : σ → ℕ} {n : ℕ} {a : σ → MvPowerSeries τ C} (ha : HasSubst a)
    (hw : ∀ s, a s ∈ ordGe C w (w' s)) {f : MvPowerSeries σ C} (hf : f ∈ ordGe C w' n) :
    subst a f ∈ ordGe C w n := by
  rw [mem_ordGe]
  refine le_trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  intro e he
  have h1 : n ≤ Finsupp.weight w' e := not_lt.1 fun h => he (hf e h)
  refine le_trans (Nat.cast_le.2 h1 : (n : ℕ∞) ≤ _) ?_
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  exact mul_le_mul_right (mem_ordGe.1 (hw i)) _
end GlobalTheory.RowLaw.CvEnd
