-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.hAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:58:07.322642+00:00
-- url     : https://prove2.me/submissions/6d69f08b-df7c-4f86-a453-4ef4ee22f21f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_GlobalTheory_RowLawSquare_subst_hCol
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
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {τ : Type}
variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
namespace GlobalTheory.RowLawSquare
theorem _root_.solution {a b : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    hAt (Y.rawSelf p) a b = sb ![colOf a 0, colOf b 0] Y.h + sb ![colOf a 1, colOf b 1] Y.h := by
  have hz : Zc (fun q : Fin 2 × (Fin 2 × Fin dd) => if q.1 = 0 then a q.2 else b q.2) := fun q => by
    dsimp only
    split_ifs
    exacts [ha _, hb _]
  unfold hAt
  show subst _ (∑ col, hCol col Y.h) = _
  rw [Fin.sum_univ_two, subst_add (hasSubst_of_constantCoeff_zero hz), subst_hCol hz, subst_hCol hz]
  simp only [if_true, one_ne_zero, if_false]
  rfl
end GlobalTheory.RowLawSquare
