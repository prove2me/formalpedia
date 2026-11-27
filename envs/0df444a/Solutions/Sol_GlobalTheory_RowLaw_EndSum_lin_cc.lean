-- Prove2me | solution 1 for GlobalTheory.RowLaw.EndSum.lin_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:09:46.247674+00:00
-- url     : https://prove2.me/submissions/74766f8f-1363-43c5-ab64-64f23e0270e1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsGaugeAdjointIntegralEndPairAdd
import Theorems.Thm_GlobalTheory_RowLaw_EndSum_lg_cc
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_RowVal_cc_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndSum
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ]
  {X : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.EndSum
theorem _root_.solution (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [smul_eq_C_mul, map_mul, cc_subst ha, lg_cc h, mul_zero]
end GlobalTheory.RowLaw.EndSum
