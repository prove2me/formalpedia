-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.subst_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:56:42.840856+00:00
-- url     : https://prove2.me/submissions/cbd4a851-5375-4fdd-bc57-532c30f7d547

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_killCompl
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_sg_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63


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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution (X : RawChart C d I κ) (v : κ → C) {τ : Type} {γ : κ → MvPowerSeries τ C}
    (hγ : ∀ s, constantCoeff (γ s) = 0) :
    subst γ (X.sg v) = -∑ i, v i •
      subst (fun p : Fin 2 × κ => if p.1 = 0 then γ p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) := by
  have hS := hasSubst_of_constantCoeff_zero hγ
  rw [sg_eq, FormalCalc.subst_neg' hS, FormalCalc.subst_sum' hS]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [subst_smul hS, subst_killCompl hγ]
end GlobalTheory.RowLaw.AddCurve
