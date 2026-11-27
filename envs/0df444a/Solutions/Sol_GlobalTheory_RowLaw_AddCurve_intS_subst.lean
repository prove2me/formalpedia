-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.intS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:07:38.210853+00:00
-- url     : https://prove2.me/submissions/74b69755-6c59-4921-ab21-e12ed36ef2a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_intS_mul
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_intS_one
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_intS_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum


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
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) := by
  intro μ
  have hS := hasSubst_of_constantCoeff_zero ha0
  rw [coeff_subst hS, finsum_eq_sum _ (coeff_subst_finite hS F μ)]
  refine VF.Ge.sum fun e _ => ?_
  rw [smul_eq_mul]
  refine (hF e).mul_int ?_
  have : IntS V (e.prod fun s m => a s ^ m) := by
    unfold Finsupp.prod
    exact Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => intS_pow (ha s) _
  exact this μ
end GlobalTheory.RowLaw.AddCurve
