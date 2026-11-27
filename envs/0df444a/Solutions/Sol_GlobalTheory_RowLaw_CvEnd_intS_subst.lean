-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.intS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:57:56.831695+00:00
-- url     : https://prove2.me/submissions/c52ddc2f-4d36-49b2-bc7f-c369219ce04e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_intS_mul
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_intS_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {V : VF C} {σ τ : Type}
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (hi : ∀ s, IntS V (a s))
    {F : MvPowerSeries σ C} (hF : IntS V F) : IntS V (subst a F) := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun x => V.Ge 0 x) (VF.Ge.zero 0) (fun _ _ => VF.Ge.add) fun μ => ?_
  rw [smul_eq_mul]
  refine (hF μ).mul_int ?_
  revert e
  show IntS V _
  refine Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => ?_
  show IntS V (a s ^ μ s)
  induction μ s with
  | zero => rw [pow_zero]; exact intS_one
  | succ k ih => rw [pow_succ]; exact intS_mul ih (hi s)
end GlobalTheory.RowLaw.CvEnd
