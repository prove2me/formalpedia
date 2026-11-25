-- Prove2me | solution 1 for GlobalTheory.SigmaDefect.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:45:28.812694+00:00
-- url     : https://prove2.me/submissions/f127b3bb-f1de-4254-a8a3-4a07ae571614

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Theorems.Thm_GlobalTheory_SigmaDefect_GP_FK
import Theorems.Thm_GlobalTheory_SigmaDefect_FK_unit_right
import Theorems.Thm_GlobalTheory_SigmaDefect_sgOf_defect
import Theorems.Thm_GlobalTheory_SigmaDefect_intAA_ev
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_IntSeries_intAA_C
import Theorems.Thm_GlobalTheory_IntSeries_intAA_X
import Theorems.Thm_GlobalTheory_IntSeries_intAA_map
import Theorems.Thm_GlobalTheory_IntSeries_intAA_mul
import Theorems.Thm_GlobalTheory_IntSeries_intAA_pderiv
import Theorems.Thm_GlobalTheory_IntSeries_intAA_sum
import Theorems.Thm_GlobalTheory_IntSeries_intAA_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_add
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.SigmaDefect
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (u : Fin d → R) (i : Fin d), IntAA (R := R) k (Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) - C ((sg1 k h).mulVec (fun j => algebraMap R k (u j)) i)) := by
  intro R _ d O _ _ k _ _ _ B h hc u i
  have hl : lin (fun j => algebraMap R k (u j)) (sgOf k h i) =
      (sg1 k h).mulVec (fun j => algebraMap R k (u j)) i := by
    simp only [lin, const_pderiv, Matrix.mulVec, dotProduct, sg1, mul_comm]
  rw [dof_eq _ (GP_FK B) (FK_unit_right B), sgOf_defect B h hc, dy_add, dy_add, formalSecondPointDerivative_subst_first_point,
    formalSecondPointDerivative_subst_second_point, hl, zero_add, add_sub_cancel_left]
  refine intAA_sum _ fun j _ => intAA_mul (intAA_C _) (intAA_ev _ hX0 ?_ (intAA_pderiv _
    (intAA_ev _ hDown ?_ (intAA_pderiv _ (intAA_map _)))))
  · intro l s
    fin_cases l
    exacts [intAA_X _, intAA_zero]
  · intro l s
    fin_cases l
    exacts [intAA_X _, intAA_X _, intAA_zero]
end GlobalTheory.SigmaDefect
