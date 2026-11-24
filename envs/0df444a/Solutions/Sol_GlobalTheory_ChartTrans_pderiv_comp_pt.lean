-- Prove2me | solution 1 for GlobalTheory.ChartTrans.pderiv_comp_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:15.406746+00:00
-- url     : https://prove2.me/submissions/bc71e9be-fc73-43f5-9d75-e743bf4c85b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution (φ : Pt k 1 d) (a b : Fin 2) (i l : Fin d) :
    pderiv k (a, i) (comp1 φ (pt k (n := 2) d b) l) =
      if a = b then ev ![pt k (n := 2) d b] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by
  change pderiv k (a, i) (ev ![pt k (n := 2) d b] (φ l)) = _
  rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, pt]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]
end GlobalTheory.ChartTrans
