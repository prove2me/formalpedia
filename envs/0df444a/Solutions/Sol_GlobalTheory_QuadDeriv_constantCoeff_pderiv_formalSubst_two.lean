-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.constantCoeff_pderiv_formalSubst_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:43.658845+00:00
-- url     : https://prove2.me/submissions/6603043a-f4ea-4e4d-8885-f95a366e631c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.QuadDeriv
theorem _root_.solution (b c : Pt k 1 d) (hb : GP b) (hc : GP c) (f : PS k 2 d) (l : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 1), l) (ev ![b, c] f)) =
      ∑ i, constantCoeff (pderiv k ((0 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (b i)) +
      ∑ i, constantCoeff (pderiv k ((1 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (c i)) := by
  rw [pderiv_ev _ (pair_points_zero_constant hb hc), Fin.sum_univ_two]
  simp only [map_add, map_sum, map_mul, gt_const_ev_eq _ (pair_points_zero_constant hb hc)]
  rfl
end GlobalTheory.QuadDeriv
