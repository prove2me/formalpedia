-- Prove2me | solution 1 for GlobalTheory.bilinPart_sub_eigen_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:47:46.837382+00:00
-- url     : https://prove2.me/submissions/8b2bd8cc-c5f6-44e9-8c57-0504473bf3d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeSubIsBiadd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Theorems.Thm_GlobalTheory_bilinPart_sub_adjoint

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory
theorem _root_.solution (B : FB R d O) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h)
    (hh' : B.IsCanonGauge k h') (u v : Fin d → k) (a : O) (s t : k)
    (hu : (dAct k B a).mulVec u = s • u) (hv : (dAct k B (star a)).mulVec v = t • v) (hst : IsUnit (s - t)) :
    dotProduct u ((bilinPart k (h' - h)).mulVec v) = 0 := by
  have e := congrArg (fun M => dotProduct u (Matrix.mulVec M v)) (bilinPart_sub_adjoint B h h' hh hh' a)
  simp only [← Matrix.mulVec_mulVec] at e
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hu, hv, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul] at e
  rw [← hst.mul_right_eq_zero, sub_mul, e, sub_self]
end GlobalTheory
