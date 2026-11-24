-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.nabVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:21.625494+00:00
-- url     : https://prove2.me/submissions/09db4755-7d4f-4dba-80cf-f3175a8744fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_FK_eq
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_actK_eq

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial ι k) : C.nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by
  unfold FB.nabVal FB.hL
  rw [FK_eq hF, actK_eq hA]
end GlobalTheory.JetSer.IntTrans
