-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.mapAt_addAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:51.938599+00:00
-- url     : https://prove2.me/submissions/c3fd2a0f-b8d4-4f61-95f4-08e95962c511

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen2
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_addAt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_addAt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_mapAt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle
variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}
namespace GlobalTheory.FormalCocycle
theorem _root_.solution {ℓ : Pt k 1 d} (hℓ : ∀ i, constantCoeff (ℓ i) = 0)
    {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    (h : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    mapAt ℓ (addAt F u v) = mapAt ℓ u + mapAt ℓ v := by
  have ha := cen2 hu hv
  have hb := hasSubst_pts ha
  have h2 : mapAt ℓ (addAt F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      mapAt ℓ (pt k (n := 2) d 0) + mapAt ℓ (pt k (n := 2) d 1) := h
  have h1 := subst_mapAt hb ℓ (cen_addAt hF (cen_pt (n := 2) 0) (cen_pt 1))
  rw [h2, subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_pt ha, subst_pt ha] at h1
  have h3 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 0)
  have h4 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 1)
  rw [subst_pt ha] at h3 h4
  refine h1.symm.trans (funext fun i => ?_)
  rw [Pi.add_apply, subst_add hb, congrFun h3 i, congrFun h4 i]
  rfl
end GlobalTheory.FormalCocycle
