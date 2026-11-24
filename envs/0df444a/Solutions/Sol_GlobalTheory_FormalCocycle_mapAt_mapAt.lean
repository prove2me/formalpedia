-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.mapAt_mapAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:11.725821+00:00
-- url     : https://prove2.me/submissions/b4744589-ec96-44cc-939a-8f7294322710

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen1
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt
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
theorem _root_.solution {φ ψ : Pt k 1 d} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (h : comp1 φ ψ = pt k (n := 1) d 0) {u : Fin d → MvPowerSeries μ k} (hu : Cen u) :
    mapAt φ (mapAt ψ u) = u := by
  have hb := hasSubst_pts (cen1 hu)
  have h1 := subst_mapAt hb φ (u := ψ) hψ
  have h2 : mapAt φ ψ = pt k (n := 1) d 0 := h
  rw [h2, subst_pt (cen1 hu)] at h1
  exact h1.symm
end GlobalTheory.FormalCocycle
