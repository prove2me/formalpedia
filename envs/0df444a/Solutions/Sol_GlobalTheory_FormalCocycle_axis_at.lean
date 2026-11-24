-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.axis_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:49.064883+00:00
-- url     : https://prove2.me/submissions/7fc23e2f-2521-4192-b335-592c75c7c413

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_ev_eq
import Theorems.Thm_GlobalTheory_FormalCocycle_cen2
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_zero
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt3
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_zero_pt
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1


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
theorem _root_.solution {c : PS k 3 d} (h : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0)
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t) : evAt ![0, u, t] c = 0 := by
  have ha := cen2 hu ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 2 × Fin d => ![u, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb cen_zero (cen_pt 0) (cen_pt 1), subst_zero_pt hb, subst_pt ha,
    subst_pt ha, GlobalTheory.FormalCalc.subst_zero' hb] at h1
  exact h1
end GlobalTheory.FormalCocycle
