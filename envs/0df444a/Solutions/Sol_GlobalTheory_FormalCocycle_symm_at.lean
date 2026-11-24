-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.symm_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:53.066607+00:00
-- url     : https://prove2.me/submissions/6995c432-ec17-4299-b051-8c15711cc467

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_ev_eq
import Theorems.Thm_GlobalTheory_FormalCocycle_cen3
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt3
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt

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
theorem _root_.solution {c : PS k 3 d} (h : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c)
    {u v t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (ht : Cen t) :
    evAt ![v, u, t] c = evAt ![u, v, t] c := by
  have ha := cen3 hu hv ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 3 × Fin d => ![u, v, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb (cen_pt 1) (cen_pt 0) (cen_pt 2), subst_pt ha,
    subst_pt ha, subst_pt ha] at h1
  exact h1
end GlobalTheory.FormalCocycle
