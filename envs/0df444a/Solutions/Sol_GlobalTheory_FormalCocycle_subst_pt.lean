-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.subst_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:46.655668+00:00
-- url     : https://prove2.me/submissions/a66bca43-1536-443b-88d0-bea70d18b8c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts

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
theorem _root_.solution {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j))
    (j : Fin m) : (fun i => subst (fun p : Fin m × Fin d => a p.1 p.2) (pt k d j i)) = a j :=
  funext fun i => subst_X (hasSubst_pts ha) (j, i)
end GlobalTheory.FormalCocycle
