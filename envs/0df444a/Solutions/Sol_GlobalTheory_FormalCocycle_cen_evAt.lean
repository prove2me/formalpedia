-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.cen_evAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:47.834161+00:00
-- url     : https://prove2.me/submissions/a9956b52-054e-4f96-9bd9-7f94e350007d

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
    {F : Fin d → PS k m d} (hF : ∀ i, constantCoeff (F i) = 0) : Cen fun i => evAt a (F i) :=
  fun i => constantCoeff_subst_eq_zero (hasSubst_pts ha) (fun p => ha p.1 p.2) (hF i)
end GlobalTheory.FormalCocycle
