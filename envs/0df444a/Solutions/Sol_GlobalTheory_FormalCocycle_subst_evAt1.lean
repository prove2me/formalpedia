-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.subst_evAt1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:44.752516+00:00
-- url     : https://prove2.me/submissions/51fb0584-907c-49c0-94a7-af1d36c6808c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen1
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt

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
theorem _root_.solution {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) (f : PS k 1 d) :
    subst b (evAt ![u] f) = evAt ![fun i => subst b (u i)] f := by
  rw [subst_evAt hb (cen1 hu)]
  congr 1; funext j; fin_cases j; rfl
end GlobalTheory.FormalCocycle
