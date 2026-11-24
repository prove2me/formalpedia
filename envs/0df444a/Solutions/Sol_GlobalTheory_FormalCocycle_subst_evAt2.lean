-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.subst_evAt2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:46.442331+00:00
-- url     : https://prove2.me/submissions/f2b84a29-8442-4c5d-b8d9-ecaa44456f75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen2
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
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (f : PS k 2 d) :
    subst b (evAt ![u, v] f) = evAt ![fun i => subst b (u i), fun i => subst b (v i)] f := by
  rw [subst_evAt hb (cen2 hu hv)]
  congr 1; funext j; fin_cases j <;> rfl
end GlobalTheory.FormalCocycle
