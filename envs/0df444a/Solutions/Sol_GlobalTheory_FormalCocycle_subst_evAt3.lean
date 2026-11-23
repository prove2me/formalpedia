-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.subst_evAt3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:28.626744+00:00
-- url     : https://prove2.me/submissions/636fde04-ed1c-46fc-aa86-b1ef83f61b86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen3
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
    {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (f : PS k 3 d) :
    subst b (evAt ![u, v, w] f) =
      evAt ![fun i => subst b (u i), fun i => subst b (v i), fun i => subst b (w i)] f := by
  rw [subst_evAt hb (cen3 hu hv hw)]
  congr 1; funext j; fin_cases j <;> rfl
end GlobalTheory.FormalCocycle
