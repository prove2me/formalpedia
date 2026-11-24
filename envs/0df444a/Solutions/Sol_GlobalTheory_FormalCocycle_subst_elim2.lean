-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.subst_elim2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:43.318071+00:00
-- url     : https://prove2.me/submissions/39aa5aa8-d506-482e-9f02-330afe0ae9f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_elim2
import Theorems.Thm_GlobalTheory_FormalCalc_subst_sumElim


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
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t)
    (K : MvPowerSeries (Fin d ⊕ Fin d) k) :
    subst b (subst (Sum.elim u t) K) =
      subst (Sum.elim (fun i => subst b (u i)) fun i => subst b (t i)) K := by
  rw [subst_comp_subst_apply (hasSubst_elim2 hu ht) hb, GlobalTheory.FormalCalc.subst_sumElim]
end GlobalTheory.FormalCocycle
