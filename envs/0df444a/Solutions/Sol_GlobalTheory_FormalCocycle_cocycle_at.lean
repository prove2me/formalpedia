-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.cocycle_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:50.697842+00:00
-- url     : https://prove2.me/submissions/9851b7c4-150e-4581-99c9-efc13aaabaae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen4
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt3
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_addAt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_addAt
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle
variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}
namespace GlobalTheory.FormalCocycle
theorem _root_.solution {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0) {c : PS k 3 d}
    (h : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
        ev (n := 4) ![addOf F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
        ev (n := 4) ![pt k d 0, addOf F (pt k d 1) (pt k d 2), pt k d 3] c)
    {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (ht : Cen t) :
    evAt ![u, v, t] c + evAt ![addAt F u v, w, t] c =
      evAt ![v, w, t] c + evAt ![u, addAt F v w, t] c := by
  have ha := cen4 hu hv hw ht
  have hb := hasSubst_pts ha
  have h0 : evAt ![pt k (n := 4) d 0, pt k d 1, pt k d 3] c +
        evAt ![addAt F (pt k (n := 4) d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      evAt ![pt k (n := 4) d 1, pt k d 2, pt k d 3] c +
        evAt ![pt k (n := 4) d 0, addAt F (pt k d 1) (pt k d 2), pt k d 3] c := h
  have h1 := congrArg (subst (fun p : Fin 4 × Fin d => ![u, v, w, t] p.1 p.2)) h0
  rw [subst_add hb, subst_add hb, subst_evAt3 hb (cen_pt 0) (cen_pt 1) (cen_pt 3),
    subst_evAt3 hb (cen_addAt hF (cen_pt 0) (cen_pt 1)) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 1) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 0) (cen_addAt hF (cen_pt 1) (cen_pt 2)) (cen_pt 3),
    subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_addAt hb F (cen_pt 1) (cen_pt 2)] at h1
  simp only [subst_pt ha] at h1
  exact h1
end GlobalTheory.FormalCocycle
