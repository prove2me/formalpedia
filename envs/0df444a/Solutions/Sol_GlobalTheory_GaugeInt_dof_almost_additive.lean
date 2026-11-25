-- Prove2me | solution 1 for GlobalTheory.GaugeInt.dof_almost_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:22.182408+00:00
-- url     : https://prove2.me/submissions/50fe0015-1b24-4239-85bb-31923447bee2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_int_pderiv
import Theorems.Thm_GlobalTheory_GaugeInt_dy_sub
import Theorems.Thm_GlobalTheory_GaugeInt_dy_int
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_add
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution {F : Pt k 2 d} (hF : GP F)
    (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    (f : PS k 1 d)
    (hf : ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f - ev ![F] f ∈ IntS φ 2 d) :
    Dof F v f - C (lin v f) ∈ IntS φ 1 d := by
  have h := neg_mem (dy_int hv (int_pderiv hf))
  rwa [dy_sub, dy_add, formalSecondPointDerivative_subst_first_point, formalSecondPointDerivative_subst_second_point, zero_add, neg_sub, ← dof_eq F hF hU] at h
end GlobalTheory.GaugeInt
