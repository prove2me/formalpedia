-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dd_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:17:42.395359+00:00
-- url     : https://prove2.me/submissions/adfc1d6a-5896-452a-84ce-6851f9f0342d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_ev_formalSecondPointDerivative
import Theorems.Thm_GlobalTheory_GaugeDiv_thirdPointDerivativeAtZeroSeries_mem_integral
import Theorems.Thm_GlobalTheory_GaugeDiv_thirdPointDerivativeAtZeroSeries_add_sub
import Theorems.Thm_GlobalTheory_GaugeDiv_thirdPointDerivativeAtZeroSeries_twoPointLift
import Theorems.Thm_GlobalTheory_GaugeDiv_thirdPointDerivativeAtZeroSeries_addOf_right
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_di_ev
import Theorems.Thm_GlobalTheory_GaugeInt_ev_defR
import Theorems.Thm_GlobalTheory_GaugeInt_ip3
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_GaugeInt_ip_up
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_right
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hr : DI φ (defR F g)) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) :
    DD F 1 v g - ev (n := 2) ![pt k d 0] (dy v g) ∈ IntS φ 2 d := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have h := neg_mem (thirdPointDerivativeAtZeroSeries_mem_integral hv (di_ev (ip3 (ip_up (ip_pt 0)) (ip_up (ip_pt 1)) (ip_pt 2)) hr))
  rw [ev_defR F iF.gp g _ _ _ (constantCoeff_up_eq_zero₂ p0) (constantCoeff_up_eq_zero₂ p1) (gp_pt 2), thirdPointDerivativeAtZeroSeries_add_sub, thirdPointDerivativeAtZeroSeries_twoPointLift,
    thirdPointDerivativeAtZeroSeries_addOf_right iF.gp hU, zero_add, neg_sub] at h
  convert h using 2
  rw [ev_formalSecondPointDerivative _ p0, dz3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dz_right g _ p0]
end GlobalTheory.GaugeDiv
