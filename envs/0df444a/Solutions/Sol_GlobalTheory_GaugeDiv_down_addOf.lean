-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.down_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:22.771439+00:00
-- url     : https://prove2.me/submissions/45ed34a6-e83f-46ab-960c-5f2f4e4b09be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_down_up
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt


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
theorem _root_.solution {F : Pt k 2 d} (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) (a : Fin 2) :
    evP (n := 2) ![pt k d 0, pt k d 1, 0] (addOf F (up (pt k d a)) (pt k d 2)) = pt k d a := by
  have ha : GP (pt k (n := 2) d a) := gp_pt a
  rw [evP_addOf _ hDown _ _ _ (constantCoeff_up_eq_zero₂ ha) (gp_pt 2), down_up, evP_pt _ hDown]
  have h := congrArg (fun b => comp1 b (pt k (n := 2) d a)) hU
  simp only [gt_comp1_pt _ ha] at h
  rw [← h]
  funext i
  change _ = ev ![pt k d a] (ev ![pt k d 0, 0] (F i))
  rw [formalSubst_single_of_formalSubst_two _ ha _ _ (gp_pt 0) gp_zero₂, gt_comp1_pt _ ha, formalComp_zero_left_point _ ha, h]
  rfl
end GlobalTheory.GaugeDiv
