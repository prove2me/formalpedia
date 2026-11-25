-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.ev_formalSecondPointDerivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:26.865009+00:00
-- url     : https://prove2.me/submissions/0c341b10-c410-4c7a-b618-c9f1bff1a202

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_C
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
theorem _root_.solution {n : ℕ} (a : Pt k n d) (ha : GP a) (v : Fin d → k) (f : PS k 2 d) :
    ev ![a] (dy v f) = ∑ i, C (v i) * ev ![a, 0] (pderiv k ((1 : Fin 2), i) f) := by
  rw [dy, ev_sum _ (single_point_zero_constant ha)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gt_ev_mul _ (single_point_zero_constant ha), ev_C, formalSubst_single_of_formalSubst_two _ ha _ _ (gp_pt 0) gp_zero₂, gt_comp1_pt _ ha,
    formalComp_zero_left_point _ ha]
end GlobalTheory.GaugeDiv
