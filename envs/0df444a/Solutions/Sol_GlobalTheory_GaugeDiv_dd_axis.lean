-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dd_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:52.70301+00:00
-- url     : https://prove2.me/submissions/c94966f6-b37a-49bd-8956-00fd4278eb1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_dof_graph
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_zero_pts
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
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
theorem _root_.solution {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (u : Fin d → k) {G : PS k 2 d} (hG : ev (n := 1) ![pt k d 0, 0] G = 0) :
    ev (n := 1) ![pt k d 0, 0] (DD F 0 u G) = 0 := by
  have h := dof_graph hF hU gp_zero₂ (by
    rw [formalComp_zero_left_point _ hF, formalComp_zero_left_point _ (gp_pt 0), formalComp_zero_left_point _ (gp_pt 1)]
    funext i
    rw [addOf, ev_zero_pts _ (by intro j; fin_cases j <;> rfl), hF i, map_zero]
    rfl) u 0 0 (by simp [lin]) G
  rw [hG, Nat.cast_zero, zero_mul, add_zero] at h
  rw [← h]
  simp [Dof]
end GlobalTheory.GaugeDiv
