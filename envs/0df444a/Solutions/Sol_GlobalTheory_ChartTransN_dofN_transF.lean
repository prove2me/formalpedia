-- Prove2me | solution 1 for GlobalTheory.ChartTransN.dofN_transF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:51.213001+00:00
-- url     : https://prove2.me/submissions/91c36e82-0991-48ba-b2e6-5388bec234e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
import Theorems.Thm_GlobalTheory_ChartTransN_dofN_ev
import Theorems.Thm_GlobalTheory_ChartTransN_dofN_inCol_ne
import Theorems.Thm_GlobalTheory_ChartTransN_dofN_eq_sum
import Theorems.Thm_GlobalTheory_ChartTransN_unit_right
import Theorems.Thm_GlobalTheory_ChartTrans_dof_transF
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum
import Theorems.Thm_GlobalTheory_NabCol_dofN_inCol
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X
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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol
open GlobalTheory GlobalTheory.ChartTransN
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.ChartTransN
theorem _root_.solution (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hφ (gp_pt c)
  have hc : ∀ (c : Fin n) l, comp1 φ (pt k (n := n) d c) l = inCol c (φ l) := fun _ _ => rfl
  have hcol : ∀ f : PS k 1 d, ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (inCol b f) =
      inCol b (ev (n := 1) ![φ] f) := by
    intro f
    unfold inCol
    rw [gt_ev_ev' _ _ hΦ (gp b), gt_ev_ev' _ _ (gp b) (single_point_zero_constant hφ), vec1, vec1, evP_pt _ hΦ]
    rfl
  rw [dofN_ev _ _ _ _ hΦ, dofN_eq_sum G.F, ev_sum _ hΦ, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ hΦ, hcol, ← dof_transF G.F G.const (unit_right G) φ φi hinv, gt_ev_X _ (single_point_zero_constant hφ), hc,
      dofN_inCol, mul_comm]
    rfl
  · intro c _ hcb
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hc, dofN_inCol_ne _ hcb, mul_zero]
  · simp
end GlobalTheory.ChartTransN
