-- Prove2me | solution 1 for GlobalTheory.SigmaDefect.ev_sgOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:49.301723+00:00
-- url     : https://prove2.me/submissions/7039cfc3-c812-4f89-aa88-b83c6c13dd0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
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
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]
namespace GlobalTheory.SigmaDefect
theorem _root_.solution (h : PS k 2 d) (i : Fin d) {n : ℕ} (a : Pt k n d) (ha : GP a) :
    ev ![a] (sgOf k h i) = -ev ![a, 0] (pderiv k ((1 : Fin 2), i) h) := by
  have h1 : ∀ j, GP ((![a] : Fin 1 → Pt k n d) j) := single_point_zero_constant ha
  have e : sgOf k h i = 0 - ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h) := by
    rw [zero_sub]; rfl
  have z : evP ![a] (0 : Pt k 1 d) = 0 := funext fun _ => gt_ev_zero _ h1
  rw [e, gt_ev_sub _ h1, gt_ev_zero _ h1, zero_sub, gt_ev_ev' _ _ h1 hX0, eval_pair_points,
    evP_pt _ h1, z]
  rfl
end GlobalTheory.SigmaDefect
