-- Prove2me | solution 1 for GlobalTheory.Up.DivInFFPf.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:28:10.99973+00:00
-- url     : https://prove2.me/submissions/ff3a5a85-f3d1-4c08-a633-f45f71fdb3b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
import Theorems.Thm_GlobalTheory_Up_DivInFFPf_phi_of_mem
import Theorems.Thm_GlobalTheory_Up_DivInFFPf_sum_pnorm_pos
import Theorems.Thm_GlobalTheory_Up_Wdiv_eq_pnorm
import Theorems.Thm_GlobalTheory_Up_pnorm_sq_eq_exp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)
namespace GlobalTheory.Up.DivInFFPf
theorem _root_.solution (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : ∃ k, Fl.s k x ≠ 0) :
    phi Xa Fl n h x = ENNReal.ofReal (‖h x‖ ^ 2) * Wdiv X Xa Fl n x := by
  have hw := sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz x hx)
  have hs' := sum_pnorm_pos (la := Xa.L) hx hs
  rw [phi_of_mem Xa Fl n h hx, Wdiv_eq_pnorm Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw,
    ENNReal.ofReal_rpow_of_pos hs', pnorm_sq_eq_exp hx (Xa.Fp + n • Xa.L),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  ring
end GlobalTheory.Up.DivInFFPf
