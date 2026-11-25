-- Prove2me | solution 1 for GlobalTheory.Up.pnorm_sq_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:28:20.288569+00:00
-- url     : https://prove2.me/submissions/02e0b368-a211-4288-b3d6-daaa4eb0fe3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_ne_zero


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}
namespace GlobalTheory.Up
theorem _root_.solution (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    X.pnorm la P x ^ 2 = Real.exp (-phla X la x) * ‖P x‖ ^ 2 := by
  have hpos : 0 < X.nfac la x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _
  have h : Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
    unfold phla
    rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) * ((2 : ℕ) : ℝ) by
      push_cast; ring, Real.exp_mul, Real.exp_log hpos, Real.rpow_natCast]
  rw [h]
  show (‖P x‖ * X.nfac la x) ^ 2 = _
  ring
end GlobalTheory.Up
