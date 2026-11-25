-- Prove2me | solution 1 for GlobalTheory.Up.phla_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:07.843993+00:00
-- url     : https://prove2.me/submissions/967d4093-677d-4bc5-aa7c-0ca1cad953a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}
namespace GlobalTheory.Up
theorem _root_.solution (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) (k : ℕ) :
    phla X (la + k • la') x = phla X la x + k * phla X la' x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.Up
