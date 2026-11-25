-- Prove2me | solution 1 for GlobalTheory.ChartChange.zOf_zOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:30:02.091051+00:00
-- url     : https://prove2.me/submissions/7f5bdf40-ae52-436d-a30a-b3929e4b4c2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_invF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ChartChange
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ExtFPf
namespace GlobalTheory.ChartChange
theorem _root_.solution {r : ℕ} {X : Data E r} {x1 b c : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hbc : ∀ τ, mat b τ * mat c τ = 1) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (hcz : cpt X (rmul x1 c) z ∈ cell D) :
    D.zOf (cpt X (rmul x1 b) (D.zOf (cpt X (rmul x1 c) z))) = z := by
  obtain ⟨-, hβ, he⟩ := D.split _ hcz.1 hcz.2
  set w := D.zOf (cpt X (rmul x1 c) z)
  set β := D.bOf (cpt X (rmul x1 c) z)
  have hx1 := IW.orth_mem_dom X x1 ho
  have key : cpt X (rmul x1 b) w = rmul (cpt X x1 z) (invF X β) := by
    funext τ
    have e : mat x1 τ * mat c τ * mat (nmat X z) τ = mat x1 τ * mat (nmat X w) τ * mat β τ := congrFun he τ
    have hu : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr (hx1 τ).1
    have huβ : IsUnit (mat β τ).det := isUnit_iff_ne_zero.mpr (hβ τ).1
    have e2 : mat c τ * mat (nmat X z) τ = mat (nmat X w) τ * mat β τ := by
      have := congrArg (fun M => (mat x1 τ)⁻¹ * M) e
      simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
    have e3 : mat (nmat X z) τ = mat b τ * mat (nmat X w) τ * mat β τ := by
      rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hbc τ, Matrix.one_mul]
    show mat x1 τ * mat b τ * mat (nmat X w) τ = mat x1 τ * mat (nmat X z) τ * (mat β τ)⁻¹
    rw [e3]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huβ, Matrix.mul_one]
  rw [key]
  exact (D.uniq z hz _ (invF_mem X hβ)).2.1
end GlobalTheory.ChartChange
