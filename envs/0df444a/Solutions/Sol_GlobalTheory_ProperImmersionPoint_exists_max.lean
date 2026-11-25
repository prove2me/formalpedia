-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.exists_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:44.846244+00:00
-- url     : https://prove2.me/submissions/0c107721-5ebe-43db-96b4-7510b750e5d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CptDifferentiable
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_pnorm_sq
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_pnorm_pos
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_ratio_pos
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_ratio_contOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_pointwiseNorm_invariance_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
open GlobalTheory GlobalTheory.ProperImmersionPoint
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ProperImmersionPoint
theorem _root_.solution {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hne : ∃ x ∈ X.dom, et x ≠ 0)
    (hprop : ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) :
    ∃ x ∈ X.dom, et x ≠ 0 ∧ ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x := by
  obtain ⟨x1, hx1, he1⟩ := hne
  have h1 : 0 < ratio X L eW a w et x1 := ratio_pos hnz hx1 he1
  have hP : PnormInvStatement (E := E) := pointwiseNorm_invariance_holds
  have hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      ratio X L eW a w et (lact γ (rmul x b)) = ratio X L eW a w et x := by
    intro γ hγ x hx b hb
    unfold ratio
    rw [hP r X _ _ het γ hγ x hx b hb]
    congr 2
    exact Finset.sum_congr rfl fun k _ => by rw [hP r X _ _ (hw k) γ hγ x hx b hb]
  obtain ⟨K, hK, hKd, hKs⟩ := hprop _ h1
  have hbig : ∀ y ∈ X.dom, ratio X L eW a w et x1 ≤ ratio X L eW a w et y →
      ∃ y' ∈ K, ratio X L eW a w et y' = ratio X L eW a w et y := by
    intro y hy hle
    obtain ⟨γ, hγ, b, hb, hk⟩ := hKs y hy
      ((le_div_iff₀ (pow_pos (sum_pnorm_pos hnz hy) a)).1 hle)
    exact ⟨_, hk, hinv γ hγ y hy b hb⟩
  obtain ⟨y1, hy1K, hy1⟩ := hbig x1 hx1 le_rfl
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨y1, hy1K⟩
    ((ratio_contOn (a := a) hw hnz het).mono hKd)
  have hx1x : ratio X L eW a w et x1 ≤ ratio X L eW a w et x := hy1 ▸ isMaxOn_iff.1 hxmax y1 hy1K
  refine ⟨x, hKd hxK, fun h0 => ?_, fun y hy => ?_⟩
  · have : ratio X L eW a w et x ≤ 0 := by
      unfold ratio
      rw [pnorm_sq X _ _ (hKd hxK), h0]
      simp
    linarith
  · rcases lt_or_ge (ratio X L eW a w et y) (ratio X L eW a w et x1) with h | h
    · exact h.le.trans hx1x
    · obtain ⟨y', hy'K, hy'⟩ := hbig y hy h
      exact hy' ▸ isMaxOn_iff.1 hxmax y' hy'K
end GlobalTheory.ProperImmersionPoint
