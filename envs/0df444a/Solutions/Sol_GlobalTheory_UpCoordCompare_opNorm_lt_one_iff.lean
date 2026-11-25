-- Prove2me | solution 1 for GlobalTheory.UpCoordCompare.opNorm_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:10.925305+00:00
-- url     : https://prove2.me/submissions/18acdd69-c7bb-4c23-8c19-63170b4da564

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
open GlobalTheory GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section
namespace GlobalTheory.UpCoordCompare
theorem _root_.solution {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Z : Matrix m n ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ < 1 ↔ (1 - Zᴴ * Z).PosDef := by
  have key : ∀ v : EuclideanSpace ℂ n, star v.ofLp ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v.ofLp) =
      ((‖v‖ ^ 2 - ‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    have e1 : star v.ofLp ⬝ᵥ v.ofLp = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      have := EuclideanSpace.inner_eq_star_dotProduct v v
      rw [inner_self_eq_norm_sq_to_K] at this
      rw [dotProduct_comm]; push_cast; exact this.symm
    have e2 : star (Z *ᵥ v.ofLp) ⬝ᵥ (Z *ᵥ v.ofLp) = ((‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ) := by
      have := EuclideanSpace.inner_eq_star_dotProduct (Matrix.toEuclideanLin Z v)
        (Matrix.toEuclideanLin Z v)
      rw [inner_self_eq_norm_sq_to_K] at this
      rw [dotProduct_comm]; push_cast; exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, e1, e2, ← Complex.ofReal_sub]
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z) with hT
  constructor
  · intro hn
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)) ?_
    intro x hx
    set v : EuclideanSpace ℂ _ := WithLp.toLp 2 x with hv
    have hv0 : 0 < ‖v‖ := by
      rw [norm_pos_iff]; intro h; apply hx
      simpa [hv] using congrArg WithLp.ofLp h
    have h1 : ‖Matrix.toEuclideanLin Z v‖ ≤ _ := T.le_opNorm v
    have h2 : ‖Matrix.toEuclideanLin Z v‖ < ‖v‖ := by nlinarith
    have h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v‖ := norm_nonneg _
    have := key v
    rw [show v.ofLp = x from rfl] at this
    rw [this]
    exact Complex.zero_lt_real.2 (by nlinarith)
  · intro hpd
    obtain ⟨v0, hv0, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (T.continuous.norm.continuousOn)
    have hv1 : ‖v0‖ ≤ 1 := by simpa using hv0
    have hlt : ‖T v0‖ < 1 := by
      by_cases h0 : v0 = 0
      · simp [h0]
      · have hne : v0.ofLp ≠ 0 := fun h => h0 (by ext i; simpa using congrFun h i)
        have := hpd.dotProduct_mulVec_pos hne
        rw [key, Complex.zero_lt_real] at this
        have h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v0‖ := norm_nonneg _
        have h4 : ‖T v0‖ = ‖Matrix.toEuclideanLin Z v0‖ := rfl
        rw [h4]
        nlinarith [norm_nonneg v0]
    refine lt_of_le_of_lt ?_ hlt
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx => ?_
    exact hmax (by simp [hx] : x ∈ Metric.closedBall (0 : EuclideanSpace ℂ n) 1)
end GlobalTheory.UpCoordCompare
