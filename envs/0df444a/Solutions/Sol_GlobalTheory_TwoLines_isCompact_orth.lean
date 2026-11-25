-- Prove2me | solution 1 for GlobalTheory.TwoLines.isCompact_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:21:12.361736+00:00
-- url     : https://prove2.me/submissions/8cc69c78-086b-48f6-9be6-611cb9de1482

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_gram_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
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
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) :
    IsCompact {x : Frame X.Ψ 2 | IsOrth X x} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : {x : Frame X.Ψ 2 | IsOrth X x} = ⋂ τ, ⋂ a, ⋂ b, {x | x τ 0 a * conj (x τ 0 b) +
        x τ 1 a * conj (x τ 1 b) =
          Matrix.diagonal (fun a : Fin 2 => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) a b} := by
      ext x
      simp only [IsOrth, hG, ← Matrix.ext_iff, gram_one, Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ?_ continuous_const
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ 2)) (r := 1)).subset fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2
      fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
    have h := congrFun (congrFun (hx τ) b) b
    rw [hG, gram_one, hp, Matrix.diagonal_apply_eq, Complex.mul_conj, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, sgn, if_pos b.2] at h
    have h' : ‖x τ 0 b‖ ^ 2 + ‖x τ 1 b‖ ^ 2 = 1 := by exact_mod_cast h
    have h4 : ‖x τ a b‖ ^ 2 ≤ 1 := by
      fin_cases a
      · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖x τ 1 b‖]
      · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖x τ 0 b‖]
    nlinarith [norm_nonneg (x τ a b)]
end GlobalTheory.TwoLines
