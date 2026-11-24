-- Prove2me | solution 1 for GlobalTheory.ThetaExist.differentiable_paTh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:07.746953+00:00
-- url     : https://prove2.me/submissions/3c6013ae-2d6f-41d0-ad43-eb6c9399acd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_ThetaExist_differentiable_Hf
import Theorems.Thm_GlobalTheory_ThetaExist_norm_term_le
import Theorems.Thm_GlobalTheory_ThetaExist_summable_gauss
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
open GlobalTheory GlobalTheory.ThetaExist
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaExist
theorem _root_.solution (Y : GT ι) (w : EuclideanSpace ℂ ι) :
    Differentiable ℂ (paTh Y 1 (expH w)) := by
  rw [← differentiableOn_univ]
  refine SCV.differentiableOn_tsum_of_locally_normal
    (F := fun (γ : lat Y.b) v => Y.ka γ * paU 1 γ (expH w) v) isOpen_univ (fun γ => ?_)
    (fun x _ => ?_)
  · have h1 := differentiable_Hf (γ : EuclideanSpace ℂ ι)
    have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf (v - γ.1) w :=
      (differentiable_Hf w).comp (differentiable_id.sub_const _)
    unfold paU expH
    refine Differentiable.differentiableOn ?_
    fun_prop
  · refine ⟨Metric.ball 0 (max (‖x‖ + 1) ‖w‖), Metric.isOpen_ball.mem_nhds ?_, _,
      (summable_gauss Y (a := Real.pi / 4) (by positivity)).mul_left _,
      fun γ z hz => norm_term_le Y w (le_max_right _ _) γ (mem_ball_zero_iff.1 hz).le⟩
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
end GlobalTheory.ThetaExist
