-- Prove2me | solution 1 for GlobalTheory.ThetaExist.paTh_centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:35.045622+00:00
-- url     : https://prove2.me/submissions/044ea604-4328-4862-a03c-cb3b354124b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_neg_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_conj_eq_sub


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
theorem _root_.solution (Y : GT ι) (v : EuclideanSpace ℂ ι) :
    paTh Y 1 (expH v) v = cexp (Real.pi * Hf v v) *
      ∑' γ : lat Y.b, (Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ)) *
        cexp (2 * Real.pi * I * ((Hf v γ).im : ℂ)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [Hf_self g, sub_eq_add_neg v, Hf_add_left, Hf_neg_left, ← Hf_conj v g, conj_eq_sub (Hf v g),
    ← Complex.exp_add, Complex.ofReal_exp, mul_assoc (Y.ka g), ← Complex.exp_add,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring
end GlobalTheory.ThetaExist
