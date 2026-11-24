-- Prove2me | solution 1 for GlobalTheory.ThetaExist.re_Hf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:54.857816+00:00
-- url     : https://prove2.me/submissions/4c84ef82-12a1-4355-a398-f827a0d46210

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_eq_inner


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
theorem _root_.solution (v a : EuclideanSpace ℂ ι) : (Hf v a).re ≤ ‖v‖ * ‖a‖ := by
  rw [FPw.Hf_eq_inner, mul_comm]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
end GlobalTheory.ThetaExist
