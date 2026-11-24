-- Prove2me | solution 1 for GlobalTheory.ThetaExist.summable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:46.189937+00:00
-- url     : https://prove2.me/submissions/0fe61398-5884-4255-90f2-e68608d9b11c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq


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
theorem _root_.solution (Y : GT ι) {a : ℝ} (ha : 0 < a) :
    Summable fun γ : lat Y.b => Real.exp (-a * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) :=
  summable_lattice_exp_neg_mul_norm_sq (lat Y.b) ha
end GlobalTheory.ThetaExist
