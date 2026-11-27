-- Prove2me | solution 1 for GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:39.699484+00:00
-- url     : https://prove2.me/submissions/04596a86-8b63-4e1a-bc65-37a0d720bb00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnitStatement
import Theorems.Thm_GlobalTheory_MulJacobian_det_jac_mulF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ), ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv R ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  first | exact @GlobalTheory.MulJacobian.det_jac_mulF | exact GlobalTheory.MulJacobian.det_jac_mulF | (intros; apply GlobalTheory.MulJacobian.det_jac_mulF <;> assumption)
end _root_.GlobalTheory.T
