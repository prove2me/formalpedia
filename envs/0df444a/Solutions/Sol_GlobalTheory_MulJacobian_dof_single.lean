-- Prove2me | solution 1 for GlobalTheory.MulJacobian.dof_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:25.739671+00:00
-- url     : https://prove2.me/submissions/79d65f49-7b17-4886-a301-ce89f2307110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open GlobalTheory GlobalTheory.MulJacobian
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.MulJacobian
theorem _root_.solution (G : FGLaw R d) (c : R) (l : Fin d) (f : PS R 1 d) :
    Dof G.F (Pi.single l c) f = C c * ∑ j, pderiv R ((0 : Fin 1), j) f * invMat G j l := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, invMat, Matrix.of_apply]
    ring
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, map_zero, zero_mul]
  · simp
end GlobalTheory.MulJacobian
