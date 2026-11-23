-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.trace_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.81732+00:00
-- url     : https://prove2.me/submissions/1f3785e0-922a-4d6f-8244-f6b4abcf7641

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) :
    LinearMap.trace ℝ W (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ W f).re := by
  classical
  let b := Module.finBasis ℂ W
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b),
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul,
    Finset.sum_add_distrib]
end GlobalTheory.PeriodNonempty
