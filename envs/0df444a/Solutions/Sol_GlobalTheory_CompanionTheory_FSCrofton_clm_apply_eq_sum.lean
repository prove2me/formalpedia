-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.clm_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:29:50.879576+00:00
-- url     : https://prove2.me/submissions/0d3e7847-b318-4ee2-a406-96999d47ef7e

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  simp [map_sum]
end GlobalTheory.CompanionTheory.FSCrofton
