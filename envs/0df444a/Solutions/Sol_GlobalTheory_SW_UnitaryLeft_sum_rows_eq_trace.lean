-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.sum_rows_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:43.088921+00:00
-- url     : https://prove2.me/submissions/cfec15f3-d36e-4d6a-9710-43f4480ca2f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution {n N : ℕ} (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, U k ⬝ᵥ A *ᵥ V k = (U * A * Vᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory.SW.UnitaryLeft
