-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.sum_rows_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:13.952403+00:00
-- url     : https://prove2.me/submissions/a81acd36-4a31-4cb6-b219-ab0b810e8cf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_eq_trace

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
theorem _root_.solution {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ A *ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ A *ᵥ V k := by
  rw [sum_rows_eq_trace, sum_rows_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc P,
    Matrix.mul_assoc P, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc _ Qᵀ, hPQ,
    Matrix.mul_one]
end GlobalTheory.SW.UnitaryLeft
