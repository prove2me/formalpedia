-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.shift_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:05.493965+00:00
-- url     : https://prove2.me/submissions/09e9bd2c-e40b-40a6-92ad-f01d278cd400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (z P Q : Matrix (Fin n) (Fin N) ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) :
    (z + Q.map conj + P.map conj * Zᵀ)ᵀ = zᵀ + Qᴴ + Z * Pᴴ := by
  rw [transpose_add, transpose_add, transpose_mul, transpose_transpose]
  rfl
end GlobalTheory.SW.HeisH
