-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.of_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:16.650139+00:00
-- url     : https://prove2.me/submissions/ee162eff-3d63-4295-a34b-8af17b3ee1ca

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
theorem _root_.solution (A : Matrix (Fin N) (Fin N) ℂ) (w : Matrix (Fin n) (Fin N) ℂ) :
    (Matrix.of fun k => w k ᵥ* A) = w * A := by
  ext k a
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
end GlobalTheory.SW.HeisH
