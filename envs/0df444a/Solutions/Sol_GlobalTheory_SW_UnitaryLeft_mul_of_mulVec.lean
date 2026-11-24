-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.mul_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:41.307528+00:00
-- url     : https://prove2.me/submissions/dde636ab-cfde-45c1-b362-c8f4a7d5360c

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution (P : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : Matrix (Fin n) (Fin N) ℂ) :
    P * (Matrix.of fun k => A *ᵥ z k) = Matrix.of fun k => A *ᵥ (P * z) k := by
  have e : ∀ w : Matrix (Fin n) (Fin N) ℂ, (Matrix.of fun k => A *ᵥ w k) = w * Aᵀ := by
    intro w; ext k a
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [e, e, Matrix.mul_assoc]
end GlobalTheory.SW.UnitaryLeft
