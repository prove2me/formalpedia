-- Prove2me | solution 1 for GlobalTheory.SW.HAct.left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.086198+00:00
-- url     : https://prove2.me/submissions/1c5662bf-dd0c-4878-97cd-0b150b40d098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) :
    -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) * γ = 1 := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT γ), h',
    Matrix.J_squared, neg_neg]
end GlobalTheory.SW.HAct
