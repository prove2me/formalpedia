-- Prove2me | solution 1 for GlobalTheory.SW.HermComp.map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:24.406803+00:00
-- url     : https://prove2.me/submissions/bdd1cf73-d281-415e-b912-715a82070fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermComp
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermComp
theorem _root_.solution (τ : E →+* ℂ) (γ : M2 E N) (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by
  have hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
    simpa using Matrix.map_J (Fin N) τ
  have hc : (ccT γ).map τ = (γ.map τ)ᴴ := by
    ext a b
    simp only [ccT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, cc]
    exact IsCMField.complexEmbedding_complexConj E τ _
  have := congrArg (fun M : M2 E N => M.map τ) h
  simpa only [Matrix.map_mul, hJ, hc] using this
end GlobalTheory.SW.HermComp
