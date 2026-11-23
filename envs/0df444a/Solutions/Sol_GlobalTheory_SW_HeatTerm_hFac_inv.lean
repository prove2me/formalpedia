-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.hFac_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:08.83359+00:00
-- url     : https://prove2.me/submissions/9acf6d3c-ec67-4d53-ba61-fee9c4dd3d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    (hFac Ψ γ Z z z')⁻¹ = ∏ τ : Ψ,
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ) (z τ) (z' τ) := by
  rw [hFac, ← Finset.prod_inv_distrib]
  rfl
end GlobalTheory.SW.HeatTerm
