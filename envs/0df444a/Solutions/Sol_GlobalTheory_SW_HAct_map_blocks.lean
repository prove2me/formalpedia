-- Prove2me | solution 1 for GlobalTheory.SW.HAct.map_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:08.889318+00:00
-- url     : https://prove2.me/submissions/de089ae5-52f1-4dba-ab8f-04aa2acd3452

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
theorem _root_.solution (τ : E →+* ℂ) (γ : M2 E N) :
    γ.map τ = fromBlocks (γ.toBlocks₁₁.map τ) (γ.toBlocks₁₂.map τ) (γ.toBlocks₂₁.map τ)
      (γ.toBlocks₂₂.map τ) := by
  rw [← fromBlocks_map, fromBlocks_toBlocks]
end GlobalTheory.SW.HAct
