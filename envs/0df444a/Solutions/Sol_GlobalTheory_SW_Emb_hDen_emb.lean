-- Prove2me | solution 1 for GlobalTheory.SW.Emb.hDen_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:18.187858+00:00
-- url     : https://prove2.me/submissions/c8e9fd2a-c213-4ae8-b3e6-2b5bc4afb8bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mul
import Theorems.Thm_GlobalTheory_SW_Emb_cor_add
import Theorems.Thm_GlobalTheory_SW_Emb_cor_map

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen Ψ γ Z τ) := by
  simp only [hDen, emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, zero_mul, zero_add]
end GlobalTheory.SW.Emb
