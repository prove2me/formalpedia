-- Prove2me | solution 1 for GlobalTheory.SW.Emb.hAct_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:39.139854+00:00
-- url     : https://prove2.me/submissions/0f6b3f64-ca73-40c2-8f50-1f9653071610

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
import Theorems.Thm_GlobalTheory_SW_Emb_cor_inv
import Theorems.Thm_GlobalTheory_SW_Emb_hDen_emb

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
theorem _root_.solution (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    hAct Ψ (emb γ) (corZ s Z) = corZ s (hAct Ψ γ Z) := by
  funext τ
  simp only [hAct]
  rw [hDen_emb, cor_inv _ (h τ)]
  simp only [emb, corZ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, one_mul, add_zero, mul_one]
  rfl
end GlobalTheory.SW.Emb
