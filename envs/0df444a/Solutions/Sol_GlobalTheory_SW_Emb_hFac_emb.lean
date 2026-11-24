-- Prove2me | solution 1 for GlobalTheory.SW.Emb.hFac_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:49.925443+00:00
-- url     : https://prove2.me/submissions/4495982e-496f-49ba-aa72-6a33d5855120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mul
import Theorems.Thm_GlobalTheory_SW_Emb_cor_map
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mulVec
import Theorems.Thm_GlobalTheory_SW_Emb_cons_dot
import Theorems.Thm_GlobalTheory_SW_Emb_cor_inv
import Theorems.Thm_GlobalTheory_SW_Emb_det_cor_one
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
theorem _root_.solution (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0)
    (z z' : CM Ψ n N) : hFac Ψ (emb γ) (corZ s Z) (corV z) (corV z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hDen_emb, det_cor_one, cor_inv _ (h τ)]
  simp only [emb, Matrix.toBlocks_fromBlocks₂₁, cor_map, map_zero, cor_mul, one_mul]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  show (Fin.cons 0 (z' τ k) : Fin (N + 1) → ℂ) ⬝ᵥ cor 0 _ *ᵥ (Fin.cons 0 (z τ k) : Fin (N + 1) → ℂ) = _
  rw [cor_mulVec, cons_dot]
  simp
end GlobalTheory.SW.Emb
