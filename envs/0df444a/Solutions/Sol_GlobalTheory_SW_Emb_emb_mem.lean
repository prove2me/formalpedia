-- Prove2me | solution 1 for GlobalTheory.SW.Emb.emb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:50.664469+00:00
-- url     : https://prove2.me/submissions/d2f0a085-41e0-4e8a-b787-e6e6e9a37881

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mul
import Theorems.Thm_GlobalTheory_SW_Emb_cor_add
import Theorems.Thm_GlobalTheory_SW_Emb_cor_neg
import Theorems.Thm_GlobalTheory_SW_Emb_cor_one
import Theorems.Thm_GlobalTheory_SW_Emb_cor_zero
import Theorems.Thm_GlobalTheory_SW_Emb_ccT_cor
import Theorems.Thm_GlobalTheory_SW_Emb_ccT_fromBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.Emb
noncomputable section
section Corner
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
end Corner
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
private theorem fromBlocks_cor_mul_fromBlocks_cor {R : Type} [CommRing R] {N : ℕ} (a b c d a' b' c' d' : R)
    (A B C D A' B' C' D' : Matrix (Fin N) (Fin N) R) :
    Matrix.fromBlocks (cor a A) (cor b B) (cor c C) (cor d D) *
        Matrix.fromBlocks (cor a' A') (cor b' B') (cor c' C') (cor d' D') =
      Matrix.fromBlocks (cor (a * a' + b * c') (A * A' + B * C')) (cor (a * b' + b * d') (A * B' + B * D'))
        (cor (c * a' + d * c') (C * A' + D * C')) (cor (c * b' + d * d') (C * B' + D * D')) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [cor_mul, cor_add]
end
end GlobalTheory.SW.Emb
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) : emb γ ∈ UU E (N + 1) := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [← Matrix.fromBlocks_toBlocks γ, ccT_fromBlocks, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h'
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp h'
  have hJ : Matrix.J (Fin (N + 1)) E =
      Matrix.fromBlocks (cor 0 0) (cor (-1) (-1)) (cor 1 1) (cor 0 0) := by
    rw [Matrix.J, cor_zero, ← cor_neg, cor_one]
  show ccT (emb γ) * Matrix.J (Fin (N + 1)) E * emb γ = Matrix.J (Fin (N + 1)) E
  rw [hJ, emb, ccT_fromBlocks, ccT_cor, ccT_cor, ccT_cor, ccT_cor, fromBlocks_cor_mul_fromBlocks_cor, fromBlocks_cor_mul_fromBlocks_cor]
  simp only [h11, h12, h21, h22, cc, map_one, map_zero]
  congr 1 <;> congr 1 <;> ring
end GlobalTheory.SW.Emb
