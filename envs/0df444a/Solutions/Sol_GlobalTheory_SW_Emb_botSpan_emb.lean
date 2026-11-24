-- Prove2me | solution 1 for GlobalTheory.SW.Emb.botSpan_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:15:01.752925+00:00
-- url     : https://prove2.me/submissions/5da92fef-a18f-4c94-909b-0e9d2feeb206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_botSpan_eq

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
omit [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution (γ : M2 E N) :
    botSpan (emb γ) = (E ∙ Pi.single (Sum.inr 0) 1) ⊔ (botSpan γ).map (extV E N) := by
  have h0 : emb γ (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    ext (j | j) <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [emb, Pi.single_apply]
  have h1 : ∀ a, emb γ (Sum.inr a) (Sum.inl 0) = 0 := by
    intro a; refine Fin.cases ?_ (fun a => ?_) a <;> simp [emb]
  have hs : (emb γ).submatrix (up N) (up N) = γ := by
    ext (i | i) (j | j) <;>
      simp [emb, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
  rw [botSpan_eq (emb γ) h0 h1, hs]
end GlobalTheory.SW.Emb
