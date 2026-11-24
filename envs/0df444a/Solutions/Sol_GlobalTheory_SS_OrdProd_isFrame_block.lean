-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.isFrame_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:49:14.524985+00:00
-- url     : https://prove2.me/submissions/ce702cf8-c375-47f8-bb0c-16a13c2c2fb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
import Theorems.Thm_GlobalTheory_SS_OrdProd_jac_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution {P X Y : Over (Sp K)} {p : P ⟶ X} {q : P ⟶ Y} (H : IsPullback p.left q.left X.hom Y.hom)
    {I I' : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] {D : I → VF X} {D' : I' → VF Y} {E : I ⊕ I' → VF P}
    (a₁ : ∀ i, Lifts p (E (.inl i)) (D i)) (a₂ : ∀ i, Lifts q (E (.inl i)) (VF.zero Y))
    (b₁ : ∀ i, Lifts q (E (.inr i)) (D' i)) (b₂ : ∀ i, Lifts p (E (.inr i)) (VF.zero X))
    (hD : IsFrame D) (hD' : IsFrame D') : IsFrame E := by
  refine ⟨?_, fun z => ?_⟩
  · have h1 := hD.1
    have h2 : SmoothOfRelativeDimension (Fintype.card I') p.left :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (Fintype.card I')).of_isPullback H.flip hD'.1
    rw [Fintype.card_sum, add_comm, ← Over.w p]
    infer_instance
  · obtain ⟨V, t, hV, ht⟩ := hD.2 (p.left z)
    obtain ⟨V', t', hV', ht'⟩ := hD'.2 (q.left z)
    have b := jac_block a₁ a₂ b₁ b₂ V V' _ inf_le_left inf_le_right t t'
    have hu := (ht.map (p.left.appLE V (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_left).hom).mul
      (ht'.map (q.left.appLE V' (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_right).hom)
    rw [← b] at hu
    exact ⟨p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V', _, ⟨hV, hV'⟩, hu⟩
end GlobalTheory.SS.OrdProd
