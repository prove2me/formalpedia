-- Prove2me | solution 1 for GlobalTheory.TorusUnit.ext_of_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:59.053705+00:00
-- url     : https://prove2.me/submissions/0ad68d03-8a12-484b-9f69-e17644717161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_isPullback_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}
attribute [local instance] TorusInj.zuAlg
namespace GlobalTheory.TorusUnit
theorem _root_.solution {f g : Γ((splitTorus S X ⊗ Y).left, ⊤)}
    (h : ∀ p : Y.left, ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y ∧ (expand y).hom f = (expand y).hom g) : f = g := by
  choose R y hy hp he using h
  refine Scheme.OpenCover.ext_elem f g (Scheme.Cover.mkOfCovers Y.left
    (fun p => Spec (grpAlg X (R p)))
    (fun p => prodPoint (fromInt X (R p)) (Spec.map (const X (R p)) ≫ y p)) (fun q => ?_)
    (fun p => ?_)) (fun p => ?_)
  · obtain ⟨r, hr⟩ := hp ((snd (splitTorus S X) Y).left q)
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_expand (X := X) (y ((snd (splitTorus S X) Y).left q))) q r hr.symm
    exact ⟨_, z, hz⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_expand (X := X) (y p)).flip (hy p)
  · exact (Scheme.ΓSpecIso (grpAlg X (R p))).commRingCatIsoToRingEquiv.injective (he p)
end GlobalTheory.TorusUnit
