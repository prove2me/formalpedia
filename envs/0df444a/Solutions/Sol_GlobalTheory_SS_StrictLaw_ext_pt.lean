-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.ext_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:41:08.517159+00:00
-- url     : https://prove2.me/submissions/8f492495-b18a-4967-95c0-ca969f57973d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_SS_StrictLaw_apply_eq_of_dominant
import Theorems.Thm_GlobalTheory_SS_StrictLaw_extends_comp
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isDominant_j

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {B B' : Over (Sp K)} {M : Model R A}
    {N : Model R B} {N' : Model R B'} {Q : Model R A'} {f : A ⟶ B} {f' : A ⟶ B'}
    {U U' : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} {g' : U'.toScheme ⟶ N'.Y.left}
    (h : Extends M N f U g) (h' : Extends M N' f' U' g') (p : N.Y ⟶ Q.Y) (p' : N'.Y ⟶ Q.Y)
    (e : f.left ≫ N.j ≫ p.left = f'.left ≫ N'.j ≫ p'.left)
    (u : U.toScheme) (u' : U'.toScheme) (hu : U.ι u = U'.ι u') :
    p.left (g u) = p'.left (g' u') := by
  have := Q.sep
  have := isDominant_j M
  let W := U ⊓ U'
  let a : W.toScheme ⟶ U.toScheme := M.Y.left.homOfLE inf_le_left
  let a' : W.toScheme ⟶ U'.toScheme := M.Y.left.homOfLE inf_le_right
  have ha : a ≫ U.ι = W.ι := Scheme.homOfLE_ι _ _
  have ha' : a' ≫ U'.ι = W.ι := Scheme.homOfLE_ι _ _
  have hd : IsDominant (M.j ∣_ W) := IsZariskiLocalAtTarget.restrict this W
  have hw : U.ι u ∈ W := ⟨u.2, hu ▸ u'.2⟩
  obtain ⟨w, hw⟩ : ∃ w : W.toScheme, W.ι w = U.ι u := ⟨⟨_, hw⟩, rfl⟩
  have key := apply_eq_of_dominant (a := a ≫ g ≫ p.left) (b := a' ≫ g' ≫ p'.left) Q.Y.hom
    (by simp only [Category.assoc, Over.w, h.1, h'.1, reassoc_of% ha, reassoc_of% ha'])
    (M.j ∣_ W) (by
      have e1 := extends_comp h (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a)
        (by rw [Category.assoc, ha, morphismRestrict_ι])
      have e2 := extends_comp h' (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a')
        (by rw [Category.assoc, ha', morphismRestrict_ι])
      rw [Category.assoc] at e1 e2
      rw [reassoc_of% e1, reassoc_of% e2, e]) w
  have b1 : a w = u := U.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha, hw])
  have b2 : a' w = u' := U'.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha', ← hu, hw])
  simpa only [Scheme.Hom.comp_apply, b1, b2] using key
end GlobalTheory.SS.StrictLaw
