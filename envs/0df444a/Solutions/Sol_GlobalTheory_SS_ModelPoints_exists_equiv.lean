-- Prove2me | solution 1 for GlobalTheory.SS.ModelPoints.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:15.747048+00:00
-- url     : https://prove2.me/submissions/b5383bac-108a-464e-9d7c-81f3634812b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpSchemePointsModelOverField
import Theorems.Thm_GlobalTheory_SS_ModelPoints_exists_push_equiv
import Theorems.Thm_GlobalTheory_SS_ModelPoints_exists_comp_equiv

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ModelPoints
namespace GlobalTheory.SS.ModelPoints
theorem _root_.solution {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl
end GlobalTheory.SS.ModelPoints
