-- Prove2me | solution 1 for GlobalTheory.TorusToProper.point_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:13.479727+00:00
-- url     : https://prove2.me/submissions/29930b99-9adf-4303-b54c-d5f428a0a817

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
namespace GlobalTheory.TorusToProper
theorem _root_.solution {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V] [Field F]
    [Algebra K F] [Algebra V F] [IsScalarTower K V F] [IsFractionRing V F]
    {B : Over (Spec (CommRingCat.of K))} [IsProper B.hom] (p : sp K F ⟶ B) :
    ∃ b : sp K V ⟶ B, spm (IsScalarTower.toAlgHom K V F) ≫ b = p := by
  have hE : ValuativeCriterion.Existence B.hom := by
    have h : UniversallyClosed B.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq B.hom :=
    { R := V, K := F, i₁ := p.left, i₂ := Spec.map (CommRingCat.ofHom (algebraMap K V)),
      commSq := ⟨(Over.w p).trans (Over.w (spm (IsScalarTower.toAlgHom K V F))).symm⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  exact ⟨Over.homMk l h2, by ext1; exact h1⟩
end GlobalTheory.TorusToProper
