-- Prove2me | solution 1 for GlobalTheory.RigidIsoCube.surjective_appTop_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:43.362558+00:00
-- url     : https://prove2.me/submissions/58d938da-acfa-40e1-8e2a-0ed31bcd72cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RigidIsoCube
namespace GlobalTheory.RigidIsoCube
theorem _root_.solution {Y S Y' S' : Scheme.{0}} {q : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {j : S' ⟶ S}
    (h : IsPullback q p' p j) [Flat p] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hs : Function.Surjective p'.appTop.hom) : Function.Surjective p.appTop.hom := by
  have : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact q := MorphismProperty.of_isPullback h.flip ‹_›
  have inj : Function.Injective q.appTop.hom := q.app_injective ⊤
  have cmp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)),
      f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  intro a
  obtain ⟨c, hc⟩ := hs (q.appTop.hom a)
  let e' : S' ⟶ Y' := h.lift (j ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : e' ≫ q = j ≫ e := h.lift_fst _ _ _
  have h₂ : e' ≫ p' = 𝟙 _ := h.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom a) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h₁, h₂, Scheme.Hom.id_appTop] at this
    rw [cmp]; exact this
  refine ⟨e.appTop.hom a, inj ?_⟩
  rw [← hc, hc', cmp q p, cmp p' j, h.w]
end GlobalTheory.RigidIsoCube
