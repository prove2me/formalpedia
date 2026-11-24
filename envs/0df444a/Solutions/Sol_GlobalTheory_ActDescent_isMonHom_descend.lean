-- Prove2me | solution 1 for GlobalTheory.ActDescent.isMonHom_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:04.527548+00:00
-- url     : https://prove2.me/submissions/5b1530ef-5592-4772-824b-52db7832ff98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators
import Theorems.Thm_GlobalTheory_ActDescent_over_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
private theorem mul_comp_of_descends_monHom {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) (T : Over S) (x y : T ⟶ G) :
    (x * y) ≫ f = x ≫ f * y ≫ f := by
  have hT : IsPullback (pullback.fst T.hom j) (pullback.snd T.hom j) T.hom j :=
    IsPullback.of_hasPullback _ _
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hT
  let T' : Over U := (Over.pullback j).obj T
  let ρ : Over.mk (T'.hom ≫ j) ⟶ T :=
    Over.homMk (pullback.fst T.hom j) (by simp [T', pullback.condition])
  let up : (T ⟶ G) → (T' ⟶ G') := fun z => Over.homMk
    (hG.1.lift (pullback.fst T.hom j ≫ z.left) T'.hom (by simp [T', pullback.condition]))
    (hG.1.lift_snd _ _ _)
  have hup : ∀ z : T ⟶ G, (up z).left ≫ φ = pullback.fst T.hom j ≫ z.left :=
    fun z => hG.1.lift_fst _ _ _
  have hpush : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG T' (up z) = ρ ≫ z :=
    fun z => Over.OverMorphism.ext (by exact hup z)
  have hpushH : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hH T' (up z ≫ f') = ρ ≫ z ≫ f := by
    intro z
    ext1
    change ((up z).left ≫ f'.left) ≫ ψ = pullback.fst T.hom j ≫ z.left ≫ f.left
    rw [Category.assoc, hf, ← Category.assoc, hup, Category.assoc]
  change (ρ ≫ (x * y) ≫ f).left = (ρ ≫ (x ≫ f * y ≫ f)).left
  rw [MonObj.comp_mul ρ (x ≫ f), ← hpushH x, ← hpushH y, ← map_mul, ← MonObj.mul_comp,
    ← Category.assoc, MonObj.comp_mul ρ x y, ← hpush x, ← hpush y, ← map_mul]
  change ((up x * up y).left ≫ φ) ≫ f.left = ((up x * up y) ≫ f').left ≫ ψ
  rw [Over.comp_left, Category.assoc, Category.assoc, hf]
end GlobalTheory.ActDescent
namespace GlobalTheory
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
namespace GlobalTheory.ActDescent
namespace _root_.GlobalTheory.ActDescent
theorem _root_.solution {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) : IsMonHom f := by
  have key := mul_comp_of_descends_monHom hG hH f' f hf
  refine ⟨?_, ?_⟩
  · have h1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have h := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h
      exact mul_eq_left.mp h.symm
    simpa [Hom.one_def] using h1
  · have h := key _ (fst G G) (snd G G)
    simpa [Hom.mul_def] using h
end _root_.GlobalTheory.ActDescent
end GlobalTheory.ActDescent
