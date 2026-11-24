-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_grpObj_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:45.461916+00:00
-- url     : https://prove2.me/submissions/f65963f6-f0df-4086-98c1-44d1924017f6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp
theorem _root_.solution {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
