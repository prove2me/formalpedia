-- Prove2me | solution 1 for GlobalTheory.ActDescent.exists_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:00.203364+00:00
-- url     : https://prove2.me/submissions/b2307516-8346-4b0e-9112-426ec466e574

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
omit [Flat j] [Surjective j]
namespace GlobalTheory.ActDescent
theorem _root_.solution {O : Type} [CommRing O] {G : Over S} [GrpObj G] {G' : Over U} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G j φ) (i : OAct O G') {s : Set O}
    (hs : Subring.closure s = ⊤) (hi : ∀ x ∈ s, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) (c : O) :
    ∃ f : G ⟶ G, (i.act c).left ≫ φ = φ ≫ f.left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hG.1.w
  let ρ := pushHom hG G'
  have key : ∀ (x : G' ⟶ G') (f : G ⟶ G), x.left ≫ φ = φ ≫ f.left ↔ ρ x = φ₀ ≫ f := fun x f =>
    ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun z => z.left) h⟩
  have h0 : i.act 0 = 1 := by
    have := i.add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hneg : ∀ x, i.act (-x) = (i.act x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← i.add, neg_add_cancel, h0])
  have hc : c ∈ Subring.closure s := hs ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => exact hi x hx
  | zero => exact ⟨1, (key _ _).2 (by rw [h0, map_one, MonObj.comp_one])⟩
  | one => exact ⟨𝟙 _, by rw [i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    exact ⟨f * g, (key _ _).2 (by rw [i.add, map_mul, MonObj.comp_mul, (key _ _).1 hf, (key _ _).1 hg])⟩
  | neg x _ hx =>
    obtain ⟨f, hf⟩ := hx
    exact ⟨f⁻¹, (key _ _).2 (by rw [hneg, map_inv, GrpObj.comp_inv, (key _ _).1 hf])⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    exact ⟨f ≫ g, by
      rw [i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]⟩
end GlobalTheory.ActDescent
