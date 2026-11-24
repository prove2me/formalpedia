-- Prove2me | solution 1 for GlobalTheory.oAct_descend_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:16.648712+00:00
-- url     : https://prove2.me/submissions/962ff1fd-a970-4a08-aa86-4f24b27f9b8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators
import Theorems.Thm_GlobalTheory_ActDescent_over_hom_ext
import Theorems.Thm_GlobalTheory_ActDescent_exists_oAct
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₀)) (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A₀] [GrpObj A] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (act₀ : J → (A₀ ⟶ A₀)), Subring.closure (Set.range a) = ⊤ → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A₀ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∃ r : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A₀, (∀ j, r.act (a j) = act₀ j) ∧ ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a K₀ K _ _ i A₀ A _ _ _ φ act act₀ hgen hG hact
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  haveI : Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  let ρ : Over.mk (A.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) ⟶ A₀ := Over.homMk φ hG.1.w
  have hiff : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), z.left ≫ φ = φ ≫ g.left →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g := fun z g h => Over.OverMorphism.ext (by exact h)
  have hback : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g →
      z.left ≫ φ = φ ≫ g.left := fun z g h => by
    have h' := congrArg (fun m => m.left) h
    exact h'
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hD : ∀ c, ∃ g : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ g.left := by
    intro c
    have hc : c ∈ Subring.closure (Set.range a) := hgen ▸ Subring.mem_top c
    induction hc using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨act₀ k, hact k⟩
    | zero =>
      refine ⟨1, hback _ _ ?_⟩
      rw [h0, map_one, MonObj.comp_one]
    | one =>
      exact ⟨𝟙 _, by simp [act.one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g * g', hback _ _ ?_⟩
      rw [act.add, map_mul, hiff _ _ hg, hiff _ _ hg', MonObj.comp_mul]
    | neg x _ hx =>
      obtain ⟨g, hg⟩ := hx
      have hneg : act.act (-x) = (act.act x)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← act.add, add_neg_cancel, h0]
      refine ⟨g⁻¹, hback _ _ ?_⟩
      rw [hneg, map_inv, hiff _ _ hg, GrpObj.comp_inv]
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g ≫ g', ?_⟩
      rw [act.mul, Over.comp_left, Over.comp_left, Category.assoc, hg', ← Category.assoc, hg,
        Category.assoc]
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.ActDescent.exists_oAct hG act hD
  refine ⟨r, fun k => ?_, hr⟩
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hG.1
  rw [← hr, hact]
end _root_.GlobalTheory
end GlobalTheory
