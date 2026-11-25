-- Prove2me | solution 1 for GlobalTheory.weilIs_grpPullback_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:49.311927+00:00
-- url     : https://prove2.me/submissions/d2ee75b3-ffd1-40cd-b524-a57c04b533a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_GlobalTheory_WeilPull_exists_rel_down
import Theorems.Thm_GlobalTheory_WeilPull_exists_rel_up
import Theorems.Thm_GlobalTheory_WeilPull_commIsOf_iff_of_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open WeilPull
namespace GlobalTheory
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x * y = y * x → x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ f φ L L' hL hL' hp ⟨w, hw⟩ T k x y x₀ y₀ c hc ex ey
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  let V₀ : (Over.mk (T.hom ≫ f)).left.Opens := V
  let τ : (overRes V).left ⟶ (overRes V₀).left := 𝟙 V.toScheme
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 V.toScheme))
  have hτ : τ ≫ (overRes V₀).hom = (overRes V).hom ≫ f := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have mv : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      τ ≫ (overResι V₀ ≫ a₀).left = (overResι V ≫ a).left ≫ φ := fun {a a₀} e =>
    (Category.id_comp _).trans ((congrArg (V.ι ≫ ·) e).trans (Category.assoc _ _ _).symm)
  have cm : ∀ {θx θy : ThetaGrp G' L' k (overRes V)} {θx₀ θy₀ : ThetaGrp G L k (overRes V₀)},
      θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y → θx₀.pt = overResι V₀ ≫ x₀ → θy₀.pt = overResι V₀ ≫ y₀ →
      Rel hp τ hτ w θx θx₀ → Rel hp τ hτ w θy θy₀ →
      (CommIsOf G' L' k θx θy (unitRes V c) ↔ CommIsOf G L k θx₀ θy₀ (unitRes V₀ c)) :=
    fun h₁ h₂ h₃ h₄ mx my => commIsOf_iff_of_rel hp τ hτ hL hL' w
      (by rw [h₁, h₂, ← MonObj.comp_mul, ← MonObj.comp_mul, hc]) (by rw [h₁, h₃]; exact mv ex)
      (by rw [h₂, h₄]; exact mv ey) mx my _ _ (fun Z r z => congrArg (fun q => gm q z ⊤ (unitRes V c))
        (Category.comp_id r))
  have up : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a →
        ∃ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ h => exists_rel_up hp τ hτ hL hL' w hw _ θ (by rw [h]; exact mv e)
  have down : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ →
        ∃ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ₀ h => exists_rel_down hp τ hτ hL hL' w hw _ θ₀ (by rw [h]; exact mv e)
  constructor
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := up ex θx h₁
    obtain ⟨b, hb, -⟩ := up ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := down ex a ha
    obtain ⟨b', hb', my⟩ := down ey b hb
    exact (cm ha' hb' ha hb mx my).1 (H a' b' ha' hb')
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := down ex θx h₁
    obtain ⟨b, hb, -⟩ := down ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := up ex a ha
    obtain ⟨b', hb', my⟩ := up ey b hb
    exact (cm ha hb ha' hb' mx my).2 (H a' b' ha' hb')
end GlobalTheory
