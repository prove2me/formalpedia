-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.hasWt_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:21:03.546531+00:00
-- url     : https://prove2.me/submissions/d3282e36-fa5a-4b12-b075-b4372f157c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_appLE_app
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_appTop_appLE
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_appLE_appLE_top
import Theorems.Thm_GlobalTheory_ZJ_charUnit_zero_val


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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution {J : Type} (e : J → Γ(S', ⊤))
    (he : ∀ (Y : Over S) (s : Finset J) (x : J → Γ(Y.left, ⊤)),
      ∑ l ∈ s, (pullback.fst Y.hom f).appTop.hom (x l) * (pullback.snd Y.hom f).appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0)
    {V : G.left.Opens} (s : Finset J) (x : J → Γ(G.left, V))
    (hu : HasWt i' (F ⁻¹ᵁ V) (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) 0) :
    ∀ l ∈ s, HasWt i V (x l) 0 := by
  intro l hl Y t g h h'
  rw [torusCompat_iff] at hi
  let Y' : Over S' := Over.mk (pullback.snd Y.hom f)
  let p : Y'.left ⟶ Y.left := pullback.fst Y.hom f
  have hp : p ≫ Y.hom = Y'.hom ≫ f := pullback.condition
  let p' : Over.mk (Y'.hom ≫ f) ⟶ Y := Over.homMk p hp
  have hT := SplitTorus.isPullback_bcMap f X
  have wt : (p ≫ t.left) ≫ (splitTorus S X).hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  have wg : (p ≫ g.left) ≫ G.hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  let t' : Y' ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ wt) (hT.lift_snd _ _ wt)
  let g' : Y' ⟶ G' := Over.homMk (hF.1.lift _ _ wg) (hF.1.lift_snd _ _ wg)
  have ht' : t'.left ≫ SplitTorus.bcMap f X = p ≫ t.left := hT.lift_fst _ _ wt
  have hg' : p ≫ g.left = g'.left ≫ F := (hF.1.lift_fst _ _ wg).symm
  have hm : p ≫ ((t ≫ i) * g).left = ((t' ≫ i') * g').left ≫ F := by
    rw [← hF.2 Y' (t' ≫ i') g' (p' ≫ t ≫ i) (p' ≫ g) ?_ hg', ← MonObj.comp_mul]
    · rfl
    · change p ≫ t.left ≫ i.left = (t'.left ≫ i'.left) ≫ F
      rw [Category.assoc, ← hi, ← Category.assoc t'.left, ht', Category.assoc]
  have key : ∀ (r : Y ⟶ G) (r' : Y' ⟶ G') (_ : p ≫ r.left = r'.left ≫ F) (k : ⊤ ≤ r.left ⁻¹ᵁ V),
      ∃ k' : ⊤ ≤ r'.left ⁻¹ᵁ F ⁻¹ᵁ V, (r'.left.appLE _ ⊤ k').hom
        (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) =
        ∑ l ∈ s, p.appTop.hom ((r.left.appLE V ⊤ k).hom (x l)) * Y'.hom.appTop.hom (e l) := by
    intro r r' hr k
    have k₁ : ⊤ ≤ (p ≫ r.left) ⁻¹ᵁ V := p.preimage_mono k
    have k₂ : ⊤ ≤ (r'.left ≫ F) ⁻¹ᵁ V := hr ▸ k₁
    refine ⟨k₂, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, appLE_app _ F _ hr V k₂ k₁, appTop_appLE p r.left _ rfl V k k₁]
    exact congrArg (_ * ·) (appLE_appLE_top _ _ _ (Over.w r') _ _ _)
  obtain ⟨k₁, e₁⟩ := key _ _ hm h'
  obtain ⟨k₂, e₂⟩ := key _ _ hg' h
  have h0 := hu Y' t' g' k₂ k₁
  rw [e₁, e₂, charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h0
  rw [charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero]
  refine he Y s (fun l => (((t ≫ i) * g).left.appLE V ⊤ h').hom (x l) - (g.left.appLE V ⊤ h).hom (x l)) ?_ l hl
  rw [← h0]
  exact Finset.sum_congr rfl fun l _ => by rw [map_sub, sub_mul]; rfl
end GlobalTheory.ZJ.SplitPull
