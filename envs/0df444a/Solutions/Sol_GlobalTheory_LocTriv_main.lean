-- Prove2me | solution 1 for GlobalTheory.LocTriv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:01:58.327163+00:00
-- url     : https://prove2.me/submissions/2cb6a522-4887-4608-9071-f95696a23271

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_LocTriv_of_basis
import Theorems.Thm_GlobalTheory_LocTriv_over_ext
import Theorems.Thm_GlobalTheory_LocTriv_incl_le
import Theorems.Thm_GlobalTheory_LocTriv_eq_of_units
import Theorems.Thm_GlobalTheory_LocTriv_exists_sum
import Theorems.Thm_GlobalTheory_LocTriv_eq_zero_of_sum
import Theorems.Thm_GlobalTheory_LocTriv_comp_eq
import Theorems.Thm_GlobalTheory_LocTriv_exists_point
import Theorems.Thm_GlobalTheory_Retract_smooth
import Theorems.Thm_GlobalTheory_Retract_surjective_retraction
import Theorems.Thm_GlobalTheory_TorusGrading_exists_point
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
namespace GlobalTheory.LocTriv
theorem _root_.solution : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left → (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) → Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧ ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g) :=  by
  intro S X _ G B _ i q hi hq hloc
  choose V hbV hV h₀ hinj hU u hu using hloc
  have hA : ∀ b, IsAffineOpen (q.left ⁻¹ᵁ V b) := fun b => (hV b).preimage q.left
  have hB : ∀ b, (q.left.app (V b)).hom.Flat ∧
      ∃ σ : Γ(G.left, q.left ⁻¹ᵁ V b) →+* Γ(B.left, V b), σ.comp (q.left.app (V b)).hom = RingHom.id _ :=
    fun b => of_basis _ (u b) (exists_sum (hV b) (h₀ b) (hU b) (u b) (hu b))
      (fun c hc => eq_zero_of_sum (hV b) (h₀ b) (hU b) (u b) (hu b) (hinj b) c hc)
  have hsec : ∀ b, ∃ s : (V b).toScheme ⟶ (q.left ⁻¹ᵁ V b).toScheme, s ≫ (q.left ∣_ V b) = 𝟙 _ := by
    intro b
    obtain ⟨σ, hσ⟩ := (hB b).2
    refine ⟨(hV b).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ) ≫ (hA b).isoSpec.inv, ?_⟩
    have e1 : q.left.app (V b) ≫ CommRingCat.ofHom σ = 𝟙 _ := by
      ext r
      exact RingHom.congr_fun hσ r
    rw [← cancel_mono (V b).ι]
    simp only [Category.assoc, morphismRestrict_ι, Category.id_comp]
    rw [← Category.assoc (hA b).isoSpec.inv, IsAffineOpen.isoSpec_inv_ι,
      ← IsAffineOpen.SpecMap_appLE_fromSpec q.left (hV b) (hA b) le_rfl, ← Spec.map_comp_assoc,
      ← Scheme.Hom.app_eq_appLE, e1, Spec.map_id, Category.id_comp, IsAffineOpen.isoSpec_hom_fromSpec]
  have hcov : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hbV x⟩
  refine ⟨⟨fun {Z} t t' h => ?_⟩, ?_, ⟨fun b => ?_⟩, fun hGs => ?_, fun Z g g' => ⟨fun h => ?_, ?_⟩⟩
  · apply over_ext
    intro z
    refine ⟨(t ≫ i).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left ((t ≫ i).left z))), hbV _, ?_⟩
    refine eq_of_units (hU (q.left ((t ≫ i).left z)))
      (fun χ => u (q.left ((t ≫ i).left z)) (Multiplicative.ofAdd χ)) (hu (q.left ((t ≫ i).left z)))
      (incl_le (t ≫ i) (q.left ⁻¹ᵁ V (q.left ((t ≫ i).left z)))) ?_
    rw [Category.assoc, Category.assoc, h]
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
      ((RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left)]
    intro x
    refine ⟨⟨V (q.left x), hV _⟩, ⟨q.left ⁻¹ᵁ V (q.left x), hA _⟩, hbV _, le_rfl, ?_⟩
    rw [← Scheme.Hom.app_eq_appLE]
    exact (hB _).1
  · obtain ⟨s, hs⟩ := hsec b
    obtain ⟨x, hx⟩ := (GlobalTheory.Retract.surjective_retraction hs).surj ⟨b, hbV b⟩
    refine ⟨(q.left ⁻¹ᵁ V b).ι x, ?_⟩
    have e2 : (V b).ι ((q.left ∣_ V b) x) = q.left ((q.left ⁻¹ᵁ V b).ι x) :=
      congrArg (fun f => f.base x) (morphismRestrict_ι q.left (V b))
    rw [← e2, hx]
    rfl
  · have h1 : HasRingHomProperty @AlgebraicGeometry.Smooth RingHom.Smooth := inferInstance
    have h2 : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth)
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Smooth) (f := B.hom) V hcov fun b => ?_
    obtain ⟨s, hs⟩ := hsec b
    have hr : (q.left ∣_ V b) ≫ ((V b).ι ≫ B.hom) = (q.left ⁻¹ᵁ V b).ι ≫ G.hom := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
    exact GlobalTheory.Retract.smooth hs hr
  · obtain ⟨W, hWg⟩ : ∃ W : Z.left → Z.left.Opens,
        ∀ z, W z = g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))) := ⟨_, fun _ => rfl⟩
    have hW : ∀ z, z ∈ W z := fun z => by rw [hWg z]; exact hbV _
    have hWI : ∀ z, ⊤ ≤ (incl Z (W z) ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))) := fun z => by
      rw [hWg z]
      exact incl_le g _
    have hWc : TopologicalSpace.IsOpenCover W := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z⟩
    have hloc : ∀ z, ∃ t : Over.mk ((W z).ι ≫ Z.hom) ⟶ splitTorus S X,
        incl Z (W z) ≫ g' = (t ≫ i) * (incl Z (W z) ≫ g) := by
      intro z
      refine exists_point (hV (q.left (g.left z))) (h₀ (q.left (g.left z))) (hU (q.left (g.left z)))
        (u (q.left (g.left z))) (hu (q.left (g.left z))) (hWI z) ?_
      rw [Category.assoc, Category.assoc, h]
    choose t ht using hloc
    let 𝒰 := Z.left.openCoverOfIsOpenCover W hWc
    have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ (t x).left =
        pullback.snd (𝒰.f x) (𝒰.f y) ≫ (t y).left := by
      intro x y
      let PO : Over S := Over.mk (pullback.fst (𝒰.f x) (𝒰.f y) ≫ (W x).ι ≫ Z.hom)
      let a : PO ⟶ Over.mk ((W x).ι ≫ Z.hom) := Over.homMk (pullback.fst (𝒰.f x) (𝒰.f y)) rfl
      let a' : PO ⟶ Over.mk ((W y).ι ≫ Z.hom) := Over.homMk (pullback.snd (𝒰.f x) (𝒰.f y))
        (pullback.condition_assoc (f := 𝒰.f x) (g := 𝒰.f y) Z.hom).symm
      have hc : a ≫ incl Z (W x) = a' ≫ incl Z (W y) := by
        apply Over.OverMorphism.ext
        exact pullback.condition (f := 𝒰.f x) (g := 𝒰.f y)
      have hgl : ⊤ ≤ (a ≫ incl Z (W x) ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left x))) := by
        rw [Over.comp_left, Scheme.Hom.comp_preimage, top_le_iff.1 (hWI x)]
        exact fun p _ => trivial
      have hti : (a ≫ t x) ≫ i = (a' ≫ t y) ≫ i := by
        have e1 := congrArg (a ≫ ·) (ht x)
        have e2 := congrArg (a' ≫ ·) (ht y)
        simp only [comp_mul, ← Category.assoc] at e1 e2
        rw [← hc] at e2
        exact _root_.mul_right_cancel (e1.symm.trans e2)
      have key : a ≫ t x = a' ≫ t y :=
        eq_of_units (hU (q.left (g.left x))) (fun χ => u (q.left (g.left x)) (Multiplicative.ofAdd χ))
          (hu (q.left (g.left x))) hgl hti
      exact congrArg (fun f => f.left) key
    let T := 𝒰.glueMorphisms (fun x => (t x).left) hcompat
    have hT : ∀ x, 𝒰.f x ≫ T = (t x).left := fun x => 𝒰.ι_glueMorphisms _ hcompat x
    let tt : Z ⟶ splitTorus S X := Over.homMk T (by
      refine Scheme.Cover.hom_ext 𝒰 _ _ fun x => ?_
      rw [← Category.assoc, hT]
      exact Over.w (t x))
    refine ⟨tt, over_ext fun z => ⟨W z, hW z, ?_⟩⟩
    have e3 : incl Z (W z) ≫ tt = t z := by
      apply Over.OverMorphism.ext
      exact hT z
    rw [ht z, comp_mul, ← Category.assoc, e3]
  · rintro ⟨t, rfl⟩
    apply over_ext
    intro z
    refine ⟨g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))), hbV _, ?_⟩
    have := comp_eq (hV (q.left (g.left z))) (h₀ (q.left (g.left z))) (hU (q.left (g.left z)))
      (incl Z (g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z)))) ≫ t)
      (incl_le g (q.left ⁻¹ᵁ V (q.left (g.left z))))
    simpa only [← Category.assoc, comp_mul] using this
end GlobalTheory.LocTriv
