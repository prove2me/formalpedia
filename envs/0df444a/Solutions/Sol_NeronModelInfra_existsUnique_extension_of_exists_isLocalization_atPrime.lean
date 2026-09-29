-- Prove2me | solution 1 for NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6e291462-ee76-5d9d-ae33-601513baa03b

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NLocProof

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TopologicalSpace

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]

section Reformulation
variable {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))

noncomputable abbrev wOf (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
    (pullback.snd f (specGenericFibreInclusion R K))) : pullback t (specGenericFibreInclusion R K) ⟶ X :=
  v.1 ≫ pullback.fst f (specGenericFibreInclusion R K)

theorem wOf_comp (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
    (pullback.snd f (specGenericFibreInclusion R K))) :
    wOf K f t v ≫ f = pullback.fst t (specGenericFibreInclusion R K) ≫ t := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, v.2, pullback.condition]

theorem genericFibreRestrict_eq_of_fst_comp_eq
    (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K)) (pullback.snd f (specGenericFibreInclusion R K)))
    (φ : SchemeHomOver t f) (hφ : pullback.fst t (specGenericFibreInclusion R K) ≫ φ.1 = wOf K f t v) :
    genericFibreRestrict R K f t φ = v := by
  apply Subtype.ext
  apply pullback.hom_ext
  · change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, hφ]
  · change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_snd, v.2]

end Reformulation

section LocalStep
variable {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A] [Algebra A K] [IsScalarTower R A K]

noncomputable abbrev ιA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))

theorem ιAK_comp_ιA : specGenericFibreInclusion A K ≫ ιA A = specGenericFibreInclusion R K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R A K]

noncomputable def pMap : pullback (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) ⟶
    pullback t (specGenericFibreInclusion R K) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst t (ιA A)) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, ιAK_comp_ιA])

noncomputable def jMap : pullback t (specGenericFibreInclusion R K) ⟶ pullback t (ιA A) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specGenericFibreInclusion A K)
    (by rw [Category.assoc, ιAK_comp_ιA]; exact pullback.condition)

@[scoped simp] theorem jMap_fst : jMap K t A ≫ pullback.fst t (ιA A) = pullback.fst t (specGenericFibreInclusion R K) :=
  pullback.lift_fst _ _ _

noncomputable def qMap : pullback t (specGenericFibreInclusion R K) ⟶
    pullback (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) :=
  pullback.lift (jMap K t A) (pullback.snd _ _) (pullback.lift_snd _ _ _)

theorem qMap_pMap : qMap K t A ≫ pMap K t A = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pMap, pullback.lift_fst, ← Category.assoc, qMap, pullback.lift_fst, jMap_fst, Category.id_comp]
  · rw [Category.assoc, pMap, pullback.lift_snd, qMap, pullback.lift_snd, Category.id_comp]

variable {f t}
variable (w : pullback t (specGenericFibreInclusion R K) ⟶ X)
  (hw : w ≫ f = pullback.fst t (specGenericFibreInclusion R K) ≫ t)

noncomputable def mMap : pullback (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) ⟶ pullback f (ιA A) :=
  pullback.lift (pMap K t A ≫ w) (pullback.snd _ _ ≫ specGenericFibreInclusion A K)
    (by rw [Category.assoc, hw, ← Category.assoc, pMap, pullback.lift_fst, Category.assoc, pullback.condition,
          ← Category.assoc, pullback.condition, Category.assoc])

noncomputable def vA : SchemeHomOver (pullback.snd (pullback.snd t (ιA A)) (specGenericFibreInclusion A K))
    (pullback.snd (pullback.snd f (ιA A)) (specGenericFibreInclusion A K)) :=
  ⟨pullback.lift (mMap K A w hw) (pullback.snd _ _) (by rw [mMap, pullback.lift_snd]), pullback.lift_snd _ _ _⟩

theorem local_extension (φA : SchemeHomOver (pullback.snd t (ιA A)) (pullback.snd f (ιA A)))
    (hφA : genericFibreRestrict A K (pullback.snd f (ιA A)) (pullback.snd t (ιA A)) φA = vA K A w hw) :
    (φA.1 ≫ pullback.fst f (ιA A)) ≫ f = pullback.fst t (ιA A) ≫ t ∧
      jMap K t A ≫ (φA.1 ≫ pullback.fst f (ιA A)) = w := by
  constructor
  · rw [Category.assoc, pullback.condition, ← Category.assoc, φA.2, pullback.condition]
  ·
    have h1 : pullback.fst (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) ≫ φA.1 = mMap K A w hw := by
      have := congrArg (fun ψ => ψ.1 ≫ pullback.fst (pullback.snd f (ιA A)) (specGenericFibreInclusion A K)) hφA
      change pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _ at this
      rwa [pullback.lift_fst, pullback.lift_fst] at this
    have h2 : pullback.fst (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) ≫ (φA.1 ≫ pullback.fst f (ιA A)) =
        pMap K t A ≫ w := by
      rw [← Category.assoc, h1, mMap, pullback.lift_fst]
    have h3 : qMap K t A ≫ pullback.fst (pullback.snd t (ιA A)) (specGenericFibreInclusion A K) = jMap K t A :=
      pullback.lift_fst _ _ _
    rw [← h3, Category.assoc, h2, ← Category.assoc, qMap_pMap, Category.id_comp]

end LocalStep

section Extends
variable {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
  (w : pullback t (specGenericFibreInclusion R K) ⟶ X)

def Extends (U : T.Opens) (hU : (U : Scheme.{u}) ⟶ X) : Prop :=
  hU ≫ f = U.ι ≫ t ∧
    ∀ (S : Scheme.{u}) (a : S ⟶ pullback t (specGenericFibreInclusion R K)) (b : S ⟶ U),
      a ≫ pullback.fst t (specGenericFibreInclusion R K) = b ≫ U.ι → b ≫ hU = a ≫ w

variable {f t w}

theorem Extends.mono {U V : T.Opens} (hVU : V ≤ U) {hU : (U : Scheme.{u}) ⟶ X} (H : Extends K f t w U hU) :
    Extends K f t w V (T.homOfLE hVU ≫ hU) := by
  refine ⟨by rw [Category.assoc, H.1, ← Category.assoc, Scheme.homOfLE_ι], fun S a b hab => ?_⟩
  rw [← Category.assoc]
  exact H.2 S a (b ≫ T.homOfLE hVU) (by rw [hab, Category.assoc, Scheme.homOfLE_ι])

end Extends

theorem Spec_map_hom_inv_id_assoc {A B : CommRingCat.{u}} (s : A ⟶ B) [IsIso s] {Z : Scheme.{u}}
    (h : Spec B ⟶ Z) : Spec.map s ≫ Spec.map (inv s) ≫ h = h := by
  rw [← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]

section PointStep
variable {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
  [IsSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian T] [IsNoetherianRing R]
  (A : Type u) [CommRing A] [Algebra R A] [Algebra A K] [IsScalarTower R A K]
  (M : Submonoid R) [IsLocalization M A]
  (w : pullback t (specGenericFibreInclusion R K) ⟶ X)
  (gA : pullback t (ιA A) ⟶ X) (hgA : gA ≫ f = pullback.fst t (ιA A) ≫ t) (hjg : jMap K t A ≫ gA = w)

include M hgA hjg in
theorem exists_extends_nhd [LocallyOfFiniteType t] (x' : ↥(pullback t (ιA A))) :
    ∃ (U : T.Opens), (pullback.fst t (ιA A)) x' ∈ U ∧ ∃ hU : (U : Scheme.{u}) ⟶ X, Extends K f t w U hU := by
  classical

  haveI : IsPreimmersion (ιA A) := IsPreimmersion.of_isLocalization M
  haveI : Flat (ιA A) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap R A).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat A M
  haveI hNoethA : IsNoetherianRing A := IsLocalization.isNoetherianRing M A inferInstance
  haveI : IsLocallyNoetherian (pullback t (ιA A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd t (ιA A))

  haveI hiso : IsIso ((pullback.fst t (ιA A)).stalkMap x') := by
    have hsurj := (pullback.fst t (ιA A)).stalkMap_surjective x'
    have hinj : Function.Injective ((pullback.fst t (ιA A)).stalkMap x').hom := by
      letI := ((pullback.fst t (ιA A)).stalkMap x').hom.toAlgebra
      haveI : Module.Flat (T.presheaf.stalk ((pullback.fst t (ιA A)) x')) ((pullback t (ιA A)).presheaf.stalk x') := Flat.stalkMap (pullback.fst t (ιA A)) x'
      haveI : IsLocalHom (algebraMap (T.presheaf.stalk ((pullback.fst t (ιA A)) x')) ((pullback t (ιA A)).presheaf.stalk x')) :=
        inferInstanceAs (IsLocalHom ((pullback.fst t (ιA A)).stalkMap x').hom)
      have hff : Module.FaithfullyFlat (T.presheaf.stalk ((pullback.fst t (ιA A)) x')) ((pullback t (ιA A)).presheaf.stalk x') :=
        Module.FaithfullyFlat.of_flat_of_isLocalHom
      exact RingHom.FaithfullyFlat.injective (f := ((pullback.fst t (ιA A)).stalkMap x').hom) hff
    have : IsIso ((forget CommRingCat).map ((pullback.fst t (ιA A)).stalkMap x')) := (isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso ((pullback.fst t (ιA A)).stalkMap x') (forget CommRingCat)

  let ψ : Spec (T.presheaf.stalk ((pullback.fst t (ιA A)) x')) ⟶ X := Spec.map (inv ((pullback.fst t (ιA A)).stalkMap x')) ≫ (pullback t (ιA A)).fromSpecStalk x' ≫ gA
  have hψf : ψ ≫ f = T.fromSpecStalk ((pullback.fst t (ιA A)) x') ≫ t := by
    simp only [ψ, Category.assoc]
    rw [hgA, ← Category.assoc ((pullback t (ιA A)).fromSpecStalk x'), ← Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.fst t (ιA A)),
      ← Category.assoc, ← Category.assoc (Spec.map (inv ((pullback.fst t (ιA A)).stalkMap x'))), ← Spec.map_comp, IsIso.hom_inv_id,
      Spec.map_id, Category.id_comp]

  obtain ⟨U, hxU, hU, hψU, hUf⟩ := spread_out_of_isGermInjective' t f ψ hψf

  let V : (pullback t (ιA A)).Opens := (pullback.fst t (ιA A)) ⁻¹ᵁ U
  have hx'V : x' ∈ V := hxU
  let x'' : ↥V := ⟨x', hx'V⟩
  let α : (V : Scheme.{u}) ⟶ X := ((pullback.fst t (ιA A)) ∣_ U) ≫ hU
  let β : (V : Scheme.{u}) ⟶ X := V.ι ≫ gA
  have k1 : (V : Scheme.{u}).fromSpecStalk x'' ≫ V.ι =
      Spec.map (V.ι.stalkMap x'') ≫ (pullback t (ιA A)).fromSpecStalk x' :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk V.ι).symm
  have kU : (V : Scheme.{u}).fromSpecStalk x'' ≫ ((pullback.fst t (ιA A)) ∣_ U) =
      (Spec.map (V.ι.stalkMap x'') ≫ Spec.map ((pullback.fst t (ιA A)).stalkMap x')) ≫ U.fromSpecStalkOfMem ((pullback.fst t (ιA A)) x') hxU := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc, k1, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    congr 1
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.fst t (ιA A))).symm
  have lhs : (V : Scheme.{u}).fromSpecStalk x'' ≫ α =
      Spec.map (V.ι.stalkMap x'') ≫ (pullback t (ιA A)).fromSpecStalk x' ≫ gA := by
    simp only [α]
    rw [← Category.assoc, kU, Category.assoc, ← hψU]
    simp only [ψ, Category.assoc]
    congr 1
    exact @Spec_map_hom_inv_id_assoc _ _ ((pullback.fst t (ιA A)).stalkMap x') hiso _ _
  have rhs : (V : Scheme.{u}).fromSpecStalk x'' ≫ β =
      Spec.map (V.ι.stalkMap x'') ≫ (pullback t (ιA A)).fromSpecStalk x' ≫ gA := by
    simp only [β]
    rw [← Category.assoc, k1, Category.assoc]
  have hαβ : (V : Scheme.{u}).fromSpecStalk x'' ≫ α = (V : Scheme.{u}).fromSpecStalk x'' ≫ β := lhs.trans rhs.symm
  obtain ⟨V', hx'V', hV'⟩ := spread_out_unique_of_isGermInjective' α β hαβ

  have hemb : Topology.IsEmbedding (pullback.fst t (ιA A)) := IsPreimmersion.isEmbedding (pullback.fst t (ιA A))
  have hopen : IsOpen ((V.ι ''ᵁ V' : (pullback t (ιA A)).Opens) : Set ↥(pullback t (ιA A))) := (V.ι ''ᵁ V').isOpen
  obtain ⟨W, hWopen, hWpre⟩ := hemb.isInducing.isOpen_iff.mp hopen
  let W' : T.Opens := ⟨W, hWopen⟩
  have hx'img : x' ∈ ((V.ι ''ᵁ V' : (pullback t (ιA A)).Opens) : Set ↥(pullback t (ιA A))) := by
    rw [Scheme.Hom.coe_image]
    exact ⟨x'', hx'V', rfl⟩
  have hxW : (pullback.fst t (ιA A)) x' ∈ W' := by
    change x' ∈ (pullback.fst t (ιA A)) ⁻¹' W
    rw [hWpre]
    exact hx'img
  refine ⟨U ⊓ W', ⟨hxU, hxW⟩, T.homOfLE inf_le_left ≫ hU, ?_, ?_⟩
  · rw [Category.assoc, hUf, ← Category.assoc, Scheme.homOfLE_ι]
  · intro S a b hab
    have hrange : Set.range (a ≫ jMap K t A) ⊆ Set.range (V'.ι ≫ V.ι) := by
      rintro _ ⟨s, rfl⟩
      have h1 : (pullback.fst t (ιA A)) ((a ≫ jMap K t A) s) = (b ≫ (U ⊓ W').ι) s := by
        rw [← hab, ← Scheme.Hom.comp_apply, Category.assoc, jMap_fst]
      have h2 : (a ≫ jMap K t A) s ∈ (pullback.fst t (ιA A)) ⁻¹' W := by
        show (pullback.fst t (ιA A)) ((a ≫ jMap K t A) s) ∈ W
        rw [h1, Scheme.Hom.comp_apply]
        exact (b s).2.2
      rw [hWpre] at h2
      change (a ≫ jMap K t A) s ∈ ((V.ι ''ᵁ V' : (pullback t (ιA A)).Opens) : Set ↥(pullback t (ιA A))) at h2
      rw [Scheme.Hom.coe_image] at h2
      obtain ⟨v, hv, hv'⟩ := h2
      exact ⟨⟨v, hv⟩, by rw [Scheme.Hom.comp_apply, ← hv']; rfl⟩
    let c : S ⟶ (V' : Scheme.{u}) := IsOpenImmersion.lift (V'.ι ≫ V.ι) (a ≫ jMap K t A) hrange
    have hc : c ≫ V'.ι ≫ V.ι = a ≫ jMap K t A := IsOpenImmersion.lift_fac _ _ _
    have hb : b ≫ T.homOfLE inf_le_left = c ≫ V'.ι ≫ ((pullback.fst t (ιA A)) ∣_ U) := by
      rw [← cancel_mono U.ι]
      simp only [Category.assoc]
      rw [Scheme.homOfLE_ι, morphismRestrict_ι, ← hab, reassoc_of% hc, jMap_fst]
    have hV'' : V'.ι ≫ (((pullback.fst t (ιA A)) ∣_ U) ≫ hU) = V'.ι ≫ (V.ι ≫ gA) := hV'
    calc b ≫ T.homOfLE inf_le_left ≫ hU = c ≫ V'.ι ≫ (((pullback.fst t (ιA A)) ∣_ U) ≫ hU) := by
          rw [← Category.assoc, hb]; simp only [Category.assoc]
      _ = c ≫ V'.ι ≫ (V.ι ≫ gA) := by rw [hV'']
      _ = a ≫ w := by rw [← hjg, ← reassoc_of% hc]

end PointStep

section Glue
variable {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
  [IsSeparated f] [IsDomain R] [IsFractionRing R K] [Flat t]
  (w : pullback t (specGenericFibreInclusion R K) ⟶ X)

include K in
theorem glue (H : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ hU : (U : Scheme.{u}) ⟶ X, Extends K f t w U hU) :
    ∃ φ : T ⟶ X, φ ≫ f = t ∧ pullback.fst t (specGenericFibreInclusion R K) ≫ φ = w := by
  classical
  choose U hxU hU hE using H
  have hcover : TopologicalSpace.IsOpenCover U := by
    refine top_le_iff.mp fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let 𝒰 := T.openCoverOfIsOpenCover U hcover
  have h𝒰f : ∀ x, 𝒰.f x = (U x).ι := fun x => Scheme.openCoverOfIsOpenCover_f T U hcover x

  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ hU x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ hU y := by
    intro x y
    let pP : pullback (𝒰.f x) (𝒰.f y) ⟶ Spec (CommRingCat.of R) := pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x ≫ t
    have hinj := genericFibreRestrict_injective_of_flat_of_isSeparated R K f pP
    have h1 : (pullback.fst (𝒰.f x) (𝒰.f y) ≫ hU x) ≫ f = pP := by
      simp only [Category.assoc, pP]
      erw [(hE x).1]
      rfl
    have h2 : (pullback.snd (𝒰.f x) (𝒰.f y) ≫ hU y) ≫ f = pP := by
      simp only [Category.assoc, pP]
      erw [(hE y).1]
      rw [pullback.condition_assoc]
      rfl
    have key : genericFibreRestrict R K f pP ⟨_, h1⟩ = genericFibreRestrict R K f pP ⟨_, h2⟩ := by
      apply Subtype.ext
      apply pullback.hom_ext
      · change pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _
        rw [pullback.lift_fst, pullback.lift_fst]
        let a : pullback pP (specGenericFibreInclusion R K) ⟶ pullback t (specGenericFibreInclusion R K) :=
          pullback.lift (pullback.fst _ _ ≫ pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x) (pullback.snd _ _)
            (by rw [Category.assoc, Category.assoc]; exact pullback.condition)
        have e1 := (hE x).2 _ a (pullback.fst pP (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f x) (𝒰.f y))
          (by rw [pullback.lift_fst]; simp only [Category.assoc]; rfl)
        have e2 := (hE y).2 _ a (pullback.fst pP (specGenericFibreInclusion R K) ≫ pullback.snd (𝒰.f x) (𝒰.f y))
          (by rw [pullback.lift_fst]; simp only [Category.assoc]; rw [pullback.condition]; rfl)
        have e1' : pullback.fst pP (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f x) (𝒰.f y) ≫ hU x = a ≫ w := by
          simp only [Category.assoc] at e1
          exact e1
        have e2' : pullback.fst pP (specGenericFibreInclusion R K) ≫ pullback.snd (𝒰.f x) (𝒰.f y) ≫ hU y = a ≫ w := by
          simp only [Category.assoc] at e2
          exact e2
        exact e1'.trans e2'.symm
      · change pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _
        rw [pullback.lift_snd, pullback.lift_snd]
    exact congrArg Subtype.val (hinj key)
  let φ := Scheme.Cover.glueMorphisms 𝒰 hU hcompat
  have hφ : ∀ x, 𝒰.f x ≫ φ = hU x := Scheme.Cover.ι_glueMorphisms 𝒰 hU hcompat
  refine ⟨φ, ?_, ?_⟩
  · apply Scheme.Cover.hom_ext 𝒰
    intro x
    rw [← Category.assoc, hφ]
    erw [(hE x).1]
    rfl
  · let UK : T → (pullback t (specGenericFibreInclusion R K)).Opens := fun x =>
      pullback.fst t (specGenericFibreInclusion R K) ⁻¹ᵁ (U x)
    have hcK : TopologicalSpace.IsOpenCover UK := by
      refine top_le_iff.mp fun z _ => ?_
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨pullback.fst t (specGenericFibreInclusion R K) z, hxU _⟩
    apply Scheme.Cover.hom_ext ((pullback t (specGenericFibreInclusion R K)).openCoverOfIsOpenCover UK hcK)
    intro x
    rw [Scheme.openCoverOfIsOpenCover_f]
    have := (hE x).2 _ (UK x).ι (pullback.fst t (specGenericFibreInclusion R K) ∣_ (U x))
      (by rw [morphismRestrict_ι])
    calc (UK x).ι ≫ pullback.fst t (specGenericFibreInclusion R K) ≫ φ
        = ((pullback.fst t (specGenericFibreInclusion R K) ∣_ (U x)) ≫ (U x).ι) ≫ φ := by
          rw [morphismRestrict_ι, Category.assoc]
      _ = (pullback.fst t (specGenericFibreInclusion R K) ∣_ (U x)) ≫ hU x := by
          rw [Category.assoc, ← hφ x]; rfl
      _ = (UK x).ι ≫ w := this

end Glue

theorem main {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A K) (_ : IsScalarTower R A K) (_ : IsFractionRing A K),
        NeronUniqueExtension A K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    NeronModelPropertyBundle R K f := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun T t ht => ?_⟩
  haveI := ht
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  refine ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t, fun v => ?_⟩
  let w := wOf K f t v
  have hw : w ≫ f = pullback.fst t (specGenericFibreInclusion R K) ≫ t := wOf_comp K f t v
  suffices H : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ hU : (U : Scheme.{u}) ⟶ X, Extends K f t w U hU by
    obtain ⟨φ, hφf, hφw⟩ := glue K f t w H
    exact ⟨⟨φ, hφf⟩, genericFibreRestrict_eq_of_fst_comp_eq K f t v ⟨φ, hφf⟩ hφw⟩
  intro x
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (t x).asIdeal (t x).isPrime.ne_top
  obtain ⟨A, _, _, _, _, _, _, hN⟩ := h 𝔪

  have hx : x ∈ Set.range (pullback.fst t (ιA A)) := by
    rw [Scheme.Pullback.range_fst]
    show t x ∈ Set.range (ιA A)
    have hr : Set.range (ιA A) = Set.range (PrimeSpectrum.comap (algebraMap R A)) := rfl
    rw [hr, PrimeSpectrum.localization_comap_range A 𝔪.primeCompl]
    show Disjoint ((𝔪.primeCompl : Submonoid R) : Set R) ((t x).asIdeal : Set R)
    rw [Set.disjoint_left]
    intro r hr1 hr2
    exact hr1 (hle hr2)
  obtain ⟨x', hx'⟩ := hx

  obtain ⟨φA, hφA⟩ := (hN _ _ inferInstance).2 (vA K A w hw)
  obtain ⟨hgA, hjg⟩ := local_extension K A w hw φA hφA
  obtain ⟨U, hxU, hU, hE⟩ :=
    exists_extends_nhd K f t A 𝔪.primeCompl w (φA.1 ≫ pullback.fst f (ιA A)) hgA hjg x'
  exact ⟨U, hx' ▸ hxU, hU, hE⟩

theorem main_ext {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [Flat t] [LocallyOfFiniteType t]
    (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K)) (pullback.snd f (specGenericFibreInclusion R K)))
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A K) (_ : IsScalarTower R A K)
        (gA : pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ X),
        gA ≫ f = pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ t ∧
        ∀ j : pullback t (specGenericFibreInclusion R K) ⟶ pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))),
          j ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) = pullback.fst t (specGenericFibreInclusion R K) →
          j ≫ gA = v.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) :
    ∃! φ : SchemeHomOver t f, genericFibreRestrict R K f t φ = v := by
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have hinj := genericFibreRestrict_injective_of_flat_of_isSeparated R K f t

  let w := wOf K f t v
  suffices H : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ hU : (U : Scheme.{u}) ⟶ X, Extends K f t w U hU by
    obtain ⟨φ, hφf, hφw⟩ := glue K f t w H
    refine ⟨⟨φ, hφf⟩, genericFibreRestrict_eq_of_fst_comp_eq K f t v ⟨φ, hφf⟩ hφw, fun ψ hψ => hinj ?_⟩
    rw [hψ, genericFibreRestrict_eq_of_fst_comp_eq K f t v ⟨φ, hφf⟩ hφw]
  intro x
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (t x).asIdeal (t x).isPrime.ne_top
  obtain ⟨A, _, _, _, _, _, gA, hgA, hj⟩ := h 𝔪
  have hx : x ∈ Set.range (pullback.fst t (ιA A)) := by
    rw [Scheme.Pullback.range_fst]
    show t x ∈ Set.range (ιA A)
    have hr : Set.range (ιA A) = Set.range (PrimeSpectrum.comap (algebraMap R A)) := rfl
    rw [hr, PrimeSpectrum.localization_comap_range A 𝔪.primeCompl]
    show Disjoint ((𝔪.primeCompl : Submonoid R) : Set R) ((t x).asIdeal : Set R)
    rw [Set.disjoint_left]
    intro r hr1 hr2
    exact hr1 (hle hr2)
  obtain ⟨x', hx'⟩ := hx
  have hjg : jMap K t A ≫ gA = w := hj _ (jMap_fst K t A)
  obtain ⟨U, hxU, hU, hE⟩ := exists_extends_nhd K f t A 𝔪.primeCompl w gA hgA hjg x'
  exact ⟨U, hx' ▸ hxU, hU, hE⟩

end NLocProof
p2m_reactivate "P2MW.S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime.NLocProof"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [Flat t] [LocallyOfFiniteType t]
    (v : NeronModelInfra.SchemeHomOver (pullback.snd t (NeronModelInfra.specGenericFibreInclusion R K))
      (pullback.snd f (NeronModelInfra.specGenericFibreInclusion R K)))
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A K) (_ : IsScalarTower R A K)
        (gA : pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ X),
        gA ≫ f = pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ t ∧
        ∀ j : pullback t (NeronModelInfra.specGenericFibreInclusion R K) ⟶
            pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))),
          j ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
            pullback.fst t (NeronModelInfra.specGenericFibreInclusion R K) →
          j ≫ gA = v.1 ≫ pullback.fst f (NeronModelInfra.specGenericFibreInclusion R K)) :
    ∃! φ : NeronModelInfra.SchemeHomOver t f, NeronModelInfra.genericFibreRestrict R K f t φ = v :=
  NLocProof.main_ext K f t v h

end S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime
end P2MW
export P2MW.S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime (solution)
