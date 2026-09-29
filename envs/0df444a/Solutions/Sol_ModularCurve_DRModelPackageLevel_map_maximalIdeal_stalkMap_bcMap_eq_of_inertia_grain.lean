-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.map_maximalIdeal_stalkMap_bcMap_eq_of_inertia_grain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/59d4f1a4-8709-526d-9a97-3d9d91264306

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_map_maximalIdeal_stalkMap_bcMap_eq_of_inertia_grain

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace E4HunrAlg

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

private theorem eq_map_of_comap_eq
    {O B k : Type*} [CommRing O] [CommRing B] [Algebra O B] [Field k] [Algebra O k]
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔭).comp (algebraMap O B)))
    (𝔓 : Ideal (B ⊗[O] k)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom = 𝔭) :
    𝔓 = 𝔭.map (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom := by
  classical
  set ι : B →+* B ⊗[O] k := (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom with hι
  set 𝔭' : Ideal (B ⊗[O] k) := 𝔭.map ι with h𝔭'

  have hle : 𝔭' ≤ 𝔓 := by
    rw [h𝔭', Ideal.map_le_iff_le_comap, h𝔓]

  let φ : k →+* (B ⊗[O] k) ⧸ 𝔭' :=
    (Ideal.Quotient.mk 𝔭').comp (Algebra.TensorProduct.includeRight (R := O) (A := B) (B := k)).toRingHom
  have hφ : ∀ c : k, φ c = Ideal.Quotient.mk 𝔭' ((1 : B) ⊗ₜ[O] c) := fun c => rfl
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨o, ho⟩ := hrat (Ideal.Quotient.mk 𝔭 b)

      have hbo : b - algebraMap O B o ∈ 𝔭 := by
        rw [← Ideal.Quotient.eq, ← ho]; rfl
      refine ⟨o • c, ?_⟩
      rw [hφ, Ideal.Quotient.eq]
      have : (1 : B) ⊗ₜ[O] (o • c) - b ⊗ₜ[O] c = (algebraMap O B o - b) ⊗ₜ[O] c := by
        rw [TensorProduct.sub_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rw [this, h𝔭']
      have hmem : (algebraMap O B o - b) ∈ 𝔭 := by
        rw [← neg_sub]; exact 𝔭.neg_mem hbo
      have : (algebraMap O B o - b) ⊗ₜ[O] c = ι (algebraMap O B o - b) * ((1 : B) ⊗ₜ[O] c) := by
        rw [hι]; simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ι hmem)
    | add s t hs ht =>
      obtain ⟨c₁, h₁⟩ := hs
      obtain ⟨c₂, h₂⟩ := ht
      exact ⟨c₁ + c₂, by rw [RingHom.map_add φ, h₁, h₂, RingHom.map_add]⟩

  have hne : 𝔭' ≠ ⊤ := fun h => Ideal.IsPrime.ne_top (inferInstance : 𝔓.IsPrime) (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial ((B ⊗[O] k) ⧸ 𝔭') := ⟨⟨0, 1, fun h => hne (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  have hbij : Function.Bijective φ := ⟨φ.injective, hsurj⟩
  have hfield : IsField ((B ⊗[O] k) ⧸ 𝔭') :=
    (RingEquiv.ofBijective φ hbij).symm.toMulEquiv.isField (Field.toIsField k)
  have hmax : 𝔭'.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

private theorem map_maximalIdeal_eq_of_comap_eq
    {O B k : Type*} [CommRing O] [CommRing B] [Algebra O B] [Field k] [Algebra O k]
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔭).comp (algebraMap O B)))
    (𝔓 : Ideal (B ⊗[O] k)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom = 𝔭)
    (R S : Type*) [CommRing R] [Algebra B R] [IsLocalization.AtPrime R 𝔭]
    [CommRing S] [Algebra (B ⊗[O] k) S] [IsLocalization.AtPrime S 𝔓]
    (f : R →+* S)
    (hf : f.comp (algebraMap B R) = (algebraMap (B ⊗[O] k) S).comp
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom) :
    haveI := IsLocalization.AtPrime.isLocalRing R 𝔭
    haveI := IsLocalization.AtPrime.isLocalRing S 𝔓
    Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  haveI := IsLocalization.AtPrime.isLocalRing R 𝔭
  haveI := IsLocalization.AtPrime.isLocalRing S 𝔓
  have h1 : IsLocalRing.maximalIdeal R = 𝔭.map (algebraMap B R) := (IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 R).symm
  have h2 : IsLocalRing.maximalIdeal S = 𝔓.map (algebraMap (B ⊗[O] k) S) := (IsLocalization.AtPrime.map_eq_maximalIdeal 𝔓 S).symm
  rw [h1, h2, Ideal.map_map, hf, ← Ideal.map_map,
    ← eq_map_of_comap_eq 𝔭 hrat 𝔓 h𝔓]

private def MapsMaxOnto {R S : CommRingCat} (f : R ⟶ S) [IsLocalRing R] [IsLocalRing S] : Prop :=
  Ideal.map f.hom (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S

private theorem mapsMaxOnto_of_arrow_iso {R S R' S' : CommRingCat} (f : R ⟶ S) (f' : R' ⟶ S')
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (e : Arrow.mk f ≅ Arrow.mk f') (h : MapsMaxOnto f) : MapsMaxOnto f' := by

  have hsq : f ≫ e.hom.right = e.hom.left ≫ f' := (Arrow.w e.hom).symm
  let eR : R ≅ R' := Arrow.leftFunc.mapIso e
  let eS : S ≅ S' := Arrow.rightFunc.mapIso e
  have heR : eR.hom = e.hom.left := rfl
  have heS : eS.hom = e.hom.right := rfl

  have hR : Ideal.map eR.hom.hom (maximalIdeal R) = maximalIdeal R' := by
    have : (Ideal.map eR.commRingCatIsoToRingEquiv (maximalIdeal R)).IsMaximal :=
      Ideal.map_isMaximal_of_equiv eR.commRingCatIsoToRingEquiv (p := maximalIdeal R)
    exact IsLocalRing.eq_maximalIdeal this
  have hS : Ideal.map eS.hom.hom (maximalIdeal S) = maximalIdeal S' := by
    have : (Ideal.map eS.commRingCatIsoToRingEquiv (maximalIdeal S)).IsMaximal :=
      Ideal.map_isMaximal_of_equiv eS.commRingCatIsoToRingEquiv (p := maximalIdeal S)
    exact IsLocalRing.eq_maximalIdeal this
  unfold MapsMaxOnto at h ⊢

  have hf' : f' = eR.inv ≫ f ≫ eS.hom := by
    have w := Arrow.w e.hom
    simp only [Arrow.mk_hom] at w
    symm
    rw [Iso.inv_comp_eq, heR, heS]
    exact w.symm
  have hR' : Ideal.map eR.inv.hom (maximalIdeal R') = maximalIdeal R := by
    rw [← hR, Ideal.map_map]
    change Ideal.map (eR.hom ≫ eR.inv).hom _ = _
    rw [Iso.hom_inv_id]; exact Ideal.map_id _
  rw [hf']
  change Ideal.map (eS.hom.hom.comp (f.hom.comp eR.inv.hom)) _ = _
  rw [← Ideal.map_map, ← Ideal.map_map, hR', h, hS]

private theorem mapsMaxOnto_SpecMap_includeLeft
    {O : Type} [CommRing O] (B k : Type) [CommRing B] [Algebra O B] [Field k] [Algebra O k]
    (𝔓 : PrimeSpectrum (B ⊗[O] k))
    (hrat : Function.Surjective ((Ideal.Quotient.mk
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom 𝔓).asIdeal).comp
        (algebraMap O B))) :
    MapsMaxOnto ((Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom)).stalkMap 𝔓) := by
  set ι := (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := B) (B := k)).toRingHom with hι
  set 𝔭 := PrimeSpectrum.comap ι 𝔓 with h𝔭

  have key := localRingHom_comp_stalkIso (CommRingCat.ofHom ι) 𝔓

  have hloc : MapsMaxOnto (R := CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)) (S := CommRingCat.of (Localization.AtPrime 𝔓.asIdeal))
      (CommRingCat.ofHom (Localization.localRingHom 𝔭.asIdeal 𝔓.asIdeal ι rfl)) := by
    unfold MapsMaxOnto
    exact map_maximalIdeal_eq_of_comap_eq 𝔭.asIdeal hrat 𝔓.asIdeal rfl (Localization.AtPrime 𝔭.asIdeal)
      (Localization.AtPrime 𝔓.asIdeal) _ (by ext b; simp [Localization.localRingHom_to_map, hι, Algebra.TensorProduct.includeLeft_apply])
  refine mapsMaxOnto_of_arrow_iso _ _ (Arrow.isoMk' _ ((Spec.map (CommRingCat.ofHom ι)).stalkMap 𝔓)
    (StructureSheaf.stalkIso B 𝔭).toCommRingCatIso (StructureSheaf.stalkIso (B ⊗[O] k) 𝔓).toCommRingCatIso ?_) hloc

  have key' : CommRingCat.ofHom (StructureSheaf.stalkIso B 𝔭).symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom (Localization.localRingHom 𝔭.asIdeal 𝔓.asIdeal ι rfl) ≫
        CommRingCat.ofHom (StructureSheaf.stalkIso (B ⊗[O] k) 𝔓).toRingEquiv.toRingHom =
      (Spec.map (CommRingCat.ofHom ι)).stalkMap 𝔓 := key
  rw [← key']
  ext x
  change (StructureSheaf.stalkIso (B ⊗[O] k) 𝔓) (Localization.localRingHom 𝔭.asIdeal 𝔓.asIdeal ι rfl
      ((StructureSheaf.stalkIso B 𝔭).symm ((StructureSheaf.stalkIso B 𝔭) x))) =
    (StructureSheaf.stalkIso (B ⊗[O] k) 𝔓) (Localization.localRingHom 𝔭.asIdeal 𝔓.asIdeal ι rfl x)
  rw [AlgEquiv.symm_apply_apply]

private theorem mapsMaxOnto_stalkMap_of_isPullback
    {O : Type} [CommRing O] {k : Type} [Field k] (toκ : O →+* k)
    {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (f : Y ⟶ X) (r : Y ⟶ Spec (CommRingCat.of k))
    (H : IsPullback f r q (Spec.map (CommRingCat.ofHom toκ)))
    (y : Y)
    (hrat : Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk (f.base y))).comp
      ((X.presheaf.germ ⊤ (f.base y) trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)))) :
    Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
  classical

  obtain ⟨R, g, hg, ⟨z, hz⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := X) (x := f.base y)
    (U := ⊤) trivial
  haveI := hg

  let φ : CommRingCat.of O ⟶ R := Spec.preimage (g ≫ q)
  have hφ : Spec.map φ = g ≫ q := Spec.map_preimage _
  letI : Algebra O R := φ.hom.toAlgebra
  letI : Algebra O k := toκ.toAlgebra

  let P := pullback g f
  have sq1 : IsPullback (pullback.snd g f) (pullback.fst g f) f g := (IsPullback.of_hasPullback g f).flip
  have sq2 : IsPullback (pullback.fst g f) (pullback.snd g f ≫ r) (Spec.map φ) (Spec.map (CommRingCat.ofHom toκ)) := by
    have := IsPullback.paste_vert (IsPullback.of_hasPullback g f) H
    rw [hφ]; exact this
  have sq3 : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := R) (B := k)).toRingHom))
      (Spec.map φ) (Spec.map (CommRingCat.ofHom toκ)) := by
    have := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O R k)
    exact this
  let e : P ≅ Spec (CommRingCat.of (R ⊗[O] k)) := sq2.isoIsPullback _ _ sq3
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom) =
      pullback.fst g f := sq2.isoIsPullback_hom_fst _ _ sq3

  obtain ⟨w, hwz, hwy⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := f) z y hz

  set 𝔓 : PrimeSpectrum (R ⊗[O] k) := e.hom.base w with h𝔓
  have h𝔭z : PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom 𝔓 = z := by
    rw [← hwz]
    change (e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom)).base w = _
    rw [he]

  have hrat' : Function.Surjective ((Ideal.Quotient.mk z.asIdeal).comp (algebraMap O R)) := by

    haveI hiso : IsIso (g.stalkMap z) := inferInstance
    let Θ : X.presheaf.stalk (f.base y) →+* (Spec R).presheaf.stalk z :=
      (g.stalkMap z).hom.comp (X.presheaf.stalkCongr (.of_eq hz.symm)).hom.hom
    have hΘ : ∀ s, Θ s = (g.stalkMap z).hom ((X.presheaf.stalkCongr (.of_eq hz.symm)).hom.hom s) := fun s => rfl

    haveI : IsLocalHom Θ := by
      haveI : IsLocalHom (X.presheaf.stalkCongr (.of_eq hz.symm)).hom.hom := inferInstance
      exact RingHom.isLocalHom_comp _ _

    have hΘsurj : Function.Surjective Θ := by
      intro s
      refine ⟨(X.presheaf.stalkCongr (.of_eq hz.symm)).inv.hom ((inv (g.stalkMap z)).hom s), ?_⟩
      rw [hΘ, ← CommRingCat.comp_apply (X.presheaf.stalkCongr (.of_eq hz.symm)).inv, Iso.inv_hom_id, CommRingCat.id_apply,
        ← CommRingCat.comp_apply (inv (g.stalkMap z)), IsIso.inv_hom_id, CommRingCat.id_apply]

    have hconst : ∀ o : O, Θ ((X.presheaf.germ ⊤ (f.base y) trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
        StructureSheaf.toStalk R z (φ.hom o) := by
      intro o
      rw [hΘ]

      have h1 : (X.presheaf.stalkCongr (.of_eq hz.symm)).hom.hom ((X.presheaf.germ ⊤ (f.base y) trivial).hom
          (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
          (X.presheaf.germ ⊤ (g.base z) trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) := by
        change (X.presheaf.stalkSpecializes (Inseparable.of_eq hz.symm).ge).hom ((X.presheaf.germ ⊤ (f.base y) trivial).hom _) = _
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
      rw [h1]

      have h2 := Scheme.Hom.germ_stalkMap_apply g ⊤ z trivial (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))
      change (g.stalkMap z) ((X.presheaf.germ ⊤ (g.base z) trivial) (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) = _ at h2 ⊢
      rw [h2]

      have h3 : g.app ⊤ (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)) = (g ≫ q).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o) := rfl
      rw [h3, Scheme.Hom.congr_app hφ.symm ⊤, CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply (Spec R).presheaf]

      have happ : (Spec.map φ).appTop = (Scheme.ΓSpecIso (CommRingCat.of O)).hom ≫ φ ≫ (Scheme.ΓSpecIso R).inv := by
        have hnat := Scheme.ΓSpecIso_naturality φ
        rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have h4 : (Spec.map φ).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o) = (Scheme.ΓSpecIso R).inv (φ o) := by
        change (Spec.map φ).appTop _ = _
        rw [happ, CommRingCat.comp_apply, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of O)).inv,
          Iso.inv_hom_id, CommRingCat.id_apply]
      rw [h4]
      change ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ _ z _) (φ.hom o) = _
      rw [Scheme.ΓSpecIso_inv]
      erw [StructureSheaf.algebraMap_germ]
      rfl

    intro r0
    obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective r0
    obtain ⟨s', hs'⟩ := hΘsurj (StructureSheaf.toStalk R z r₀)
    obtain ⟨o, ho⟩ := hrat (IsLocalRing.residue _ s')
    refine ⟨o, ?_⟩
    change Ideal.Quotient.mk _ (φ.hom o) = Ideal.Quotient.mk _ r₀
    rw [Ideal.Quotient.eq]
    have hm : (X.presheaf.germ ⊤ (f.base y) trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) - s' ∈
        IsLocalRing.maximalIdeal _ := by
      rw [← Ideal.Quotient.eq]
      exact ho
    have hm' : Θ ((X.presheaf.germ ⊤ (f.base y) trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) - s') ∈
        IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => (IsLocalRing.mem_maximalIdeal _).mp hm (isUnit_of_map_unit Θ _ hu))
    rw [map_sub, hconst, hs'] at hm'
    have key := IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec.structureSheaf R).presheaf.stalk z) z.asIdeal (φ.hom o - r₀)
    refine key.mp ?_
    change StructureSheaf.toStalk R z (φ.hom o - r₀) ∈ _
    rw [map_sub]
    exact hm'

  have harrow : Nonempty (Arrow.mk ((Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom)).stalkMap 𝔓) ≅
      Arrow.mk (f.stalkMap y)) := by
    subst hwy
    haveI : IsIso ((pullback.snd g f).stalkMap w) := inferInstance
    haveI : IsIso (g.stalkMap ((pullback.fst g f).base w)) := inferInstance
    haveI : IsIso (e.hom.stalkMap w) := inferInstance

    have eA : Arrow.mk (f.stalkMap ((pullback.snd g f).base w)) ≅ Arrow.mk ((pullback.snd g f ≫ f).stalkMap w) :=
      Arrow.isoMk' (f.stalkMap ((pullback.snd g f).base w)) ((pullback.snd g f ≫ f).stalkMap w) (Iso.refl _)
        (asIso ((pullback.snd g f).stalkMap w)) (by rw [Scheme.Hom.stalkMap_comp]; simp)

    have eB : Arrow.mk ((pullback.snd g f ≫ f).stalkMap w) = Arrow.mk ((pullback.fst g f ≫ g).stalkMap w) :=
      congrArg (fun h : pullback g f ⟶ X => Arrow.mk (h.stalkMap w)) pullback.condition.symm

    have eC : Arrow.mk ((pullback.fst g f).stalkMap w) ≅ Arrow.mk ((pullback.fst g f ≫ g).stalkMap w) :=
      Arrow.isoMk' ((pullback.fst g f).stalkMap w) ((pullback.fst g f ≫ g).stalkMap w)
        (asIso (g.stalkMap ((pullback.fst g f).base w))).symm (Iso.refl _) (by rw [Scheme.Hom.stalkMap_comp]; simp)

    have eD : Arrow.mk ((pullback.fst g f).stalkMap w) =
        Arrow.mk ((e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom)).stalkMap w) :=
      congrArg (fun h : pullback g f ⟶ Spec R => Arrow.mk (h.stalkMap w)) he.symm
    have eE : Arrow.mk ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom)).stalkMap 𝔓) ≅
        Arrow.mk ((e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom)).stalkMap w) :=
      Arrow.isoMk' _ _ (Iso.refl _) (asIso (e.hom.stalkMap w)) (by rw [Scheme.Hom.stalkMap_comp]; simp; rfl)
    exact ⟨eE ≪≫ eqToIso eD.symm ≪≫ eC ≪≫ eqToIso eB.symm ≪≫ eA.symm⟩
  have hrat'' : Function.Surjective ((Ideal.Quotient.mk
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := R) (B := k)).toRingHom 𝔓).asIdeal).comp
        (algebraMap O R)) := by rw [h𝔭z]; exact hrat'
  exact mapsMaxOnto_of_arrow_iso _ _ harrow.some (mapsMaxOnto_SpecMap_includeLeft R k 𝔓 hrat'')

end E4HunrAlg

namespace E4HunrDRLevel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel

private theorem e4_isPullback_bcMap (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    {O κ : Type} [CommRing O] [CommRing κ] (ρO : DRLevel.R q →+* O) (toκ : O →+* κ) :
    IsPullback (DRLevel.bcMap (N₀ := N₀) ρO toκ)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
      (Spec.map (CommRingCat.ofHom toκ)) := by
  have e1 : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    simp only [DRLevel.bcMap, pullback.lift_fst, Category.comp_id]
  have e2 : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom (toκ.comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e3 : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [DRLevel.bcMap, pullback.lift_snd]
  refine IsPullback.of_right ?_ e3 (IsPullback.of_hasPullback _ _)
  rw [e1, e2]
  exact IsPullback.of_hasPullback _ _

end E4HunrDRLevel

section Face

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (𝔓 : DRModelPackageLevel N₀ q hqN)
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))

    (hrat : Function.Surjective ((IsLocalRing.residue ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((DRLevel.bcMap ρO toκ).base ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))))).comp
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ((DRLevel.bcMap ρO toκ).base ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))) trivial).hom.comp
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)))) :
    Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
    Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1).base ((pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
  have H := E4HunrDRLevel.e4_isPullback_bcMap N₀ q ρO toκ
  refine ⟨E4HunrAlg.mapsMaxOnto_stalkMap_of_isPullback toκ _ _ _ H _ hrat, ?_⟩

  have hpt : (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1).base
        ((pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n) =
      (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base
        ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n) := by
    have := congrArg (fun h : pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ⟶ _ => h.base n)
      (pullback.condition (f := 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (g := 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1))
    simpa using this.symm
  have hrat₂ := hrat
  rw [← hpt] at hrat₂
  exact E4HunrAlg.mapsMaxOnto_stalkMap_of_isPullback toκ _ _ _ H _ hrat₂

end Face

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_map_maximalIdeal_stalkMap_bcMap_eq_of_inertia_grain
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_map_maximalIdeal_stalkMap_bcMap_eq_of_inertia_grain (solution)
