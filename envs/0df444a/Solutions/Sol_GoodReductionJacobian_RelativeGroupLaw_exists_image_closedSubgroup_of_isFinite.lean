-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_image_closedSubgroup_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/187c443e-dc75-586f-aa86-9f7130332636

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace C1aux

theorem isReduced_carrier_of_formallyUnramified_Spec {F : Type u} [Field F] {S : CommRingCat.{u}}
    (f : Spec S ⟶ Spec (CommRingCat.of F)) [hfu : FormallyUnramified f] [hft : LocallyOfFiniteType f] :
    _root_.IsReduced S := by
  rw [← Spec.map_preimage f] at hfu hft
  have h1 := (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).1 hfu
  have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
  letI := (Spec.preimage f).hom.toAlgebra
  haveI : Algebra.FormallyUnramified F S := h1
  haveI : Algebra.FiniteType F S := h2
  exact Algebra.FormallyUnramified.isReduced_of_field F S

theorem isReduced_of_formallyUnramified_of_locallyOfFiniteType_of_field {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) [FormallyUnramified f] [LocallyOfFiniteType f] : IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    haveI hfu : FormallyUnramified (X.affineCover.f i ≫ f) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
    haveI hft : LocallyOfFiniteType (X.affineCover.f i ≫ f) := inferInstance
    haveI := @isReduced_carrier_of_formallyUnramified_Spec F _ _ (X.affineCover.f i ≫ f) hfu hft
    change IsReduced (Spec _)
    infer_instance
  exact IsReduced.of_openCover X X.affineCover

theorem isReduced_of_etale_of_field {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) [Etale f] : IsReduced X :=
  isReduced_of_formallyUnramified_of_locallyOfFiniteType_of_field f

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem one_coe_eq {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have := congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  exact this.symm

theorem inv_unique {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) (h : L.mul t y x = L.one t) :
    y = L.inv t x := by
  have := congrArg (fun z => L.mul t z (L.inv t x)) h
  rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem inv_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  apply inv_unique
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

theorem nsmulPt_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih => simp only [nsmulPt]; rw [L.mul_natural, ih]

section ptsA

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    DiscreteTopology ↥Z := by
  have h0 : DiscreteTopology ↥(Spec (CommRingCat.of K)) := ⟨Subsingleton.elim _ _⟩
  have h1 : _root_.IsDiscrete (Set.univ : Set ↥(Spec (CommRingCat.of K))) := isDiscrete_univ_iff.mpr h0
  have h2 := g.isDiscrete_preimage h1
  rw [Set.preimage_univ] at h2
  exact isDiscrete_univ_iff.mp h2

theorem isClosed_singleton_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (x : ↥Z) :
    IsClosed ({x} : Set ↥Z) := by
  haveI := discreteTopology_of_isFinite g
  exact isClosed_discrete _

theorem eq_specMap_comp_pointOfClosedPoint {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k')
    (z : Spec (CommRingCat.of k') ⟶ Z) (hz : z ≫ g = Spec.map (CommRingCat.ofHom sk)) :
    z = Spec.map (CommRingCat.ofHom sk) ≫
      pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _) := by
  set x := z.base (IsLocalRing.closedPoint k') with hx
  have hxc : IsClosed ({x} : Set ↥Z) := isClosed_singleton_of_isFinite g _
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  have hrange : Set.range z.base ⊆ {x} := by
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim p (IsLocalRing.closedPoint k')]
  obtain ⟨t, ht⟩ :=
    AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton z x hxc hrange
  have hfrom : Z.fromSpecResidueField x =
      Spec.map (residueFieldIsoBase g x hxc).inv ≫ pointOfClosedPoint g x hxc := by
    rw [pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have ht' : t ≫ Spec.map (residueFieldIsoBase g x hxc).inv = Spec.map (CommRingCat.ofHom sk) := by
    have := hz
    rw [← ht, hfrom, Category.assoc, Category.assoc, pointOfClosedPoint_comp, Category.comp_id] at this
    exact this
  rw [← ht', Category.assoc, ← hfrom, ht]

omit [IsAlgClosed K] in
theorem base_specMap_comp {Z : Scheme.{u}} (k' : Type u) [Field k'] (sk : K →+* k')
    (p : Spec (CommRingCat.of K) ⟶ Z) :
    (Spec.map (CommRingCat.ofHom sk) ≫ p).base (IsLocalRing.closedPoint k') = p.base (IsLocalRing.closedPoint K) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Subsingleton.elim ((Spec.map (CommRingCat.ofHom sk)).base (IsLocalRing.closedPoint k')) (IsLocalRing.closedPoint K)]

theorem bijective_specMap_comp {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g]
    (k' : Type u) [Field k'] (sk : K →+* k') :
    Function.Bijective (fun p : {p : Spec (CommRingCat.of K) ⟶ Z // p ≫ g = 𝟙 _} =>
      (⟨Spec.map (CommRingCat.ofHom sk) ≫ p.1, by rw [Category.assoc, p.2, Category.comp_id]⟩ :
        {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)})) := by
  constructor
  · rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ h
    have h' := congrArg (fun z : {z : Spec (CommRingCat.of k') ⟶ Z // z ≫ g = Spec.map (CommRingCat.ofHom sk)} =>
      z.1.base (IsLocalRing.closedPoint k')) h
    simp only [base_specMap_comp] at h'
    exact Subtype.ext (ext_of_apply_closedPoint_eq g hp₁ hp₂ h')
  · rintro ⟨z, hz⟩
    refine ⟨⟨pointOfClosedPoint g (z.base (IsLocalRing.closedPoint k')) (isClosed_singleton_of_isFinite g _),
      pointOfClosedPoint_comp _ _ _⟩, Subtype.ext ?_⟩
    exact (eq_specMap_comp_pointOfClosedPoint g k' sk z hz).symm

end ptsA

end C1aux

section
open CategoryTheory AlgebraicGeometry
namespace LEVRED

variable {k : Type u} [Field k]

theorem finrank_sections_eq {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [Flat z] [IsAffine C]
    (n : ℕ) (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), z.finrank s = n) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Module.Finite k Γ(C, ⊤) ∧ Module.finrank k Γ(C, ⊤) = n := by
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  letI alg : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hFin : φ.hom.Finite := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite
    exact z.finite_appTop.comp (RingHom.Finite.of_surjective _ hbij.surjective)
  have hFlat : φ.hom.Flat := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Flat
    exact (RingHom.Flat.of_bijective hbij).comp z.flat_appTop
  have hfin : Module.Finite k Γ(C, ⊤) := hFin
  refine ⟨hfin, ?_⟩

  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hFin
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat

  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have h1 := hrank s
  rw [hz, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hFin hFlat] at h1

  have h2 : φ.hom.finrank s = Module.finrank k Γ(C, ⊤) := by
    have : φ.hom = algebraMap k Γ(C, ⊤) := rfl
    rw [this, RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, h1]

theorem finite_algHom (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B] : Finite (B →ₐ[k] k) := by
  classical
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let F : (B →ₐ[k] k) → MaximalSpectrum B := fun φ =>
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun x => ⟨algebraMap k B x, by simp⟩)⟩
  refine Finite.of_injective F ?_
  intro φ ψ h
  have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal h
  apply AlgHom.ext
  intro x

  have h1 : x - algebraMap k B (φ x) ∈ RingHom.ker φ.toRingHom := by simp [RingHom.mem_ker]
  rw [hker] at h1
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes] at h1
  exact (sub_eq_zero.1 h1).symm

theorem natCard_algHom_ge {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C]
    (hfin : letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra; Module.Finite k Γ(C, ⊤))
    (ι : Type) (e : ι ↪ {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) [Finite ι] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Nat.card ι ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  haveI := hfin
  haveI : Finite (Γ(C, ⊤) →ₐ[k] k) := finite_algHom Γ(C, ⊤)

  let Φ : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} → (Γ(C, ⊤) →ₐ[k] k) := fun x =>
    { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := by
        intro c
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
        rw [← Scheme.Hom.comp_appTop_assoc, x.2]
        simp }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have happ : x.1.appTop = y.1.appTop := by
      have := congrArg (fun φ : Γ(C, ⊤) →ₐ[k] k => φ.toRingHom) hxy
      have h2 : (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) = (y.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) := by
        ext1; exact this
      simpa [← Iso.eq_comp_inv] using h2
    apply Subtype.ext
    have hx := Scheme.isoSpec_hom_naturality x.1
    have hy := Scheme.isoSpec_hom_naturality y.1
    rw [happ] at hx
    rw [← cancel_mono C.isoSpec.hom, ← hx, hy]
  calc Nat.card ι ≤ Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := by
          haveI : Finite {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := Finite.of_injective Φ hΦ
          exact Nat.card_le_card_of_injective e e.injective
    _ ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := Nat.card_le_card_of_injective Φ hΦ

end LEVRED

namespace RANKFIN

variable {k : Type u} [Field k]

theorem flat_of_field {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] : Flat z := by
  haveI : IsAffine C := isAffine_of_isAffineHom z
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  have hFlat : φ.hom.Flat := by
    letI : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
    have : Module.Flat k Γ(C, ⊤) := inferInstance
    exact this
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  rw [hz]; infer_instance

theorem natCard_sections_eq_natCard_algHom {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} = Nat.card (Γ(C, ⊤) →ₐ[k] k) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  let Φ : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} → (Γ(C, ⊤) →ₐ[k] k) := fun x =>
    { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := by
        intro c
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
        rw [← Scheme.Hom.comp_appTop_assoc, x.2]
        simp }
  apply Nat.card_eq_of_bijective Φ
  constructor
  · intro x y hxy
    have happ : x.1.appTop = y.1.appTop := by
      have := congrArg (fun φ : Γ(C, ⊤) →ₐ[k] k => φ.toRingHom) hxy
      have h2 : (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) = (y.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) := by
        ext1; exact this
      simpa [← Iso.eq_comp_inv] using h2
    apply Subtype.ext
    have hx := Scheme.isoSpec_hom_naturality x.1
    have hy := Scheme.isoSpec_hom_naturality y.1
    rw [happ] at hx
    rw [← cancel_mono C.isoSpec.hom, ← hx, hy]
  · intro ψ

    let x : Spec (CommRingCat.of k) ⟶ C := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ C.isoSpec.inv
    have hz : z = C.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop) ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
      ext c
      exact ψ.commutes c
    have hx : x ≫ z = 𝟙 _ := by
      rw [hz]
      simp only [x, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp, hcomp, Spec.map_id]
    refine ⟨⟨x, hx⟩, ?_⟩
    apply AlgHom.ext
    intro c
    change ((x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) c = ψ c
    have hx' : x.appTop = C.isoSpec.inv.appTop ≫ (Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop := by
      simp [x]
    have hinv : C.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(C, ⊤)).inv := by
      have h := congrArg Scheme.Hom.appTop C.isoSpec.inv_hom_id
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
      have hh : C.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(C, ⊤)).hom := Scheme.toSpecΓ_appTop C
      rw [hh] at h

      rw [← Iso.eq_inv_comp, Category.comp_id] at h
      exact h
    rw [hx', hinv, Category.assoc, Scheme.ΓSpecIso_naturality]
    change ((Scheme.ΓSpecIso Γ(C, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(C, ⊤)).hom ≫ CommRingCat.ofHom ψ.toRingHom).hom c = ψ c
    rw [Iso.inv_hom_id_assoc]; rfl

end RANKFIN

namespace RANKFIN

theorem finrank_eq_natCard_sections {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [IsReduced C] (s : ↥(Spec (CommRingCat.of k))) :
    z.finrank s = Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := by
  haveI : IsAffine C := isAffine_of_isAffineHom z
  haveI : Flat z := flat_of_field z
  have hconst : ∀ s' : ↥(Spec (CommRingCat.of k)), z.finrank s' = z.finrank s := by
    intro s'; congr 1; exact Subsingleton.elim _ _
  obtain ⟨hfin, hrank⟩ := LEVRED.finrank_sections_eq z (z.finrank s) hconst
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  haveI := hfin
  haveI : _root_.IsReduced Γ(C, ⊤) := IsReduced.component_reduced ⊤
  rw [← hrank, ← AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed k Γ(C, ⊤), natCard_sections_eq_natCard_algHom z]

end RANKFIN

end

theorem solution
    {k : Type} [Field k] [IsAlgClosed k]
    {A₀ A : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of k)} {f : A ⟶ Spec (CommRingCat.of k)}
    (L₀ : RelativeGroupLaw k f₀) (L : RelativeGroupLaw k f)
    (hA_sep : IsSeparated f) (hA_lft : LocallyOfFiniteType f)
    (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p)
    (C : Scheme.{0}) (j : C ⟶ A₀) (hj_closed : IsClosedImmersion j) (hj_finite : IsFinite (j ≫ f₀)) (hC_red : IsReduced C)
    (hC_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j (L₀.one t))
    (hC_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      FactorsThrough j P → FactorsThrough j Q → FactorsThrough j (L₀.mul t P Q) ∧ FactorsThrough j (L₀.inv t P)) :
    ∃ (C' : Scheme.{0}) (j' : C' ⟶ A),
      IsClosedImmersion j' ∧ IsFinite (j' ≫ f) ∧ Flat (j' ≫ f) ∧ LocallyOfFinitePresentation (j' ≫ f) ∧ IsReduced C' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j' (L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        FactorsThrough j' P → FactorsThrough j' Q → FactorsThrough j' (L.mul t P Q) ∧ FactorsThrough j' (L.inv t P)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough j P → FactorsThrough j' (mapPt p hp P)) ∧

      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f),
        FactorsThrough j' Q ↔ ∃ P : SchemeHomOver (geomPoint k' sk) f₀, FactorsThrough j P ∧ mapPt p hp P = Q) ∧

      (∀ s : ↥(Spec (CommRingCat.of k)),
        (j' ≫ f).finrank s = Nat.card {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough j' Q}) ∧

      (∀ m : ℕ, (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → nsmulPt L t m (mapPt p hp P) = L.one t) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → nsmulPt L t m Q = L.one t) ∧

      (∀ (e₀ : A₀ ⟶ A₀) (he₀ : e₀ ≫ f₀ = f₀) (e : A ⟶ A) (he : e ≫ f = f), e₀ ≫ p = p ≫ e →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → FactorsThrough j (pushPt e₀ he₀ P)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → FactorsThrough j' (pushPt e he Q)) := by
  classical
  haveI := hA_sep; haveI := hA_lft; haveI := hj_closed; haveI := hj_finite; haveI := hC_red; haveI := hp_finite

  have hp_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), mapPt p hp (L₀.one t) = L.one t := by
    intro T t
    apply C1aux.eq_one_of_mul_self L t
    rw [← hp_hom, L₀.one_mul]
  have hp_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
      mapPt p hp (L₀.inv t P) = L.inv t (mapPt p hp P) := by
    intro T t P
    apply C1aux.inv_unique L t
    rw [← hp_hom, L₀.inv_mul_cancel, hp_one]

  let Z : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
    {Q | ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f₀, FactorsThrough j P ∧ mapPt p hp P = Q}

  haveI : CompactSpace ↥C := by
    haveI : QuasiCompact (j ≫ f₀) := inferInstance
    have := QuasiCompact.isCompact_preimage (f := j ≫ f₀) (U := ⊤) isOpen_univ CompactSpace.isCompact_univ
    exact ⟨by simpa using this⟩
  haveI : DiscreteTopology ↥C := C1aux.discreteTopology_of_isFinite (j ≫ f₀)
  haveI : Finite ↥C := finite_of_compact_of_discrete
  have hCpts_fin : Set.Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f₀ | FactorsThrough j P} := by

    let φ : ↥C → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f₀ := fun x =>
      ⟨pointOfClosedPoint (j ≫ f₀) x (C1aux.isClosed_singleton_of_isFinite (j ≫ f₀) x) ≫ j, by
        rw [Category.assoc]; exact (pointOfClosedPoint_comp (j ≫ f₀) x _)⟩
    refine (Set.finite_range φ).subset ?_
    rintro P ⟨c, hc⟩
    have hcg : c ≫ (j ≫ f₀) = Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
      rw [← Category.assoc, hc, P.2, CommRingCat.ofHom_id]; exact (Spec.map_id _).symm
    have := C1aux.eq_specMap_comp_pointOfClosedPoint (j ≫ f₀) k (RingHom.id k) c hcg
    refine ⟨c.base (IsLocalRing.closedPoint k), Subtype.ext ?_⟩
    show pointOfClosedPoint (j ≫ f₀) _ _ ≫ j = P.1
    rw [← hc]
    conv_rhs => rw [this]
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hZfin : Z.Finite := by
    have : Z = (fun P => mapPt p hp P) '' {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f₀ | FactorsThrough j P} := by
      ext Q; constructor
      · rintro ⟨P, hP, rfl⟩; exact ⟨P, hP, rfl⟩
      · rintro ⟨P, hP, rfl⟩; exact ⟨P, hP, rfl⟩
    rw [this]; exact hCpts_fin.image _
  have hZ_one : L.one _ ∈ Z := ⟨L₀.one _, hC_one _, hp_one _⟩
  have hZ_mul : ∀ x ∈ Z, ∀ y ∈ Z, L.mul _ x y ∈ Z := by
    rintro x ⟨P, hP, rfl⟩ y ⟨Q, hQ, rfl⟩
    exact ⟨L₀.mul _ P Q, (hC_sub _ P Q hP hQ).1, hp_hom _ P Q⟩
  have hZ_inv : ∀ x ∈ Z, L.inv _ x ∈ Z := by
    rintro x ⟨P, hP, rfl⟩
    exact ⟨L₀.inv _ P, (hC_sub _ P P hP hP).2, hp_inv _ P⟩

  obtain ⟨B, g, LB, i, hred, hfin, hci, hhom, ⟨eB, heB⟩⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
      f L Z hZfin hZ_one hZ_mul hZ_inv
  haveI := hred; haveI := hfin; haveI := hci
  have hi : i.1 ≫ f = g := i.2

  have hone_i : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)),
      NeronModelInfra.schemeHomOverComp (LB.one t) i = L.one t := by
    intro T t
    apply C1aux.eq_one_of_mul_self
    rw [← hhom, LB.one_mul]
  have hinv_i : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (z : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.inv t z) i = L.inv t (NeronModelInfra.schemeHomOverComp z i) := by
    intro T t z
    apply C1aux.inv_unique
    rw [← hhom, LB.inv_mul_cancel, hone_i]

  have hFT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      FactorsThrough i.1 P ↔ ∃ z : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp z i = P := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀, ?_⟩, Subtype.ext hP₀⟩
      rw [← hi, ← Category.assoc, hP₀]; exact P.2
    · rintro ⟨z, hz⟩; exact ⟨z.1, congrArg Subtype.val hz⟩

  have hBpt : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g, NeronModelInfra.schemeHomOverComp y i ∈ Z :=
    fun y => heB y ▸ (eB y).2
  have hZpt : ∀ z ∈ Z, ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g, NeronModelInfra.schemeHomOverComp y i = z :=
    fun z hz => ⟨eB.symm ⟨z, hz⟩, by rw [← heB, Equiv.apply_symm_apply]⟩

  haveI : LocallyOfFiniteType (j ≫ f₀) := inferInstance
  obtain ⟨c, hc⟩ : ∃ c : C ⟶ B, c ≫ i.1 = j ≫ p := by
    refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k (j ≫ f₀) f i.1 (j ≫ p)
      (by rw [Category.assoc, hp]) ?_
    intro z
    have hmem : mapPt (j ≫ p) (by rw [Category.assoc, hp]) z ∈ Z := by
      refine ⟨⟨z.1 ≫ j, by rw [Category.assoc]; exact z.2⟩, ⟨z.1, rfl⟩, Subtype.ext ?_⟩
      simp only [mapPt_coe, Category.assoc]
    obtain ⟨y, hy⟩ := hZpt _ hmem
    exact (hFT _ _).2 ⟨y, hy⟩
  have hinto : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
      FactorsThrough j P → FactorsThrough i.1 (mapPt p hp P) := by
    rintro T t P ⟨P₀, hP₀⟩
    exact ⟨P₀ ≫ c, by rw [Category.assoc, hc, ← Category.assoc, hP₀]; rfl⟩

  set e₀ : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of k)))).1 with he₀
  have he₀f : e₀ ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of k)))).2
  haveI : IsClosedImmersion (e₀ ≫ f) := by rw [he₀f]; infer_instance
  haveI : IsClosedImmersion e₀ := IsClosedImmersion.of_comp e₀ f

  have hfin' : IsFinite (i.1 ≫ f) := by rw [hi]; exact hfin
  have hflat' : Flat (i.1 ≫ f) := by rw [hi]; exact RANKFIN.flat_of_field g
  have hlfp' : LocallyOfFinitePresentation (i.1 ≫ f) := by rw [hi]; infer_instance
  refine ⟨B, i.1, hci, hfin', hflat', hlfp', hred, ?_, ?_, hinto, ?_, ?_, ?_, ?_⟩
  ·
    intro T t; exact (hFT t _).2 ⟨LB.one t, hone_i t⟩
  ·
    intro T t P Q hP hQ
    obtain ⟨zP, rfl⟩ := (hFT t P).1 hP
    obtain ⟨zQ, rfl⟩ := (hFT t Q).1 hQ
    exact ⟨(hFT t _).2 ⟨LB.mul t zP zQ, hhom t zP zQ⟩, (hFT t _).2 ⟨LB.inv t zP, hinv_i t zP⟩⟩
  ·
    intro k' _ _ sk Q
    constructor
    · intro hQ
      obtain ⟨zQ, hzQ⟩ := (hFT _ Q).1 hQ

      have hz1 : zQ.1 ≫ g = Spec.map (CommRingCat.ofHom sk) := zQ.2
      obtain ⟨⟨y, hy⟩, hyz⟩ := (C1aux.bijective_specMap_comp g k' sk).2 ⟨zQ.1, hz1⟩
      have hyz' : Spec.map (CommRingCat.ofHom sk) ≫ y = zQ.1 := congrArg Subtype.val hyz
      obtain ⟨P₀, hP₀, hP₀y⟩ := hBpt ⟨y, hy⟩
      refine ⟨GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) P₀, ?_, ?_⟩
      · obtain ⟨c₀, hc₀⟩ := hP₀; exact ⟨Spec.map (CommRingCat.ofHom sk) ≫ c₀, by rw [Category.assoc, hc₀]; rfl⟩
      · apply Subtype.ext
        rw [← hzQ]
        show (Spec.map (CommRingCat.ofHom sk) ≫ P₀.1) ≫ p = zQ.1 ≫ i.1
        rw [← hyz', Category.assoc, Category.assoc]
        congr 1
        exact congrArg Subtype.val hP₀y
    · rintro ⟨P, hP, rfl⟩; exact hinto _ P hP
  ·
    intro s
    rw [hi, RANKFIN.finrank_eq_natCard_sections g s]
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨x.1 ≫ i.1, by rw [Category.assoc, hi, x.2]⟩, ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩
    · intro x x' h
      have h' := congrArg (fun P : {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough i.1 Q} => P.1.1) h
      exact Subtype.ext ((cancel_mono i.1).1 h')
    · rintro ⟨Q, ⟨z, hz⟩⟩
      refine ⟨⟨z, ?_⟩, Subtype.ext (Subtype.ext hz)⟩
      rw [← hi, ← Category.assoc, hz, Q.2]
  ·
    intro m hm T t Q hQ

    have hDfac : ∃ g₀ : B ⟶ Spec (CommRingCat.of k), g₀ ≫ e₀ = (nsmulPt L g m i).1 := by
      refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k g f e₀ (nsmulPt L g m i).1
        (nsmulPt L g m i).2 ?_
      intro z
      have hnat : mapPt (nsmulPt L g m i).1 (nsmulPt L g m i).2 z =
          nsmulPt L (𝟙 _) m (NeronModelInfra.schemeHomOverComp z i) := C1aux.nsmulPt_natural L g (𝟙 _) z.1 z.2 m i
      obtain ⟨P₀, hP₀, hP₀z⟩ := hBpt z
      refine ⟨𝟙 _, ?_⟩
      rw [Category.id_comp, he₀, congrArg Subtype.val hnat, ← hP₀z, hm _ P₀ hP₀]
    have hD : nsmulPt L g m i = L.one g := by
      obtain ⟨g₀, hg₀⟩ := hDfac
      have hg : g₀ = g := by
        rw [← Category.comp_id g₀, ← he₀f, ← Category.assoc, hg₀]; exact (nsmulPt L g m i).2
      apply Subtype.ext
      rw [← hg₀, hg, C1aux.one_coe_eq L g]
    obtain ⟨zQ, rfl⟩ := (hFT t Q).1 hQ
    have := C1aux.nsmulPt_natural L g t zQ.1 zQ.2 m i
    rw [hD, L.one_natural] at this
    exact this.symm
  ·
    intro e₁ he₁ e he hcomm hstab T t Q hQ
    have hact : ∃ am : B ⟶ B, am ≫ i.1 = i.1 ≫ e := by
      refine CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k g f i.1 (i.1 ≫ e)
        (by rw [Category.assoc, he, hi]) ?_
      intro z
      obtain ⟨P₀, hP₀, hP₀z⟩ := hBpt z
      have hmem : pushPt e he (NeronModelInfra.schemeHomOverComp z i) ∈ Z := by
        refine ⟨pushPt e₁ he₁ P₀, hstab _ P₀ hP₀, ?_⟩
        rw [← hP₀z]
        apply Subtype.ext
        simp only [mapPt_coe, Category.assoc, hcomm]
      obtain ⟨y, hy⟩ := hZpt _ hmem
      refine ⟨y.1, ?_⟩
      have := congrArg Subtype.val hy
      simp only [mapPt_coe] at this ⊢
      rw [← Category.assoc]
      exact this
    obtain ⟨zQ, rfl⟩ := (hFT t Q).1 hQ
    obtain ⟨am, ham⟩ := hact
    exact ⟨zQ.1 ≫ am, by simp only [mapPt_coe, Category.assoc, ham]; rfl⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite (solution)
