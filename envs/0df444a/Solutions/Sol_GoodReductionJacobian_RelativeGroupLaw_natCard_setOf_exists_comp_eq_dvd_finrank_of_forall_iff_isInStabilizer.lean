-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cd1cd0e6-88c4-5145-911a-7744533a2147

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Theorems.Thm_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

universe u

namespace N8Asm

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

noncomputable def secAlgHom {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k))
    (x : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Γ(C, ⊤) →ₐ[k] k :=
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    commutes' := by
      intro c
      change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
      rw [← Scheme.Hom.comp_appTop_assoc, x.2]
      simp }

theorem secAlgHom_apply {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k))
    (x : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) (b : Γ(C, ⊤)) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    secAlgHom z x b = (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom b := rfl

theorem secAlgHom_bijective {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Function.Bijective (secAlgHom z) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
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

noncomputable def ΓAlgEquiv {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) (τ : C ≅ C) (hτ : τ.hom ≫ z = z) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Γ(C, ⊤) ≃ₐ[k] Γ(C, ⊤) :=
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f :=
    { toFun := τ.hom.appTop.hom
      invFun := τ.inv.appTop.hom
      left_inv := fun b => by
        change (τ.hom.appTop ≫ τ.inv.appTop).hom b = b
        rw [← Scheme.Hom.comp_appTop, τ.inv_hom_id, Scheme.Hom.id_appTop]; rfl
      right_inv := fun b => by
        change (τ.inv.appTop ≫ τ.hom.appTop).hom b = b
        rw [← Scheme.Hom.comp_appTop, τ.hom_inv_id, Scheme.Hom.id_appTop]; rfl
      map_mul' := fun a b => map_mul _ a b
      map_add' := fun a b => map_add _ a b }) (fun c => by
    change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop) ≫ τ.hom.appTop).hom c =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom c
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hτ])

theorem ΓAlgEquiv_apply {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) (τ : C ≅ C) (hτ : τ.hom ≫ z = z)
    (b : Γ(C, ⊤)) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    ΓAlgEquiv z τ hτ b = τ.hom.appTop.hom b := rfl

theorem secAlgHom_comp {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) (τ : C ≅ C) (hτ : τ.hom ≫ z = z)
    (y : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    (secAlgHom z y).comp (ΓAlgEquiv z τ hτ : Γ(C, ⊤) →ₐ[k] Γ(C, ⊤)) =
      secAlgHom z ⟨y.1 ≫ τ.hom, by rw [Category.assoc, hτ, y.2]⟩ := by
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  apply AlgHom.ext
  intro b
  change (secAlgHom z y) (τ.hom.appTop.hom b) = secAlgHom z ⟨y.1 ≫ τ.hom, _⟩ b
  rw [secAlgHom_apply, secAlgHom_apply]
  change _ = ((y.1 ≫ τ.hom).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom b
  rw [Scheme.Hom.comp_appTop]
  rfl

end N8Asm

open N8Asm in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules)
    (ι : K ⟶ A) (hι : IsClosedImmersion ι) (hfin : IsFinite (ι ≫ f))
    (hK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓜 t x) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1} ∣
      (ι ≫ f).finrank (IsLocalRing.closedPoint k) := by
  classical
  haveI := hι
  haveI := hfin
  haveI : IsAffine K := isAffine_of_isAffineHom (ι ≫ f)
  haveI : Flat (ι ≫ f) := flat_of_field (ι ≫ f)
  letI alg : Algebra k Γ(K, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ f).appTop).hom.toAlgebra

  let g : {y : Spec (CommRingCat.of k) ⟶ K // y ≫ (ι ≫ f) = 𝟙 _} →
      {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1} :=
    fun y => ⟨⟨y.1 ≫ ι, by rw [Category.assoc, y.2]⟩, y.1, rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · intro y y' h
      have h1 : (g y).1.1 = (g y').1.1 := by rw [h]
      exact Subtype.ext ((cancel_mono ι).1 h1)
    · rintro ⟨x, y, hy⟩
      refine ⟨⟨y, ?_⟩, ?_⟩
      · rw [← Category.assoc, hy, x.2]
      · apply Subtype.ext; apply Subtype.ext; exact hy
  rw [← Nat.card_eq_of_bijective g hg]

  have hconst : ∀ s : ↥(Spec (CommRingCat.of k)), (ι ≫ f).finrank s = (ι ≫ f).finrank (IsLocalRing.closedPoint k) := by
    intro s; congr 1; exact Subsingleton.elim _ _
  obtain ⟨hfinB, hrank⟩ := finrank_sections_eq (ι ≫ f) ((ι ≫ f).finrank (IsLocalRing.closedPoint k)) hconst
  haveI := hfinB

  rw [Nat.card_eq_of_bijective _ (secAlgHom_bijective (ι ≫ f)), ← hrank]

  apply AlgHom.natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed k Γ(K, ⊤)
  intro φ ψ
  obtain ⟨y₁, rfl⟩ := (secAlgHom_bijective (ι ≫ f)).2 φ
  obtain ⟨y₂, rfl⟩ := (secAlgHom_bijective (ι ≫ f)).2 ψ
  obtain ⟨τ, hτz, hτ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer L 𝓜 ι hK y₁.1 y₂.1 y₁.2 y₂.2
  refine ⟨ΓAlgEquiv (ι ≫ f) τ hτz, ?_⟩
  rw [secAlgHom_comp (ι ≫ f) τ hτz y₁]
  congr 1
  exact Subtype.ext hτ

end S_GoodReductionJacobian_RelativeGroupLaw_natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer (solution)
