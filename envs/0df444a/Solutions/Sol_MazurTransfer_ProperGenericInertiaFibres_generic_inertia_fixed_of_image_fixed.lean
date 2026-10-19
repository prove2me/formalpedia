-- Prove2me | solution 1 for MazurTransfer.ProperGenericInertiaFibres.generic_inertia_fixed_of_image_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:46:03.462148+00:00
-- url     : https://prove2.me/submissions/38671a37-d58d-4352-86d5-21923378b110

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transfer proper unramified inertia lift uniqueness to
the generic fibre, retaining the actual scalar and Galois maps.
Named downstream consumer: good-prime inertia fixed rational norm lifts.
-/
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_MazurTransfer_ProperUnramifiedInertiaFibres_inertia_fixed_of_image_fixed

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
theorem solution
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (φ : SchemeHomOver f f) [FormallyUnramified φ.val] [LocallyOfFiniteType φ.val]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫
      (genericFibreRestrict R K f f φ).val =
      x.val ≫ (genericFibreRestrict R K f f φ).val) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  let p := pullback.fst f (specGenericFibreInclusion R K)
  have hb : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [specGenericFibreInclusion_eq, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    exact (IsScalarTower.algebraMap_eq R K Ω).symm
  let y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f :=
    ⟨x.val ≫ p, by rw [Category.assoc, pullback.condition, ← Category.assoc,
      x.property, hb]⟩
  have hyimage : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ y.val ≫ φ.val =
      y.val ≫ φ.val := by
    have h := congrArg (fun z => z ≫ p) hx
    simpa only [p, Category.assoc, genericFibreRestrict_coe_comp_fst, y] using h
  have hy := ProperUnramifiedInertiaFibres.inertia_fixed_of_image_fixed K
    f φ.val φ.property A hA σ hσ y hyimage
  apply pullback.hom_ext
  · simpa only [Category.assoc, y] using hy
  · rw [Category.assoc, x.property]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    exact RingHom.ext (fun k => σ.commutes k)

#print axioms solution
