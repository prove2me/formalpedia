-- Prove2me | solution 1 for MazurTransfer.galois_fixed_scheme_point_unique_descent
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T19:27:13.421719+00:00
-- url     : https://prove2.me/submissions/3845400f-7a4f-420f-8dad-d08fb302cac7

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. -/
import Mathlib
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace MazurTransfer.PublicGaloisFixedRingMapDescent
variable (F K A : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K] [CommRing A]

theorem exists_descent (f : A →+* K) (hf : ∀ σ : K ≃ₐ[F] K, ∀ a, σ (f a) = f a) :
    ∃ g : A →+* F, (algebraMap F K).comp g = f := by
  classical
  have hrange (a : A) : ∃ x : F, algebraMap F K x = f a :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (f a)).mpr (fun σ => hf σ a)
  let d : A → F := fun a => Classical.choose (hrange a)
  have hd (a : A) : algebraMap F K (d a) = f a := Classical.choose_spec (hrange a)
  have hinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
  let g : A →+* F :=
    { toFun := d
      map_zero' := hinj (by rw [hd, map_zero, map_zero])
      map_one' := hinj (by rw [hd, map_one, map_one])
      map_add' a b := hinj (by rw [hd, map_add, map_add, hd, hd])
      map_mul' a b := hinj (by rw [hd, map_mul, map_mul, hd, hd]) }
  refine ⟨g, ?_⟩
  ext a
  exact hd a

end MazurTransfer.PublicGaloisFixedRingMapDescent

namespace MazurTransfer.PublicGaloisFixedSchemePointDescent
open CategoryTheory AlgebraicGeometry
variable (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K]

theorem exists_descent (X : Scheme.{0}) (b : Spec (CommRingCat.of K) ⟶ X)
    (hb : ∀ σ : K ≃ₐ[F] K, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b) :
    ∃ a : Spec (CommRingCat.of F) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ a = b := by
  let z := Scheme.SpecToEquivOfField K X b
  have hfactor : Spec.map z.2 ≫ X.fromSpecResidueField z.1 = b :=
    (Scheme.SpecToEquivOfField K X).symm_apply_apply b
  have hmap (σ : K ≃ₐ[F] K) : z.2 ≫ CommRingCat.ofHom σ.toRingHom = z.2 := by
    apply Spec.map_inj.mp
    apply (cancel_mono (X.fromSpecResidueField z.1)).mp
    simp only [Spec.map_comp, Category.assoc, hfactor, hb]
  have hfixed (σ : K ≃ₐ[F] K) (r : X.residueField z.1) : σ (z.2.hom r) = z.2.hom r :=
    congrArg (fun f : X.residueField z.1 ⟶ CommRingCat.of K => f.hom r) (hmap σ)
  obtain ⟨g, hg⟩ := PublicGaloisFixedRingMapDescent.exists_descent F K (X.residueField z.1) z.2.hom hfixed
  have hg' : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap F K) = z.2 := by
    ext r
    exact RingHom.congr_fun hg r
  refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField z.1, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hg', hfactor]

end MazurTransfer.PublicGaloisFixedSchemePointDescent


theorem solution
    (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K]
    (X : Scheme.{0}) (b : Spec (CommRingCat.of K) ⟶ X)
    (hb : ∀ σ : K ≃ₐ[F] K, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b) :
    ∃! a : Spec (CommRingCat.of F) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ a = b := by
  letI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  letI : Epi (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    Flat.epi_of_flat_of_surjective _
  obtain ⟨a, ha⟩ := MazurTransfer.PublicGaloisFixedSchemePointDescent.exists_descent F K X b hb
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap F K)))).mp
  exact ha'.trans ha.symm

#print axioms solution
