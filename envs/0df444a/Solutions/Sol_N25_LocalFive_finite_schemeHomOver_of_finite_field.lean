-- Prove2me | solution 1 for N25.LocalFive.finite_schemeHomOver_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:21.606722+00:00
-- url     : https://prove2.me/submissions/64387b41-a4bd-4b65-9aba-ad7f8bc78cd6

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_N25_LocalFive_finite_algHom_of_finite_target

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace N25.LocalFive

private theorem finite_affine_sections
    {k : Type} [Field k] [Finite k]
    {X : Scheme.{0}} [IsAffine X]
    (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] :
    Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q) := by
  let A : CommRingCat := Γ(X, ⊤)
  let ι : CommRingCat.of k ⟶ A := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop
  letI : Algebra k A := ι.hom.toAlgebra
  haveI : Algebra.FiniteType k A := by
    have hq : q.appTop.hom.FiniteType :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) q inferInstance
    exact RingHom.FiniteType.comp hq (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let β : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q →
      (A ⟶ CommRingCat.of k) := fun x =>
    x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom
  have split : ∀ x, ι ≫ β x = 𝟙 _ := by
    intro x
    simp only [ι, β, Category.assoc]
    rw [← Category.assoc q.appTop, ← Scheme.Hom.comp_appTop, x.2,
      Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  let toAlg : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q →
      (A →ₐ[k] k) := fun x =>
    { (β x).hom with
      commutes' := by
        intro a
        have h := congrArg (fun m : CommRingCat.of k ⟶ CommRingCat.of k => m.hom a)
          (split x)
        exact h }
  haveI : Finite (A →ₐ[k] k) := finite_algHom_of_finite_target
  apply Finite.of_injective toAlg
  intro x y h
  apply Subtype.ext
  apply ext_of_isAffine
  have hh : β x = β y := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h
  have hh' := congrArg (fun m => m ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) hh
  simpa [β] using hh'

private theorem finite_sections
    {k : Type} [Field k] [Finite k]
    {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] [QuasiCompact q] :
    Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q) := by
  classical
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let C := X.affineCover.finiteSubcover
  letI (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C]
    infer_instance
  letI (i : C.I₀) : Finite
      (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (C.f i ≫ q)) :=
    finite_affine_sections (C.f i ≫ q)
  let push : (Σ i : C.I₀,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (C.f i ≫ q)) →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q := fun z =>
    ⟨z.2.1 ≫ C.f z.1, by rw [Category.assoc, z.2.2]⟩
  apply Finite.of_surjective push
  intro x
  let s : Spec (CommRingCat.of k) := default
  let i := C.idx (x.1 s)
  have range : Set.range x.1 ⊆ Set.range (C.f i) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = s := Subsingleton.elim _ _
    rw [ha]
    exact C.covers (x.1 s)
  let l := IsOpenImmersion.lift (C.f i) x.1 range
  have hl : l ≫ C.f i = x.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨i, ⟨l, ?_⟩⟩, ?_⟩
  · rw [← Category.assoc, hl, x.2]
  · apply Subtype.ext
    exact hl

/-- A quasi-compact finite-type scheme has finitely many points over a finite field. -/
theorem _root_.solution
    {R k : Type} [CommRing R] [Field k]
    [Algebra R k] [Finite k]
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Finite (SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R k))) f) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let q := pullback.snd f t
  let toSec : SchemeHomOver t f →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q := fun x =>
    ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  haveI : Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) q) :=
    finite_sections q
  apply Finite.of_injective toSec
  intro x y h
  apply Subtype.ext
  have hh := congrArg (fun z => z.1 ≫ pullback.fst f t) h
  simpa only [toSec, pullback.lift_fst] using hh

end N25.LocalFive
