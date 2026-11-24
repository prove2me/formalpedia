-- Prove2me | solution 1 for IsLocalRing.exists_approximable_henselization_of_localization_atPrime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T21:22:38.885647+00:00
-- url     : https://prove2.me/submissions/f6c87866-2201-4460-b4e0-66d07b26dc20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Unramified.LocalStructure
import Theorems.Thm_IsLocalRing_exists_noetherian_henselization
import Theorems.Thm_IsLocalRing_exists_smooth_factorization_over_henselization_of_localization_atPrime

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial


namespace PhilipponHenselianEtaleSection

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

private abbrev ρ := Algebra.ofId R (ResidueField R)

private theorem exists_section_standardPair (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R, (ρ R).comp ψ = φ := by
  have hx := (StandardEtalePair.hasMap_X (P := P)).map φ
  have hLift : ∀ p : R[X], p.Monic → ∀ a : ResidueField R,
      aeval a p = 0 → aeval a p.derivative ≠ 0 →
      ∃ b : R, p.IsRoot b ∧ residue R b = a :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp (show HenselianLocalRing R from inferInstance)
  obtain ⟨b, hb, hres⟩ := hLift P.f P.monic_f (φ P.X)
    hx.1 (hx.isUnit_derivative_f.ne_zero)
  have hb' : P.HasMap b := by
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        Polynomial.IsRoot.def] using hb
    · have h := hx.2.ne_zero
      rw [← hres, Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.eval₂_at_apply] at h
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
        (residue_ne_zero_iff_isUnit _).mp h
  refine ⟨P.lift b hb', P.hom_ext ?_⟩
  change residue R (P.lift b hb' P.X) = φ P.X
  rw [P.lift_X, hres]

private theorem exists_section_standard {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsStandardEtale R S] (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let P : StandardEtalePresentation R S := Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨ψ, hψ⟩ := exists_section_standardPair R P.P (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    DFunLike.congr_fun hψ (P.equivRing x)

/-- An algebra map from an étale algebra to the residue field of a Henselian
local ring lifts to an algebra map to the ring. -/
theorem exists_section {S : Type*} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) : ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let Q := RingHom.ker φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let : Algebra.IsEtaleAt R Q := Algebra.FormallyEtale.comp R S _
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φ' : Localization.Away g →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom g hu
  obtain ⟨ψ, hψ⟩ := exists_section_standard R φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), ?_⟩
  ext x
  exact (DFunLike.congr_fun hψ (algebraMap S (Localization.Away g) x)).trans
    (IsLocalization.Away.lift_eq g hu x)

universe u

/-- A lift of the residue point to an étale scheme over a Henselian local
ring extends to a section over the ring. -/
theorem exists_scheme_section {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [Etale g]
    (x : Spec (CommRingCat.of (ResidueField R)) ⟶ Y)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ Y,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = x := by
  obtain ⟨A, i, hi, hxI, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x default) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let e := IsOpenImmersion.lift i x hr
  have he : e ≫ i = x := IsOpenImmersion.lift_fac ..
  obtain ⟨p, hp⟩ := Spec.map_surjective (i ≫ g)
  obtain ⟨q, hq⟩ := Spec.map_surjective e
  have hpq : p ≫ q = CommRingCat.ofHom (residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hp, ← Category.assoc, he, hx]
  have hpe : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (i ≫ g))
  let : Algebra R A := p.hom.toAlgebra
  let : Algebra.Etale R A := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hpe
  let q' : A →ₐ[R] ResidueField R :=
    { toRingHom := q.hom
      commutes' := fun a => ConcreteCategory.congr_hom hpq a }
  obtain ⟨k, hk⟩ := exists_section R q'
  let k' : A ⟶ CommRingCat.of R := CommRingCat.ofHom k.toRingHom
  have hpk : p ≫ k' = 𝟙 _ := ConcreteCategory.hom_ext_iff.mpr k.commutes
  have hkq : k' ≫ CommRingCat.ofHom (residue R) = q := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun hk a
  refine ⟨Spec.map k' ≫ i, ?_, ?_⟩
  · rw [Category.assoc, ← hp, ← Spec.map_comp, hpk, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hkq, hq, he]

end PhilipponHenselianEtaleSection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing
open scoped TensorProduct


namespace PhilipponHenselianSmoothPoints

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

/-- A residue-field point of a smooth algebra over a henselian local ring
lifts to a point over the ring. -/
theorem exists_section {S : Type*} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  let p := RingHom.ker φ.toRingHom
  let : p.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let : Algebra.IsSmoothAt R p := inferInstance
  obtain ⟨g, hg, n, hAlg, hTower, hEt⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let L := Localization.Away g
  let P := MvPolynomial (Fin n) R
  let : Algebra P L := hAlg
  let : IsScalarTower R P L := hTower
  let : Algebra.IsStandardEtale P L := hEt
  let : Algebra.Etale P L := inferInstance
  have hu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φ' : L →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom g hu
  choose x hx using fun i : Fin n => residue_surjective (R := R) (φ' (algebraMap P L (MvPolynomial.X i)))
  let θ : P →ₐ[R] R := MvPolynomial.aeval x
  have hθ : (Algebra.ofId R (ResidueField R)).comp θ = φ'.comp (IsScalarTower.toAlgHom R P L) := by
    apply MvPolynomial.algHom_ext
    intro i
    change residue R (MvPolynomial.aeval x (MvPolynomial.X i)) = φ' (algebraMap P L (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact hx i
  let : Algebra P R := θ.toRingHom.toAlgebra
  let : IsScalarTower R P R := IsScalarTower.of_algebraMap_eq (fun x => (θ.commutes x).symm)
  let : Algebra P (ResidueField R) := ((residue R).comp θ.toRingHom).toAlgebra
  let : IsScalarTower P R (ResidueField R) := IsScalarTower.of_algebraMap_eq' rfl
  let T := R ⊗[P] L
  let b : L →ₐ[P] ResidueField R :=
    { toRingHom := φ'.toRingHom
      commutes' := fun y => (DFunLike.congr_fun hθ y).symm }
  let β : T →ₐ[R] ResidueField R :=
    Algebra.TensorProduct.lift (Algebra.ofId R (ResidueField R)) b (fun _ _ => Commute.all _ _)
  let : Algebra.Etale R T := inferInstanceAs (Algebra.Etale R (R ⊗[P] L))
  obtain ⟨η, hη⟩ := PhilipponHenselianEtaleSection.exists_section R β
  let I : L →ₐ[R] T := (Algebra.TensorProduct.includeRight : L →ₐ[P] T).restrictScalars R
  refine ⟨η.comp (I.comp (IsScalarTower.toAlgHom R S L)), ?_⟩
  ext z
  have h := DFunLike.congr_fun hη (I (algebraMap S L z))
  change residue R (η (I (algebraMap S L z))) = φ z
  rw [show residue R (η (I (algebraMap S L z))) = β (I (algebraMap S L z)) from h]
  change β (Algebra.TensorProduct.includeRight (algebraMap S L z)) = φ z
  have hβ := DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
    (Algebra.ofId R (ResidueField R)) b (fun _ _ => Commute.all _ _)) (algebraMap S L z)
  exact hβ.trans (IsLocalization.Away.lift_eq g hu z)

end PhilipponHenselianSmoothPoints

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits IsLocalRing


namespace PhilipponApproximationFromSmoothColimit

universe u v w

variable {R : Type u} [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R]

private abbrev C := AdicCompletion (maximalIdeal R) R

/-- A map that factors through a smooth algebra has a lift to the henselian
base with the same reduction as its map to the completion. -/
theorem exists_residue_approximation_of_smooth_factor
    {S B : Type u} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : S →ₐ[R] B) (f : B →ₐ[R] C (R := R)) :
    ∃ h : S →ₐ[R] R, ∀ s, residue (C (R := R)) (f (g s)) =
      ResidueField.map (algebraMap R (C (R := R))) (residue R (h s)) := by
  let e := RingEquiv.ofBijective (ResidueField.map (algebraMap R (C (R := R))))
    (AdicCompletion.residueField_map_bijective R)
  let ψ : B →ₐ[R] ResidueField R :=
    { toRingHom := e.symm.toRingHom.comp ((residue (C (R := R))).comp f.toRingHom)
      commutes' := fun r => by
        apply e.injective
        change e (e.symm (residue (C (R := R)) (f (algebraMap R B r)))) = e (residue R r)
        rw [e.apply_symm_apply, f.commutes]
        exact (ResidueField.map_residue (algebraMap R (C (R := R))) r).symm }
  obtain ⟨s, hs⟩ := PhilipponHenselianSmoothPoints.exists_section R ψ
  refine ⟨s.comp g, fun y => ?_⟩
  have hy := DFunLike.congr_fun hs (g y)
  change residue R (s (g y)) = e.symm (residue (C (R := R)) (f (g y))) at hy
  change residue (C (R := R)) (f (g y)) = e (residue R (s (g y)))
  rw [hy, e.apply_symm_apply]

variable {J : Type w} [Category.{v} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (α : (Functor.const J).obj (CommRingCat.of R) ⟶ F)
  (ι : F ⟶ (Functor.const J).obj (CommRingCat.of (C (R := R))))

/-- If the completion is a filtered colimit of smooth algebras, a point
of a finitely presented parameter algebra over the completion has a point
over the henselian ring with the same residue. -/
theorem exists_residue_approximation
    (hcolim : IsColimit (Cocone.mk _ ι)) [PreservesColimit F (forget CommRingCat.{u})]
    (hα : ∀ i, α.app i ≫ ι.app i = CommRingCat.ofHom (algebraMap R (C (R := R))))
    (hSmooth : ∀ i, (α.app i).hom.Smooth)
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (f : S →ₐ[R] C (R := R)) :
    ∃ g : S →ₐ[R] R, ∀ s, residue (C (R := R)) (f s) =
      ResidueField.map (algebraMap R (C (R := R))) (residue R (g s)) := by
  let T := CommRingCat.of R
  let q : T ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let f' : CommRingCat.of S ⟶ CommRingCat.of (C (R := R)) := CommRingCat.ofHom f.toRingHom
  have hq : q.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hf : ∀ i, q ≫ f' = α.app i ≫ ι.app i := fun i =>
    (CommRingCat.hom_ext (RingHom.ext f.commutes)).trans (hα i).symm
  obtain ⟨i, m, hm, hfm⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    T F α q (Cocone.mk _ ι) hcolim hq f' hf
  let : Algebra R (F.obj i) := (α.app i).hom.toAlgebra
  let : Algebra.Smooth R (F.obj i) := RingHom.smooth_algebraMap.mp (hSmooth i)
  let m' : S →ₐ[R] F.obj i :=
    { toRingHom := m.hom
      commutes' := fun r => ConcreteCategory.congr_hom hm r }
  let b : F.obj i →ₐ[R] C (R := R) :=
    { toRingHom := (ι.app i).hom
      commutes' := fun r => ConcreteCategory.congr_hom (hα i) r }
  obtain ⟨g, hg⟩ := exists_residue_approximation_of_smooth_factor m' b
  exact ⟨g, fun z => (congrArg (residue (C (R := R))) (ConcreteCategory.congr_hom hfm z)).trans (hg z)⟩

private theorem exists_polynomial_approximation_of_residue_approximation
    (approx : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      (f : S →ₐ[R] C (R := R)), ∃ g : S →ₐ[R] R, ∀ s, residue (C (R := R)) (f s) =
        ResidueField.map (algebraMap R (C (R := R))) (residue R (g s)))
    (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x : Fin n → C (R := R))
    (hx : ∀ k, MvPolynomial.aeval x (P k) = 0) :
    ∃ y : Fin n → R, (∀ k, MvPolynomial.aeval y (P k) = 0) ∧
      ∀ k, residue (C (R := R)) (x k) = ResidueField.map (algebraMap R (C (R := R))) (residue R (y k)) := by
  classical
  let K := Ideal.span (Set.range P)
  let S := MvPolynomial (Fin n) R ⧸ K
  let q : MvPolynomial (Fin n) R →ₐ[R] S := Ideal.Quotient.mkₐ R K
  have hK : K.FG := ⟨Finset.univ.image P, by simp [K]⟩
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.quotient hK
  have hle : K ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom :=
    Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hx k)
  let f : S →ₐ[R] C (R := R) := Ideal.Quotient.liftₐ K (MvPolynomial.aeval x) hle
  obtain ⟨g, hg⟩ := approx S f
  let y (k : Fin n) := g (q (MvPolynomial.X k))
  have hEval : MvPolynomial.aeval y = g.comp q := MvPolynomial.algHom_ext (by simp [y])
  refine ⟨y, ?_, ?_⟩
  · intro k
    have hq : q (P k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
    rw [hEval, AlgHom.comp_apply, hq, map_zero]
  · intro k
    have hq : f (q (MvPolynomial.X k)) = x k := by
      change (MvPolynomial.aeval x) (MvPolynomial.X k) = x k
      exact MvPolynomial.aeval_X _ _
    simpa only [hq] using hg (q (MvPolynomial.X k))

/-- A filtered smooth presentation of the completion implies polynomial
approximation modulo the maximal ideal of the henselian ring. -/
theorem exists_polynomial_approximation
    (hcolim : IsColimit (Cocone.mk _ ι)) [PreservesColimit F (forget CommRingCat.{u})]
    (hα : ∀ i, α.app i ≫ ι.app i = CommRingCat.ofHom (algebraMap R (C (R := R))))
    (hSmooth : ∀ i, (α.app i).hom.Smooth)
    (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x : Fin n → C (R := R))
    (hx : ∀ k, MvPolynomial.aeval x (P k) = 0) :
    ∃ y : Fin n → R, (∀ k, MvPolynomial.aeval y (P k) = 0) ∧
      ∀ k, residue (C (R := R)) (x k) = ResidueField.map (algebraMap R (C (R := R))) (residue R (y k)) :=
  exists_polynomial_approximation_of_residue_approximation
    (exists_residue_approximation F α ι hcolim hα hSmooth) n m P x hx

/-- The smooth factorization form of Néron desingularization suffices for
the polynomial approximation property. -/
theorem exists_polynomial_approximation_of_smooth_factorizations
    (factor : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      (f : S →ₐ[R] C (R := R)), ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Smooth R B)
        (g : S →ₐ[R] B) (h : B →ₐ[R] C (R := R)), h.comp g = f)
    (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x : Fin n → C (R := R))
    (hx : ∀ k, MvPolynomial.aeval x (P k) = 0) :
    ∃ y : Fin n → R, (∀ k, MvPolynomial.aeval y (P k) = 0) ∧
      ∀ k, residue (C (R := R)) (x k) = ResidueField.map (algebraMap R (C (R := R))) (residue R (y k)) := by
  apply exists_polynomial_approximation_of_residue_approximation _ n m P x hx
  intro S _ _ _ f
  obtain ⟨B, hRing, hAlgebra, hSmooth, g, h, hcomp⟩ := factor S f
  let := hRing
  let := hAlgebra
  let := hSmooth
  obtain ⟨g', hg'⟩ := exists_residue_approximation_of_smooth_factor g h
  exact ⟨g', fun s => (congrArg (fun f => residue (C (R := R)) (f s)) hcomp.symm).trans (hg' s)⟩

end PhilipponApproximationFromSmoothColimit

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (D S A : Type u) [CommRing D] [CommRing S] [CommRing A] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] (p : Ideal D) [p.IsPrime] [Algebra D S]
    [IsLocalization p.primeCompl S] [IsLocalRing S] [HenselianLocalRing A]
    (f : S →+* A) [IsLocalHom f] :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (b : S →+* R) (_ : IsLocalHom b),
      a.comp b = f ∧
        let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
        ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x' : Fin n → C),
          (∀ k, MvPolynomial.aeval x' (P k) = 0) →
          ∃ x : Fin n → R, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
            ∀ k, IsLocalRing.residue C (x' k) = IsLocalRing.ResidueField.map (algebraMap R C)
              (IsLocalRing.residue R (x k)) := by
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℤ D
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  obtain ⟨R, hRing, hHens, hNoeth, b, hb, _, hUniversal⟩ := IsLocalRing.exists_noetherian_henselization S
  let := hRing
  let := hHens
  let := hNoeth
  let := hb
  obtain ⟨a, ⟨ha, hcomp⟩, _⟩ := hUniversal A f
  refine ⟨R, hRing, hHens, hNoeth, a, ha, b, hb, hcomp, ?_⟩
  exact PhilipponApproximationFromSmoothColimit.exists_polynomial_approximation_of_smooth_factorizations
    (IsLocalRing.exists_smooth_factorization_over_henselization_of_localization_atPrime D S R p b hUniversal)

end

end
