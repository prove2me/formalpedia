-- Prove2me | solution 1 for OAI.MaximalSeshadri.FinitePointBlowup.smooth_finite_point_blowup_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:49.306573+00:00
-- url     : https://prove2.me/submissions/9d8497b5-64ff-41ed-b1f1-499e6db7ba0e

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007
import Definitions.Def_Q223SES008

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Gluing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry MaximalSeshadri.Geometry

lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsRegular r) : IsRegular (f r) := by
  let :=  f.toAlgebra
  let : Module.Flat R S := hf
  apply (Commute.isRegular_iff (fun s => Commute.all _ s)).mpr
  change Function.Injective (fun s : S => f r * s)
  exact Module.Flat.isSMulRegular_of_isRegular hr

variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)

lemma invertible_flat_pullback (hf : InvertiblePullbackIdeal I f)
    (g : Z ⟶ Y) [Flat g] : InvertiblePullbackIdeal I (g ≫ f) := by
  apply invertible_of_local_equations
  intro z
  obtain ⟨U, hzU, r, hr, hI⟩ := local_equations hf (g z)
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ g ⁻¹ᵁ U.1 from hzU)
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.toScheme := hV
  let g' := g.resLE U.1 V hVU
  let : IsZariskiLocalAtSource (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  let : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  let : Flat g' := IsZariskiLocalAtSource.resLE hVU (inferInstanceAs (Flat g))
  have he : V.ι ≫ g = g' ≫ U.1.ι := (g.resLE_comp_ι hVU).symm
  refine ⟨⟨V, hV⟩, hzV, g'.appTop r,
    regular_map_flat g'.appTop.hom g'.flat_appTop hr, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Category.assoc, he,
    Category.assoc, Scheme.IdealSheafData.comap_comp,
    IdealPullback.comap_top, Scheme.IdealSheafData.comap_comp, hI,
    Ideal.map_span, Set.image_singleton]

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.flat_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X) [Flat j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_flat_pullback I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

end
end MaximalSeshadri.Geometry


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open KaehlerDifferential

section CoordinateBasis
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

theorem formallyUnramified_polynomial_of_basis
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyUnramified (MvPolynomial ι R) S := by
  have hz : KaehlerDifferential.map R (MvPolynomial ι R) S S = 0 := by
    apply b.ext
    intro i
    rw [hb, KaehlerDifferential.map_D]
    change D (MvPolynomial ι R) S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) = 0
    exact Derivation.map_algebraMap _ _
  constructor
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S y
  rw [hz]
  rfl

theorem formallySmooth_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallySmooth (MvPolynomial ι R) S := by
  classical
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial ι R))
  let : IsScalarTower R (MvPolynomial ι R) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (f.restrictScalars R)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let correction (i : ι) : I := ⟨algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) -
      g (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)), by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    change _ = (Ideal.Quotient.mkₐ R I) (g _)
    rw [← AlgHom.comp_apply, hg]
    exact (f.commutes _).symm⟩
  let d : Derivation R S I := (b.constr S correction).compDer (D R S)
  let g' : S →ₐ[R] B := liftOfDerivationToSquareZero I hI d
  have hcoords (i : ι) : g' (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) := by
    change ((b.constr S correction) (D R S (algebraMap _ _ (MvPolynomial.X i))) : B) +
      g (algebraMap _ _ (MvPolynomial.X i)) = _
    rw [← hb, b.constr_basis]
    exact sub_add_cancel _ _
  have hcomm : g'.comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) B := by
    apply MvPolynomial.algHom_ext
    exact hcoords
  let lift : S →ₐ[MvPolynomial ι R] B :=
    { g'.toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  refine ⟨lift, ?_⟩
  ext s
  change Ideal.Quotient.mk I (g' s) = f s
  rw [liftOfDerivationToSquareZero_mk_apply]
  exact AlgHom.congr_fun hg s

theorem formallyEtale_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := formallySmooth_polynomial_of_basis b hb
  let := formallyUnramified_polynomial_of_basis b hb
  constructor <;> infer_instance

end CoordinateBasis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_formallyEtale {σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  apply formallyEtale_polynomial_of_basis P.basisKaehler
  intro i
  rw [P.basisKaehler_apply]
  change D R S (P.val i) = D R S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

end

noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_etale {ι σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R)
      (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R)
    (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  have hφ := presentation_coordinate_formallyEtale P
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  let : Algebra.FinitePresentation (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := hφ
  change Algebra.Etale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  constructor <;> infer_instance

theorem exists_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (κ : Type) (_ : Finite κ) (x : κ → S), Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R) x).toRingHom.Etale := by
  classical
  obtain ⟨κ, σ, hσ, hκ, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := S)
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨((Set.range P.map)ᶜ : Set κ), inferInstance, (fun i => P.val i), ?_,
    presentation_coordinate_etale P⟩
  rw [← hP]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
    Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]

end

end MaximalSeshadri.AlgebraicJets


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtalePointChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

lemma etale_aeval_reindex {ι κ : Type} (x : ι → S) (h : (aeval (R := K) x).toRingHom.Etale)
    (e : κ ≃ ι) : (aeval (R := K) (fun i => x (e i))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (renameEquiv K e).toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply RingHom.ext
  intro p
  change aeval (fun i => x (e i)) p = aeval x (rename e p)
  exact (aeval_rename e x p).symm

lemma etale_aeval_center {ι : Type} (x : ι → S)
    (h : (aeval (R := K) x).toRingHom.Etale) (ρ : S →ₐ[K] K) :
    (aeval (R := K) (fun i => x i - algebraMap K S (ρ (x i)))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (polynomialTranslate (fun i => ρ (x i))).symm.toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply ringHom_ext
  · intro c; simp [polynomialTranslate]
  · intro i; simp [polynomialTranslate]

theorem exists_centered_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ x : Fin n → S, (∀ i, ρ (x i) = 0) ∧
      (aeval (R := K) x).toRingHom.Etale := by
  obtain ⟨κ, hκ, x, hcard, hx⟩ := exists_etale_coordinates (R := K) (S := S) n
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hcard)
  let y := fun i : Fin n => x (e.symm i)
  refine ⟨fun i => y i - algebraMap K S (ρ (y i)), ?_,
    etale_aeval_center y (etale_aeval_reindex x hx e.symm) ρ⟩
  intro i
  simp

end

noncomputable section
variable {R : Type*} [CommRing R]

lemma exists_away_map_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) ≤
      J.map (algebraMap R (Localization.Away s)) := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hden : ∀ x : t, ∃ s : p.primeCompl, s.val * x.val ∈ J := by
    intro x
    have hx : algebraMap R (Localization.AtPrime p) x.val ∈
        J.map (algebraMap R (Localization.AtPrime p)) :=
      hle (Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span x.property))
    obtain ⟨s, hs, h⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ J x.val).mp hx
    exact ⟨⟨s, hs⟩, h⟩
  choose d hd using hden
  let s : p.primeCompl := ∏ x : t, d x
  refine ⟨s.val, s.property, Ideal.map_le_iff_le_comap.mpr ?_⟩
  rw [← ht, Ideal.span_le]
  intro x hx
  have hdiv : d ⟨x, hx⟩ ∣ s := Finset.dvd_prod_of_mem d (Finset.mem_univ _)
  obtain ⟨c, hc⟩ := hdiv
  have hmul : s.val * x ∈ J := by
    have h := J.mul_mem_left c.val (hd ⟨x, hx⟩)
    simpa only [hc, Submonoid.coe_mul, mul_assoc, mul_left_comm] using h
  change algebraMap R (Localization.Away s.val) x ∈
    J.map (algebraMap R (Localization.Away s.val))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s.val) _ J x).mpr
  exact ⟨s.val, Submonoid.mem_powers _, hmul⟩

lemma exists_away_map_eq_of_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hJI : J ≤ I)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hs, hle⟩ := exists_away_map_le I J p hI heq.le
  exact ⟨s, hs, le_antisymm hle (Ideal.map_mono hJI)⟩

end

noncomputable section
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma unramified_map_under_local [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] (q : Ideal S) [q.IsPrime] :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      q.map (algebraMap S (Localization.AtPrime q)) := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have hmax : (maximalIdeal Rp).map (algebraMap Rp Sq) = maximalIdeal Sq :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal q Sq] at hmax
  exact hmax

theorem exists_unramified_fiber_neighborhood [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (q : Ideal S) [q.IsPrime] :
    ∃ s : S, s ∉ q ∧ q.map (algebraMap S (Localization.Away s)) =
      ((q.under R).map (algebraMap R S)).map
        (algebraMap S (Localization.Away s)) := by
  apply exists_away_map_eq_of_le q ((q.under R).map (algebraMap R S)) q
    (Ideal.fg_of_isNoetherianRing q) Ideal.map_comap_le
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact (unramified_map_under_local (R := R) q).symm

end

noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem exists_centered_etale_point_chart (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ (x : Fin n → S) (s : S), ρ s ≠ 0 ∧ (∀ i, ρ (x i) = 0) ∧
      ((algebraMap S (Localization.Away s)).comp (aeval (R := K) x).toRingHom).Etale ∧
      (RingHom.ker ρ).map (algebraMap S (Localization.Away s)) =
        (idealOfVars (Fin n) K).map
          ((algebraMap S (Localization.Away s)).comp (aeval (R := K) x).toRingHom) := by
  obtain ⟨x, hx, he⟩ := exists_centered_etale_coordinates n ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin n) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin n) K) S := he
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := K) (S := S)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let q := RingHom.ker ρ
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
    (fun c => ⟨algebraMap K S c, by simp⟩)
  have hp : q.under (MvPolynomial (Fin n) K) = idealOfVars (Fin n) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  obtain ⟨s, hs, hI⟩ :=
    exists_unramified_fiber_neighborhood (R := MvPolynomial (Fin n) K) q
  refine ⟨x, s, hs, hx, ?_, ?_⟩
  · change (algebraMap (MvPolynomial (Fin n) K) (Localization.Away s)).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  · rw [hp, Ideal.map_map] at hI
    convert hI using 1
    all_goals try with_reducible_and_instances rfl

end
end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PlaneCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial ReesGrading
variable (K : Type) [Field K]

lemma plane_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension 2 (MvPolynomial.C : K →+* PlaneRing K) := by
  change RingHom.IsStandardSmoothOfRelativeDimension 2 (algebraMap K (PlaneRing K))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact (planePresentation K).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

lemma chart_standardSmooth (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 2
      ((chartBase (originIdeal K) (coordinate K i)).comp MvPolynomial.C) := by
  have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2)).left (T := chart (originIdeal K) (coordinate K i))
    (MvPolynomial.C : K →+* PlaneRing K) (chartEquiv K i).symm (plane_standardSmooth K)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply RingHom.ext
  intro c
  exact (fromPolynomial_C K i c).symm

theorem smooth_structureMap : SmoothOfRelativeDimension 2 (structureMap K) := by
  have : ∀ i, IsAffine ((planeCover K).openCover.X i) :=
    fun i => inferInstanceAs (IsAffine (Spec (.of (chart (originIdeal K) (coordinate K i)))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
    (planeCover K).openCover
  intro i
  apply HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension.{0} 2)
  change Fin 2 at i
  change SmoothOfRelativeDimension 2
    ((chartCover (originIdeal K)).f (coordinate K i) ≫
      (projection (originIdeal K) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)))
  rw [← Category.assoc, chartCover_projection]
  apply (congrArg (SmoothOfRelativeDimension 2)
    (Spec.map_comp (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K))
      (CommRingCat.ofHom (chartBase (originIdeal K) (coordinate K i))))).mp
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{0} 2)).mpr
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2))
    _ (chart_standardSmooth K i)

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReesGrading MaximalSeshadri.Geometry
variable (K : Type) [Field K]

theorem smooth_etale_baseChange {Y B : Scheme}
    (j : Y ⟶ Spec (.of (PlaneRing K))) [Etale j]
    (ρ : B ⟶ Y) (hρ : IsBlowup ((IdealPullback.specIdeal (originIdeal K)).comap j) ρ) :
    SmoothOfRelativeDimension 2
      (ρ ≫ j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K))) := by
  let π := projection (originIdeal K)
  let hπ := rees_isBlowup (originIdeal K)
  let e := hρ.iso (hπ.flat_baseChange j)
  have hc : e.hom ≫ pullback.snd j π ≫ structureMap K =
      ρ ≫ j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
    have he : e.hom ≫ pullback.fst j π = ρ :=
      hρ.iso_hom_comp (hπ.flat_baseChange j)
    calc
      _ = e.hom ≫ (pullback.snd j π ≫ π) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        simp only [structureMap, π, Category.assoc]
      _ = e.hom ≫ (pullback.fst j π ≫ j) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        rw [pullback.condition]
      _ = (e.hom ≫ pullback.fst j π) ≫ j ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        simp only [Category.assoc]
      _ = _ := by rw [he]
  rw [← hc]
  have : SmoothOfRelativeDimension 2 (structureMap K) := smooth_structureMap K
  have : SmoothOfRelativeDimension 2 (pullback.snd j π ≫ structureMap K) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry MaximalSeshadri.AlgebraicJets
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem exists_smooth_point_blowup_neighborhood
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (IdealPullback.specIdeal (RingHom.ker ρ)) π) :
    ∃ s : S, ρ s ≠ 0 ∧ SmoothOfRelativeDimension 2
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) π ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s)))) := by
  obtain ⟨x, s, hs, hx, hj, hI⟩ := exists_centered_etale_point_chart 2 ρ
  let f := (algebraMap S (Localization.Away s)).comp (MvPolynomial.aeval (R := K) x).toRingHom
  let j := Spec.map (CommRingCat.ofHom f)
  have : Etale j := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hj
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let θ := pullback.fst a π
  have hθ : IsBlowup ((IdealPullback.specIdeal (PlaneBlowup.originIdeal K)).comap j) θ := by
    have h := hπ.flat_baseChange a
    rw [IdealPullback.specIdeal_comap] at h ⊢
    simpa only [hI] using h
  have ht := PlaneBlowup.smooth_etale_baseChange K j θ hθ
  have hc : j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneBlowup.PlaneRing K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    simp [f, ← IsScalarTower.algebraMap_apply K S (Localization.Away s)]
  rw [hc] at ht
  exact ⟨s, hs, ht⟩

end
end MaximalSeshadri.PointBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplaneIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} {R : Type} [CommRing R]

lemma specIdeal_support (I : Ideal R) :
    ((specIdeal I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  change ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom : Set R) = _
  rw [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

end
end MaximalSeshadri.IdealPullback

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PointSmoothness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem smooth_point_blowup
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (IdealPullback.specIdeal (RingHom.ker ρ)) π) :
    SmoothOfRelativeDimension 2
      (π ≫ Spec.map (CommRingCat.ofHom (algebraMap K S))) := by
  obtain ⟨s, hs, hsm⟩ := exists_smooth_point_blowup_neighborhood ρ π hπ
  let I := IdealPullback.specIdeal (RingHom.ker ρ)
  let U : (Spec (.of S)).Opens := I.support.compl
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let base := Spec.map (CommRingCat.ofHom (algebraMap K S))
  have hb : SmoothOfRelativeDimension 2 base := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mpr
    exact RingHom.locally_of
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2)) _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr inferInstance)
  let obj : Bool → Scheme := fun b => if b then U.toScheme else Spec (.of (Localization.Away s))
  let map : (b : Bool) → obj b ⟶ Spec (.of S) := fun b =>
    Bool.rec a U.ι b
  have cover : ∀ p : Spec (.of S), ∃ b y, map b y = p := by
    intro p
    by_cases hp : p ∈ (I.support : Set (Spec (.of S)))
    · have hq : RingHom.ker ρ ≤ p.asIdeal := by
        rw [show (I.support : Set (Spec (.of S))) = PrimeSpectrum.zeroLocus (RingHom.ker ρ)
          from IdealPullback.specIdeal_support _] at hp
        exact (PrimeSpectrum.mem_zeroLocus p _).mp hp
      have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
        (fun c => ⟨algebraMap K S c, by simp⟩)
      have heq : p.asIdeal = RingHom.ker ρ :=
        (hmax.eq_of_le p.isPrime.ne_top hq).symm
      have hm : s ∉ p.asIdeal := by simpa only [heq, RingHom.mem_ker] using hs
      have hr := (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s)
      have hp' : p ∈ Set.range a := by
        change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s)))
        rw [hr]
        exact hm
      obtain ⟨y, hy⟩ := hp'
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨p, hp⟩ : U), rfl⟩
  let C : (Spec (.of S)).OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  intro b
  cases b
  · change SmoothOfRelativeDimension 2 (pullback.fst π a ≫ π ≫ base)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    have hc : a ≫ base =
        Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
      rw [← Spec.map_comp]
      rfl
    rw [hc]
    have hsp : (pullbackSymmetry π a).hom ≫ pullback.fst a π = pullback.snd π a :=
      pullbackSymmetry_hom_comp_fst π a
    rw [← hsp, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  · change SmoothOfRelativeDimension 2 (pullback.fst π U.ι ≫ π ≫ base)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    let := hπ.isIso_over_complement
    have : IsIso (pullback.snd π U.ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π U.ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 (U.ι ≫ base) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PointBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S]
lemma specMap_ker (f : R →+* S) :
    (Spec.map (CommRingCat.ofHom f)).ker = specIdeal (RingHom.ker f) := by
  rw [Scheme.ker_of_isAffine, specIdeal]
  congr 1
  apply Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]
  ext r
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  have he := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r
  change (Scheme.ΓSpecIso (.of S)).inv (f r) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) at he
  rw [← he]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).1

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme}

theorem smooth_rational_point_blowup (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 2 f] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (π : B ⟶ X) (hπ : IsBlowup p.ker π) :
    SmoothOfRelativeDimension 2 (π ≫ f) := by
  let point : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  let := isClosedImmersion_of_comp_eq_id f p hp
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 2) (f := f) (p point)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f (p point) := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst U
  let A := Γ(X, V)
  let g : CommRingCat.of K ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension 2 g.hom := by
    let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K A := hng.toAlgebra
  let j := hV.fromSpec
  have hmap : Spec.map g = j ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  have hps : Set.range p ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rw [show z = point from Subsingleton.elim _ _]
    rwa [hV.range_fromSpec]
  let l := IsOpenImmersion.lift j p hps
  have hlj : l ≫ j = p := IsOpenImmersion.lift_fac j p hps
  let q := Spec.preimage l
  have hq : Spec.map q = l := Spec.map_preimage l
  have hqg : g ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hmap, ← Category.assoc, hlj, hp, Spec.map_id]
  let ρ : A →ₐ[K] K :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hqg c }
  have hker : p.ker.comap j = IdealPullback.specIdeal (RingHom.ker ρ) := by
    have sq := IsOpenImmersion.isPullback_lift_id p j hps
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion p j,
      ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
      sq.isoPullback_hom_fst]
    change l.ker = _
    rw [← hq]
    exact IdealPullback.specMap_ker q.hom
  have hs : SmoothOfRelativeDimension 2 (pullback.fst j π ≫ j ≫ f) := by
    rw [← hmap]
    exact smooth_point_blowup ρ _ (by simpa only [hker] using hπ.flat_baseChange j)
  let W : X.Opens := p.ker.support.compl
  let obj : Bool → Scheme := fun b => if b then W.toScheme else Spec A
  let map : (b : Bool) → obj b ⟶ X := fun b => Bool.rec j W.ι b
  have cover : ∀ x : X, ∃ b y, map b y = x := by
    intro x
    by_cases hx : x ∈ (p.ker.support : Set X)
    · rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hx
      obtain ⟨y, hy⟩ := hps hx
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨x, hx⟩ : W), rfl⟩
  let C : X.OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  intro b
  cases b
  · change SmoothOfRelativeDimension 2 (pullback.fst π j ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc,
      ← pullbackSymmetry_hom_comp_fst π j, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  · change SmoothOfRelativeDimension 2 (pullback.fst π W.ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    let := hπ.isIso_over_complement
    have : IsIso (pullback.snd π W.ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π W.ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 (W.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PointBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_FiniteCenters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

lemma comap_mul_open {Y : Scheme.{0}} (I J : X.IdealSheafData)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (I * J).comap f = I.comap f * J.comap f := by
  ext U : 2
  let V : X.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := fun x hx => ⟨x, hx, rfl⟩
  rw [IdealPullback.comap_ideal _ f U V e]
  change ((I.ideal V) * (J.ideal V)).map _ = _
  rw [Ideal.map_mul]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    IdealPullback.comap_ideal _ f U V e]

lemma comap_prod_open {Y : Scheme.{0}} {α : Type} (s : Finset α)
    (I : α → X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f] :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, comap_mul_open, ih]

lemma comap_eq_top_of_disjoint (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (I.support : Set X) U) : I.comap U.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change x.val ∈ I.support ↔ False
  exact iff_false_intro (fun hx => Set.disjoint_left.mp h hx x.property)

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

omit [Fintype α] in
lemma pointOpen_comap_other (i j : α) (hji : j ≠ i) :
    (p j).ker.comap (pointOpen p i).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hx hxU
  exact hxU (show x ∈ (⨆ j : {j : α // j ≠ i}, (p j).ker.support) from
    (le_iSup (fun j : {j : α // j ≠ i} => (p j).ker.support) ⟨j, hji⟩) hx)

lemma pointOpen_comap_centre (i : α) :
    (pointCentre p).comap (pointOpen p i).ι = (p i).ker.comap (pointOpen p i).ι := by
  classical
  rw [pointCentre, comap_prod_open]
  exact Finset.prod_eq_single i (fun j _ hji => by
    simpa only [Scheme.IdealSheafData.one_eq_top] using pointOpen_comap_other p i j hji)
    (by simp)

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd

theorem smooth_finite_point_blowup_s01_oai [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) :
    SmoothOfRelativeDimension 2 (π ≫ f) := by
  let C := pointCover p f hp hd
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  change ∀ a : Option α, SmoothOfRelativeDimension 2
    (pullback.fst π (C.f a) ≫ π ≫ f)
  intro a
  cases a with
  | none =>
    change SmoothOfRelativeDimension 2
      (pullback.fst π (outsideOpen p).ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    have : IsIso (pullback.fst (outsideOpen p).ι π) := hπ.isIso_over_complement
    have : IsIso (pullback.snd π (outsideOpen p).ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π (outsideOpen p).ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 ((outsideOpen p).ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  | some i =>
    let U := pointOpen p i
    have hps : Set.range (p i) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, point_mem_own_open p f hp hd i z⟩, rfl⟩
    let l := IsOpenImmersion.lift U.ι (p i) hps
    have hlj : l ≫ U.ι = p i := IsOpenImmersion.lift_fac U.ι (p i) hps
    have hl : l ≫ (U.ι ≫ f) = 𝟙 _ := by rw [← Category.assoc, hlj, hp]
    have : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
    have hker : (p i).ker.comap U.ι = l.ker := by
      have sq := IsOpenImmersion.isPullback_lift_id (p i) U.ι hps
      rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (p i) U.ι,
        ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
        sq.isoPullback_hom_fst]
    have : SmoothOfRelativeDimension 2 (U.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    have hs : SmoothOfRelativeDimension 2 (pullback.fst U.ι π ≫ U.ι ≫ f) := by
      apply PointBlowup.smooth_rational_point_blowup (U.ι ≫ f) l hl
      have he : (pointCentre p).comap U.ι = l.ker :=
        (pointOpen_comap_centre p i).trans hker
      simpa only [he] using hπ.open_baseChange U.ι
    change SmoothOfRelativeDimension 2 (pullback.fst π U.ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc,
      ← pullbackSymmetry_hom_comp_fst π U.ι, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.FinitePointBlowup.smooth_finite_point_blowup_s01_oai := @OAI.MaximalSeshadri.FinitePointBlowup.smooth_finite_point_blowup_s01_oai
