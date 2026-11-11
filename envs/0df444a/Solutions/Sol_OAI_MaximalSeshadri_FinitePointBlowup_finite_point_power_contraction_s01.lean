-- Prove2me | solution 1 for OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:59.051068+00:00
-- url     : https://prove2.me/submissions/8b384d50-ed46-4e93-b1ec-ebcbba9cc15f

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
-- module Solutions.Q223_SES.Seshadri_Blowup_OrderContraction
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial
variable (K : Type) [Field K]

lemma chartExponent_injective (i : Fin 2) : Function.Injective (chartExponent i) := by
  intro d e h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  fin_cases i <;> simp [chartExponent_apply] at h0 h1
  all_goals ext j; fin_cases j <;> simpa using (by omega : _ )

lemma chartExponent_self (i : Fin 2) (d : Fin 2 →₀ ℕ) :
    chartExponent i d i = Finsupp.degree d := by
  simp only [chartExponent_apply, ite_true, if_true]
  rw [Finsupp.degree_eq_sum]
  simp

lemma chartSubstitution_eq_mapDomain (i : Fin 2) :
    chartSubstitution K i = AddMonoidAlgebra.mapDomainRingHom K (chartExponent i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change chartSubstitution K i (C c) = _
    rw [substitution_C]
    change AddMonoidAlgebra.single 0 c =
      AddMonoidAlgebra.mapDomain (chartExponent i) (AddMonoidAlgebra.single 0 c)
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  · intro j
    change chartSubstitution K i (X j) = _
    rw [chartSubstitution, MvPolynomial.eval₂Hom_X']
    change (if j = i then AddMonoidAlgebra.single (Finsupp.single i 1) 1 else
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 *
        AddMonoidAlgebra.single (Finsupp.single j 1) 1) =
      AddMonoidAlgebra.mapDomain (chartExponent i)
        (AddMonoidAlgebra.single (Finsupp.single j 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single]
    split_ifs with h
    · subst j
      congr 1
      ext j
      fin_cases i <;> fin_cases j <;> simp [chartExponent_apply]
    · rw [AddMonoidAlgebra.single_mul_single, one_mul]
      congr 1
      ext q
      fin_cases i <;> fin_cases j <;> fin_cases q <;> simp_all [chartExponent_apply]

lemma variable_pow_dvd_iff {σ : Type} [DecidableEq σ]
    (i : σ) (m : ℕ) (p : MvPolynomial σ K) :
    X i ^ m ∣ p ↔ ∀ d : σ →₀ ℕ, d i < m → p.coeff d = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have he : ¬ Finsupp.single i m ≤ d := by
      simpa only [Finsupp.single_le_iff] using (not_le.mpr hd)
    rw [← MvPolynomial.coeff_modMonomial_of_not_le p he, h, MvPolynomial.coeff_zero]
  · intro h
    ext d
    by_cases hd : Finsupp.single i m ≤ d
    · simp [MvPolynomial.coeff_modMonomial_of_le p hd]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le p hd]
      exact h d (by simpa only [Finsupp.single_le_iff, not_le] using hd)

lemma substitution_coeff (i : Fin 2) (p : PlaneRing K) (d : Fin 2 →₀ ℕ) :
    (chartSubstitution K i p).coeff (chartExponent i d) = p.coeff d := by
  rw [chartSubstitution_eq_mapDomain]
  exact Finsupp.mapDomain_apply (chartExponent_injective i)
    (AddMonoidAlgebra.coeff p) d

lemma substitution_coeff_outside (i : Fin 2) (p : PlaneRing K) (d : Fin 2 →₀ ℕ)
    (hd : d ∉ Set.range (chartExponent i)) :
    (chartSubstitution K i p).coeff d = 0 := by
  rw [chartSubstitution_eq_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range (AddMonoidAlgebra.coeff p) d hd

lemma substitution_variable_pow_dvd_iff (i : Fin 2) (m : ℕ) (p : PlaneRing K) :
    X i ^ m ∣ chartSubstitution K i p ↔ p ∈ originIdeal K ^ m := by
  rw [variable_pow_dvd_iff, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h d hd
    rw [← substitution_coeff K i p d]
    exact h _ (by simpa only [chartExponent_self] using hd)
  · intro h d hd
    by_cases he : d ∈ Set.range (chartExponent i)
    · obtain ⟨e, rfl⟩ := he
      rw [substitution_coeff]
      exact h e (by simpa only [chartExponent_self] using hd)
    · exact substitution_coeff_outside K i p d he

lemma chart_exceptional_pow_dvd_iff (i : Fin 2) (m : ℕ) (p : PlaneRing K) :
    (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m ∣
      ReesGrading.chartBase (originIdeal K) (coordinate K i) p ↔
        p ∈ originIdeal K ^ m := by
  have he := map_dvd_iff (chartEquiv K i)
    (a := (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m)
    (b := ReesGrading.chartBase (originIdeal K) (coordinate K i) p)
  rw [← he]
  change toPolynomial K i ((ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) ^ m) ∣
    toPolynomial K i (ReesGrading.chartBase (originIdeal K) (coordinate K i) p) ↔ _
  rw [map_pow (toPolynomial K i)
    (ReesGrading.chartBase (originIdeal K) (coordinate K i) (X i)) m,
    toPolynomial_base, substitution_self, toPolynomial_base]
  exact substitution_variable_pow_dvd_iff K i m p

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.FlatContraction
noncomputable section
open TensorProduct
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]

theorem contraction (J : Ideal S) :
    (J.map (Algebra.TensorProduct.includeRight (R := R) (A := A))).comap
        (algebraMap A (A ⊗[R] S)) =
      (J.comap (algebraMap R S)).map (algebraMap R A) := by
  let I := J.comap (algebraMap R S)
  let q : R ⧸ I →ₐ[R] S ⧸ J := Ideal.quotientMapₐ J (Algebra.ofId R S) le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  have ht := Module.Flat.lTensor_preserves_injective_linearMap
    (M := A) q.toLinearMap hq
  ext a
  change algebraMap A (A ⊗[R] S) a ∈ J.map _ ↔ a ∈ I.map (algebraMap R A)
  have hleft : algebraMap A (A ⊗[R] S) a ∈ J.map
      (Algebra.TensorProduct.includeRight (R := R) (A := A)) ↔
      a ⊗ₜ[R] (1 : S ⧸ J) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← (Algebra.TensorProduct.tensorQuotientEquiv (R := R) A S A J).symm.map_eq_zero_iff]
    change (Algebra.TensorProduct.tensorQuotientEquiv (R := R) A S A J).symm
      (Ideal.Quotient.mk _ (a ⊗ₜ[R] (1 : S))) = 0 ↔ _
    simp
  have hright : a ∈ I.map (algebraMap R A) ↔ a ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).map_eq_zero_iff]
    rfl
  rw [hleft, hright]
  constructor
  · intro h
    apply ht
    simpa using h
  · intro h
    have he := congrArg (q.toLinearMap.lTensor A) h
    simpa using he

end
end MaximalSeshadri.FlatContraction

namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading TensorProduct
variable (K : Type) [Field K]

lemma exceptionalChart_comap_pow (i : Fin 2) (m : ℕ) :
    ((exceptionalChartIdeal K i)^m).comap (chartBase (originIdeal K) (coordinate K i)) =
      (originIdeal K)^m := by
  ext p
  change chartBase (originIdeal K) (coordinate K i) p ∈
    (Ideal.span {chartBase (originIdeal K) (coordinate K i) (X i)})^m ↔ _
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact chart_exceptional_pow_dvd_iff K i m p

lemma flat_chart_order {A : Type} [CommRing A] [Algebra (PlaneRing K) A]
    [Module.Flat (PlaneRing K) A] (i : Fin 2) (m : ℕ) :
    letI : Algebra (PlaneRing K) (chart (originIdeal K) (coordinate K i)) :=
      (chartBase (originIdeal K) (coordinate K i)).toAlgebra
    (((exceptionalChartIdeal K i)^m).map
      (Algebra.TensorProduct.includeRight (R := PlaneRing K) (A := A))).comap
      (algebraMap A (A ⊗[PlaneRing K] chart (originIdeal K) (coordinate K i))) =
      ((originIdeal K).map (algebraMap (PlaneRing K) A))^m := by
  let : Algebra (PlaneRing K) (chart (originIdeal K) (coordinate K i)) :=
    (chartBase (originIdeal K) (coordinate K i)).toAlgebra
  rw [FlatContraction.contraction]
  change (((exceptionalChartIdeal K i)^m).comap
    (chartBase (originIdeal K) (coordinate K i))).map _ = _
  rw [exceptionalChart_comap_pow, Ideal.map_pow]

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (m : ℕ) :
    (I^m).comap f = (I.comap f)^m := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I^m) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)^m).map _ = ((I.comap f).ideal (U y))^m
    rw [Ideal.map_pow, comap_ideal I f (U y) (V y) (hUV y)]

lemma specIdeal_pow {R : Type} [CommRing R] (I : Ideal R) (m : ℕ) :
    specIdeal (I^m) = (specIdeal I)^m := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa only [specIdeal_top, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using
    Ideal.map_pow (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I m

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

lemma invertible_of_affine_equation [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    (r : Γ(Y, ⊤)) (hr : IsRegular r)
    (hI : (I.comap f).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  apply invertible_of_local_equations
  intro y
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  refine ⟨U, trivial, U.1.topIso.inv r, ?_, ?_⟩
  · exact regular_map_flat U.1.topIso.inv.hom (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso U.1.topIso.inv)) hr
  · rw [IdealPullback.comap_ι_top, hI, Ideal.map_span, Set.image_singleton]

lemma invertible_Spec_of_span_regular {R S : Type} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (r : S) (hr : IsRegular r)
    (hI : I.map f = Ideal.span {r}) :
    InvertiblePullbackIdeal (IdealPullback.specIdeal I)
      (Spec.map (CommRingCat.ofHom f)) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of S)
  apply invertible_of_affine_equation _ _ (e.inv r)
  · exact regular_map_flat e.inv.hom (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso e.inv)) hr
  · rw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, hI,
      Ideal.map_span, Set.image_singleton]

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry

lemma specIdeal_map {R S : Type} [CommRing R] [CommRing S]
    (J : Ideal S) (f : R →+* S) :
    (specIdeal J).map (Spec.map (CommRingCat.ofHom f)) = specIdeal (J.comap f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [map_top, specIdeal_top, specIdeal_top]
  apply Ideal.comap_injective_of_surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp,
    ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f), CommRingCat.hom_comp,
    ← Ideal.comap_comap, Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv),
    Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.FlatContraction
noncomputable section
open TensorProduct
variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]

lemma includeRight_flat :
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).Flat := by
  have he : (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom =
      (Algebra.TensorProduct.comm R S A).toRingHom.comp (algebraMap S (S ⊗[R] A)) := by
    ext x
    simp
  rw [he]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R S A).bijective)

end
end MaximalSeshadri.FlatContraction


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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PowerContraction
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct ReesGrading
open MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
variable (K : Type) [Field K]

theorem blowup_power_contraction {A : Type} [CommRing A] [Algebra (PlaneRing K) A]
    [Module.Flat (PlaneRing K) A]
    {B : Scheme} {π : B ⟶ Spec (CommRingCat.of A)}
    (hπ : IsBlowup (specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))) π)
    (m : ℕ) :
    (((specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))).comap π)^m).map π =
      specIdeal (((originIdeal K).map (algebraMap (PlaneRing K) A))^m) := by
  let J : Ideal A := (originIdeal K).map (algebraMap (PlaneRing K) A)
  let S := chart (originIdeal K) (coordinate K 0)
  let : Algebra (PlaneRing K) S := (chartBase (originIdeal K) (coordinate K 0)).toAlgebra
  let C := A ⊗[PlaneRing K] S
  let α : A →+* C := algebraMap A C
  let β : S →+* C := (Algebra.TensorProduct.includeRight (R := PlaneRing K) (A := A)).toRingHom
  have hcomm : α.comp (algebraMap (PlaneRing K) A) =
      β.comp (chartBase (originIdeal K) (coordinate K 0)) := by
    apply RingHom.ext
    intro x
    change (algebraMap (PlaneRing K) A) x ⊗ₜ[PlaneRing K] (1 : S) =
      (1 : A) ⊗ₜ[PlaneRing K] (algebraMap (PlaneRing K) S) x
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have hmap : J.map α = (exceptionalChartIdeal K 0).map β := by
    change ((originIdeal K).map _).map _ = _
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_ideal_principal]
    rfl
  have hf : InvertiblePullbackIdeal (specIdeal J) (Spec.map (CommRingCat.ofHom α)) := by
    apply InvertibleLocal.invertible_Spec_of_span_regular J α
      (β (chartBase (originIdeal K) (coordinate K 0) (MvPolynomial.X 0)))
    · exact InvertibleLocal.regular_map_flat β FlatContraction.includeRight_flat
        (chart_generator_regular (originIdeal K) (coordinate K 0))
    · rw [hmap]
      exact Ideal.map_span β {chartBase (originIdeal K) (coordinate K 0) (MvPolynomial.X 0)} |>.trans
        (by rw [Set.image_singleton])
  obtain ⟨e, he, _⟩ := hπ.2 _ _ hf
  have hcontract : ((J.map α)^m).comap α = J^m := by
    rw [hmap, ← Ideal.map_pow]
    exact flat_chart_order K 0 m
  apply le_antisymm
  · have hh := Scheme.IdealSheafData.map_mono π
      ((((specIdeal J).comap π)^m).le_map_comap e)
    dsimp only at hh
    rw [← Scheme.IdealSheafData.map_comp, he, comap_pow,
      ← Scheme.IdealSheafData.comap_comp, he, specIdeal_comap,
      ← specIdeal_pow, specIdeal_map, hcontract] at hh
    exact hh
  · rw [specIdeal_pow, ← comap_pow]
    exact ((specIdeal J)^m).le_map_comap π

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X Y X' Y' : Scheme}

lemma comap_map_le_of_commSq (I : X.IdealSheafData)
    (f : X ⟶ Y) (g : X' ⟶ X) (j : Y' ⟶ Y) (f' : X' ⟶ Y')
    (h : g ≫ f = f' ≫ j) :
    (I.map f).comap j ≤ (I.comap g).map f' := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.comap_comp, ← h, Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.comap_mono g (I.comap_map_le f)

lemma le_of_openCover (C : Y.OpenCover) {I J : Y.IdealSheafData}
    (h : ∀ i, I.comap (C.f i) ≤ J.comap (C.f i)) : I ≤ J := by
  let U (i : Σ i : C.I₀, (C.X i).affineOpens) : Y.affineOpens :=
    ⟨C.f i.1 ''ᵁ i.2.1, i.2.2.image_of_isOpenImmersion (C.f i.1)⟩
  apply Scheme.IdealSheafData.le_of_iSup_eq_top U
  · apply top_unique
    intro y _
    obtain ⟨i, x, rfl⟩ := C.exists_eq y
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : (C.X i).Opens) from trivial)
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, x, hxV, rfl⟩
  · intro i
    have hi := h i.1 i.2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
    exact Ideal.comap_le_comap_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso (C.f i.1 |>.appIso i.2).inv).surjective _ _ |>.mp hi

lemma power_contraction_of_openCover (I : Y.IdealSheafData) (f : X ⟶ Y)
    (C : Y.OpenCover) (m : ℕ)
    (h : ∀ i, (((I.comap (C.f i)).comap (pullback.fst (C.f i) f))^m).map
      (pullback.fst (C.f i) f) = (I.comap (C.f i))^m) :
    ((I.comap f)^m).map f = I^m := by
  apply le_antisymm
  · apply le_of_openCover C
    intro i
    have hi := comap_map_le_of_commSq ((I.comap f)^m) f
      (pullback.snd (C.f i) f) (C.f i) (pullback.fst (C.f i) f)
      (pullback.condition.symm)
    rw [comap_pow, ← Scheme.IdealSheafData.comap_comp, ← pullback.condition,
      Scheme.IdealSheafData.comap_comp, h i] at hi
    simpa only [comap_pow] using hi
  · rw [← comap_pow]
    exact (I^m).le_map_comap f

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry MaximalSeshadri.AlgebraicJets MaximalSeshadri.IdealPullback
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem point_power_contraction
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (specIdeal (RingHom.ker ρ)) π) (m : ℕ) :
    (((specIdeal (RingHom.ker ρ)).comap π)^m).map π =
      (specIdeal (RingHom.ker ρ))^m := by
  obtain ⟨x, s, hs, _, hj, hI⟩ := exists_centered_etale_point_chart 2 ρ
  let φ := (algebraMap S (Localization.Away s)).comp (MvPolynomial.aeval (R := K) x).toRingHom
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let I := specIdeal (RingHom.ker ρ)
  let U : (Spec (.of S)).Opens := I.support.compl
  let obj : Bool → Scheme := fun b => if b then U.toScheme else Spec (.of (Localization.Away s))
  let map : (b : Bool) → obj b ⟶ Spec (.of S) := fun b => Bool.rec a U.ι b
  have cover : ∀ p : Spec (.of S), ∃ b y, map b y = p := by
    intro p
    by_cases hp : p ∈ (I.support : Set (Spec (.of S)))
    · have hq : RingHom.ker ρ ≤ p.asIdeal := by
        rw [show (I.support : Set (Spec (.of S))) = PrimeSpectrum.zeroLocus (RingHom.ker ρ)
          from specIdeal_support _] at hp
        exact (PrimeSpectrum.mem_zeroLocus p _).mp hp
      have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
        (fun c => ⟨algebraMap K S c, by simp⟩)
      have heq : p.asIdeal = RingHom.ker ρ := (hmax.eq_of_le p.isPrime.ne_top hq).symm
      have hm : s ∉ p.asIdeal := by simpa only [heq, RingHom.mem_ker] using hs
      have hp' : p ∈ Set.range a := by
        change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s)))
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
        exact hm
      obtain ⟨y, hy⟩ := hp'
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨p, hp⟩ : U), rfl⟩
  let C : (Spec (.of S)).OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  apply power_contraction_of_openCover I π C m
  intro b
  cases b
  · change (((I.comap a).comap (pullback.fst a π))^m).map (pullback.fst a π) = (I.comap a)^m
    have he : I.comap a = specIdeal ((PlaneBlowup.originIdeal K).map φ) := by
      rw [specIdeal_comap]
      exact congrArg specIdeal hI
    rw [he]
    let : Algebra (PlaneBlowup.PlaneRing K) (Localization.Away s) := φ.toAlgebra
    have : Algebra.Etale (PlaneBlowup.PlaneRing K) (Localization.Away s) :=
      RingHom.etale_algebraMap.mp hj
    have hθ : IsBlowup (specIdeal ((PlaneBlowup.originIdeal K).map φ)) (pullback.fst a π) := by
      have hb : IsBlowup (I.comap a) (pullback.fst a π) := hπ.flat_baseChange a
      rwa [he] at hb
    rw [← specIdeal_pow]
    exact PlaneBlowup.blowup_power_contraction K hθ m
  · change (((I.comap U.ι).comap (pullback.fst U.ι π))^m).map (pullback.fst U.ι π) =
      (I.comap U.ι)^m
    have he : I.comap U.ι = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_comap]
      ext p
      exact iff_false_intro p.property
    rw [he, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst U.ι π)

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme}

theorem rational_point_power_contraction (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 2 f] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (π : B ⟶ X) (hπ : IsBlowup p.ker π) (m : ℕ) :
    ((p.ker.comap π)^m).map π = p.ker^m := by
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
  apply IdealPullback.power_contraction_of_openCover p.ker π C m
  intro b
  cases b
  · change (((p.ker.comap j).comap (pullback.fst j π))^m).map (pullback.fst j π) =
      (p.ker.comap j)^m
    rw [hker]
    exact point_power_contraction ρ _ (by simpa only [hker] using hπ.flat_baseChange j) m
  · change (((p.ker.comap W.ι).comap (pullback.fst W.ι π))^m).map (pullback.fst W.ι π) =
      (p.ker.comap W.ι)^m
    have he : p.ker.comap W.ι = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_comap]
      ext x
      exact iff_false_intro x.property
    rw [he, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst W.ι π)

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

lemma outside_comap_centre : (pointCentre p).comap (outsideOpen p).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  exact disjoint_compl_right

end
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd

theorem finite_point_power_contraction_s01_oai [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : ℕ) :
    (((pointCentre p).comap π)^m).map π = (pointCentre p)^m := by
  let C := pointCover p f hp hd
  apply IdealPullback.power_contraction_of_openCover (pointCentre p) π C m
  intro a
  cases a with
  | none =>
    change ((((pointCentre p).comap (outsideOpen p).ι).comap
      (pullback.fst (outsideOpen p).ι π))^m).map (pullback.fst (outsideOpen p).ι π) =
      ((pointCentre p).comap (outsideOpen p).ι)^m
    rw [outside_comap_centre, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst (outsideOpen p).ι π)
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
    have he : (pointCentre p).comap U.ι = l.ker :=
      (pointOpen_comap_centre p i).trans hker
    have : SmoothOfRelativeDimension 2 (U.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    change ((((pointCentre p).comap U.ι).comap (pullback.fst U.ι π))^m).map
      (pullback.fst U.ι π) = ((pointCentre p).comap U.ι)^m
    rw [he]
    exact PointBlowup.rational_point_power_contraction (U.ι ≫ f) l hl _
      (by simpa only [he] using hπ.open_baseChange U.ι) m

end

end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01_oai := @OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01_oai
