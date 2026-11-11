-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:50.93307+00:00
-- url     : https://prove2.me/submissions/1c7bbaff-d0cf-472e-95e3-fae516beedfc

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES007
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_etale_line_frame_inside_s01

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem exists_standard_smooth_affine_inside
    (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g U.1) := by
  obtain ⟨B, hB, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := g) x
  have hBtop : B = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = g x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst B
  let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g V) := by
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, hfW, ?_⟩
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have hs := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (Γ(X, X.basicOpen f)) f (openScalars g V) hstd
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  exact (openScalars_restrict g (X.basicOpen_le f)).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupAffineSections
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames

variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.preIso (hπ : IsBlowup I π) (e : B' ≅ B) :
    IsBlowup I (e.hom ≫ π) := by
  refine ⟨InvertibleLocal.invertible_restrict_general I π hπ.1 e.hom,?_⟩
  intro Y f hf
  obtain ⟨g,hg,huniq⟩ := hπ.2 Y f hf
  refine ⟨g ≫ e.inv,by simp only [Category.assoc,Iso.inv_hom_id_assoc,hg],?_⟩
  intro g' hg'
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using huniq (g' ≫ e.hom) hg'

lemma IsBlowup.morphismRestrict (hπ : IsBlowup I π) (U : X.Opens) :
    IsBlowup (I.comap U.ι) (π ∣_ U) := by
  have H := (hπ.open_baseChange U.ι).preIso (isPullback_morphismRestrict π U).isoPullback
  rwa [(isPullback_morphismRestrict π U).isoPullback_hom_fst] at H

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma complement_nonempty (hI : I.support ≠ ⊤) : Nonempty (centreComplement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

lemma IsBlowup.nonempty_of_support_ne_top (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    Nonempty B :=
  (complement_nonempty hI).map hπ.complementLift

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} [IrreducibleSpace X] (I : X.IdealSheafData)

lemma support_comap_ne_top_of_open (hI : I.support ≠ ⊤) (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (centreComplement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri
noncomputable section
open Cardinal

theorem algebraic_of_countable_presentation
    {F E σ : Type} [Field F] [Uncountable F] [Field E] [Algebra F E]
    [Countable σ] (φ : MvPolynomial σ F →ₐ[F] E) (hφ : Function.Surjective φ) :
    Algebra.IsAlgebraic F E := by
  constructor
  intro x
  by_contra hx
  have hLI := (show Transcendental F x from hx).linearIndependent_sub_inv
  have hrank : Module.rank F E ≤ ℵ₀ := by
    calc
      _ ≤ Module.rank F (MvPolynomial σ F) :=
        LinearMap.rank_le_of_surjective φ.toLinearMap hφ
      _ = #(σ →₀ ℕ) := MvPolynomial.rank_eq
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
  exact (not_le_of_gt (Cardinal.aleph0_lt_mk (α := F)))
    (hLI.cardinal_le_rank.trans hrank)

theorem point_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [Nontrivial A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ) :
    Nonempty (A →ₐ[F] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →ₐ[F] A ⧸ m := Ideal.Quotient.mkₐ F m
  let ψ : MvPolynomial σ F →ₐ[F] A ⧸ m := q.comp φ
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp hφ
  let : Algebra.IsAlgebraic F (A ⧸ m) :=
    algebraic_of_countable_presentation ψ hψ
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] F).comp q⟩

theorem point_avoiding_sequence_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ)
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  classical
  let S : Submonoid A := Submonoid.closure (Set.range a)
  have hcount : (S : Set A).Countable := by
    change ((Submonoid.closure (Set.range a) : Submonoid A) : Set A).Countable
    rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
    exact Set.countable_range _
  let : Countable S := hcount.to_subtype
  have hden : S ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro b ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (ha n)
  let B := Localization S
  let : IsDomain B := IsLocalization.isDomain_localization hden
  let j : A →ₐ[F] B := IsScalarTower.toAlgHom F A B
  let vals : σ ⊕ S → B := Sum.elim (fun i => j (φ (MvPolynomial.X i)))
    (fun s => IsLocalization.mk' B 1 s)
  let ψ : MvPolynomial (σ ⊕ S) F →ₐ[F] B := MvPolynomial.aeval vals
  have hre : ψ.comp (MvPolynomial.rename Sum.inl) = j.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ψ, vals]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
    obtain ⟨p, rfl⟩ := hφ b
    refine ⟨MvPolynomial.rename Sum.inl p * MvPolynomial.X (Sum.inr s), ?_⟩
    rw [map_mul]
    have he := DFunLike.congr_fun hre p
    change ψ (MvPolynomial.rename Sum.inl p) = j (φ p) at he
    rw [he]
    simp only [ψ, MvPolynomial.aeval_X, vals, Sum.elim_inr]
    exact (IsLocalization.mk'_eq_mul_mk'_one _ _).symm
  obtain ⟨g⟩ := point_of_countable_presentation ψ hψ
  refine ⟨g.comp j, fun n => ?_⟩
  let s : S := ⟨a n, Submonoid.subset_closure ⟨n, rfl⟩⟩
  exact ((IsLocalization.map_units B s).map g.toMonoidHom).ne_zero

theorem point_avoiding_sequence
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType F A)
  exact point_avoiding_sequence_of_countable_presentation φ hφ a ha

end

end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_factor {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (p : Over.mk (𝟙 complexBase) ⟶ Over.mk f)
    (hp : p.left (fieldPoint ℂ) ∈ U.1) :
    ∃ ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ,
      affineComplexPoint f U ρ = p := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range p.left ⊆ Set.range U.2.fromSpec := by
    rintro _ ⟨z,rfl⟩
    change Spec (CommRingCat.of ℂ) at z
    rw [show z = fieldPoint ℂ from Subsingleton.elim _ _,U.2.range_fromSpec]
    exact hp
  let l := IsOpenImmersion.lift U.2.fromSpec p.left hr
  let q := Spec.preimage l
  have hq : Spec.map q ≫ U.2.fromSpec = p.left := by
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ hr
  have hg : CommRingCat.ofHom (openScalars f U.1) ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,← Category.assoc,hq,Spec.map_id]
    exact p.w
  let ρ : Γ(X,U.1) →ₐ[ℂ] ℂ :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hg c }
  refine ⟨ρ,?_⟩
  apply Over.OverMorphism.ext
  exact hq

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupHartogsCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_not_mem_basicOpen (S : Surface) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (t : Γ(S.scheme,U.1)) (ht : ρ t = 0) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∉ S.scheme.basicOpen t := by
  let z : PrimeSpectrum Γ(S.scheme,U.1) := ⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩
  change ¬ U.2.fromSpec z ∈ S.scheme.basicOpen t
  change ¬ z ∈ U.2.fromSpec ⁻¹ᵁ S.scheme.basicOpen t
  rw [U.2.fromSpec_preimage_basicOpen]
  exact fun h => h ht

lemma Surface.hartogs_chart (S : Surface) {r : ℕ} (p : Configuration S r)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        ∀ i, S.scheme.basicOpen (t i) ≤ centreComplement (centreIdeal S r p) := by
  classical
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  have hq : ∀ i, q i ≫ S.structureMap = 𝟙 _ := fun i => (p.val i).w
  have hd : Function.Injective (fun i => q i (fieldPoint ℂ)) := p.property
  by_cases hc : x ∈ (centreIdeal S r p).support
  · obtain ⟨j,hj⟩ := (FinitePointBlowup.mem_centre_support q x).mp hc
    have hxj : x = q j (fieldPoint ℂ) := by
      change x ∈ ((q j).ker.support : Set S.scheme) at hj
      rwa [FinitePointBlowup.point_support q S.structureMap hq j] at hj
    obtain ⟨U,hxU,hUW,e,t,het⟩ := S.etale_line_frame_inside_s01 (⟨O S.scheme, fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩)
      (W ⊓ FinitePointBlowup.pointOpen q j) x
      ⟨hx,hxj ▸ FinitePointBlowup.point_mem_own_open q S.structureMap hq hd j _⟩
    have hp : (p.val j).left (fieldPoint ℂ) ∈ U.1 := hxj ▸ hxU
    obtain ⟨ρ,hρ⟩ := affineComplexPoint_factor S.structureMap U (p.val j) hp
    let := (openScalars S.structureMap U.1).toAlgebra
    let a : Fin 2 → Γ(S.scheme,U.1) := fun i => t i - algebraMap ℂ _ (ρ (t i))
    refine ⟨U,hxU,hUW.trans inf_le_left,a,
      MaximalSeshadri.AlgebraicJets.etale_aeval_center t het ρ,?_⟩
    intro i y hy hyc
    obtain ⟨k,hk⟩ := (FinitePointBlowup.mem_centre_support q y).mp hyc
    have hyU := S.scheme.basicOpen_le (a i) hy
    have hyOpen := (hUW hyU).2
    have hkj : k = j := by
      by_contra hne
      exact (FinitePointBlowup.mem_pointOpen q j y).mp hyOpen k hne hk
    subst k
    have hyj : y = q j (fieldPoint ℂ) := by
      change y ∈ ((q j).ker.support : Set S.scheme) at hk
      rwa [FinitePointBlowup.point_support q S.structureMap hq j] at hk
    have hn := affineComplexPoint_not_mem_basicOpen S U ρ (a i) (by simp [a])
    rw [hρ] at hn
    exact hn (hyj ▸ hy)
  · obtain ⟨U,hxU,hUW,e,t,het⟩ := S.etale_line_frame_inside_s01 (⟨O S.scheme, fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩)
      (W ⊓ centreComplement (centreIdeal S r p)) x ⟨hx,hc⟩
    exact ⟨U,hxU,hUW.trans inf_le_left,t,het,fun i =>
      (S.scheme.basicOpen_le (t i)).trans (hUW.trans inf_le_right)⟩

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothSurfaceDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

open MvPolynomial
open MaximalSeshadri.AlgebraicJets

theorem two_le_dimension_of_standard_smooth {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) : 2 ≤ ringKrullDim S := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let q := RingHom.ker ρ
  have : q.IsPrime := RingHom.ker_isPrime ρ
  have hq : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  let : (idealOfVars (Fin 2) K).IsPrime := by
    rw [idealOfVars_eq_ker_constantCoeff]
    exact RingHom.ker_isPrime _
  let : q.LiesOver (idealOfVars (Fin 2) K) := ⟨hq.symm⟩
  let P : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {X (0 : Fin 2)}
  let : P.IsPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  have hP : P < idealOfVars (Fin 2) K := by
    refine lt_of_le_of_ne (Ideal.span_le.mpr (by
      rintro _ rfl
      exact Ideal.subset_span ⟨0,rfl⟩)) ?_
    intro H
    have h1 : X (1 : Fin 2) ∈ P := H ▸ Ideal.subset_span ⟨1,rfl⟩
    have hd : (X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 1 :=
      Ideal.mem_span_singleton.mp h1
    have := X_dvd_X.mp hd
    norm_num at this
  obtain ⟨Q,hQ,hQP,hQL⟩ := Ideal.exists_ideal_lt_liesOver_of_lt q hP
  have := hQP
  have := hQL
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < P := by
    apply bot_lt_iff_ne_bot.mpr
    intro H
    have h0 : X (0 : Fin 2) ∈ P := Ideal.subset_span (by simp)
    rw [H,Ideal.mem_bot] at h0
    exact X_ne_zero 0 h0
  obtain ⟨Q₀,hQ₀,hQ₀P,hQ₀L⟩ := Ideal.exists_ideal_lt_liesOver_of_lt Q hbot
  let l : LTSeries (PrimeSpectrum S) :=
    ((RelSeries.singleton {(a,b) : PrimeSpectrum S × PrimeSpectrum S | a < b} (⟨Q₀,hQ₀P⟩ : PrimeSpectrum S)).snoc
      (⟨Q,hQP⟩ : PrimeSpectrum S) hQ₀).snoc (⟨q,inferInstance⟩ : PrimeSpectrum S) hQ
  simpa only [show l.length = 2 from rfl, Nat.cast_ofNat, ringKrullDim] using
    Order.LTSeries.length_le_krullDim l
end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma Surface.two_le_dimension (S : Surface) : 2 ≤ topologicalKrullDim S.scheme := by
  obtain ⟨U,hxU,hU,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (Classical.ofNonempty : S.scheme) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  have : Uncountable ℂ := by
    rw [← Cardinal.aleph0_lt_mk_iff, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨ρ,-⟩ := point_avoiding_sequence (F := ℂ) (A := Γ(S.scheme,U.1))
    (fun _ => 1) (fun _ => one_ne_zero)
  have hd := LocalCurve.two_le_dimension_of_standard_smooth ρ
  have : IsOpenImmersion U.2.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  have he := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(S.scheme,U.1)) ≤ _ at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  exact hd.trans he
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PointBlowupExistence
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

lemma Surface.centre_support_ne_top (S : Surface) (r : ℕ) (p : Configuration S r) :
    (centreIdeal S r p).support ≠ ⊤ := by
  classical
  intro h
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  let f : Fin r → Set S.scheme := fun i => ((q i).ker.support : Set S.scheme)
  have hc : ∀ i, IsClosed (f i) := fun i => ((q i).ker.support).isClosed
  have hu : Set.univ ⊆ ⋃₀ (↑(Finset.univ.image f) : Set (Set S.scheme)) := by
    intro x _
    have hx : x ∈ (centreIdeal S r p).support := by rw [h]; trivial
    obtain ⟨i,hi⟩ := (FinitePointBlowup.mem_centre_support q x).mp hx
    exact Set.mem_sUnion.mpr ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  obtain ⟨z,hz,huz⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ S.scheme : IsIrreducible (Set.univ : Set S.scheme))
    (Finset.univ.image f) (by
      intro z hz
      obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
      exact hc i) hu
  obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
  have hs := FinitePointBlowup.point_support q
    S.structureMap (fun i => (p.val i).w) i
  let : Subsingleton S.scheme := ⟨fun x y => by
    have hx := huz (show x ∈ Set.univ from trivial)
    have hy := huz (show y ∈ Set.univ from trivial)
    change x ∈ ((q i).ker.support : Set S.scheme) at hx
    change y ∈ ((q i).ker.support : Set S.scheme) at hy
    rw [hs] at hx hy
    exact hx.trans hy.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology S.scheme
  have h2 := S.two_le_dimension
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 0) (h2.trans hd)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_SchemeHartogs
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open MvPolynomial
open scoped Pointwise
variable (K : Type) [Field K]

lemma variable_pow_dvd_iff {σ : Type} [DecidableEq σ]
    (i : σ) (m : ℕ) (p : MvPolynomial σ K) :
    X i ^ m ∣ p ↔ ∀ d : σ →₀ ℕ, d i < m → p.coeff d = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have he : ¬ Finsupp.single i m ≤ d := by
      simpa only [Finsupp.single_le_iff] using (not_le.mpr hd)
    simp only [← MvPolynomial.coeff_modMonomial_of_not_le p he, h,
      MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · intro h
    ext d
    by_cases hd : Finsupp.single i m ≤ d
    · simp [MvPolynomial.coeff_modMonomial_of_le p hd]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le p hd, MvPolynomial.coeff_zero]
      exact h d (by simpa only [Finsupp.single_le_iff, not_le] using hd)

lemma power_variable_dvd_other_mul {σ : Type} [DecidableEq σ]
    (i j : σ) (hij : i ≠ j) (m n : ℕ) (p : MvPolynomial σ K)
    (hp : X i ^ m ∣ X j ^ n * p) : X i ^ m ∣ p := by
  rw [variable_pow_dvd_iff] at hp ⊢
  intro d hd
  have h := hp (Finsupp.single j n + d) (by simpa [Finsupp.single_eq_of_ne hij] using hd)
  rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul] at h
  exact h

lemma mem_smul_top_iff_dvd {A : Type*} [CommRing A] (x a : A) :
    a ∈ x • (⊤ : Submodule A A) ↔ x ∣ a := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    smul_eq_mul, dvd_def, eq_comm]

lemma polynomial_power_sequence {σ : Type} [DecidableEq σ] (i j : σ)
    (hij : i ≠ j) (m n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) [(X i : MvPolynomial σ K) ^ m, X j ^ n] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨(isRegular_iff_ne_zero.mpr (pow_ne_zero m (X_ne_zero i))).isSMulRegular, ?_,
    RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  rw [mem_smul_top_iff_dvd] at hp ⊢
  exact power_variable_dvd_other_mul K i j hij m n p hp

lemma flat_power_sequence {A : Type*} [CommRing A]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    (m n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular A
      [(algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m,
       (algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n] := by
  simpa using (polynomial_power_sequence K (0 : Fin 2) 1 (by decide) m n).of_flat (S := A)

lemma flat_cancel_other_coordinate {A : Type*} [CommRing A]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    (m n : ℕ) (a : A)
    (h : (algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m ∣
      (algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n * a) :
    (algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m ∣ a := by
  have hs := flat_power_sequence K (A := A) m n
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff] at hs
  have ht := (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hs.2.1 a
  simpa only [mem_smul_top_iff_dvd, smul_eq_mul] using ht (by
    simpa only [mem_smul_top_iff_dvd, smul_eq_mul] using h)

theorem flat_hartogs {A F : Type*} [CommRing A] [IsDomain A] [Field F]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    [Algebra A F] [IsFractionRing A F] (z : F)
    (hx : ∃ m : ℕ, ∃ a : A,
      algebraMap A F ((algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m) * z = algebraMap A F a)
    (hy : ∃ n : ℕ, ∃ b : A,
      algebraMap A F ((algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n) * z = algebraMap A F b) :
    ∃ c : A, algebraMap A F c = z := by
  obtain ⟨m, a, ha⟩ := hx
  obtain ⟨n, b, hb⟩ := hy
  let x : A := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y : A := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have hc : y^n * a = x^m * b := by
    apply IsFractionRing.injective A F
    simp only [map_mul]
    change algebraMap A F (y^n) * algebraMap A F a =
      algebraMap A F (x^m) * algebraMap A F b
    rw [← ha, ← hb]
    ring
  obtain ⟨c, hc⟩ := flat_cancel_other_coordinate K m n a ⟨b, hc⟩
  refine ⟨c, ?_⟩
  have hx0 : x ≠ 0 := by
    have hr := (flat_power_sequence K (A := A) 1 0)
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hr
    have hi := hr.1
    simp only [pow_one] at hi
    intro hx0
    have he : x • (1 : A) = x • (0 : A) := by simp [hx0]
    exact one_ne_zero (hi he)
  have hxF : algebraMap A F (x^m) ≠ 0 :=
    fun h => pow_ne_zero m hx0 ((IsFractionRing.injective A F) (by simpa using h))
  apply mul_left_cancel₀ hxF
  rw [← map_mul, ← hc]
  exact ha.symm

end
end MaximalSeshadri.Hartogs

namespace MaximalSeshadri.Hartogs
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (K : Type) [Field K] (X : Scheme) [IsIntegral X] [IsAffine X]

omit [IsAffine X] in
lemma functionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : U ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map (homOfLE h).op s) =
      X.germToFunctionField V s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

omit [IsAffine X] in
lemma basicOpen_nonempty (x : Γ(X, ⊤)) (hx : x ≠ 0) : Nonempty (X.basicOpen x) := by
  by_contra h
  exact hx ((basicOpen_eq_bot_iff x).mp ((Opens.not_nonempty_iff_eq_bot _).mp (fun ⟨p, hp⟩ => h ⟨⟨p, hp⟩⟩)))

attribute [local instance] OAI.MaximalSeshadri.Hartogs.instNonemptyCarrierCarrierCommRingCatToSchemeTopOpens_solutions
lemma coordinate_denominator {U : X.Opens} [Nonempty U] (s : Γ(X, U))
    (x : Γ(X, ⊤)) (hx : x ≠ 0) (h : X.basicOpen x ≤ U) :
    ∃ m : ℕ, ∃ a : Γ(X, ⊤),
      algebraMap Γ(X, ⊤) X.functionField (x^m) * X.germToFunctionField U s =
        algebraMap Γ(X, ⊤) X.functionField a := by
  let := basicOpen_nonempty X x hx
  let t : Γ(X, X.basicOpen x) := X.presheaf.map (homOfLE h).op s
  let q := IsLocalization.Away.sec x t
  refine ⟨q.2, q.1, ?_⟩
  have he := congrArg (X.germToFunctionField (X.basicOpen x))
    (IsLocalization.Away.sec_spec x t)
  change (X.germToFunctionField (X.basicOpen x)).hom
      (t * algebraMap Γ(X, ⊤) Γ(X, X.basicOpen x) (x^q.2)) =
    (X.germToFunctionField (X.basicOpen x)).hom
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen x) q.1) at he
  rw [map_mul] at he
  change X.germToFunctionField (X.basicOpen x) t *
      X.germToFunctionField (X.basicOpen x)
        (X.presheaf.map (homOfLE (X.basicOpen_le x)).op (x^q.2)) =
    X.germToFunctionField (X.basicOpen x)
      (X.presheaf.map (homOfLE (X.basicOpen_le x)).op q.1) at he
  rw [functionField_restrict, functionField_restrict] at he
  dsimp only [t] at he
  rw [functionField_restrict] at he
  exact (mul_comm _ _).trans he

theorem affine_hartogs
    [Algebra (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    [Module.Flat (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    (U : X.Opens)
    (h0 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 0)) ≤ U)
    (h1 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 1)) ≤ U) (s : Γ(X, U)) :
    ∃! t : Γ(X, ⊤), X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op t = s := by
  let x : Γ(X, ⊤) := algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤) (MvPolynomial.X 0)
  let y : Γ(X, ⊤) := algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤) (MvPolynomial.X 1)
  have hreg := flat_power_sequence K (A := Γ(X, ⊤)) 1 1
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
  have hx : x ≠ 0 := by
    intro he
    have hi := hreg.1
    simp only [pow_one] at hi
    apply one_ne_zero (hi (a₁ := (1 : Γ(X, ⊤))) (a₂ := 0) ?_)
    change x * 1 = x * 0
    simp [he]
  have hy : y ≠ 0 := by
    have hs := (polynomial_power_sequence K (1 : Fin 2) 0 (by decide) 1 1).of_flat
      (S := Γ(X, ⊤))
    simp only [List.map_cons, List.map_nil] at hs
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hs
    have hi := hs.1
    simp only [pow_one] at hi
    intro he
    apply one_ne_zero (hi (a₁ := (1 : Γ(X, ⊤))) (a₂ := 0) ?_)
    change y * 1 = y * 0
    simp [he]
  let : Nonempty U := (basicOpen_nonempty X x hx).map fun p => ⟨p.1, h0 p.2⟩
  let := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  obtain ⟨t, ht⟩ := flat_hartogs K (X.germToFunctionField U s)
    (coordinate_denominator X s x hx h0) (coordinate_denominator X s y hy h1)
  refine ⟨t, ?_, ?_⟩
  · apply X.germToFunctionField_injective U
    rw [functionField_restrict]
    exact ht
  · intro t' ht'
    apply X.germToFunctionField_injective ⊤
    change algebraMap Γ(X, ⊤) X.functionField t' =
      algebraMap Γ(X, ⊤) X.functionField t
    rw [ht]
    rw [← ht', functionField_restrict]
    rfl

end
end MaximalSeshadri.Hartogs

namespace MaximalSeshadri.Hartogs
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X B U : Scheme.{0}}

lemma open_appTop_injective [IsIntegral X] [Nonempty U]
    (j : U ⟶ X) [IsOpenImmersion j] : Function.Injective j.appTop := by
  let : Nonempty (j.opensRange ⊓ ⊤ : X.Opens) :=
    Nonempty.map (fun u : U => ⟨j u, ⟨⟨u, rfl⟩, trivial⟩⟩) inferInstance
  intro a b h
  apply map_injective_of_isIntegral X (homOfLE (show j.opensRange ⊓ ⊤ ≤ ⊤ from le_top))
  have he := congrArg (IsOpenImmersion.ΓIso j ⊤).hom h
  change (j.app ⊤ ≫ (IsOpenImmersion.ΓIso j ⊤).hom) a =
    (j.app ⊤ ≫ (IsOpenImmersion.ΓIso j ⊤).hom) b at he
  rwa [IsOpenImmersion.app_ΓIso_hom] at he

lemma restrict_topIso (V : X.Opens) :
    V.ι.appTop ≫ V.topIso.hom = X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  exact (X.presheaf.map_comp (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op
    (eqToHom V.ι_image_top.symm).op).symm

theorem blowup_descend (K : Type) [Field K] [IsIntegral X] [IsAffine X] [IsIntegral B]
    [Algebra (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    [Module.Flat (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    {I : X.IdealSheafData} {π : B ⟶ X} (hπ : Geometry.IsBlowup I π)
    (hI : I.support ≠ ⊤)
    (h0 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 0)) ≤ Geometry.centreComplement I)
    (h1 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 1)) ≤ Geometry.centreComplement I)
    (s : Γ(B, ⊤)) : ∃! a : Γ(X, ⊤), π.appTop a = s := by
  let V := Geometry.centreComplement I
  let : Nonempty V.toScheme := Geometry.complement_nonempty hI
  let t : Γ(X, V) := V.topIso.hom (hπ.complementLift.appTop s)
  obtain ⟨a, ha, huniq⟩ := affine_hartogs K X V h0 h1 t
  have hae : π.appTop a = s := by
    apply open_appTop_injective hπ.complementLift
    apply (ConcreteCategory.bijective_of_isIso V.topIso.hom).injective
    change (π.appTop ≫ hπ.complementLift.appTop ≫ V.topIso.hom) a = t
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, Geometry.IsBlowup.complementLift_comp,
      restrict_topIso]
    exact ha
  refine ⟨a, hae, fun b hb => ?_⟩
  apply huniq b
  change (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) b = t
  rw [← restrict_topIso]
  rw [← Geometry.IsBlowup.complementLift_comp hπ, Scheme.Hom.comp_appTop]
  change V.topIso.hom (hπ.complementLift.appTop (π.appTop b)) = t
  rw [hb]

end
end MaximalSeshadri.Hartogs

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupSectionDescent
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma IsBlowup.dominant {X B : Scheme.{0}} [IsIntegral X]
    {I : X.IdealSheafData} {π : B ⟶ X} (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    IsDominant π := by
  have hd : Dense (centreComplement I : Set X) :=
    (centreComplement I).isOpen.dense (by
      obtain ⟨x⟩ := complement_nonempty hI
      exact ⟨x.val,x.property⟩)
  let : IsDominant (centreComplement I).ι := Opens.isDominant_ι hd
  let : IsDominant (hπ.complementLift ≫ π) := by rw [hπ.complementLift_comp]; infer_instance
  exact IsDominant.of_comp hπ.complementLift π

lemma Surface.blowup_chart_app_surjective (S : Surface) {r : ℕ} (p : Configuration S r)
    {B : Scheme.{0}} [IsIntegral B] {π : B ⟶ S.scheme}
    (hπ : IsBlowup (centreIdeal S r p) π)
    (U : S.scheme.affineOpens) [Nonempty U.1]
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ht : ∀ i, S.scheme.basicOpen (t i) ≤ centreComplement (centreIdeal S r p)) :
    Function.Surjective (π.app U.1) := by
  let X := U.1.toScheme
  let φ : MvPolynomial (Fin 2) ℂ →+* Γ(X,⊤) :=
    U.1.topIso.inv.hom.comp (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t)
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) :=
    RingHom.Etale.respectsIso.1 _ U.1.topIso.symm.commRingCatIsoToRingEquiv het
  let : Module.Flat (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) := inferInstance
  have hI := support_comap_ne_top_of_open (centreIdeal S r p)
    (S.centre_support_ne_top r p) U.1.ι
  let : Nonempty (π ⁻¹ᵁ U.1).toScheme := (hπ.morphismRestrict U.1).nonempty_of_support_ne_top hI
  have hb (i : Fin 2) : X.basicOpen (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(X,⊤) (MvPolynomial.X i)) ≤
      centreComplement ((centreIdeal S r p).comap U.1.ι) := by
    intro y hy hyc
    have hy' : U.1.ι y ∈ S.scheme.basicOpen (t i) := by
      rw [← U.1.ι_image_basicOpen_topIso_inv]
      refine ⟨y,?_,rfl⟩
      change y ∈ U.1.toScheme.basicOpen (U.1.topIso.inv
        ((MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t) (MvPolynomial.X i))) at hy
      change y ∈ U.1.toScheme.basicOpen (U.1.topIso.inv (t i))
      simpa only [MvPolynomial.eval₂Hom_X'] using hy
    rw [Scheme.IdealSheafData.support_comap] at hyc
    exact ht i hy' hyc
  intro s
  obtain ⟨a,ha,-⟩ := MaximalSeshadri.Hartogs.blowup_descend ℂ
    (hπ.morphismRestrict U.1) hI (hb 0) (hb 1) ((π ⁻¹ᵁ U.1).topIso.inv s)
  refine ⟨U.1.topIso.hom a,?_⟩
  apply (ConcreteCategory.bijective_of_isIso (π ⁻¹ᵁ U.1).topIso.inv).injective
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at ha
  simpa only [Scheme.Hom.appLE_eq_app,CommRingCat.comp_apply] using ha

theorem Surface.blowup_structureMap_isIso_s01_oai (S : Surface) {r : ℕ} (p : Configuration S r)
    {B : Scheme.{0}} [IsIntegral B] {π : B ⟶ S.scheme} [QuasiCompact π]
    (hπ : IsBlowup (centreIdeal S r p) π) :
    IsIso (IdealModule.structureMap π) := by
  let : IsDominant π := hπ.dominant (S.centre_support_ne_top r p)
  let : IsSchemeTheoreticallyDominant π := .of_isDominant π
  have hm : Mono (IdealModule.structureMap π).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact π.app_injective U.unop
  let : Mono (IdealModule.structureMap π) :=
    (SheafOfModules.forget S.scheme.ringCatSheaf).mono_of_mono_map hm
  let F := SheafOfModules.toSheaf S.scheme.ringCatSheaf
  have hl : TopCat.Presheaf.IsLocallySurjective (F.map (IdealModule.structureMap π)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U s x hx
    obtain ⟨V,hxV,hVU,t,het,ht⟩ := S.hartogs_chart p U x hx
    let : Nonempty V.1 := ⟨⟨x,hxV⟩⟩
    obtain ⟨a,ha⟩ := S.blowup_chart_app_surjective p hπ V t het ht
      (((F.obj ((Scheme.Modules.pushforward π).obj (IdealModule.unit B))).obj.map
        (homOfLE hVU).op) s)
    exact ⟨V.1,hVU,⟨a,ha⟩,hxV⟩
  let : Epi (F.map (IdealModule.structureMap π)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hl
  let : Epi (IdealModule.structureMap π) := F.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso_s01_oai
