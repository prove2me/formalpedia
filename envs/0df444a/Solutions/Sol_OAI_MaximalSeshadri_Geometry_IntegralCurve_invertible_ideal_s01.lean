-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:07.259351+00:00
-- url     : https://prove2.me/submissions/7f9f4cfa-e7bd-4a02-8c7b-b73b4853c88c

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES004

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothSurfaceDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_IntegralCurveIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.affine_ideal_prime (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    (C.embedding.ker.ideal U).IsPrime := by
  have := hne
  rw [Scheme.Hom.ker_apply]
  exact RingHom.ker_isPrime _

lemma IntegralCurve.affine_ideal_not_maximal (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    ¬ (C.embedding.ker.ideal U).IsMaximal := by
  intro hmax
  have := hmax
  have : Smooth S.structureMap := SmoothOfRelativeDimension.smooth 2 S.structureMap
  have : JacobsonSpace C.scheme := LocallyOfFiniteType.jacobsonSpace
    (C.embedding ≫ S.structureMap)
  let I := C.embedding.ker.ideal U
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he : (Set.range C.embedding) ∩ (U.1 : Set S.scheme) =
      {U.2.fromSpec ⟨I,inferInstance⟩} := by
    rw [← hr,C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.image_singleton
  obtain ⟨x,hx⟩ := hne
  have hxq : C.embedding x = U.2.fromSpec ⟨I,inferInstance⟩ :=
    Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self x,hx⟩)
  have hs : (C.embedding ⁻¹ᵁ U.1 : Set C.scheme) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply C.embedding.isEmbedding.injective
      exact (Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self y,hy⟩)).trans hxq.symm
    · rintro rfl
      exact hx
  have ho : IsOpen ({x} : Set C.scheme) := hs ▸ (C.embedding ⁻¹ᵁ U.1).isOpen
  have hc : IsClosed ({x} : Set C.scheme) :=
    isClosed_singleton_of_isLocallyClosed_singleton ho.isLocallyClosed
  have hu : ({x} : Set C.scheme) = Set.univ := by
    rw [← hc.closure_eq]
    exact (ho.dense (Set.singleton_nonempty x)).closure_eq
  have : Subsingleton C.scheme := ⟨fun y z => by
    have hy : y = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ y)
    have hz : z = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ z)
    exact hy.trans hz.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dimension] at hd
  norm_num at hd

lemma IntegralCurve.affine_ideal_ne_bot (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    C.embedding.ker.ideal U ≠ ⊥ := by
  intro hzero
  have affineOpen : IsAffineOpen U.1 := U.2
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he := C.embedding.ker.coe_support_inter U
  rw [hr,← affineOpen.fromSpec_image_zeroLocus,hzero,PrimeSpectrum.zeroLocus_bot] at he
  change Set.range C.embedding ∩ (U.1 : Set S.scheme) =
    affineOpen.fromSpec '' (Set.univ : Set (Spec Γ(S.scheme, U.1))) at he
  rw [Set.image_univ,affineOpen.range_fromSpec] at he
  have hsub : (U.1 : Set S.scheme) ⊆ Set.range C.embedding := fun x hx =>
    (he.symm ▸ hx).1
  obtain ⟨x,hx⟩ := hne
  have hd := U.1.isOpen.dense ⟨C.embedding x,hx⟩
  have hall : Set.range C.embedding = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact closure_minimal hsub C.embedding.isClosedEmbedding.isClosed_range
  have hh : IsHomeomorph C.embedding := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨C.embedding.isEmbedding,Set.range_eq_univ.mp hall⟩
  have heq := hh.topologicalKrullDim_eq C.embedding
  have hdS := S.two_le_dimension
  rw [← heq,C.dimension] at hdS
  norm_num at hdS

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalCurvePrincipal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem principal_of_principal_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (hm : (maximalIdeal R).IsPrincipal) : IsPrincipalIdealRing R := by
  classical
  obtain ⟨t,ht⟩ := hm
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    infer_instance
  have hex : ∃ n : ℕ, ¬ I ≤ maximalIdeal R ^ (n+1) := by
    by_contra! H
    apply hI
    apply le_antisymm
    · rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top]
      apply le_iInf
      rintro (_ | n)
      · simp
      · exact H n
    · exact bot_le
  let n := Nat.find hex
  have hle : I ≤ maximalIdeal R ^ n := by
    cases hn : n with
    | zero => simp
    | succ j =>
      have hj : j < Nat.find hex := by change j < n; omega
      exact not_not.mp (Nat.find_min hex hj)
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp (Nat.find_spec hex)
  have hat : t^n ∣ a := by
    have H := hle ha
    rw [ht,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at H
    exact H
  obtain ⟨b,hb⟩ := hat
  have hbu : IsUnit b := by
    by_contra h
    have hbmem : b ∈ maximalIdeal R := h
    apply han
    change a ∉ maximalIdeal R ^ (n+1) at han
    have htn : t^n ∈ maximalIdeal R^n := by
      exact Ideal.pow_mem_pow (by rw [ht]; exact Ideal.subset_span (by simp)) n
    rw [hb]
    exact Ideal.mul_mem_mul htn hbmem
  have he : I = maximalIdeal R^n := by
    apply le_antisymm hle
    rw [ht,Ideal.span_singleton_pow,Ideal.span_le,Set.singleton_subset_iff]
    obtain ⟨u,hu⟩ := hbu
    have H := I.mul_mem_left (↑(u⁻¹) : R) ha
    rw [hb,← hu] at H
    simpa [mul_left_comm,mul_comm,mul_assoc] using H
  rw [he,ht,Ideal.span_singleton_pow]
  infer_instance

end
end MaximalSeshadri.LocalCurve

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalBinaryPrime
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem prime_principal_of_binary_maximal_of_not_mem {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (ha : a ∉ p) : p.IsPrincipal := by
  classical
  let J : Ideal R := Ideal.span {a}
  have hJm : J ≤ maximalIdeal R := by
    rw [hm]
    exact Ideal.span_mono (by simp)
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let q := Ideal.Quotient.mk J
  let : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hmQ : maximalIdeal (R ⧸ J) = Ideal.span {q b} := by
    rw [← map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,hm,Ideal.map_span]
    have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp only [Set.image_insert_eq,Set.image_singleton,hqa,Ideal.span_insert_zero]
  let : IsPrincipalIdealRing (R ⧸ J) := principal_of_principal_maximal ⟨q b,hmQ⟩
  obtain ⟨c₀,hc₀⟩ := (inferInstance : (p.map q).IsPrincipal)
  change p.map q = Ideal.span {c₀} at hc₀
  have hc₀mem : c₀ ∈ p.map q := by rw [hc₀]; exact Ideal.subset_span (by simp)
  obtain ⟨c,hcp,hc⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hc₀mem
  have hp_le : p ≤ Ideal.span {c} ⊔ J • p := by
    intro z hz
    have hzq : q z ∈ Ideal.span {c₀} := by
      rw [← hc₀]
      exact Ideal.mem_map_of_mem q hz
    obtain ⟨w₀,hw₀⟩ := Ideal.mem_span_singleton.mp hzq
    obtain ⟨w,hw⟩ := Ideal.Quotient.mk_surjective w₀
    have hdiff : z-c*w ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (z-c*w) = 0
      rw [map_sub,map_mul,hc,hw,hw₀,sub_self]
    obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp hdiff
    have hat : a*t ∈ p := ht ▸ p.sub_mem hz (p.mul_mem_right w hcp)
    have htp : t ∈ p := (hp.mem_or_mem hat).resolve_left ha
    have hleft : c*w ∈ Ideal.span {c} := Ideal.mem_span_singleton.mpr ⟨w,rfl⟩
    have hright : a*t ∈ J • p := by
      exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) htp
    have H := Submodule.add_mem_sup hleft hright
    have he : c*w+a*t = z := by linear_combination -ht
    exact he ▸ H
  have hple : p ≤ Ideal.span {c} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian p) (by rw [jacobson_eq_maximalIdeal _ bot_ne_top]; exact hJm) hp_le
  exact ⟨c,le_antisymm hple (Ideal.span_le.mpr (by simpa using hcp))⟩

theorem prime_principal_of_binary_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (hne : p ≠ maximalIdeal R) : p.IsPrincipal := by
  by_cases ha : a ∈ p
  · have hb : b ∉ p := by
      intro hb
      apply hne
      apply le_antisymm (le_maximalIdeal hp.ne_top)
      rw [hm,Ideal.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
      exact ⟨ha,hb⟩
    exact prime_principal_of_binary_maximal_of_not_mem b a
      (hm.trans Ideal.span_pair_comm) p hb
  · exact prime_principal_of_binary_maximal_of_not_mem a b hm p ha
end
end MaximalSeshadri.LocalCurve

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_SmoothCurvePrincipal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing MvPolynomial
open MaximalSeshadri.AlgebraicJets

attribute [local instance] OAI.MaximalSeshadri.LocalCurve.residueKernelIsPrime
theorem standard_smooth_binary_maximal {K S : Type} [Field K] [CommRing S] [Algebra K S]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K) :
    ∃ a b : Localization.AtPrime (RingHom.ker ρ),
      maximalIdeal (Localization.AtPrime (RingHom.ker ρ)) = Ideal.span {a,b} := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let q := RingHom.ker ρ
  have hp : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  have H := unramified_map_under_local (R := MvPolynomial (Fin 2) K) q
  rw [hp,IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q),
    Ideal.map_span,← Set.range_comp] at H
  have hr : Set.range ((algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q)) ∘ X) =
      {algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 0),
       algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 1)} := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with h | h
      · exact ⟨0,h.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  rw [hr] at H
  exact ⟨_,_,H.symm⟩

theorem spread_principal_prime {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I q : Ideal S) [I.IsPrime] [q.IsPrime]
    (hI : (I.map (algebraMap S (Localization.AtPrime q))).IsPrincipal) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, s ∉ q ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  obtain ⟨u,hu⟩ := hI
  have hum : u ∈ I.map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu]; exact Ideal.subset_span (by simp)
  obtain ⟨⟨c,d⟩,hcd⟩ := (IsLocalization.mem_map_algebraMap_iff q.primeCompl
    (Localization.AtPrime q)).mp hum
  have he : I.map (algebraMap S (Localization.AtPrime q)) =
      (Ideal.span {c.val}).map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu,Ideal.map_span,Set.image_singleton,← hcd,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units (Localization.AtPrime q) d)]
  obtain ⟨s,hs,hseq⟩ := exists_away_map_eq_of_le I (Ideal.span {c.val}) q
    (Ideal.fg_of_isNoetherianRing I) (Ideal.span_le.mpr (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) he
  exact ⟨c.val,c.property,s,hs,by simpa only [Ideal.map_span,Set.image_singleton] using hseq⟩

theorem standard_smooth_prime_principal_neighborhood {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) (I : Ideal S) [hI : I.IsPrime]
    (hle : I ≤ RingHom.ker ρ) (hne : I ≠ RingHom.ker ρ) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, ρ s ≠ 0 ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let q := RingHom.ker ρ
  have hdis : Disjoint (q.primeCompl : Set S) I :=
    Set.disjoint_left.mpr (fun _ hq hi => hq (hle hi))
  let : (I.map (algebraMap S (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) I hI hdis
  obtain ⟨a,b,hm⟩ := standard_smooth_binary_maximal ρ
  have hneq : I.map (algebraMap S (Localization.AtPrime q)) ≠ maximalIdeal (Localization.AtPrime q) := by
    intro H
    apply hne
    have HH := congrArg (Ideal.comap (algebraMap S (Localization.AtPrime q))) H
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)] at HH
    change (I.map _).under S = (q.map _).under S at HH
    rw [IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) hI hdis,
      IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q)
        (inferInstance : q.IsPrime) (Set.disjoint_left.mpr (fun _ hx hy => hx hy))] at HH
    exact HH
  have hp := prime_principal_of_binary_maximal a b hm
    (I.map (algebraMap S (Localization.AtPrime q))) hneq
  obtain ⟨c,hc,s,hs,he⟩ := spread_principal_prime I q hp
  exact ⟨c,hc,s,hs,he⟩
end
end MaximalSeshadri.LocalCurve

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.InvertibleLocal

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry

theorem invertible_of_affine_equations {X : Scheme} (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    InvertiblePullbackIdeal I (𝟙 X) := by
  apply invertible_of_local_equations
  intro x
  obtain ⟨U, hx, r, hr, he⟩ := hI x
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have hreg : IsLeftRegular (e.symm r) := by
    intro a b hab
    apply e.injective
    apply hr.1
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  refine ⟨U, hx, e.symm r, ⟨hreg, hreg.right_of_commute (fun a => mul_comm _ a)⟩, ?_⟩
  rw [Scheme.IdealSheafData.comap_id, IdealPullback.comap_ι_top, he,
    Ideal.map_span, Set.image_singleton]
  rfl

end
end MaximalSeshadri.InvertibleLocal
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_IntegralCurveCartier
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

lemma rational_of_maximal {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    (q : Ideal R) [q.IsMaximal] : ∃ ρ : R →ₐ[K] K, RingHom.ker ρ = q := by
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  let : Module.Finite K (R ⧸ q) := finite_of_finite_type_of_isJacobsonRing K _
  let φ : (R ⧸ q) →ₐ[K] K := IsAlgClosed.lift
  let ρ := φ.comp (Ideal.Quotient.mkₐ K q)
  refine ⟨ρ, ?_⟩
  ext x
  change φ (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  change φ.toRingHom (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  rw [← map_zero φ.toRingHom, φ.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.equation_at_support (S : Surface) (C : IntegralCurve S)
    (x : C.scheme) : ∃ U : S.scheme.affineOpens, C.embedding x ∈ U.1 ∧
      ∃ c : Γ(S.scheme,U.1), IsRegular c ∧ C.embedding.ker.ideal U = Ideal.span {c} := by
  obtain ⟨U,hxU,-,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (C.embedding x) (by trivial)
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨x,hxU⟩⟩
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let I := C.embedding.ker.ideal U
  let : I.IsPrime := C.affine_ideal_prime S U inferInstance
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hxrange : C.embedding x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]; exact hxU
  obtain ⟨p,hp⟩ := hxrange
  have hIp : I ≤ p.asIdeal := by
    have hz : p ∈ PrimeSpectrum.zeroLocus I := by
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hh : C.embedding x ∈ (C.embedding.ker.support : Set S.scheme) ∩ U.1 :=
        ⟨hr ▸ Set.mem_range_self x,hxU⟩
      rw [C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus] at hh
      obtain ⟨p',hp',he⟩ := hh
      have ep : p' = p := U.2.fromSpec.isOpenEmbedding.injective (he.trans hp.symm)
      subst p'
      exact hp'
    exact hz
  obtain ⟨q,hq,hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let := hq
  obtain ⟨ρ,hρ⟩ := LocalCurve.rational_of_maximal (K := ℂ) q
  have hIq : I ≠ RingHom.ker ρ := by
    rw [hρ]
    intro he
    exact C.affine_ideal_not_maximal S U inferInstance (by change I.IsMaximal; rw [he]; exact hq)
  obtain ⟨c,hc,s,hs,he⟩ := LocalCurve.standard_smooth_prime_principal_neighborhood
    ρ I (hρ.symm ▸ hIp.trans hpq) hIq
  let V : S.scheme.affineOpens := ⟨S.scheme.basicOpen s,U.2.basicOpen s⟩
  have hxV : C.embedding x ∈ V.1 := by
    have hz : p ∈ PrimeSpectrum.basicOpen s := fun hh =>
      hs (show s ∈ RingHom.ker ρ from hρ.symm ▸ hpq hh)
    rw [← U.2.fromSpec_preimage_basicOpen] at hz
    change U.2.fromSpec p ∈ S.scheme.basicOpen s at hz
    rwa [hp] at hz
  let : Nonempty (C.embedding ⁻¹ᵁ V.1) := ⟨⟨x,hxV⟩⟩
  let : Nonempty V.1 := ⟨⟨_,hxV⟩⟩
  let : IsLocalization.Away s Γ(S.scheme,V.1) := U.2.isLocalization_basicOpen s
  let e := IsLocalization.algEquiv (Submonoid.powers s)
    (Localization.Away s) Γ(S.scheme,V.1)
  let c' : Γ(S.scheme,V.1) := algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) c
  have he' : C.embedding.ker.ideal V = Ideal.span {c'} := by
    have H := congrArg (Ideal.map e.toRingHom) he
    rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H
    have comp : e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s)) =
        algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) := by
      ext z; exact e.commutes z
    change I.map (e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s))) =
      Ideal.span {e (algebraMap Γ(S.scheme,U.1) (Localization.Away s) c)} at H
    rw [comp,e.commutes] at H
    exact (C.embedding.ker.map_ideal_basicOpen U s).symm.trans H
  have hc' : c' ≠ 0 := by
    intro hz
    have H := C.affine_ideal_ne_bot S V inferInstance
    rw [he',hz,Ideal.span_singleton_zero] at H
    exact H rfl
  exact ⟨V,hxV,c',isRegular_iff_ne_zero.mpr hc',he'⟩

theorem IntegralCurve.invertible_ideal_s01_oai (S : Surface) (C : IntegralCurve S) :
    InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme) := by
  apply InvertibleLocal.invertible_of_affine_equations
  intro x
  by_cases hx : x ∈ Set.range C.embedding
  · obtain ⟨z,rfl⟩ := hx
    exact C.equation_at_support S z
  · let W : S.scheme.Opens := ⟨(Set.range C.embedding)ᶜ,
      C.embedding.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U,hU,hxU,hUW⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W from hx)
    have htop : C.embedding.ker.ideal ⟨U,hU⟩ = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hz : hU.fromSpec p ∈ (C.embedding.ker.support : Set S.scheme) ∩ U := by
        rw [C.embedding.ker.coe_support_inter ⟨U,hU⟩,← hU.fromSpec_image_zeroLocus]
        exact ⟨p,hp,rfl⟩
      exact hUW hz.2 (hr ▸ hz.1)
    exact ⟨⟨U,hU⟩,hxU,1,isRegular_one,by rw [htop,Ideal.span_singleton_one]⟩

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01_oai := @OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01_oai
