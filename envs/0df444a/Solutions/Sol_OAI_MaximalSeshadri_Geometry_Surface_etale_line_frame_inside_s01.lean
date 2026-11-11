-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:52.141466+00:00
-- url     : https://prove2.me/submissions/fd4a65c2-d597-47e7-a2ba-fdc388046422

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES006
import Definitions.Def_Q223SES007

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end

noncomputable section
open KaehlerDifferential
universe u v w
variable {R : Type u} {S : Type v} {ι : Type w}
  [CommRing R] [CommRing S] [Algebra R S]

lemma differentials_span_of_generators (v : ι → S)
    (hv : Function.Surjective (MvPolynomial.aeval (R := R) v)) :
    Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation R S, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  obtain ⟨q, rfl⟩ := hv s
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, Derivation.map_algebraMap]
      exact Submodule.zero_mem _
  | add f g hf hg =>
      simp only [map_add]
      exact Submodule.add_mem _ hf hg
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
        (Submodule.smul_mem _ _ hf)

theorem exists_local_differential_basis [Algebra.Smooth R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ g : S, g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι)
      (b : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap S (Localization.Away g) (v (a i))) := by
  let w : ι → Ω[Localization.AtPrime p⁄R] :=
    fun i => map R R S (Localization.AtPrime p) (D R S (v i))
  have hw : Submodule.span (Localization.AtPrime p) (Set.range w) = ⊤ := by
    have hh := span_eq_top_of_isLocalizedModule (Localization.AtPrime p) p.primeCompl
      (map R R S (Localization.AtPrime p)) hv
    simpa only [← Set.range_comp, Function.comp_def, w] using hh
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat w hw
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ => D R S (v (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p]
      Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have he : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, w]
  have heₚ : Function.Bijective eₚ := he ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] := map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ : (κ →₀ Localization.Away g) →ₗ[Localization.Away g]
      Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, κ, inferInstance, a, .ofRepr (LinearEquiv.ofBijective eₜ h).symm, ?_⟩
  intro i
  change eₜ (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e (l₁ₜ (Finsupp.single i 1))
  · simp [eₜ, -IsLocalizedModule.map_apply, l₁ₜ]
  · simp [l₂ₜ, e]

theorem coordinate_map_etale [Algebra.Smooth R S] [Finite ι]
    (v : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (v i)) :
    (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R) v
  let : Algebra (MvPolynomial ι R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation (MvPolynomial ι R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ι R) S :=
    formallyEtale_polynomial_of_basis b (by
      intro i
      change b i = D R S (φ (MvPolynomial.X i))
      simpa only [φ, MvPolynomial.aeval_X] using hb i)
  change Algebra.Etale (MvPolynomial ι R) S
  constructor <;> infer_instance

theorem exists_local_etale_from_spanning (n : ℕ)
    [IsDomain S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S), g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι),
      Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap S (Localization.Away g) (v (a i)))).toRingHom.Etale := by
  let : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨g, hg, κ, hκ, a, b, hb⟩ := exists_local_differential_basis v hv p
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem p)
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 S (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
  let : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    simpa using (Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := S)
      (T := Localization.Away g) (n := n) (m := 0))
  let : Algebra.IsStandardSmooth R (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine ⟨g, hg, κ, hκ, a, ?_, coordinate_map_etale _ b hb⟩
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away g) n
  rw [rank_eq_card_basis b] at hr
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hr

end

noncomputable section
open KaehlerDifferential TensorProduct
variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma differentials_span_of_formallyEtale [Algebra.FormallyEtale S T]
    (v : ι → S) (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤) :
    Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i)))) = ⊤ := by
  let M := Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i))))
  have hmem (s : Ω[S⁄R]) : map R R S T s ∈ M := by
    have hh : Submodule.span S (Set.range (fun i => D R S (v i))) ≤
        (M.restrictScalars S).comap (map R R S T) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change map R R S T (D R S (v i)) ∈ M
      rw [map_D]
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [hv] at hh
    exact hh (Submodule.mem_top)
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨z, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale R S T).surjective x
  induction z using OAI.tensorInductionOn with
  | tmul t s =>
      rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
      exact M.smul_mem t (hmem s)
  | add x y hx hy =>
      rw [map_add]
      exact M.add_mem hx hy

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

end

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma spec_openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars g U.1)) = U.2.fromSpec ≫ g := by
  rw [openScalars, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom]
  rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) U.2 _

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
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in
                                                                            
lemma projective_affine_constants {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (g : Y ⟶ Spec (CommRingCat.of R)) (hbase : h ≫ projectiveToSpec = g)
    (U : Y.affineOpens) [Algebra R Γ(Y, U.1)]
    (hOver : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))) = U.2.fromSpec ≫ g)
    (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h) :
    ∀ c, φ (chartConstants i c) = algebraMap R Γ(Y, U.1) c := by
  have he : CommRingCat.ofHom (φ.comp (chartConstants i)) =
      CommRingCat.ofHom (algebraMap R Γ(Y, U.1)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← chart_toSpec,
      ← Category.assoc, hφ, Category.assoc, hbase, hOver]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he)

end
end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma affine_restriction_etale (U V : X.affineOpens) (e : U.1 ≤ V.1) :
    (X.presheaf.map (homOfLE e).op).hom.Etale := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  have he := hV.map_fromSpec hU (homOfLE e).op
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op) ≫ hV.fromSpec) := by
    rw [he]
    infer_instance
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op)) :=
    IsOpenImmersion.of_comp _ hV.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance

lemma awayToSection_awayι (i : σ) :
    Spec.map (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
      (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)).fromSpec := by
  let hV := Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  rw [← cancel_epi hV.isoSpec.hom, ← Category.assoc, hV.isoSpec_hom]
  change Proj.basicOpenToSpec _ _ ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom _ _ (poly_X_mem i) (by decide),
    Proj.awayι, Iso.hom_inv_id_assoc]
  exact hV.toSpecΓ_fromSpec.symm

theorem closed_projective_affine_surjective (h : X ⟶ Proj (PolyGrade K σ))
    [IsClosedImmersion h] (i : σ) :
    ∃ (U : X.affineOpens) (φ : PolyChart (R := K) i →+* Γ(X, U.1)),
      U.1 = h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ∧
      Function.Surjective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
          U.2.fromSpec ≫ h := by
  let V := Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  have hV : IsAffineOpen V := Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)
  let U : X.affineOpens := ⟨h ⁻¹ᵁ V, hV.preimage h⟩
  let e := Proj.basicOpenIsoAway (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) := (h.app V).hom.comp e.hom.hom
  refine ⟨U, φ, rfl, ?_, ?_⟩
  · exact (h.app_surjective V hV).comp (ConcreteCategory.bijective_of_isIso e.hom).surjective
  · change Spec.map (e.hom ≫ h.app V) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have he : e.hom = Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) := rfl
    rw [he, awayToSection_awayι]
    rw [Scheme.Hom.app_eq_appLE]
    exact hV.SpecMap_appLE_fromSpec h U.2 le_rfl

open KaehlerDifferential MaximalSeshadri.AlgebraicJets

lemma differentials_span_projective_chart {A : Type} [CommRing A] [Algebra K A]
    (i : σ) (φ : PolyChart (R := K) i →+* A) (hφ : Function.Surjective φ)
    (hconst : ∀ c, φ (chartConstants i c) = algebraMap K A c) :
    Submodule.span A (Set.range (fun j : ChartVariables i =>
      D K A (-φ (chartCoordinate i j.1)))) = ⊤ := by
  have he : (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))).toRingHom =
      φ.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval _ (MvPolynomial.C c) = φ (polyToChart i (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
      simpa only [polyToChart, MvPolynomial.eval₂Hom_C] using (hconst c).symm
    · intro j
      change MvPolynomial.aeval _ (MvPolynomial.X j) = φ (polyToChart i (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, polyToChart, MvPolynomial.eval₂Hom_X']
  have hp : Function.Surjective (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))) := by
    change Function.Surjective (MvPolynomial.aeval _).toRingHom
    rw [he]
    exact hφ.comp (polynomialChartEquiv (R := K) i).symm.surjective
  have hs := differentials_span_of_generators _ hp
  have hr : Set.range (fun j : ChartVariables i => D K A (-φ (chartCoordinate i j.1))) =
      -(Set.range (fun j : ChartVariables i => D K A (φ (chartCoordinate i j.1)))) := by
    ext x
    simp only [Set.mem_range, Set.mem_neg, map_neg, neg_eq_iff_eq_neg]
  rw [hr, Submodule.span_neg]
  exact hs

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma restrict_projective_factor (h : X ⟶ Proj (PolyGrade K σ))
    (U V : X.affineOpens) (e : U.1 ≤ V.1) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom ((X.presheaf.map (homOfLE e).op).hom.comp φ)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ, ← Category.assoc,
    CommRingCat.ofHom_hom, V.2.map_fromSpec U.2]

lemma etale_aeval_equiv {A B ι : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (v : ι → A)
    (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := K) (fun i => e (v i))).toRingHom.Etale := by
  have hh := RingHom.Etale.respectsIso.1 _ e.toRingEquiv hv
  change (e.toAlgHom.comp (MvPolynomial.aeval (R := K) v)).toRingHom.Etale at hh
  rw [MvPolynomial.comp_aeval] at hh
  exact hh

theorem exists_etale_projective_chart [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (hxi : h x ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
  obtain ⟨V, φ, hV, hsurj, hφ⟩ := closed_projective_affine_surjective h i
  have hxV : x ∈ V.1 := by rwa [hV]
  obtain ⟨U, hxU, hUW, hstd⟩ := exists_standard_smooth_affine_inside g 2
    (W ⊓ V.1) x ⟨hxW, hxV⟩
  have e : U.1 ≤ V.1 := hUW.trans inf_le_right
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let : Algebra K Γ(X, V.1) := (openScalars g V.1).toAlgebra
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let r : Γ(X, V.1) →+* Γ(X, U.1) := (X.presheaf.map (homOfLE e).op).hom
  let : Algebra Γ(X, V.1) Γ(X, U.1) := r.toAlgebra
  let : IsScalarTower K Γ(X, V.1) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g e).symm
  let : Algebra.Etale Γ(X, V.1) Γ(X, U.1) := affine_restriction_etale U V e
  have hconst := projective_affine_constants h g hbase V (spec_openScalars g V) i φ hφ
  have hspan := differentials_span_projective_chart i φ hsurj hconst
  have hs := differentials_span_of_formallyEtale (T := Γ(X, U.1))
    (fun j : ChartVariables i => -φ (chartCoordinate i j.1)) hspan
  let φU := r.comp φ
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K Γ(X, U.1) := hstd
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨x, hxU⟩
  obtain ⟨f, hfp, κ, hκ, a, hcard, het⟩ := exists_local_etale_from_spanning 2
    (fun j : ChartVariables i => -φU (chartCoordinate i j.1))
    (by simpa only [φU, RingHom.comp_apply, map_neg, RingHom.algebraMap_toAlgebra] using hs) p.asIdeal
  let T : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  have hxf : x ∈ T.1 := by
    have hp : U.2.fromSpec p = x := by
      change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨x, hxU⟩ = x
      rw [U.2.isoSpec_hom_fromSpec]
      rfl
    have hm : p ∈ PrimeSpectrum.basicOpen f := hfp
    rw [← U.2.fromSpec_preimage_basicOpen f] at hm
    change U.2.fromSpec p ∈ X.basicOpen f at hm
    rwa [hp] at hm
  let r' : Γ(X, U.1) →+* Γ(X, T.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra K Γ(X, T.1) := (openScalars g T.1).toAlgebra
  let : IsScalarTower K Γ(X, U.1) Γ(X, T.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g (X.basicOpen_le f)).symm
  let : IsLocalization.Away f Γ(X, T.1) := U.2.isLocalization_basicOpen f
  let ρ := (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, T.1)).restrictScalars K
  have het' := etale_aeval_equiv ρ _ het
  let φT := r'.comp φU
  have hφU := restrict_projective_factor h U V e i φ hφ
  refine ⟨{ U := T
            coord := i
            nonempty := ⟨⟨x, hxf⟩⟩
            φ := φT
            factor := restrict_projective_factor h T U (X.basicOpen_le f) i φU hφU
            κ := κ
            finite := hκ
            a := a
            card := hcard
            etale := ?_ }, hxf,
      (X.basicOpen_le f).trans (hUW.trans inf_le_left), rfl⟩
  convert het' using 1
  all_goals try with_reducible_and_instances rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) =
      MvPolynomial.aeval _ (MvPolynomial.C c)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
    rfl
  · intro k
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X k) =
      MvPolynomial.aeval _ (MvPolynomial.X k)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
    change -r' (φU (chartCoordinate i (a k).1)) =
      ρ (algebraMap Γ(X, U.1) (Localization.Away f) (-φU (chartCoordinate i (a k).1)))
    rw [← map_neg]
    exact ((IsLocalization.algEquiv (Submonoid.powers f)
      (Localization.Away f) Γ(X, T.1)).commutes
      (-φU (chartCoordinate i (a k).1))).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FiniteAtlas
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma projective_standard_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

 theorem exists_etale_projective_neighborhood [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (W : X.Opens) (x : X) (hxW : x ∈ W) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
  have hx : h x ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
    rw [projective_standard_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨C, hxC, hCW, _⟩ := exists_etale_projective_chart g h hbase i W x hxW hi
  exact ⟨C, hxC, hCW⟩

end

end MaximalSeshadri.ProjectiveBertini

end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_EtaleLineFrame
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

lemma Surface.etale_line_frame_inside_s01_oai (S : Surface) (J : LineBundle S.scheme)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ _ : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        ∃ t : Fin 2 → Γ(S.scheme,U.1),
          (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale := by
  classical
  obtain ⟨V,hV,⟨e⟩⟩ := J.locallyRankOne x
  obtain ⟨C,hxC,hC⟩ := @exists_etale_projective_neighborhood ℂ _ S.scheme
    (Fin (S.embeddingDimension + 1)) S.integral S.structureMap S.smooth
    S.embedding S.closedImmersion S.overComplex (V ⊓ W) x ⟨hV,hx⟩
  let := C.finite
  let := Fintype.ofFinite C.κ
  let eκ : Fin 2 ≃ C.κ := (Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using C.card)).symm
  let := (openScalars S.structureMap C.U.1).toAlgebra
  let a : C.κ → Γ(S.scheme,C.U.1) := fun k => -C.φ (MaximalSeshadri.Projective.chartCoordinate C.coord (C.a k).1)
  refine ⟨C.U,hxC,hC.trans inf_le_right,frameOnSmaller e C.U.1 (hC.trans inf_le_left),a ∘ eκ,?_⟩
  exact etale_aeval_reindex a C.etale eκ

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01_oai
