-- Prove2me | solution 1 for OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:00:39.231288+00:00
-- url     : https://prove2.me/submissions/c7dfa7f8-7a71-4a51-bf9e-fcd98aace2e8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A019
import Theorems.Thm_OAI_PiExponentJets_W22_homogeneous_local_regular_bezout_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FlatLocalLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B]

theorem simple_baseChange_of_map_maximalIdeal
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    IsSimpleModule B (B ⊗[A] M) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := A) (M := M)).mp inferInstance
  have hJmax : J = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hJ
  subst J
  have : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal))
  let eB : (B ⊗[A] M) ≃ₗ[B] (B ⧸ IsLocalRing.maximalIdeal B) :=
    (e.baseChange A B M (A ⧸ IsLocalRing.maximalIdeal A)).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (IsLocalRing.maximalIdeal A)).toLinearEquiv.symm.trans
        (Submodule.quotEquivOfEq _ _ hmax))
  exact IsSimpleModule.congr eB

theorem length_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  induction hM with
  | of_subsingleton =>
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    have : IsSimpleModule B (B ⊗[A] (M ⧸ N)) :=
      simple_baseChange_of_map_maximalIdeal hmax
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hinj : Function.Injective (N.subtype.baseChange B) :=
      Module.Flat.lTensor_preserves_injective_linearMap N.subtype
        (Submodule.subtype_injective N)
    have hsurj : Function.Surjective (N.mkQ.baseChange B) :=
      LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N)
    have hbaseexact : Function.Exact (N.subtype.baseChange B) (N.mkQ.baseChange B) :=
      Module.Flat.lTensor_exact B hexact
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hB := Module.length_eq_add_of_exact (N.subtype.baseChange B)
      (N.mkQ.baseChange B) hinj hsurj hbaseexact
    calc
      Module.length B (B ⊗[A] M) =
          Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := hB
      _ = Module.length A N + Module.length A (M ⧸ N) := by
        rw [ih, Module.length_eq_one B (B ⊗[A] (M ⧸ N)),
          Module.length_eq_one A (M ⧸ N)]
      _ = Module.length A M := hA.symm

theorem length_quotient_map_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  calc
    Module.length B (B ⧸ I.map (algebraMap A B)) =
        Module.length B (B ⊗[A] (A ⧸ I)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq
    _ = Module.length A (A ⧸ I) := length_baseChange_of_flat_local hmax hI

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeLocalLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

section ExtendedPrime

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

theorem localized_maximalIdeal_map_eq (hQ : Q = P.map (algebraMap A B)) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) =
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq A (Localization.AtPrime P)
      (Localization.AtPrime Q),
    IsScalarTower.algebraMap_eq A B (Localization.AtPrime Q), ← Ideal.map_map, ← hQ]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal Q (Localization.AtPrime Q)

end ExtendedPrime

section LaurentExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

theorem laurentLocal_maximalIdeal_map_eq :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime A P))) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (laurentPrime A P)) :=
  localized_maximalIdeal_map_eq P (laurentPrime A P) rfl

theorem laurentLocal_quotient_length
    (I : Ideal (Localization.AtPrime P))
    (hI : IsFiniteLength (Localization.AtPrime P) (Localization.AtPrime P ⧸ I)) :
    Module.length (Localization.AtPrime (laurentPrime A P))
      (Localization.AtPrime (laurentPrime A P) ⧸ I.map
        (algebraMap (Localization.AtPrime P)
          (Localization.AtPrime (laurentPrime A P)))) =
    Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ I) :=
  PiExponentJets.W25.length_quotient_map_of_flat_local
    (laurentLocal_maximalIdeal_map_eq A P) I hI

end LaurentExtension

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientLengthEquivalence
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem quotient_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : J = I.map e.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  let eQ : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ J) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r x
        change eQ ((Ideal.Quotient.mk I r) * x) =
          Ideal.Quotient.mk J (e r) * eQ x
        rw [map_mul]
        change Ideal.quotientEquiv I J e hIJ (Ideal.Quotient.mk I r) * eQ x = _
        rfl }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact length_eq_of_semilinear_bijective e.toRingHom f eQ.bijective

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConePrimeLocalization
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem homogenizing_coordinate_not_mem_conePrime :
    (MvPolynomial.X none : ConeRing k σ) ∉ conePrime k σ P := by
  intro h
  change algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) ∈
    awayChartPrime k σ P at h
  exact (show (awayChartPrime k σ P).IsPrime from inferInstance).ne_top
    ((awayChartPrime k σ P).eq_top_of_isUnit_mem h
      (IsLocalization.Away.algebraMap_isUnit (S := ConeAway k σ)
        (MvPolynomial.X none : ConeRing k σ)))

theorem affineLocalToConeLocal_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (affineLocalToConeLocal k σ P) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (conePrime k σ P)) := by
  rw [affineLocalToConeLocal, ← Ideal.map_map,
    laurentLocal_maximalIdeal_map_eq (AffineRing k σ) P]
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (conePrimeLocalizationEquiv k σ P).symm.toRingHom
    (conePrimeLocalizationEquiv k σ P).symm.surjective

theorem affineLocalToConeLocal_flat :
    letI := affineLocalConeAlgebra k σ P
    Module.Flat (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let e : Localization.AtPrime (conePrime k σ P) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
    { conePrimeLocalizationEquiv k σ P with
      commutes' := by
        intro a
        change conePrimeLocalizationEquiv k σ P
          ((conePrimeLocalizationEquiv k σ P).symm (algebraMap _ _ a)) = _
        exact (conePrimeLocalizationEquiv k σ P).apply_symm_apply _ }
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_Homogenization
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators
open MvPolynomial

variable {k σ : Type*} [CommRing k]

theorem homogenize_isHomogeneous (p : MvPolynomial σ k) :
    (homogenize p).IsHomogeneous p.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcomponent :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).rename_isHomogeneous
      (f := (some : σ → Option σ))
  simpa only [Nat.add_sub_of_le hi'] using
    hcomponent.mul (MvPolynomial.isHomogeneous_X_pow (none : Option σ) (p.totalDegree - i))

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_ConeHomogeneousEquations
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace PiExponentSiegel.W17.ConeLocalLength

section Scaling

variable {k B σ : Type*} [CommRing k] [CommRing B]

theorem eval₂_scale_of_isHomogeneous (F : MvPolynomial σ k) (d : ℕ)
    (hF : F.IsHomogeneous d) (c : k →+* B) (x : σ → B) (t : B) :
    MvPolynomial.eval₂ c (fun i => x i * t) F =
      MvPolynomial.eval₂ c x F * t ^ d := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hF.degree_eq_sum_deg_support hm, mul_assoc]

end Scaling

variable (k σ : Type*) [CommRing k]

private theorem coneToLaurent_scaled_eval (F : ConeRing k σ) :
    coneToLaurent k σ F =
      MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
        (fun i : Option σ =>
          LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
            (LaurentPolynomial.T 1 : LaurentChart k σ)) F := by
  have hv : (fun i : Option σ => i.elim (LaurentPolynomial.T 1 : LaurentChart k σ)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) =
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
        (LaurentPolynomial.T 1 : LaurentChart k σ)) := by
    funext i
    cases i <;> simp only [Option.elim_none, Option.elim_some, map_one, one_mul]
  change MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i : Option σ => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) F = _
  rw [hv]

private theorem laurent_eval_dehomogenize (F : ConeRing k σ) :
    MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X)) F =
      (LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) : LaurentChart k σ) :=
  (MvPolynomial.map_eval₂Hom MvPolynomial.C
    (fun i : Option σ => i.elim 1 MvPolynomial.X) LaurentPolynomial.C F).symm

theorem coneToLaurent_homogeneous (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    coneToLaurent k σ F =
      LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) *
        (LaurentPolynomial.T 1 : LaurentChart k σ) ^ d := by
  rw [coneToLaurent_scaled_eval]
  rw [eval₂_scale_of_isHomogeneous F d hF, laurent_eval_dehomogenize]

theorem coneToLaurent_homogenize (f : AffineRing k σ) :
    coneToLaurent k σ (PiExponentJets.W22.homogenize f) =
      LaurentPolynomial.C f * (LaurentPolynomial.T 1 : LaurentChart k σ) ^ f.totalDegree := by
  simpa using coneToLaurent_homogeneous k σ (PiExponentJets.W22.homogenize f)
    f.totalDegree (PiExponentJets.W22.homogenize_isHomogeneous f)

theorem map_homogenized_span_eq_laurent_span {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
      (coneToLaurent k σ) =
    (Ideal.span (Set.range f)).map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change coneToLaurent k σ (PiExponentJets.W22.homogenize (f i)) ∈
      (Ideal.span (Set.range f)).map
        (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)
    rw [coneToLaurent_homogenize]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
      (Ideal.subset_span (Set.mem_range_self i)))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (LaurentPolynomial.C (f i) : LaurentChart k σ) ∈
      (Ideal.span (Set.range (fun j => PiExponentJets.W22.homogenize (f j)))).map
        (coneToLaurent k σ)
    apply (Ideal.mul_unit_mem_iff_mem _
      ((LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).pow (f i).totalDegree)).mp
    rw [← coneToLaurent_homogenize]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ConePrimeProperties
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mapped_minimalPrime_of_prime_extension
    (f : A →+* B) {I P : Ideal A} (hP : P ∈ I.minimalPrimes)
    (hprime : (P.map f).IsPrime) (hcontract : (P.map f).comap f = P) :
    P.map f ∈ (I.map f).minimalPrimes := by
  refine ⟨⟨hprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  apply Ideal.map_le_iff_le_comap.mpr
  apply hP.2 ⟨hQ.1.comap f, Ideal.map_le_iff_le_comap.mp hQ.2⟩
  exact (Ideal.comap_mono hQP).trans hcontract.le

end General

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrime_minimal_over_homogenized {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    conePrime k σ P ∈
      (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).minimalPrimes := by
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hLP : laurentPrime (AffineRing k σ) P ∈ (H.map (coneToLaurent k σ)).minimalPrimes := by
    rw [map_homogenized_span_eq_laurent_span k σ f]
    exact mapped_minimalPrime_of_prime_extension LaurentPolynomial.C hP inferInstance
      (laurentPrime_comap (AffineRing k σ) P)
  have hcomp : coneToLaurent k σ = (coneLaurentEquiv k σ).toRingHom.comp
      (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    apply RingHom.ext
    intro F
    exact (coneAwayToLaurent_algebraMap k σ F).symm
  have hI : (H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom =
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    rw [hcomp, ← Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv]
    apply Ideal.ext
    intro z
    change (coneLaurentEquiv k σ).symm ((coneLaurentEquiv k σ) z) ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) ↔ z ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ))
    rw [RingEquiv.symm_apply_apply]
  have hchart := Ideal.minimalPrimes_comap_of_surjective
    (coneLaurentEquiv k σ).surjective hLP
  change awayChartPrime k σ P ∈
    ((H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom).minimalPrimes at hchart
  rw [hI, IsLocalization.minimalPrimes_map
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (ConeAway k σ)] at hchart
  exact hchart

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeEquationLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrimeLocalizationEquiv_algebraMap (F : ConeRing k σ) :
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) F) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (coneToLaurent k σ F) := by
  let a := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (awayChartPrime k σ P)
  let b := PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
    (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl
  change b (a (algebraMap (ConeRing k σ) _ F)) = _
  rw [a.commutes F]
  change b (algebraMap (ConeAway k σ) _ (algebraMap (ConeRing k σ) (ConeAway k σ) F)) = _
  rw [show b (algebraMap (ConeAway k σ) _
      (algebraMap (ConeRing k σ) (ConeAway k σ) F)) =
      algebraMap (LaurentChart k σ) _ ((coneLaurentEquiv k σ)
        (algebraMap (ConeRing k σ) (ConeAway k σ) F)) from
    IsLocalization.ringEquivOfRingEquiv_eq
      (PiExponentJets.W22.primeCompl_map_eq_of_comap (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl) _]
  exact congrArg (algebraMap (LaurentChart k σ)
    (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))
    (coneAwayToLaurent_algebraMap k σ F)

theorem conePrimeLocalizationEquiv_map_ideal (J : Ideal (ConeRing k σ)) :
    (J.map (algebraMap (ConeRing k σ)
      (Localization.AtPrime (conePrime k σ P)))).map
        (conePrimeLocalizationEquiv k σ P).toRingHom =
    (J.map (coneToLaurent k σ)).map (algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact conePrimeLocalizationEquiv_algebraMap k σ P F

theorem affine_ideal_map_to_laurent_local (J : Ideal (AffineRing k σ)) :
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) =
    (J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

theorem homogenized_cone_local_length_eq {ι : Type*} (f : ι → AffineRing k σ)
    (hfinite : IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    Module.length (Localization.AtPrime (conePrime k σ P))
      (Localization.AtPrime (conePrime k σ P) ⧸
        (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
          (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) =
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P))) := by
  let J := Ideal.span (Set.range f)
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hid := conePrimeLocalizationEquiv_map_ideal k σ P H
  rw [map_homogenized_span_eq_laurent_span k σ f] at hid
  have hlength := PiExponentJets.W22.quotient_length_eq_of_ringEquiv
    (conePrimeLocalizationEquiv k σ P)
    (H.map (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))))
    ((J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))) hid.symm
  apply hlength.trans
  have h := laurentLocal_quotient_length (AffineRing k σ) P
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))) hfinite
  rw [affine_ideal_map_to_laurent_local k σ P J] at h
  exact h

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeRegularSequence
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

open RingTheory.Sequence

section Units

variable {R τ M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ofList_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x)) :
    Ideal.ofList (xs.map (fun x => a x * u x)) = Ideal.ofList (xs.map a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩))
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    apply (Ideal.mul_unit_mem_iff_mem _ (hu x)).mp
    exact Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem isRegular_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x))
    (hreg : IsRegular M (xs.map a)) :
    IsRegular M (xs.map (fun x => a x * u x)) := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro i hi
    have hi' : i < xs.length := by simpa only [List.length_map] using hi
    have ha := hreg.regular_mod_prev i (by simpa only [List.length_map] using hi')
    simp only [List.getElem_map] at ha ⊢
    have hI : Ideal.ofList ((xs.map (fun x => a x * u x)).take i) =
        Ideal.ofList ((xs.map a).take i) := by
      simp only [← List.map_take]
      exact ofList_map_mul_units (xs.take i) a u hu
    have hN : (Ideal.ofList ((xs.map (fun x => a x * u x)).take i) •
        (⊤ : Submodule R M)) = Ideal.ofList ((xs.map a).take i) • ⊤ :=
      congrArg (fun J : Ideal R => J • (⊤ : Submodule R M)) hI
    exact Eq.mp (congrArg (fun N : Submodule R M =>
      IsSMulRegular (M ⧸ N) (a xs[i] * u xs[i])) hN.symm)
      (ha.mul ((hu xs[i]).isSMulRegular _))
  · rw [ofList_map_mul_units xs a u hu]
    exact hreg.top_ne_smul

end Units

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem coneLocalCoordinate_isUnit : IsUnit (coneLocalCoordinate k σ P) :=
  IsLocalization.map_units (Localization.AtPrime (conePrime k σ P))
    (⟨MvPolynomial.X none, homogenizing_coordinate_not_mem_conePrime k σ P⟩ :
      (conePrime k σ P).primeCompl)

theorem homogenized_local_eq_affine_mul_coordinate (f : AffineRing k σ) :
    algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f) =
    affineLocalToConeLocal k σ P (algebraMap (AffineRing k σ) (Localization.AtPrime P) f) *
      coneLocalCoordinate k σ P ^ f.totalDegree := by
  let e := conePrimeLocalizationEquiv k σ P
  have ha : e (affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f)) =
      algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) := by
    change e (e.symm (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) = _
    rw [e.apply_symm_apply]
    exact (IsScalarTower.algebraMap_apply (AffineRing k σ) (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f).symm.trans
        (IsScalarTower.algebraMap_apply (AffineRing k σ) (LaurentChart k σ)
          (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f)
  apply e.injective
  rw [e.map_mul, e.map_pow, ha]
  change conePrimeLocalizationEquiv k σ P
    (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f)) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) *
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
        (MvPolynomial.X none)) ^ f.totalDegree
  rw [conePrimeLocalizationEquiv_algebraMap, conePrimeLocalizationEquiv_algebraMap,
    coneToLaurent_homogenize, coneToLaurent_X_none, map_mul, map_pow]

theorem affineLocalToConeLocal_faithfullyFlat :
    letI := affineLocalConeAlgebra k σ P
    Module.FaithfullyFlat (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_flat k σ P
  let : IsLocalHom (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P))) :=
    ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
      (affineLocalToConeLocal_map_maximalIdeal k σ P).le
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem homogenized_list_regular_at_cone (fs : List (AffineRing k σ))
    (hreg : IsRegular (Localization.AtPrime P)
      (fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map PiExponentJets.W22.homogenize).map
        (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_faithfullyFlat k σ P
  have hbase : IsRegular (Localization.AtPrime (conePrime k σ P))
      (fs.map (fun f => affineLocalToConeLocal k σ P
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) := by
    have hb := hreg.of_faithfullyFlat (S := Localization.AtPrime (conePrime k σ P))
    change IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
        (affineLocalToConeLocal k σ P)) at hb
    simpa only [List.map_map, Function.comp_def] using hb
  have hscaled := isRegular_map_mul_units fs
    (fun f => affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))
    (fun f => coneLocalCoordinate k σ P ^ f.totalDegree)
    (fun f => (coneLocalCoordinate_isUnit k σ P).pow f.totalDegree) hbase
  simpa only [List.map_map, Function.comp_def,
    homogenized_local_eq_affine_mul_coordinate] using hscaled

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedComponent
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem radical_mem_minimalPrimes (I : Ideal R) [I.radical.IsPrime] :
    I.radical ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedRadical
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem localized_radical_eq_maximal_of_mem_minimalPrimes
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hreverse : P.map (algebraMap R (Localization.AtPrime P)) ≤
      (I.map (algebraMap R (Localization.AtPrime P))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨hqI, hq⟩
    obtain ⟨hqprime, hqP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime P) P) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap] at hqI ⊢
    exact hP.2 ⟨hqprime, hqI⟩ hqP
  have hmprime : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrime := inferInstance
  apply le_antisymm
  · apply hmprime.radical_le_iff.mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hP.1.2
  · simpa only [Localization.AtPrime.map_eq_maximalIdeal] using hreverse

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineLocalRegularBezout
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open PiExponentSiegel.W17.ConeLocalLength
open scoped BigOperators Classical

theorem span_range_list_get {R : Type*} [CommSemiring R] (gs : List R) :
    Ideal.span (Set.range gs.get) = Ideal.ofList gs := by
  congr 1
  ext x
  exact List.mem_iff_get.symm

theorem span_range_map_list_get {R S : Type*} [CommSemiring S]
    (gs : List R) (f : R → S) :
    Ideal.span (Set.range (fun i => f (gs.get i))) = Ideal.ofList (gs.map f) := by
  congr 1
  ext x
  change (∃ i, f (gs.get i) = x) ↔ x ∈ gs.map f
  constructor
  · rintro ⟨i,rfl⟩
    exact List.mem_map.mpr ⟨gs.get i,List.mem_iff_get.mpr ⟨i,rfl⟩,rfl⟩
  · intro hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i,rfl⟩

theorem finiteLength_localized_minimal_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let J := I.map (algebraMap R L)
  have hrad : J.radical = IsLocalRing.maximalIdeal L :=
    localized_radical_eq_maximal_of_mem_minimalPrimes I P hP
  let : J.radical.IsPrime := by rw [hrad]; infer_instance
  have hmin : IsLocalRing.maximalIdeal L ∈ J.minimalPrimes := by
    rw [← hrad]
    exact radical_mem_minimalPrimes J
  let : IsArtinianRing (L ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmin
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_of_surjective (M := L ⧸ J)
    (show Function.Surjective (algebraMap L (L ⧸ J)) from Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

theorem affine_local_regular_list_bezout_q68_oai
    {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (gs : List (MvPolynomial (Fin n) k)) (D : ℕ)
    (hdegree : ∀ g ∈ gs, g.totalDegree ≤ D)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
    (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ gs.length : ℕ) : ℕ∞) := by
  let hs := gs.map homogenize
  let degrees : Fin hs.length → ℕ := fun i =>
    (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt)).totalDegree
  have hhom : ∀ i : Fin hs.length, hs[i].IsHomogeneous (degrees i) := by
    intro i
    simpa only [hs, List.getElem_map, Fin.getElem_fin, degrees] using
      homogenize_isHomogeneous (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt))
  have hconeReg := homogenized_list_regular_at_cone k (Fin n) P gs hreg
  have hget : P ∈ (Ideal.span (Set.range gs.get)).minimalPrimes := by
    simpa only [span_range_list_get] using hP
  have hconeMin := conePrime_minimal_over_homogenized k (Fin n) P gs.get hget
  rw [span_range_map_list_get] at hconeMin
  have hconeLen : hs.length < Fintype.card (Option (Fin n)) := by
    simp only [hs,List.length_map,Fintype.card_option,Fintype.card_fin]
    omega
  have hbound := homogeneous_local_regular_bezout_q68 (conePrime k (Fin n) P) none
    (homogenizing_coordinate_not_mem_conePrime k (Fin n) P)
    hs degrees hhom hconeReg hconeLen hconeMin
  have hfinite := finiteLength_localized_minimal_quotient
    (Ideal.span (Set.range gs.get)) P hget
  have hlength := homogenized_cone_local_length_eq k (Fin n) P gs.get hfinite
  rw [span_range_list_get, span_range_map_list_get] at hlength
  have hprod : (∏ i ∈ Finset.range hs.length, degreeAt degrees i) ≤ D ^ gs.length := by
    calc
      _ ≤ ∏ _i ∈ Finset.range hs.length, D := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi' : i < hs.length := Finset.mem_range.mp hi
        simp only [degreeAt,dite_eq_left hi',degrees]
        exact hdegree _ (List.getElem_mem _)
      _ = D ^ gs.length := by simp only [Finset.prod_const,Finset.card_range,hs,List.length_map]
  calc
    _ = Module.length (Localization.AtPrime (conePrime k (Fin n) P))
      (Localization.AtPrime (conePrime k (Fin n) P) ⧸ (Ideal.ofList hs).map
        (algebraMap (MvPolynomial (Option (Fin n)) k)
          (Localization.AtPrime (conePrime k (Fin n) P)))) := hlength.symm
    _ ≤ ((∏ i ∈ Finset.range hs.length, degreeAt degrees i : ℕ) : ℕ∞) := hbound
    _ ≤ _ := by exact_mod_cast hprod

end PiExponentJets.W22

end OAI
end

theorem solution : type_of% @OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68_oai := @OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68_oai
