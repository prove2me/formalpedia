-- Prove2me | solution 1 for OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:08:50.937798+00:00
-- url     : https://prove2.me/submissions/8a3b786a-467f-40e4-9b6c-3c8d07a581bf

import Mathlib
import Definitions.Def_OAIQ068A019
import Definitions.Def_OAIQ068A027

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateTranscendenceLocalization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

lemma residueCoordinate_aeval (f : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval (residueCoordinate K n Q) f =
      algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) f := by
  have he : MvPolynomial.aeval (residueCoordinate K n Q) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) := by
    ext i
    simp only [MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun he f

theorem residueCoordinate_adjoin_top :
    IntermediateField.adjoin K (Set.range (residueCoordinate K n Q)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, hb, hz⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin n) K ⧸ Q) z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (IntermediateField.mem_adjoin_range_iff K (residueCoordinate K n Q) z).mpr
  refine ⟨f, g, ?_⟩
  simpa only [residueCoordinate_aeval,
    Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem exists_coordinate_residue_basis :
    ∃ t : Set (LocalPolynomialResidue K n Q),
      t.Finite ∧ t ⊆ Set.range (residueCoordinate K n Q) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  have htop := residueCoordinate_adjoin_top K n Q
  let : Algebra.IsAlgebraic
      (Algebra.adjoin K (Set.range (residueCoordinate K n Q)))
      (LocalPolynomialResidue K n Q) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, ht, htb⟩ :=
    exists_isTranscendenceBasis_subset (R := K) (Set.range (residueCoordinate K n Q))
  exact ⟨t, (Set.finite_range _).subset ht, ht, htb⟩

theorem exists_coordinate_basis_indices :
    ∃ (t : Set (LocalPolynomialResidue K n Q)) (j : t → Fin n),
      t.Finite ∧ Function.Injective j ∧
      (∀ a, residueCoordinate K n Q (j a) = (a : LocalPolynomialResidue K n Q)) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  classical
  obtain ⟨t, hfin, ht, htb⟩ := exists_coordinate_residue_basis K n Q
  choose j hj using fun a : t => ht a.property
  refine ⟨t, j, hfin, ?_, hj, htb⟩
  intro a b hab
  apply Subtype.ext
  exact (hj a).symm.trans ((congrArg (residueCoordinate K n Q) hab).trans (hj b))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialCoordinateMinpolyQuotient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W08

open Polynomial

variable {K : Type*} [Field K]

theorem coordinateMinpolyIdeal_le_of_mem_contraction (n : ℕ) (f : K[X])
    (m : Ideal (MvPolynomial (Fin (n+1)) K))
    (hf : f ∈ m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))).toRingHom) :
    coordinateMinpolyIdeal n f ≤ m := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact hf

end PiExponentSiegel.W08

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TriangularLocalParameters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S]

theorem regular_cons_of_principal_kernel (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (xs : List R) (hxs : IsRegular S (xs.map π)) : IsRegular R (r :: xs) := by
  let e := principalModuleQuotientEquiv π hπ r hker
  apply IsRegular.cons hr
  apply (e.toAddEquiv.isRegular_congr ?_).mpr hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change e (Submodule.Quotient.mk (a * z)) = π a * e (Submodule.Quotient.mk z)
    calc
      e (Submodule.Quotient.mk (a * z)) = π (a * z) :=
        principalModuleQuotientEquiv_mk π hπ r hker (a * z)
      _ = π a * π z := π.map_mul a z
      _ = π a * e (Submodule.Quotient.mk z) :=
        congrArg (fun y : S => π a * y)
          (principalModuleQuotientEquiv_mk π hπ r hker z).symm

theorem ofList_cons_eq_comap (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (xs : List R) :
    Ideal.ofList (r :: xs) = Ideal.comap π (Ideal.ofList (xs.map π)) := by
  rw [← Ideal.map_ofList, Ideal.comap_map_of_surjective π hπ, Ideal.ofList_cons]
  change Ideal.span {r} ⊔ Ideal.ofList xs = Ideal.ofList xs ⊔ RingHom.ker π
  rw [hker, sup_comm]

theorem lift_parameters [IsLocalRing R] [IsLocalRing S]
    (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (ys : List S) (hys : IsRegular S ys)
    (hspan : Ideal.ofList ys = IsLocalRing.maximalIdeal S) :
    ∃ xs : List R, xs.length = ys.length + 1 ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R := by
  obtain ⟨xs, hxs⟩ := (List.map_surjective_iff.mpr hπ) ys
  refine ⟨r :: xs, ?_, ?_, ?_⟩
  · simpa using congrArg (fun zs : List S => zs.length + 1) hxs
  · apply regular_cons_of_principal_kernel π hπ r hker hr xs
    simpa [hxs] using hys
  · rw [ofList_cons_eq_comap π hπ r hker xs, hxs, hspan]
    let : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact IsLocalRing.maximalIdeal_comap π

theorem regular_element_of_ne_zero [IsDomain R] (r : R) (hr : r ≠ 0) : IsSMulRegular R r :=
  fun _ _ h => mul_left_cancel₀ hr h

section ZeroVariables
variable (K : Type*) [Field K] (m : Ideal (MvPolynomial (Fin 0) K)) [m.IsMaximal]

theorem zeroVariable_maximal_eq_bot : m = ⊥ := by
  apply le_antisymm
  · intro p hp
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    by_cases hc : c = 0
    · simp [hc]
    · have hu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 0) K) :=
        (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
      exact False.elim ((inferInstance : m.IsMaximal).ne_top (m.eq_top_of_isUnit_mem hp hu))
  · exact bot_le

theorem zeroVariable_parameters :
    ∃ xs : List (Localization.AtPrime m), xs.length = 0 ∧
      IsRegular (Localization.AtPrime m) xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  refine ⟨[], rfl, IsRegular.nil _ _, ?_⟩
  rw [Ideal.ofList_nil, ← Localization.AtPrime.map_eq_maximalIdeal]
  simpa only [Ideal.map_bot] using
    (congrArg (Ideal.map
      (algebraMap (MvPolynomial (Fin 0) K) (Localization.AtPrime m)))
      (zeroVariable_maximal_eq_bot K m)).symm

end ZeroVariables

variable (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin (n + 1)) K)) [m.IsMaximal]

theorem maximal_coefficient_contraction {A : Type*} [CommRing A] [IsJacobsonRing A]
    (j : ℕ) (q : Ideal (MvPolynomial (Fin j) A)) [q.IsMaximal] :
    (q.comap (MvPolynomial.C : A →+* MvPolynomial (Fin j) A)).IsMaximal := by
  rw [← @Ideal.mk_ker _ _ q, RingHom.ker_eq_comap_bot, Ideal.comap_comap]
  let := (Ideal.bot_quotient_isMaximal_iff _).mpr (inferInstance : q.IsMaximal)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _
    (MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing q) ⊥

theorem firstCoordinateContraction_isMaximal : (firstCoordinateContraction K n m).IsMaximal := by
  let e := PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n
  let q := m.comap e.symm.toRingEquiv.toRingHom
  let : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have he : e.symm.toRingEquiv.toRingHom.comp MvPolynomial.C =
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom := by
    apply RingHom.ext
    intro f
    change e.symm (MvPolynomial.C f) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    apply e.symm_apply_eq.mpr
    exact (PiExponentSiegel.W08.coordinateCoefficientSplit_aeval n f).symm
  have hq := maximal_coefficient_contraction n q
  simpa only [q, Ideal.comap_comap, he, firstCoordinateContraction] using hq

theorem firstCoordinatePolynomial_irreducible : Irreducible (firstCoordinatePolynomial K n m) := by
  let := firstCoordinateContraction_isMaximal K n m
  apply (Submodule.IsPrincipal.prime_generator_of_isPrime
    (firstCoordinateContraction K n m) ?_).irreducible
  exact Ring.ne_bot_of_isMaximal_of_not_isField
    (firstCoordinateContraction_isMaximal K n m) (Polynomial.not_isField K)

omit [m.IsMaximal] in
theorem firstCoordinatePolynomial_mem :
    firstCoordinatePolynomial K n m ∈ firstCoordinateContraction K n m :=
  Submodule.IsPrincipal.generator_mem _

omit [m.IsMaximal] in
theorem firstCoordinateIdeal_le :
    PiExponentSiegel.W08.coordinateMinpolyIdeal n (firstCoordinatePolynomial K n m) ≤ m :=
  PiExponentSiegel.W08.coordinateMinpolyIdeal_le_of_mem_contraction n
    (firstCoordinatePolynomial K n m) m (firstCoordinatePolynomial_mem K n m)

theorem firstCoordinateRelation_ne_zero :
    Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)
      (firstCoordinatePolynomial K n m) ≠ 0 := by
  intro h
  have h' := congrArg (PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n) h
  rw [PiExponentSiegel.W08.coordinateCoefficientSplit_aeval, map_zero] at h'
  apply (firstCoordinatePolynomial_irreducible K n m).ne_zero
  simpa using h'

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TriangularLocalParametersAssembly
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
universe u

theorem polynomialMaximal_regularParameters (n : ℕ) :
    ∀ (K : Type u) [Field K] (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal],
      ∃ xs : List (Localization.AtPrime m), xs.length = n ∧
        IsRegular (Localization.AtPrime m) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  induction n with
  | zero =>
    intro K _ m _
    exact zeroVariable_parameters K m
  | succ n ih =>
    intro K _ m _
    let A := MvPolynomial (Fin (n + 1)) K
    let f : Polynomial K := firstCoordinatePolynomial K n m
    let : Fact (Irreducible f) := ⟨firstCoordinatePolynomial_irreducible K n m⟩
    let I : Ideal A := PiExponentSiegel.W08.coordinateMinpolyIdeal n f
    have hI : I ≤ m := firstCoordinateIdeal_le K n m
    let e := (PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv n f).toRingEquiv
    let qm := PiExponentSiegel.W23.quotientParameterPrime I m hI
    let p : Ideal (MvPolynomial (Fin n) (AdjoinRoot f)) := qm.map e.toRingHom
    let : p.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := e.toRingHom) (m := qm) e.surjective (by simp)
    obtain ⟨ys, hylen, hyreg, hyspan⟩ := ih (AdjoinRoot f) p
    let J : Ideal (Localization.AtPrime m) := PiExponentSiegel.W23.parameterLocalizedIdeal I m
    let E : (Localization.AtPrime m ⧸ J) ≃+* Localization.AtPrime p :=
      PiExponentSiegel.W23.localizationQuotientParametersEquivTrans I m hI e
    let π : Localization.AtPrime m →+* Localization.AtPrime p :=
      E.toRingHom.comp (Ideal.Quotient.mk J)
    have hπ : Function.Surjective π := E.surjective.comp Ideal.Quotient.mk_surjective
    let g : A := Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    let r : Localization.AtPrime m := algebraMap A (Localization.AtPrime m) g
    have hg : g ≠ 0 := firstCoordinateRelation_ne_zero K n m
    have hr : r ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff A (Localization.AtPrime m)).not.mpr hg
    have hker : RingHom.ker π = Ideal.span {r} := by
      rw [show π = E.toRingHom.comp (Ideal.Quotient.mk J) from rfl,
        RingHom.ker_comp_of_injective _ E.injective, Ideal.mk_ker]
      change (Ideal.span {g}).map (algebraMap A (Localization.AtPrime m)) = Ideal.span {r}
      rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨xs, hxlen, hxreg, hxspan⟩ := lift_parameters π hπ r hker
      (regular_element_of_ne_zero r hr) ys hyreg hyspan
    refine ⟨xs, ?_, hxreg, hxspan⟩
    simpa [hylen] using hxlen

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TriangularLocalParametersTransport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem regular_map_ringEquiv (e : R ≃+* S) (xs : List R)
    (hxs : IsRegular R xs) : IsRegular S (xs.map e.toRingHom) := by
  apply (e.toAddEquiv.isRegular_congr ?_).mp hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  exact e.map_mul a z

theorem regularParameters_transport [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (n : ℕ)
    (h : ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R) :
    ∃ ys : List S, ys.length = n ∧ IsRegular S ys ∧
      Ideal.ofList ys = IsLocalRing.maximalIdeal S := by
  obtain ⟨xs, hlen, hreg, hspan⟩ := h
  refine ⟨xs.map e.toRingHom, ?_, regular_map_ringEquiv e xs hreg, ?_⟩
  · simpa using hlen
  · rw [← Ideal.map_ofList, hspan]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

theorem polynomialMaximal_regularParameters_of_ringEquiv (n : ℕ) (K : Type*) [Field K]
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal]
    [IsLocalRing R] (e : R ≃+* Localization.AtPrime m) :
    ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R :=
  regularParameters_transport e.symm n (polynomialMaximal_regularParameters n K m)

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialMaximalHeight
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K]

theorem polynomialMaximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] :
    m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let p : Ideal K := m.comap e.symm.toRingHom
      let : p.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      have hp : p = ⊥ := p.eq_bot_or_top.resolve_right (Ideal.IsMaximal.ne_top (inferInstance : p.IsMaximal))
      calc
        m.height = p.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = (0 : ℕ∞) := by rw [hp, Ideal.height_bot]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        m.comap e.symm.toRingHom
      let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
      let : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      let : P.LiesOver p := ⟨rfl⟩
      calc
        m.height = P.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih p]; simp

end PiExponentSiegelAux.W09

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialLocalRegularParameters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

theorem exists_regularParameters_actual_height_q68_oai :
    ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
      ∃ xs : List (Localization.AtPrime Q),
        xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  classical
  obtain ⟨t, j, htfinite, hj, hcoord, ht⟩ := exists_coordinate_basis_indices K n Q
  let A := RemainingCoordinate j
  let F := SplitCoefficientField K t
  let Qs := coordinateSplitPrime K Q t j hj
  let hB := coordinateSplitPrime_basis K Q t j hj hcoord ht
  let m₀ := closedPolynomialIdeal K A t Qs hB
  let : m₀.IsMaximal := closedPolynomialIdeal_isMaximal K A t Qs hB
  let e₀ : Localization.AtPrime Q ≃+* Localization.AtPrime m₀ :=
    coordinateBasisClosedPointEquiv K Q t j hj hcoord ht
  let h := Fintype.card A
  let eFin : MvPolynomial A F ≃ₐ[F] MvPolynomial (Fin h) F :=
    MvPolynomial.renameEquiv F (Fintype.equivFin A)
  let m : Ideal (MvPolynomial (Fin h) F) := m₀.map eFin.toRingHom
  let : m.IsMaximal := (inferInstance : m₀.IsMaximal).map_bijective eFin.toRingHom eFin.bijective
  let e : Localization.AtPrime Q ≃+* Localization.AtPrime m :=
    e₀.trans (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv eFin.toRingEquiv m₀)
  have hheight : Q.height = (h : ℕ∞) := by
    have he := ringKrullDim_eq_of_ringEquiv e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      PiExponentSiegelAux.W09.polynomialMaximal_height F h m] at he
    exact WithBot.coe_injective he
  refine ⟨h, hheight, ?_⟩
  exact PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters_of_ringEquiv
    h F m e

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68_oai.{u_1} := @OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68_oai.{u_1}
