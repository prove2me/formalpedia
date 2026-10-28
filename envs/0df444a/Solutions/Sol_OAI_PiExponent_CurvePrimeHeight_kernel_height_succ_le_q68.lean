-- Prove2me | solution 1 for OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:07:16.913342+00:00
-- url     : https://prove2.me/submissions/5ba082c6-21f1-4794-9630-09b16f32a9ab

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
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineClosedPointLocalization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23
open PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]

attribute [local instance] affineCoefficientAlgebra

variable (Q : Ideal (SplitPolynomial K α β)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

include hB in

theorem affineDenominators_disjoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β)) (P : Set _) := by
  have hd : Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β))
      (Q : Set _) := by
    rw [← affineCoefficientMap_comap_closedPoint K α β Q hB]
    exact (IsLocalization.disjoint_under_iff (coefficientDenominators K α β)
      (FractionCoefficientPolynomial K α β) (closedPolynomialIdeal K α β Q hB)).mpr
      (Ideal.IsMaximal.ne_top inferInstance)
  exact Set.disjoint_left.mpr fun x hx hxP => Set.disjoint_left.mp hd hx (hPQ hxP)

include hB in

theorem affineMappedIdeal_isPrime (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : (affineMappedIdeal K α β P).IsPrime := by
  exact IsLocalization.isPrime_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) P inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

include hB in

theorem affineMappedIdeal_comap (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    (affineMappedIdeal K α β P).comap (affineCoefficientMap K α β) = P :=
  IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

attribute [local instance] affineQuotientAlgebra

include hB in

theorem affineQuotientMap_injective (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : Function.Injective (affineQuotientMap K α β P) :=
  Ideal.quotientMap_injective' (affineMappedIdeal_comap K α β Q hB P hPQ).le

include hB in

theorem affineQuotient_faithfulSMul (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    FaithfulSMul (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (affineQuotientMap_injective K α β Q hB P hPQ)

include hB in

theorem affineQuotient_isDomain (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsDomain (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  let := affineMappedIdeal_isPrime K α β Q hB P hPQ
  infer_instance

theorem affineQuotient_finiteType [Finite α] (P : Ideal (SplitPolynomial K α β)) :
    Algebra.FiniteType (SplitCoefficientField K β)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ (SplitCoefficientField K β) (affineMappedIdeal K α β P))
    Ideal.Quotient.mk_surjective

include hB in

theorem affineQuotient_isLocalization (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsLocalization ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply (isLocalization_iff
    ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
    (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨a, ha, he⟩ := s.property
    change IsUnit (affineQuotientMap K α β P (s : SplitPolynomial K α β ⧸ P))
    rw [← he, affineQuotientMap_mk]
    exact (IsLocalization.map_units (FractionCoefficientPolynomial K α β)
      (⟨a, ha⟩ : coefficientDenominators K α β)).map
        (Ideal.Quotient.mk (affineMappedIdeal K α β P))
  · intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (coefficientDenominators K α β) t
    refine ⟨⟨Ideal.Quotient.mk P a,
      ⟨Ideal.Quotient.mk P (s : SplitPolynomial K α β),
        Submonoid.mem_map_of_mem (Ideal.Quotient.mk P) s.property⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ t *
      affineQuotientMap K α β P (Ideal.Quotient.mk P (s : SplitPolynomial K α β)) =
      affineQuotientMap K α β P (Ideal.Quotient.mk P a)
    rw [affineQuotientMap_mk, affineQuotientMap_mk, ← map_mul]
    exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P)) hs
  · intro x y hxy
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_mul] using
      (affineQuotientMap_injective K α β Q hB P hPQ hxy)

end PiExponentSiegel.W23

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add, WithBot.coe_natCast] using hd

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineTranscendenceDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section Normalization

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]

theorem normalization_trdeg_toNat (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] B)
    (hg : Function.Injective g) (hi : g.IsIntegral) :
    (Algebra.trdeg k B).toNat = s := by
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hi⟩
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have ht := congrArg Cardinal.toNat
    (lift_trdeg_add_eq k (MvPolynomial (Fin s) k) B)
  simpa [trdeg_eq_zero] using ht.symm

theorem finiteType_domain_krullDim_eq_trdeg [Algebra.FiniteType k B] :
    ringKrullDim B = ((Algebra.trdeg k B).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin, hdim⟩ := exists_finite_normalization_with_dimension k B
  rw [hdim, normalization_trdeg_toNat k B s g hg hfin.to_isIntegral]

end Normalization

section AlgebraicTower

variable (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
  [IsScalarTower k B C] [FaithfulSMul B C]

theorem trdeg_toNat_eq_of_algebraic_tower [Algebra.IsAlgebraic B C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k B C)
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.toNat_lift] using ht

theorem localization_trdeg_toNat_eq (M : Submonoid B) [IsLocalization M C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  exact trdeg_toNat_eq_of_algebraic_tower k B C

end AlgebraicTower

variable (k F B C : Type*) [Field k] [Field F] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k F] [Algebra k B] [Algebra k C]
  [Algebra B C] [Algebra F C] [IsScalarTower k B C] [IsScalarTower k F C]
  [FaithfulSMul B C] [Algebra.FiniteType k B] [Algebra.FiniteType F C]

theorem coefficient_localization_dimension
    (M : Submonoid B) [IsLocalization M C]
    (hF : Algebra.trdeg k F < Cardinal.aleph0) :
    ringKrullDim C + ((Algebra.trdeg k F).toNat : WithBot ℕ∞) = ringKrullDim B := by
  have hFC : Algebra.trdeg F C < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType (R := F) (S := C)
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k F C)
  rw [Cardinal.toNat_lift_add_lift hF hFC, Cardinal.toNat_lift] at ht
  have hl := localization_trdeg_toNat_eq k B C M
  rw [finiteType_domain_krullDim_eq_trdeg F C,
    finiteType_domain_krullDim_eq_trdeg k B, hl, ← ht, Nat.cast_add]
  exact add_comm _ _

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineResidueTranscendence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open scoped nonZeroDivisors

theorem trdeg_lt_aleph0_of_algebraic_tower
    (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
    [IsScalarTower k B C] [FaithfulSMul B C] [Algebra.IsAlgebraic B C]
    (hB : Algebra.trdeg k B < Cardinal.aleph0) :
    Algebra.trdeg k C < Cardinal.aleph0 := by
  have ht := lift_trdeg_add_eq k B C
  simp only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] at ht
  have hlt := Cardinal.lift_lt_aleph0.mpr hB
  rw [ht] at hlt
  exact Cardinal.lift_lt_aleph0.mp hlt

theorem affine_prime_quotient_dimension_eq_residue_trdeg
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime] :
    ringKrullDim (A ⧸ Q) = ((Algebra.trdeg k Q.ResidueField).toNat : WithBot ℕ∞) := by
  have : FaithfulSMul (A ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      Q.injective_algebraMap_quotient_residueField
  rw [finiteType_domain_krullDim_eq_trdeg k (A ⧸ Q),
    localization_trdeg_toNat_eq k (A ⧸ Q) Q.ResidueField (nonZeroDivisors (A ⧸ Q))]

theorem affine_prime_quotient_dimension_eq_basis_card
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ringKrullDim (A ⧸ Q) = (Nat.card β : WithBot ℕ∞) := by
  have ht := congrArg Cardinal.toNat hb.lift_cardinalMk_eq_trdeg
  simp only [Cardinal.toNat_lift] at ht
  rw [affine_prime_quotient_dimension_eq_residue_trdeg k A Q, ← ht]
  rfl

theorem rational_coefficient_trdeg_toNat (k β : Type*) [Field k] :
    (Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat = Nat.card β := by
  rw [← localization_trdeg_toNat_eq k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k)) (nonZeroDivisors (MvPolynomial β k))]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.toNat_lift, Nat.card]

theorem rational_coefficient_trdeg_lt_aleph0
    (k β : Type*) [Field k] [Finite β] :
    Algebra.trdeg k (FractionRing (MvPolynomial β k)) < Cardinal.aleph0 := by
  have : Algebra.IsAlgebraic (MvPolynomial β k) (FractionRing (MvPolynomial β k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial β k))
  apply trdeg_lt_aleph0_of_algebraic_tower k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k))
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_lt_aleph0,
    Cardinal.mk_lt_aleph0]

theorem coefficient_trdeg_eq_prime_quotient_dimension
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ((Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat : WithBot ℕ∞) =
      ringKrullDim (A ⧸ Q) := by
  rw [rational_coefficient_trdeg_toNat k β,
    affine_prime_quotient_dimension_eq_basis_card k A β Q b hb]

end PiExponentJets.W24

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
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ClosedPointLocalDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W29

section GoingDownHeight

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.HasGoingDown A B]

theorem under_height_le_of_goingDown (P : Ideal B) [P.IsPrime] :
    (P.under A).height ≤ P.height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P.under A, inferInstance⟩ : PrimeSpectrum A),
    PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B)]
  apply Order.height_le
  intro l hl
  let : P.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hl⟩
  obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have h : (L.length : ℕ∞) ≤ Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) :=
    Order.length_le_height (le_of_eq hlast)
  simpa only [hlen] using h

end GoingDownHeight

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

include k

theorem affineDomain_maximal_height (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨d, g, hg, hfin, hdim⟩ := W24.exists_finite_normalization_with_dimension k B
  let A := MvPolynomial (Fin d) k
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hg
  have : IsIntegrallyClosed A := inferInstance
  have : Algebra.HasGoingDown A B := inferInstance
  let p : Ideal A := m.under A
  have : p.IsMaximal := by
    dsimp [p]
    infer_instance
  have hp : p.height = (d : ℕ∞) :=
    PiExponentSiegelAux.W09.polynomialMaximal_height k d p
  have hlo : (d : ℕ∞) ≤ m.height := by
    rw [← hp]
    exact under_height_le_of_goingDown m
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))
  · rw [hdim]
    exact WithBot.coe_le_coe.mpr hlo

theorem closedPoint_local_dimension (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact affineDomain_maximal_height k B m

end PiExponentJets.W29

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffinePrimeDimensionBridge
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24

theorem affine_prime_dimension_of_closedPoint_presentation
    (k B β C : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] [Finite β]
    [CommRing C] [IsDomain C] [Algebra k C] [Algebra B C]
    [Algebra (FractionRing (MvPolynomial β k)) C]
    [IsScalarTower k B C]
    [IsScalarTower k (FractionRing (MvPolynomial β k)) C]
    [FaithfulSMul B C]
    [Algebra.FiniteType (FractionRing (MvPolynomial β k)) C]
    (q : Ideal B) [q.IsPrime]
    (b : β → q.ResidueField) (hb : IsTranscendenceBasis k b)
    (M : Submonoid B) [IsLocalization M C]
    (m : Ideal C) [m.IsMaximal]
    (e : Localization.AtPrime q ≃+* Localization.AtPrime m) :
    (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = ringKrullDim B := by
  have he : (q.height : WithBot ℕ∞) = ringKrullDim C := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      e.ringKrullDim, W29.closedPoint_local_dimension (FractionRing (MvPolynomial β k)) C m]
  have hd := coefficient_localization_dimension k (FractionRing (MvPolynomial β k)) B C M
    (rational_coefficient_trdeg_lt_aleph0 k β)
  rw [coefficient_trdeg_eq_prime_quotient_dimension k B β q b hb] at hd
  exact he.symm ▸ hd

end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientPrimeResidueBasis
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem quotientPrimeResidueAlgEquiv_basis
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q)
    {ι : Type*} (b : ι → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    IsTranscendenceBasis k (fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (b i)) := by
  exact (quotientPrimeResidueAlgEquiv (k := k) P Q hPQ).isTranscendenceBasis hb

end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPrimeDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open PiExponentSiegel.W23 PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

section Split
variable (k α β : Type*) [Field k] [Finite α] [Finite β]
variable (P Q : Ideal (SplitPolynomial k α β)) [P.IsPrime] [Q.IsPrime]

theorem split_polynomial_prime_pair_local_dimension
    (hPQ : P ≤ Q)
    (hB : IsTranscendenceBasis k (splitResidueBeta k α β Q)) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (SplitPolynomial k α β ⧸ Q) =
        ringKrullDim (SplitPolynomial k α β ⧸ P) := by
  let C := FractionCoefficientPolynomial k α β ⧸ affineMappedIdeal k α β P
  let q := quotientParameterPrime P Q hPQ
  let m := quotientParameterPrime (affineMappedIdeal k α β P)
    (closedPolynomialIdeal k α β Q hB)
    (affineMappedIdeal_le_closedPoint k α β Q hB P hPQ)
  let := affineCoefficientAlgebra k α β
  let := affineQuotientAlgebra k α β P
  let := affineQuotient_scalarTower k α β P
  let := affineQuotient_faithfulSMul k α β Q hB P hPQ
  let := affineQuotient_isDomain k α β Q hB P hPQ
  let := affineQuotient_finiteType k α β P
  let := affineQuotient_isLocalization k α β Q hB P hPQ
  let b : β → q.ResidueField :=
    fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (splitResidueBeta k α β Q i)
  have hb : IsTranscendenceBasis k b :=
    quotientPrimeResidueAlgEquiv_basis P Q hPQ (splitResidueBeta k α β Q) hB
  have hd := affine_prime_dimension_of_closedPoint_presentation k
    (SplitPolynomial k α β ⧸ P) β C q b hb
    ((coefficientDenominators k α β).map (Ideal.Quotient.mk P)) m
    (affineClosedQuotientLocalEquiv k α β Q hB P hPQ)
  have hlocal := (localizationQuotientParametersEquiv P Q hPQ).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (quotientParameterPrime P Q hPQ) (Localization.AtPrime (quotientParameterPrime P Q hPQ))] at hlocal
  have hquot := @ringKrullDim_eq_of_ringEquiv
    ((SplitPolynomial k α β ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P))
    (SplitPolynomial k α β ⧸ Q)
    (inferInstance : CommRing ((SplitPolynomial k α β ⧸ P) ⧸
      Q.map (Ideal.Quotient.mk P))).toCommSemiring
    (inferInstance : CommRing (SplitPolynomial k α β ⧸ Q)).toCommSemiring
    (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
  change ringKrullDim ((SplitPolynomial k α β ⧸ P) ⧸ q) =
    ringKrullDim (SplitPolynomial k α β ⧸ Q) at hquot
  rw [← hlocal, hquot] at hd
  exact hd

end Split

section FinVariables
variable (k : Type*) [Field k] (n : ℕ)
variable (P Q : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] [Q.IsPrime]

theorem fin_polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) =
        ringKrullDim (MvPolynomial (Fin n) k ⧸ P) := by
  classical
  obtain ⟨t, j, hfin, hj, hcoord, ht⟩ := exists_coordinate_basis_indices k n Q
  let : Finite t := hfin.to_subtype
  let e := coordinateBasisRenaming j hj k
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hpq : P' ≤ Q' := Ideal.map_mono hPQ
  have hb : IsTranscendenceBasis k (splitResidueBeta k (RemainingCoordinate j) t Q') :=
    coordinateSplitPrime_basis k Q t j hj hcoord ht
  have hd := split_polynomial_prime_pair_local_dimension k (RemainingCoordinate j) t P' Q' hpq hb
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

end FinVariables


end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePrimeHeight
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurvePrimeHeight


open PiExponentJets.W24 PiExponentSiegel.W23
open PiExponentJets.PolynomialLocalResidueResolution

theorem height_add_one_eq_of_quotient_dimension
    (F : Type*) [Field F] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = 1) :
    P.height + 1 = (n : ℕ∞) := by
  have h := fin_polynomial_prime_pair_local_dimension F n ⊥ P bot_le
  have hbot : parameterLocalizedIdeal (⊥ : Ideal (MvPolynomial (Fin n) F)) P = ⊥ :=
    Ideal.map_bot
  rw [hbot] at h
  have hlocal : ringKrullDim (Localization.AtPrime P ⧸ (⊥ : Ideal (Localization.AtPrime P))) =
      ringKrullDim (Localization.AtPrime P) := by
    with_unfolding_all exact (RingEquiv.quotientBot (Localization.AtPrime P)).ringKrullDim
  have hpoly : ringKrullDim (MvPolynomial (Fin n) F ⧸ (⊥ : Ideal (MvPolynomial (Fin n) F))) =
      ringKrullDim (MvPolynomial (Fin n) F) := by
    with_unfolding_all exact (RingEquiv.quotientBot (MvPolynomial (Fin n) F)).ringKrullDim
  rw [hlocal, hpoly, IsLocalization.AtPrime.ringKrullDim_eq_height P
    (Localization.AtPrime P), hdim] at h
  apply WithBot.coe_injective
  simpa only [WithBot.coe_add, WithBot.coe_one,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard,
    Nat.card_fin, zero_add, WithBot.coe_natCast] using h

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem residue_trdeg_toNat_eq {ι : Type*} (z : ι → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (P : Ideal (MvPolynomial ι F)) [P.IsPrime]
    (hker : P = RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom) :
    (Algebra.trdeg F P.ResidueField).toNat = (Algebra.trdeg F E).toNat := by
  have hk : P ≤ RingHom.ker (MvPolynomial.aeval (R := F) z) := by
    intro p hp
    rw [hker] at hp
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp
  have hu : P.primeCompl ≤
      (IsUnit.submonoid E).comap (MvPolynomial.aeval (R := F) z) := by
    intro p hp
    change p ∉ P at hp
    change IsUnit (MvPolynomial.aeval (R := F) z p)
    rw [isUnit_iff_ne_zero]
    simpa only [hker, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp
  let f : P.ResidueField →ₐ[F] E :=
    Ideal.ResidueField.liftₐ P (MvPolynomial.aeval (R := F) z) hk hu
  have hf : Function.Surjective f := by
    apply AlgHom.fieldRange_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨algebraMap (MvPolynomial ι F) P.ResidueField (MvPolynomial.X i), by
      change Ideal.ResidueField.liftₐ P (MvPolynomial.aeval (R := F) z) hk hu
        (algebraMap (MvPolynomial ι F) P.ResidueField (MvPolynomial.X i)) = z i
      rw [Ideal.ResidueField.liftₐ_algebraMap]
      exact MvPolynomial.aeval_X z i⟩
  have he := (AlgEquiv.ofBijective f ⟨f.injective, hf⟩).lift_trdeg_eq
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat he

theorem quotient_dimension_eq_one {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1)
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (hker : P = RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = 1 := by
  rw [PiExponentJets.W24.affine_prime_quotient_dimension_eq_residue_trdeg F _ P,
    residue_trdeg_toNat_eq z hgen P hker, htrdeg]
  simp

theorem kernel_height_add_one_eq {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height + 1 = (n : ℕ∞) := by
  let P := RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom
  let : P.IsPrime := RingHom.ker_isPrime (MvPolynomial.aeval (R := F) z).toRingHom
  exact height_add_one_eq_of_quotient_dimension F n P
    (quotient_dimension_eq_one z hgen htrdeg P rfl)

theorem kernel_height_succ_eq {m : ℕ} (z : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height = (m : ℕ∞) := by
  apply (WithTop.add_right_inj (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
  simpa only [Nat.cast_add, Nat.cast_one] using! kernel_height_add_one_eq z hgen htrdeg

theorem kernel_height_succ_le_q68_oai {m : ℕ} (z : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height ≤ (m : ℕ∞) :=
  (kernel_height_succ_eq z hgen htrdeg).le

end PiExponent.CurvePrimeHeight

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le_q68_oai.{u_1, u_2} := @OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le_q68_oai.{u_1, u_2}
