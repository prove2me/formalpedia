-- Prove2me | solution 1 for OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:21.193227+00:00
-- url     : https://prove2.me/submissions/8b574a97-b8cb-4626-83d4-65c750ed804e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A029
import Definitions.Def_OAIQ068A031
import Definitions.Def_OAIQ068A032
import Definitions.Def_OAIQ068A033

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

theorem SupportBound.mono {ρ : σ → ℝ} {M N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hMN : M ≤ N) : SupportBound ρ N p :=
  fun d hd => (hp d hd).trans hMN

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem supportBound_X (ρ : σ → ℝ) (i : σ) :
    SupportBound ρ (ρ i) (MvPolynomial.X i : MvPolynomial σ E) := by
  classical
  intro d hd
  have he : d = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

theorem fiberDegree_eq_rank {R : Type*} [CommRing R] [IsDomain R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank R S := by
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  exact Ideal.sum_ramification_inertia_eq_finrank p S

theorem fiberDegree_eq_fractionField_rank
    (R K S L : Type*) [CommRing R] [IsDomain R] [Field K]
    [CommRing S] [Field L] [Algebra R S] [Algebra K L]
    [Algebra R K] [Algebra S L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank K L := by
  rw [fiberDegree_eq_rank, IsFractionRing.finrank_eq R K S L]

theorem functionField_fiberDegree
    (F E : Type*) [Field F] [Field E]
    [Algebra F[X] E] [Algebra (RatFunc F) E]
    [IsScalarTower F[X] (RatFunc F) E]
    [FunctionField F E] [Algebra.IsSeparable (RatFunc F) E]
    (p : Ideal F[X]) [p.IsPrime] :
    fiberDegree (FunctionField.ringOfIntegers F E) p =
      Module.finrank (RatFunc F) E := by
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact fiberDegree_eq_fractionField_rank F[X] (RatFunc F)
    (FunctionField.ringOfIntegers F E) E p

theorem parameter_inverse_degree_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    Module.finrank (IntermediateField.adjoin F {f⁻¹}) E =
      Module.finrank (IntermediateField.adjoin F {f}) E := by
  rw [adjoin_inverse_eq]

theorem parameter_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    Module.finrank (RatFunc F) E = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  apply Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental f hf).toRingEquiv (RingEquiv.refl E)
  rfl

theorem parameterFiberDegree_eq {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterFiberDegree f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F) = _
  rw [functionField_fiberDegree]
  exact parameter_finrank f hf

theorem zeroFiber_inertiaDeg_eq_one (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (zeroPrime F)] :
    q.inertiaDeg F[X] = 1 := by
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (zeroPrime F)
  let : Field (F[X] ⧸ zeroPrime F) := Ideal.Quotient.field _
  let : Field (S ⧸ q) := Ideal.Quotient.field _
  let : IsAlgClosed (F[X] ⧸ zeroPrime F) :=
    IsAlgClosed.of_ringEquiv F _ (zeroPrimeQuotientEquiv F).symm
  rw [Ideal.inertiaDeg_eq_of_isMaximal (zeroPrime F) q]
  apply Module.finrank_of_bijective_algebraMap
  apply IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem zeroFiberLength_eq_fiberDegree (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S] :
    zeroFiberLength F S = fiberDegree S (zeroPrime F) := by
  unfold zeroFiberLength fiberDegree
  apply Finset.sum_congr rfl
  intro q _
  rw [zeroFiber_inertiaDeg_eq_one F S q.1, mul_one,
    Ideal.ramificationIdx_eq (zeroPrime F) q.1]
  have hm : (zeroPrime F).map (algebraMap F[X] (Localization.AtPrime q.1)) =
      Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X} := by
    calc
      _ = (Ideal.span {Polynomial.X}).map
          (algebraMap F[X] (Localization.AtPrime q.1)) :=
        congrArg (Ideal.map (algebraMap F[X] (Localization.AtPrime q.1))) (zeroPrime_eq_span_X F)
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun I : Ideal (Localization.AtPrime q.1) =>
    (Module.length (Localization.AtPrime q.1) ((Localization.AtPrime q.1) ⧸ I)).toNat) hm.symm

theorem parameterZeroLength_eq_degree
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroLength f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change zeroFiberLength F (FunctionField.ringOfIntegers F E) = _
  rw [zeroFiberLength_eq_fiberDegree]
  exact parameterFiberDegree_eq f hf

theorem zero_pole_length_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroLength f hf = parameterZeroLength f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroLength_eq_degree, parameterZeroLength_eq_degree, parameter_inverse_degree_eq]

theorem primeFieldValuation_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (Module.length (Localization.AtPrime q.asIdeal)
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E]
  apply CurveLocalOrder.fraction_order_eq_principal_colength
  exact (map_ne_zero_iff _ (IsLocalization.injective A
    q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem primeField_integerOrder_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (primeFieldValuation S E q)
      (Units.mk0 (algebraMap S E a) ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr ha)) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})).toNat : ℤ) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  have ha' : algebraMap S A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A
      q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change primeFieldValuation S E q (algebraMap S E a) = _
  rw [primeFieldValuation_algebraMap S E q a ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (CurveLocalOrder.principal_colength_ne_top ha')
  change CurveLocalOrder.enatToIntegerOrder
    (Module.length A (A ⧸ Ideal.span {algebraMap S A a})) = _
  rw [← hn]
  simp

theorem zeroFiberIntegerOrderSum_eq_length (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] :
    zeroFiberIntegerOrderSum F S E = (zeroFiberLength F S : ℤ) := by
  unfold zeroFiberIntegerOrderSum zeroFiberLength
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hx : algebraMap F[X] S Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero
  have he := primeField_integerOrder_algebraMap S E
    (zeroFiberHeightOne F S q) (algebraMap F[X] S Polynomial.X) hx
  calc
    _ = WeightedCurveDegree.integerOrder
        (primeFieldValuation S E (zeroFiberHeightOne F S q))
        (Units.mk0 (algebraMap S E (algebraMap F[X] S Polynomial.X))
          ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hx)) := by
      congr 1
      ext
      exact IsScalarTower.algebraMap_apply F[X] S E Polynomial.X
    _ = _ := he
    _ = _ := by
      let A := Localization.AtPrime q.1
      have hi : Ideal.span {algebraMap S A (algebraMap F[X] S Polynomial.X)} =
          Ideal.span {algebraMap F[X] A Polynomial.X} :=
        congrArg (fun z : A => Ideal.span {z})
          (IsScalarTower.algebraMap_apply F[X] S A Polynomial.X).symm
      exact congrArg (fun I : Ideal A => ((Module.length A (A ⧸ I)).toNat : ℤ)) hi

theorem parameterZeroOrder_eq_length
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroOrder f hf = (parameterZeroLength f hf : ℤ) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact zeroFiberIntegerOrderSum_eq_length F (FunctionField.ringOfIntegers F E) E

theorem zero_pole_order_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroOrder_eq_length, parameterZeroOrder_eq_length, zero_pole_length_eq]

theorem parameterZeroOrder_eq_sum
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI := parameterZeroPlacesFintype f hf
    parameterZeroOrder f hf =
      ∑ q : parameterZeroPlaces f hf,
        WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
          (Units.mk0 f hf.ne_zero) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  dsimp only [parameterZeroOrder, zeroFiberIntegerOrderSum, parameterPlaceValuation]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ext
  change parameterEmbedding f hf RatFunc.X = f
  exact parameterEmbedding_X f hf

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProductFormula
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

theorem sum_positiveOrders_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∑ p ∈ positivePlaces f hf, placeOrder p (Units.mk0 f hf.ne_zero) = parameterZeroOrder f hf := by
  let := positivePlacesFintype f hf
  let := parameterZeroPlacesFintype f hf
  rw [Finset.sum_subtype (positivePlaces f hf) (mem_positivePlaces f hf)]
  calc
    _ = ∑ q : parameterZeroPlaces f hf,
        placeOrder (parameterNormalizedPlace f hf q) (Units.mk0 f hf.ne_zero) :=
      ((positivePlaceEquivZeroPlaces f hf).symm.sum_comp
        (fun p => placeOrder p.1 (Units.mk0 f hf.ne_zero))).symm
    _ = _ := (parameterZeroOrder_eq_sum f hf).symm

theorem parameterZeroOrder_inst_irrel {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (g : E) (hg : Transcendental F g)
    (i1 i2 : FiniteDimensional (IntermediateField.adjoin F {g}) E) :
    @parameterZeroOrder F E _ _ _ _ g hg i1 = @parameterZeroOrder F E _ _ _ _ g hg i2 := by
  cases Subsingleton.elim i1 i2
  rfl

theorem principalDivisor_degree_zero
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (principalDivisor f hf).sum (fun _ n => n) = 0 := by
  classical
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let z : Eˣ := Units.mk0 f hf.ne_zero
  let zi : Eˣ := Units.mk0 f⁻¹ (transcendental_inverse f hf).ne_zero
  have hiz : zi = z⁻¹ := by ext; simp [zi, z]
  have hsup : (principalDivisor f hf).support ⊆
      positivePlaces f hf ∪ positivePlaces f⁻¹ (transcendental_inverse f hf) := by
    intro p hp
    have hn : placeOrder p z ≠ 0 := by simpa [z] using Finsupp.mem_support_iff.mp hp
    simpa only [Finset.mem_union, mem_positivePlaces, z, Units.val_mk0] using
      (order_ne_zero_iff_positive_or_inverse p z).mp hn
  have hdisj : Disjoint (positivePlaces f hf)
      (positivePlaces f⁻¹ (transcendental_inverse f hf)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hi
    have hp' : 0 < placeOrder p z :=
      (valuation_pos_iff_order_pos p z).mp ((mem_positivePlaces f hf p).mp hp)
    have hi' : 0 < placeOrder p zi :=
      (valuation_pos_iff_order_pos p zi).mp
        ((mem_positivePlaces f⁻¹ (transcendental_inverse f hf) p).mp hi)
    rw [hiz, placeOrder_inv] at hi'
    omega
  rw [Finsupp.sum_of_support_subset _ hsup _ (by intro _ _; rfl)]
  simp only [principalDivisor_apply]
  rw [Finset.sum_union hdisj, sum_positiveOrders_eq]
  have hi : (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p z) =
      -parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
    calc
      _ = ∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), -(placeOrder p zi) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hiz, placeOrder_inv, neg_neg]
      _ = -(∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p zi) :=
        Finset.sum_neg_distrib (fun p => placeOrder p zi)
      _ = _ := congrArg Neg.neg (sum_positiveOrders_eq f⁻¹ (transcendental_inverse f hf))
  change parameterZeroOrder f hf + (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf),
    placeOrder p z) = 0
  have h3 : parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) :=
    (zero_pole_order_eq f hf).trans (parameterZeroOrder_inst_irrel _ _ _ _)
  rw [hi, h3]
  exact add_neg_cancel _

end PiExponent.CurveProductFormula

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchOrderRational
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem rational_weight_le_of_contact
    (v : σ → ℚ) (μ : ℚ) (a : σ → MvPowerSeries τ S)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ))
    (d : σ →₀ ℕ) (n : ℕ)
    (hbound : d.weight (order ∘ a) ≤ (n : ℕ∞)) :
    μ * d.weight v ≤ (n : ℚ) := by
  classical
  have hfinite : ∀ i ∈ d.support, (a i).order ≠ ⊤ := by
    intro i hi
    apply ne_top_of_le_ne_top (by simp : (n : ℕ∞) ≠ ⊤)
    exact (Finsupp.le_weight_of_ne_zero' (order ∘ a)
      (Finsupp.mem_support_iff.mp hi)).trans hbound
  have hsum :
      ((∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) : ℕ∞) =
        d.weight (order ∘ a) := by
    simp only [Nat.cast_sum, Nat.cast_mul, Finsupp.weight_apply,
      Finsupp.sum, Function.comp_apply, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENat.natCast_toNat (hfinite i hi)]
  have hnat : (∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) ≤ n := by
    exact_mod_cast hsum.symm ▸ hbound
  calc
    μ * d.weight v = ∑ i ∈ d.support, (d i : ℚ) * (μ * v i) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ d.support, (d i : ℚ) * ((a i).order.toNat : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hcontact i _ (ENat.natCast_toNat (hfinite i hi)).symm) (by positivity)
    _ ≤ (n : ℚ) := by exact_mod_cast hnat

theorem rational_order_subst_of_jet_vanishing
    (v : σ → ℚ) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a)
    (hjet : ∀ d : σ →₀ ℕ, d.weight v < H → coeff d f = 0)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order := by
  classical
  by_cases htop : (f.subst a).order = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn, ENat.natCast_le_natCast, Nat.ceil_le]
  obtain ⟨d, hd⟩ := ENat.exists_eq_iInf
    (fun d : σ →₀ ℕ => ⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a))
  have hbound : (⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a)) ≤ (n : ℕ∞) :=
    hd.le.trans ((le_weightedOrder_subst (fun _ : τ => 1) ha f).trans hn.ge)
  have hdne : coeff d f ≠ 0 := by
    intro he
    simp [he] at hbound
  have hbound' : d.weight (order ∘ a) ≤ (n : ℕ∞) := by
    simpa [hdne] using hbound
  have hH : H ≤ d.weight v := by
    by_contra! h
    exact hdne (hjet d h)
  exact (mul_le_mul_of_nonneg_left hH hμ).trans
    (rational_weight_le_of_contact v μ a hcontact d n hbound')

theorem rational_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order :=
  rational_order_subst_of_jet_vanishing v μ H hμ f a ha hf hcontact

theorem rational_powerSeries_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → PowerSeries S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ PowerSeries.order (f.subst a) := by
  simp only [PowerSeries.order_eq_order] at hcontact ⊢
  exact rational_order_subst_of_mem_weightedIdeal v hv μ H hμ f a ha hf hcontact

end PiExponent.FormalBranchOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalJetDerivatives
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalJetDerivatives
open MvPowerSeries
open PiExponent.JetGeometry

variable {σ R : Type*} [CommRing R]

theorem pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    pderiv R i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.weight_single, one_nsmul]
  linarith

end PiExponent.FormalJetDerivatives

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalLogJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries
open PiExponent.FormalJetDerivatives

variable {R : Type*} [CommRing R]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

end PiExponent.FormalLogJet

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPoleBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

theorem monomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D : ℝ)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (d : σ →₀ ℕ) (c : C) :
    ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) =
      ∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ) := by
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_sum]
    apply congrArg (fun r : ℝ => (r : WithTop ℝ))
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      Finset.sum_mul, neg_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    (∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ)) ≤
      ∑ i ∈ d.support, v (x i ^ d i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [v.map_pow]
        exact nsmul_le_nsmul_right (hx i) (d i)
    _ ≤ v (algebraMap C K c) + ∑ i ∈ d.support, v (x i ^ d i) :=
      le_add_of_nonneg_left (hc c)

theorem polynomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D N : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (p : MvPolynomial σ C)
    (hp : ∀ d ∈ p.support, Finsupp.weight w d ≤ N) :
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by
  classical
  rw [p.as_sum, map_sum]
  apply v.map_le_sum
  intro d hd
  have hnum : -N * D ≤ -Finsupp.weight w d * D :=
    mul_le_mul_of_nonneg_right (neg_le_neg (hp d hd)) hD
  exact (WithTop.coe_le_coe.mpr hnum).trans (monomial_order_lower v x w D hx hc d _)

end PiExponent.PolynomialPoleBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedPolynomialPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedPolynomialPole
open WeightedCurveDegree PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

theorem coordinate_order_lower (v : AddValuation K (WithTop ℤ))
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι) :
    ((-(w i : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (x i) := by
  by_cases hx : x i = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v (x i) hx]
    apply WithTop.coe_le_coe.mpr
    have h := (div_le_iff₀ (hw i)).mp
      (div_le_weightedPole w (fun j => (coordinateOrder v (x j) : ℚ)) i)
    have hq : -(w i) * coordinatePole v x w ≤ (coordinateOrder v (x i) : ℚ) := by
      dsimp [coordinatePole]
      nlinarith
    exact_mod_cast hq

end PiExponent.WeightedPolynomialPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem contact_sum_le_of_principal_sum
    {P : Type*} (z : P →₀ ℤ) (pole : P →₀ ℚ)
    (hz : z.sum (fun _ n => n) = 0) (hpole_nonneg : ∀ p, 0 ≤ pole p)
    (S : Finset P) (μ : P → ℝ) (N B : ℝ) (hN : 0 ≤ N)
    (hlocal : ∀ p ∈ S, B * μ p ≤ (z p : ℝ))
    (hglobal : ∀ p, -N * (pole p : ℝ) ≤ (z p : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * pole.sum (fun _ n => (n : ℝ)) := by
  classical
  let T := S ∪ z.support ∪ pole.support
  have hST : S ⊆ T := by intro p hp; simp [T, hp]
  have hzT : z.support ⊆ T := by intro p hp; simp [T, hp]
  have hpT : pole.support ⊆ T := by intro p hp; simp [T, hp]
  have hzsum : (∑ p ∈ T, (z p : ℝ)) = 0 := by
    have hh := z.sum_of_support_subset hzT (fun _ n => n) (by simp)
    have hi : (∑ p ∈ T, z p) = 0 := hh.symm.trans hz
    exact_mod_cast hi
  have hpsum : (∑ p ∈ T, (pole p : ℝ)) = pole.sum (fun _ n => (n : ℝ)) :=
    (pole.sum_of_support_subset hpT (fun _ n => (n : ℝ)) (by simp)).symm
  calc
    B * (∑ p ∈ S, μ p) = ∑ p ∈ S, B * μ p := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ S, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hlocal p hp).trans (le_add_of_nonneg_right
        (mul_nonneg hN (by exact_mod_cast hpole_nonneg p)))
    _ ≤ ∑ p ∈ T, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro p hp hnot
      have hh := hglobal p
      linarith
    _ = N * pole.sum (fun _ n => (n : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, zero_add, hpsum]

theorem coordinateOrderDivisor_degree_zero {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : (coordinateOrderDivisor hfinite f).sum (fun _ n => n) = 0 := by
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    rw [coordinateOrderDivisor, dite_eq_left ht]
    exact CurveProductFormula.principalDivisor_degree_zero f ht
  · simp [coordinateOrderDivisor, ht]

theorem weightedDegree_nonneg {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : 0 ≤ weightedDegree hfinite x w := by
  apply Finset.sum_nonneg
  intro p hp
  change (0 : ℝ) ≤ (coordinatePole p.valuation x w : ℚ)
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))

theorem constants_real_nonneg {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) :
    0 ≤ realValuation p.valuation (algebraMap ℂ E c) := by
  have h := (show Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) from
    (Int.cast_mono (R := ℝ)).withTop_map) (p.constants_nonneg c)
  have hz : WithTop.map (fun z : ℤ => (z : ℝ)) (0 : WithTop ℤ) = (0 : WithTop ℝ) := by
    change (((0 : ℤ) : ℝ) : WithTop ℝ) = 0
    norm_num
  rw [hz] at h
  exact h

theorem polynomial_order_lower {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N : ℝ)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0) (p : NormalizedPlace ℂ E) :
    -N * (coordinatePole p.valuation x w : ℝ) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ) := by
  have h := PolynomialPoleBound.polynomial_order_lower (realValuation p.valuation) x
    (fun i => (w i : ℝ)) (coordinatePole p.valuation x w : ℝ) N
    (by exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ)))
    (coordinate_order_lower p.valuation x w hw) (constants_real_nonneg p) f hdegree
  rw [realValuation_of_ne_zero _ _ hne] at h
  exact WithTop.coe_le_coe.mp h

theorem polynomial_contact_sum_le {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * weightedDegree hfinite x w := by
  refine contact_sum_le_of_principal_sum
    (coordinateOrderDivisor hfinite (MvPolynomial.aeval x f)) (weightedPoleDivisor hfinite x w)
    (coordinateOrderDivisor_degree_zero hfinite _) ?_ S μ N B hN ?_ ?_
  · intro p
    exact weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))
  · intro p hp
    simpa only [coordinateOrderDivisor_apply] using hlocal p hp
  · intro p
    simpa only [weightedPoleDivisor_apply, coordinateOrderDivisor_apply] using
      polynomial_order_lower x w hw N f hdegree hne p

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCenters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

open CurveValuationCenter

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

theorem Centered.constant_coordinate {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c) : c = a i := by
  by_contra hne
  have h := ha i
  rw [hc, ← map_sub, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr hne)] at h
  exact lt_irrefl _ h

theorem center_index_unique_of_constant
    (x : ι → E) (a : J → ι → ℂ) (ha : ∀ i, Function.Injective (fun j => a j i))
    (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c)
    (j l : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered x (a j) p) (hq : Centered x (a l) q) : j = l := by
  apply ha i
  exact (hp.constant_coordinate i c hc).symm.trans (hq.constant_coordinate i c hc)

end PiExponent.CurveCenters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryJetDerivatives
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

theorem formalJet_pderiv {n : ℕ} (c : Fin n → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℂ) :
    formalJet c (MvPolynomial.pderiv i p) = MvPowerSeries.pderiv _ i (formalJet c p) := by
  apply FormalLogJet.derivation_map_of_X (formalJet c) (MvPolynomial.pderiv i)
    (MvPowerSeries.pderiv _ i) _ p
  intro j
  by_cases hij : i = j
  · subst j
    simp [formalJet]
  · simp [formalJet, MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_word_vanishing {n : ℕ} (c : Fin n → ℂ)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin n)) :
    formalJet c (OrdinaryDerivatives.word n word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa only [OrdinaryDerivatives.word_nil, List.map_nil, List.sum_nil, sub_zero] using hp
  | cons i word ih =>
    rw [OrdinaryDerivatives.word_cons, formalJet_pderiv]
    have h := FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (formalJet c (OrdinaryDerivatives.word n word p)) ih i
    simpa only [List.map_cons, List.sum_cons, sub_sub, add_comm] using h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryBranchEvaluation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

open MvPowerSeries

theorem branchCoordinates_hasSubst {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (x i - PowerSeries.C (c i)) = 0
  rw [map_sub, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem formalJet_subst_branch {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : MvPolynomial (Fin n) ℂ) :
    subst (branchCoordinates c x) (formalJet c p) = MvPolynomial.aeval x p := by
  let ha := branchCoordinates_hasSubst c x hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, formalJet, MvPolynomial.aeval_X, map_add]
    rw [substAlgHom_X, substAlgHom_apply, subst_C]
    change PowerSeries.C (c i) + (x i - PowerSeries.C (c i)) = x i
    ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem ordinaryWord_branch_order {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (word : List (Fin n)) :
    (⌈mu * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv mu (H - (word.map v).sum) hmu
    (formalJet c (OrdinaryDerivatives.word n word p)) (branchCoordinates c x)
    (branchCoordinates_hasSubst c x hx)
    (formalJet_word_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c x hx] at h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryDVRBranchJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDVRBranchJet
open OrdinaryAuxiliaryJet

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

theorem coordinates_centered {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c x i) = 0 := by
  intro i
  change PowerSeries.constantCoeff
    (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i)) = 0
  rw [map_sub, DVRBranch.expansion_constantCoeff, hx i,
    PowerSeries.constantCoeff_C, sub_self]

theorem contact_pos {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c x hx)

theorem ordinaryWord_addVal_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n)) :
    (⌈contact v c x hnc * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := ordinaryWord_branch_order c (fun i => DVRBranch.expansion ℂ A (x i))
    (fun i => by simpa using hx i) v (fun i => (hv i).le)
    (contact v c x hnc) H (contact_pos v hv c x hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word
  rwa [← expansion_aeval, DVRBranch.expansion_order] at h

theorem ordinaryWord_addVal_toNat_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p))).toNat : ℚ) := by
  have h := ordinaryWord_addVal_lower v hv H c x hx hnc p hp word
  have hn := IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

theorem ordinaryWord_colength_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact ordinaryWord_addVal_toNat_lower v hv H c x hx hnc p hp word hne

end PiExponent.OrdinaryDVRBranchJet
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FibreContact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FibreContact

theorem contact_zero_cons {m : ℕ} (v : Fin (m+1) → ℚ)
    (a : Fin m → PowerSeries ℂ) (ha : ∃ i, a i ≠ 0)
    (hfull : ∃ i, (Fin.cases 0 a : Fin (m+1) → PowerSeries ℂ) i ≠ 0) :
    BranchContact.contact v (Fin.cases 0 a) hfull =
      BranchContact.contact (fun i => v i.succ) a ha := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v i.succ) a ha
    have hh := BranchContact.contact_le v
      (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull i.succ
      (by simpa only [Fin.cases_succ] using hi)
    simp only [Fin.cases_succ] at hh
    exact hh.trans_eq he.symm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains v (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i =>
      have hh := BranchContact.contact_le (fun i => v i.succ) a ha i
        (by simpa only [Fin.cases_succ] using hi)
      simp only [Fin.cases_succ] at he
      exact hh.trans_eq he.symm

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem coordinates_one {m : ℕ} (c : Fin m → ℂ) (x : Fin m → A) :
    DVRBranchJet.coordinates c (1 : A) x =
      Fin.cases 0 (OrdinaryDVRBranchJet.coordinates c x) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates]
  | succ i =>
    simp only [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates,
      Fin.cases_succ, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero]
    rfl

theorem logarithmic_contact_eq_ordinary {m : ℕ} (v : Fin (m+1) → ℚ)
    (c : Fin m → ℂ) (x : Fin m → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    DVRBranchJet.contact v c (1 : A) x (Or.inr hnc) =
      OrdinaryDVRBranchJet.contact (fun i => v i.succ) c x hnc := by
  have ha := OrdinaryDVRBranchJet.coordinates_nonzero c x hnc
  have hb : ∃ i, (Fin.cases (0 : PowerSeries ℂ)
      (OrdinaryDVRBranchJet.coordinates c x) : Fin (m+1) → PowerSeries ℂ) i ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i.succ, by simpa only [Fin.cases_succ] using hi⟩
  have hcongr {b d : Fin (m+1) → PowerSeries ℂ} (he : b = d)
      (hb : ∃ i, b i ≠ 0) (hd : ∃ i, d i ≠ 0) :
      BranchContact.contact v b hb = BranchContact.contact v d hd := by subst d; rfl
  exact (hcongr (coordinates_one c x)
    (DVRBranchJet.coordinates_nonzero c 1 x (Or.inr hnc)) hb).trans
      (contact_zero_cons v (OrdinaryDVRBranchJet.coordinates c x) ha hb)

theorem weightedPole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (t : ℚ) (ht : 0 ≤ t) (hcoord : ∀ i, -z i / w i ≤ t) :
    WeightedCurveDegree.weightedPole w z ≤ t := by
  apply Finset.sup'_le
  intro i hi
  cases i with
  | none => exact ht
  | some i => exact hcoord i

theorem weightedPole_zero_cons {m : ℕ} (w : Fin (m+1) → ℚ) (z : Fin m → ℚ) :
    WeightedCurveDegree.weightedPole w (Fin.cases 0 z) =
      WeightedCurveDegree.weightedPole (fun i => w i.succ) z := by
  let zz : Fin (m+1) → ℚ := Fin.cases 0 z
  let ww : Fin m → ℚ := fun i => w i.succ
  change WeightedCurveDegree.weightedPole w zz = WeightedCurveDegree.weightedPole ww z
  have hz0 : zz 0 = 0 := rfl
  have hzs (i : Fin m) : zz i.succ = z i := rfl
  have hws (i : Fin m) : ww i = w i.succ := rfl
  have hleft0 := WeightedCurveDegree.weightedPole_nonneg w zz
  have hright0 := WeightedCurveDegree.weightedPole_nonneg ww z
  apply le_antisymm
  · apply weightedPole_le w zz _ hright0
    intro i
    cases i using Fin.cases with
    | zero => simpa only [hz0, neg_zero, zero_div] using hright0
    | succ i =>
      rw [hzs]
      have hh := WeightedCurveDegree.div_le_weightedPole ww z i
      rw [hws] at hh
      exact hh
  · apply weightedPole_le ww z _ hleft0
    intro i
    have hh := WeightedCurveDegree.div_le_weightedPole w zz i.succ
    rw [hzs] at hh
    rw [hws]
    exact hh

theorem coordinatePole_one {E : Type*} [Field E] {m : ℕ}
    (val : AddValuation E (WithTop ℤ)) (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    WeightedPolynomialPole.coordinatePole val (Fin.cases 1 x) w =
      WeightedPolynomialPole.coordinatePole val x (fun i => w i.succ) := by
  have h1 : WeightedPolynomialPole.coordinateOrder val 1 = 0 := by
    simp [WeightedPolynomialPole.coordinateOrder]
  have he : (fun i : Fin (m+1) =>
      (WeightedPolynomialPole.coordinateOrder val ((Fin.cases (1 : E) x : Fin (m+1) → E) i) : ℚ)) =
      Fin.cases 0 (fun i => (WeightedPolynomialPole.coordinateOrder val (x i) : ℚ)) := by
    funext i
    cases i using Fin.cases <;> simp [h1]
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact weightedPole_zero_cons w _

theorem weightedDegree_one {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite
      (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ) := by
    ext p
    exact coordinatePole_one p.valuation w x
  unfold CurveContactSum.weightedDegree
  rw [he]

end PiExponent.FibreContact
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

theorem coordinateOrder_aeval_eq_length
    (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ) (hc : Centered z c p)
    (f : MvPolynomial ι ℂ) (hne : MvPolynomial.aeval z f ≠ 0) :
    coordinateOrder p.valuation (MvPolynomial.aeval z f) =
      ((Module.length (ring p) ((ring p) ⧸
        Ideal.span {MvPolynomial.aeval (lift p z c hc) f})).toNat : ℤ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) f ≠ 0 := by
    intro h
    apply hne
    rw [← lift_aeval p z c hc f, h, map_zero]
  rw [coordinateOrder, dite_eq_right hne, valuation_eq_fractionAddValuation p]
  have hu : Units.mk0 (MvPolynomial.aeval z f) hne =
      Units.mk0 (algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f))
        ((map_ne_zero_iff _ (IsFractionRing.injective (ring p) E)).mpr hn) := by
    apply Units.ext
    exact (lift_aeval p z c hc f).symm
  rw [hu]
  exact CurveLocalOrder.integerOrder_field_image_eq_length hn

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem ordinaryWord_field_order_lower {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : MvPolynomial (Fin n) ℂ)
    (hf : OrdinaryAuxiliaryJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval z (OrdinaryDerivatives.word n word f) ≠ 0) :
    ordinaryContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (OrdinaryDerivatives.word n word f)) : ℚ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) (OrdinaryDerivatives.word n word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z c hc, hz, map_zero]
  rw [coordinateOrder_aeval_eq_length p z c hc _ hne]
  simpa only [Int.cast_natCast, ordinaryContact] using
    OrdinaryDVRBranchJet.ordinaryWord_colength_lower v hv H c (lift p z c hc)
      (lift_residue p z c hc) (lift_nonconstant p z c hc hnc) f hf word hn

theorem logContact_one {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) :
    logContact p (Fin.cases (1 : E) x) c hc hnc v =
      ordinaryContact p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc)
        (fun i => v i.succ) := by
  have hy : lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc 0 = 1 :=
    Subtype.ext rfl
  have hx : (fun i => lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc i.succ) =
      lift p x c (fun i => hc i.succ) := rfl
  simpa only [logContact, ordinaryContact, hy, hx] using
    FibreContact.logarithmic_contact_eq_ordinary v c (lift p x c (fun i => hc i.succ))
      (lift_nonconstant p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc))

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactFamily
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] {m K : ℕ}

variable [Algebra ℂ E]

theorem contact_one
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite (fibre x) c hz) :
    letI := hres p
    contact hres hfinite (fibre x) c hz v p =
      PlaceCenteredBranch.ordinaryContact p x
        (c (center hfinite (fibre x) c hz p hp))
        (fun i => centered hfinite (fibre x) c hz p hp i.succ)
        (PlaceCenteredBranch.fibre_nonconstant x _ (nonconstant _ _ hz))
        (fun i => v i.succ) := by
  let := hres p
  dsimp only [contact]
  rw [dite_eq_left hp]
  exact PlaceCenteredBranch.logContact_one p x _
      (centered hfinite (fibre x) c hz p hp) (nonconstant _ _ hz) v

end PiExponent.CurveContactFamily
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateContactBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CoordinateContactBound

open WeightedSliceDegree CurveValuationCenter CurveCenters

theorem supportBound_X_sub_C
    {K ι : Type*} [Field K] (W : ι → ℝ) (i : ι) (hi : 0 ≤ W i) (c : K) :
    SupportBound W (W i) (MvPolynomial.X i - MvPolynomial.C c) := by
  have hX : SupportBound W (W i) (MvPolynomial.X i : MvPolynomial ι K) :=
    supportBound_X W i
  have hC : SupportBound W (W i) (MvPolynomial.C (-c)) := (supportBound_C W (-c)).mono hi
  simpa only [map_neg, sub_eq_add_neg] using hX.add hC

theorem X_mem_rationalWeightedIdeal
    {K ι : Type*} [CommRing K] (V : ι → ℚ) (hV : ∀ i, 0 ≤ V i) (i : ι) :
    MvPowerSeries.X i ∈ (JetGeometry.rationalWeightedIdeal V hV (V i) :
      Ideal (MvPowerSeries ι K)) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X, ite_eq_right]
  intro he
  subst d
  simp [Finsupp.weight_single] at hd

theorem ordinary_formalJet_coordinate_mem {n : ℕ} (c : Fin n → ℂ)
    (V : Fin n → ℚ) (hV : ∀ i, 0 ≤ V i) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) ∈
      JetGeometry.rationalWeightedIdeal V hV (V i) := by
  rw [ordinary_formalJet_X_sub_C]
  exact X_mem_rationalWeightedIdeal V hV i

theorem coordinate_contact_sum_le
    {E : Type*} [Field E] [Algebra ℂ E] {n : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin n → E) (c : Fin n → ℂ)
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (i : Fin n) (hne : x i - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered x c p)
    (hres : ∀ p ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp)
        ⟨i, sub_ne_zero.mp hne⟩ V : ℝ)) :
    (V i : ℝ) * (∑ p ∈ S, μ p) ≤
      (W i : ℝ) * CurveContactSum.weightedDegree hfinite x W := by
  let f : MvPolynomial (Fin n) ℂ := MvPolynomial.X i - MvPolynomial.C (c i)
  have hfe : MvPolynomial.aeval x f = x i - algebraMap ℂ E (c i) := by simp [f]
  apply CurveContactSum.polynomial_contact_sum_le hfinite x W hW
    (W i : ℝ) (V i : ℝ) (by exact_mod_cast (hW i).le) f
    (supportBound_X_sub_C (fun j => (W j : ℝ)) i (by exact_mod_cast (hW i).le) (c i))
    (hfe ▸ hne) S μ
  intro p hp
  let := hres p hp
  rw [hμ p hp]
  have h := PlaceCenteredBranch.ordinaryWord_field_order_lower p x c (hc p hp)
    ⟨i, sub_ne_zero.mp hne⟩ V hV (V i) f
    (ordinary_formalJet_coordinate_mem c V (fun j => (hV j).le) i) []
    (by simpa only [OrdinaryDerivatives.word_nil, hfe] using hne)
  simp only [List.map_nil, List.sum_nil, sub_zero, OrdinaryDerivatives.word_nil] at h
  exact_mod_cast (by simpa only [mul_comm] using h :
    V i * PlaceCenteredBranch.ordinaryContact p x c (hc p hp) ⟨i, sub_ne_zero.mp hne⟩ V ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℚ))

end PiExponent.CoordinateContactBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveInequality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.CurveInequality

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison


theorem no_fibre_excess_of_constant_coordinate_q68_oai
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (hconst : ∃ i : Fin m, ∃ a : ℂ, x i = algebraMap ℂ E a) :
    ¬ CurveContactSum.weightedDegree hfinite (fibre x) w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre x) c hz,
        (contact hres hfinite (fibre x) c hz v p : ℝ) := by
  intro hexcess
  let z : Fin (m+1) → E := fibre x
  let S := places hfinite z c hz
  let μ := fun p => (contact hres hfinite z c hz v p : ℝ)
  have hdeg : CurveContactSum.weightedDegree hfinite (fibre x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) :=
    FibreContact.weightedDegree_one hfinite w x
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p := by
    rw [hdeg] at hexcess
    exact hexcess
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1+sigma := by exact_mod_cast (by linarith : (0 : ℚ)<1+sigma)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨p0,hp0⟩ := hS
  let j0 := center hfinite z c hz p0 hp0
  obtain ⟨i0,a,ha⟩ := hconst
  have hcenters : ∀ p (hp : p ∈ S), center hfinite z c hz p hp = j0 := by
    intro p hp
    exact CurveCenters.center_index_unique_of_constant x c hc i0 a ha
      _ _ p p0 (fun i => centered hfinite z c hz p hp i.succ)
      (fun i => centered hfinite z c hz p0 hp0 i.succ)
  have hcenter : ∀ p ∈ S, CurveCenters.Centered x (c j0) p := by
    intro p hp i
    simpa only [hcenters p hp, z, fibre_succ, fullCenter_succ] using
      centered hfinite z c hz p hp i.succ
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i) :=
    PlaceCenteredBranch.fibre_nonconstant x (c j0) (nonconstant z (c j0) hz)
  obtain ⟨i,hi⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x (c j0)
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ)
    i (sub_ne_zero.mpr hi) S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have heq := contact_one hres hfinite x c hz v p hp
      have hcongr {a b : Fin m → ℂ} (hab : a = b)
          (ha : CurveCenters.Centered x a p) (hna : ∃ i, x i ≠ algebraMap ℂ E (a i))
          (hb : CurveCenters.Centered x b p) (hnb : ∃ i, x i ≠ algebraMap ℂ E (b i)) :
          PlaceCenteredBranch.ordinaryContact p x a ha hna (fun i => v i.succ) =
            PlaceCenteredBranch.ordinaryContact p x b hb hnb (fun i => v i.succ) := by
        subst b
        rfl
      have hcontact := heq.trans (hcongr (congrArg c (hcenters p hp)) _ _
        (hcenter p hp) ⟨i, hi⟩)
      exact congrArg (fun q : ℚ => (q : ℝ)) hcontact)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hex hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

end PiExponent.CurveInequality
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68_oai.{u_1} := @OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68_oai.{u_1}
