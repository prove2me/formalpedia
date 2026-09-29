-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/2d04f90b-f98e-56e8-95bb-108375a032a8

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_two_le_ringKrullDim
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing ModularCurve.UVCrossingModel

namespace R4S195
namespace NodePlace

theorem exists_prime_ne_bot_not_mem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) (π : R) (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ p ≠ ⊥ ∧ π ∉ p := by
  classical
  have hmh : (2 : ℕ∞) ≤ (maximalIdeal R).height := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [← h] at hdim
    have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((maximalIdeal R).height : WithBot ℕ∞) := hdim
    exact WithBot.coe_le_coe.mp h2

  have hI : (Ideal.span {π} : Ideal R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπ
  have hm_not : maximalIdeal R ∉ (Ideal.span {π} : Ideal R).minimalPrimes := by
    intro hmem
    have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {π}) _ hmem
    have h2 : (2 : ℕ∞) ≤ 1 := hmh.trans this
    exact absurd h2 (by decide)

  have hfin := (Ideal.span {π} : Ideal R).finite_minimalPrimes_of_isNoetherianRing
  obtain ⟨p₀, hp₀, -⟩ := Ideal.exists_minimalPrimes_le hI
  set s : Finset (Ideal R) := hfin.toFinset with hs
  have hprime : ∀ i ∈ s, i ≠ p₀ → i ≠ p₀ → (i : Ideal R).IsPrime := by
    intro i hi _ _
    exact (hfin.mem_toFinset.mp hi).1.1

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), ((id i : Ideal R) : Set R)) := by
    intro hsub
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime p₀ p₀ hprime).mp hsub
    have hi' := hfin.mem_toFinset.mp hi
    have hip : i.IsPrime := hi'.1.1
    have : i = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hip.ne_top) hle
    exact hm_not (this ▸ hi')
  rw [Set.not_subset] at havoid
  obtain ⟨x, hxm, hxU⟩ := havoid
  have hxnot : ∀ i ∈ (Ideal.span {π} : Ideal R).minimalPrimes, x ∉ i := by
    intro i hi hxi
    apply hxU
    simp only [Set.mem_iUnion, Finset.mem_coe, id]
    exact ⟨i, hfin.mem_toFinset.mpr hi, hxi⟩
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hxnot p₀ hp₀ (zero_mem _)

  have hxle : (Ideal.span {x} : Ideal R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hxm
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hxle
  have hpP : p.IsPrime := hp.1.1
  have hxp : x ∈ p := hp.1.2 (Ideal.subset_span rfl)
  refine ⟨p, hpP, ?_, ?_⟩
  · rintro rfl
    exact hx0 (by simpa using hxp)
  · intro hπp
    have hle : (Ideal.span {π} : Ideal R) ≤ p := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hle
    have hqP : q.IsPrime := hq.1.1
    have hqne : q ≠ p := fun h => hxnot q hq (h ▸ hxp)
    have hlt : q < p := lt_of_le_of_ne hqp hqne
    have hq0 : (⊥ : Ideal R) < q := by
      rw [bot_lt_iff_ne_bot]
      rintro rfl
      have : π ∈ (⊥ : Ideal R) := hq.1.2 (Ideal.subset_span rfl)
      exact hπ0 (by simpa using this)

    have h1 : (⊥ : Ideal R).height < q.height := Ideal.height_strict_mono_of_isPrime hq0
    have h2 : q.height < p.height := Ideal.height_strict_mono_of_isPrime hlt
    have h3 : p.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hp
    rw [Ideal.height_bot] at h1
    have hq1 : (1 : ℕ∞) ≤ q.height := ENat.one_le_iff_ne_zero.mpr (ne_of_gt h1)
    have : (1 : ℕ∞) < 1 := lt_of_le_of_lt hq1 (lt_of_lt_of_le h2 h3)
    exact lt_irrefl _ this

theorem two_le_ringKrullDim_of_ringEquiv_uvCrossingModel
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (ϖ : C) (hϖ : Irreducible ϖ)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal O) O ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal C) C) ((algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ) ^ E)) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim O := by
  obtain ⟨_, _, _, hirr, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete C ϖ hϖ
  have h2 := ModularCurve.UVCrossingModel.two_le_ringKrullDim
    (algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ) hirr E hE
  rw [← ringKrullDim_eq_of_ringEquiv ι, IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq] at h2
  exact h2

theorem exists_transcendental_finiteDimensional_fieldBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∃ x : ↥(fieldBar q M'), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(fieldBar q M')))
        ↥(fieldBar q M') := by
  haveI : NeZero (q ^ 2 * M') :=
    ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI := hess
  obtain ⟨t, ht, hfd, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional
      (K := AlgebraicClosure ℚ) (F := ↥(fieldBar q M'))).mp hcurve
  exact ⟨t, ht, hfd⟩

theorem isRational_of_transcendental {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) : v.IsRational := by
  set e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    RatFunc.algEquivOfTranscendental x hx with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
      (e.symm.toRingEquiv : ↥(IntermediateField.adjoin K ({x} : Set F)) →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F)
          (algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F (e (e.symm a)) =
      algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a =
        algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

theorem exists_place_isRational_fieldBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (V : ValuationSubring ↥(fieldBar q M'))
    (hK : ∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a ∈ V) (hV : V ≠ ⊤) :
    ∃ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.toValuationSubring = V ∧ P.IsRational := by
  obtain ⟨x, hx, hfd⟩ := exists_transcendental_finiteDimensional_fieldBar q M'
  haveI := hfd
  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    (K := AlgebraicClosure ℚ) x V hK hV
  exact ⟨P, hP, isRational_of_transcendental x hx P⟩

theorem ne_top_of_mem_nonunits {F : Type*} [Field F] (V : ValuationSubring F) {a : F}
    (ha : a ∈ V.nonunits) (ha0 : a ≠ 0) : V ≠ ⊤ := by
  intro hV
  have hlt : V.valuation a < 1 := (ValuationSubring.mem_nonunits_iff (A := V)).mp ha
  have hinv : a⁻¹ ∈ V := by rw [hV]; exact ValuationSubring.mem_top _
  have hle : V.valuation a⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
  have h1 : V.valuation a * V.valuation a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
  have : V.valuation a * V.valuation a⁻¹ < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hlt hle zero_le' zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

theorem mem_of_isIntegral_valuationSubring {F : Type*} [Field F] (V : ValuationSubring F) {y : F}
    (hy : IsIntegral ↥V y) : y ∈ V := by
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := F)).mp hy
  rw [← hz]
  exact z.2

section Residue

noncomputable def constEquiv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P : Place K F) (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

theorem constEquiv_apply {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P : Place K F) (hP : P.IsRational) (c : K) :
    constEquiv P hP c = algebraMap K P.ResidueField c := rfl

theorem evalAt_eq_symm_residue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = (constEquiv P hP).symm (residue P.toValuationSubring ⟨f, hf⟩) := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP hf, ← constEquiv_apply P hP, RingEquiv.apply_symm_apply]

end Residue

end R4S195.NodePlace

open R4S195.NodePlace in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O)
      (ιO : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)),
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ∃ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
        (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
          ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) := by
  intro F₀ hF₀ hLD O instLoc instNoe hOA hOc hfrac E₀ hE₀ hπO ιO hιconst

  clear hιconst hLD hOc hfrac hF₀ hκ hres
  classical

  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  set A₀ : ValuationSubring ↥k₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) with hA₀def
  haveI : IsDiscreteValuationRing ↥A₀ := hdvr
  haveI : HenselianLocalRing ↥A₀ := hhens
  have hmemA₀ : ∀ x : ↥k₀, x ∈ A₀ ↔ (x : AlgebraicClosure ℚ) ∈ A := fun x => Iff.rfl

  set ϖ : ↥A₀ := ⟨π₀, hπ⟩ with hϖdef
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hunif
  have hπ0k : (π₀ : ↥k₀) ≠ 0 := by
    intro h
    apply hirr.ne_zero
    exact Subtype.ext h
  have hπnu : ¬ IsUnit ϖ := hirr.not_isUnit

  have hkF : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun x => rfl

  have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim ↥O :=
    two_le_ringKrullDim_of_ringEquiv_uvCrossingModel (O := ↥O) (C := ↥A₀) ϖ hirr E₀ hE₀ ιO
  clear ιO

  have hπO0 : (⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩ : ↥O) ≠ 0 := by
    intro h
    have : algebraMap ↥k₀ ↥F₀ π₀ = 0 := congrArg Subtype.val h
    exact hπ0k ((map_eq_zero _).mp this)
  have hπOmax : (⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩ : ↥O) ∈ maximalIdeal ↥O := by

    intro hu
    obtain ⟨u, hu⟩ := hu
    have hinvO : algebraMap ↥k₀ ↥F₀ π₀⁻¹ ∈ O := by
      have hval : ((u⁻¹ : (↥O)ˣ) : ↥O).val = (algebraMap ↥k₀ ↥F₀ π₀)⁻¹ := by
        have h1 : ((u : ↥O) : ↥F₀) * ((u⁻¹ : (↥O)ˣ) : ↥O) = 1 := by
          rw [← Subring.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        have hne : (algebraMap ↥k₀ ↥F₀ π₀) ≠ 0 := (map_ne_zero _).mpr hπ0k
        calc ((u⁻¹ : (↥O)ˣ) : ↥O).val = (algebraMap ↥k₀ ↥F₀ π₀)⁻¹ * ((algebraMap ↥k₀ ↥F₀ π₀) *
              ((u⁻¹ : (↥O)ˣ) : ↥O).val) := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
          _ = (algebraMap ↥k₀ ↥F₀ π₀)⁻¹ := by
              rw [show ((u⁻¹ : (↥O)ˣ) : ↥O).val = (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥F₀) from rfl, h1, mul_one]
      rw [map_inv₀, ← hval]
      exact ((u⁻¹ : (↥O)ˣ) : ↥O).2
    have hinvA : (π₀⁻¹ : ↥k₀) ∈ A₀ := (hmemA₀ _).mpr ((hOA _).mpr hinvO)
    apply hπnu
    refine isUnit_iff_exists_inv.mpr ⟨⟨π₀⁻¹, hinvA⟩, ?_⟩
    apply Subtype.ext
    show (π₀ : ↥k₀) * π₀⁻¹ = 1
    exact mul_inv_cancel₀ hπ0k
  obtain ⟨𝔭, h𝔭P, h𝔭0, hπ𝔭⟩ := exists_prime_ne_bot_not_mem hdim _ hπOmax hπO0
  haveI : 𝔭.IsPrime := h𝔭P

  let ιF : ↥F₀ →+* ↥(fieldBar q M') := algebraMap ↥F₀ ↥(fieldBar q M')
  have hιF : Function.Injective ιF := (algebraMap ↥F₀ ↥(fieldBar q M')).injective
  have hιF_apply : ∀ f : ↥F₀, ιF f = (f : ↥(fieldBar q M')) := fun f => rfl
  let O' : Subring ↥(fieldBar q M') := O.map ιF
  let e : ↥O ≃+* ↥O' := O.equivMapOfInjective ιF hιF
  have he : ∀ g : ↥O, ((e g : ↥O') : ↥(fieldBar q M')) = ((g : ↥F₀) : ↥(fieldBar q M')) := fun g =>
    Subring.coe_equivMapOfInjective_apply O ιF hιF g
  let 𝔭' : Ideal ↥O' := 𝔭.comap (e.symm : ↥O' →+* ↥O)
  haveI : 𝔭'.IsPrime := Ideal.comap_isPrime _ _
  have hmem𝔭' : ∀ g : ↥O, e g ∈ 𝔭' ↔ g ∈ 𝔭 := by
    intro g
    show (e.symm : ↥O' →+* ↥O) (e g) ∈ 𝔭 ↔ g ∈ 𝔭
    rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  let L : LocalSubring ↥(fieldBar q M') := LocalSubring.ofPrime O' 𝔭'
  obtain ⟨V, hV⟩ := L.exists_le_valuationSubring
  obtain ⟨hLV, hloc⟩ := hV

  have hOV : ∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ V := by
    intro f hf
    have h1 : (f : ↥(fieldBar q M')) ∈ O' := Subring.mem_map.mpr ⟨f, hf, rfl⟩
    exact hLV (LocalSubring.le_ofPrime O' 𝔭' h1)

  have h𝔭V : ∀ g : ↥O, g ∈ 𝔭 → ((g : ↥F₀) : ↥(fieldBar q M')) ∈ V.nonunits := by
    intro g hg
    have hg' : e g ∈ 𝔭' := (hmem𝔭' g).mpr hg
    have hmax : algebraMap ↥O' ↥L.toSubring (e g) ∈ maximalIdeal ↥L.toSubring :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥L.toSubring 𝔭' (e g)).mpr hg'
    have hnuL : ¬ IsUnit (algebraMap ↥O' ↥L.toSubring (e g)) := hmax
    have hnuV : ¬ IsUnit (Subring.inclusion hLV (algebraMap ↥O' ↥L.toSubring (e g))) :=
      fun hu => hnuL (hloc.map_nonunit _ hu)
    have hcoe : ((Subring.inclusion hLV (algebraMap ↥O' ↥L.toSubring (e g)) : ↥V.toSubring) :
        ↥(fieldBar q M')) = ((g : ↥F₀) : ↥(fieldBar q M')) := by
      rw [Subring.coe_inclusion, ← he g]; rfl
    rw [← hcoe]
    exact (ValuationSubring.coe_mem_nonunits_iff).mpr hnuV

  have hπV : (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ))⁻¹ ∈ V := by
    have hnot : e ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩ ∉ 𝔭' := fun h => hπ𝔭 ((hmem𝔭' _).mp h)
    have huL : IsUnit (algebraMap ↥O' ↥L.toSubring (e ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩)) :=
      IsLocalization.map_units ↥L.toSubring (⟨e ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩, hnot⟩ : 𝔭'.primeCompl)
    have huV : IsUnit (Subring.inclusion hLV (algebraMap ↥O' ↥L.toSubring (e ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩))) := huL.map _
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp huV
    have hcoe : ((Subring.inclusion hLV (algebraMap ↥O' ↥L.toSubring (e ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩)) : ↥V.toSubring) :
        ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) := by
      rw [Subring.coe_inclusion, ← hkF, ← he ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩]; rfl
    have hw' : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) *
        ((w : ↥V.toSubring) : ↥(fieldBar q M')) = 1 := by
      have := congrArg (fun z : ↥V.toSubring => (z : ↥(fieldBar q M'))) hw
      simpa [hcoe] using this
    have hne : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) ≠ 0 := by
      rw [map_ne_zero]
      exact fun h => hπ0k (Subtype.ext h)
    have : ((w : ↥V.toSubring) : ↥(fieldBar q M')) =
        (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ))⁻¹ :=
      eq_inv_of_mul_eq_one_right hw'
    rw [← this]
    exact w.2

  have hkV : ∀ x : ↥k₀, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) ∈ V := by
    intro x
    by_cases hxA : (x : AlgebraicClosure ℚ) ∈ A
    · rw [← hkF]
      exact hOV _ ((hOA x).mp hxA)
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hxA (by simpa using A.zero_mem)
      have hxinv : (x⁻¹ : ↥k₀) ∈ A₀ := by
        rw [hmemA₀]
        rcases A.mem_or_inv_mem (x : AlgebraicClosure ℚ) with h | h
        · exact absurd h hxA
        · simpa using h
      have hxinv0 : (⟨x⁻¹, hxinv⟩ : ↥A₀) ≠ 0 := by
        intro h
        have : (x⁻¹ : ↥k₀) = 0 := congrArg Subtype.val h
        exact (inv_ne_zero hx0) this
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxinv0 hirr

      have hxeq : (x : ↥k₀) = ((u⁻¹ : (↥A₀)ˣ) : ↥A₀) * (π₀⁻¹) ^ n := by
        have h1 : (x⁻¹ : ↥k₀) = ((u : ↥A₀) : ↥k₀) * (π₀ : ↥k₀) ^ n := by
          have := congrArg (fun z : ↥A₀ => (z : ↥k₀)) hu
          simpa using this
        have huinv : (((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥k₀) = (((u : ↥A₀)) : ↥k₀)⁻¹ := by
          have h2 : ((u : ↥A₀) : ↥k₀) * (((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥k₀) = 1 := by
            rw [show ((u : ↥A₀) : ↥k₀) * (((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥k₀) =
              (((u : ↥A₀) * ((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥A₀) : ↥k₀) from rfl, Units.mul_inv]; rfl
          exact (eq_inv_of_mul_eq_one_right h2)
        rw [huinv, inv_pow, ← mul_inv, ← h1, inv_inv]
      have hcoe : (((((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥k₀) * (π₀⁻¹) ^ n : ↥k₀) : AlgebraicClosure ℚ) =
          ((((u⁻¹ : (↥A₀)ˣ) : ↥A₀) : ↥k₀) : AlgebraicClosure ℚ) *
            (((π₀ : ↥k₀) : AlgebraicClosure ℚ)⁻¹) ^ n := by
        push_cast
        rfl
      rw [hxeq, hcoe, map_mul, map_pow, map_inv₀]
      refine V.mul_mem _ _ ?_ (pow_mem hπV n)
      rw [← hkF]
      exact hOV _ ((hOA _).mp ((hmemA₀ _).mp ((u⁻¹ : (↥A₀)ˣ) : ↥A₀).2))

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
  have hKV : ∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a ∈ V := by
    intro a
    obtain ⟨p, hpm, hp0⟩ : IsIntegral ↥k₀ a := (Algebra.IsAlgebraic.isAlgebraic (R := ↥k₀) a).isIntegral

    let φ : ↥k₀ →+* ↥V.toSubring :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).codRestrict
        V.toSubring (fun x => hkV x)
    refine mem_of_isIntegral_valuationSubring V ⟨p.map φ, hpm.map φ, ?_⟩
    have hcomp : (algebraMap ↥V ↥(fieldBar q M')).comp φ =
        (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ)) :=
      RingHom.ext (fun _ => rfl)
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp0, map_zero]

  have hVtop : V ≠ ⊤ := by
    obtain ⟨g, hg𝔭, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭0
    refine ne_top_of_mem_nonunits V (h𝔭V g hg𝔭) ?_
    intro h
    apply hg0
    apply Subtype.ext
    exact hιF (by rw [hιF_apply]; exact h.trans (map_zero ιF).symm)

  obtain ⟨P, hPV, hrat⟩ := exists_place_isRational_fieldBar q M' V hKV hVtop
  have hOP : ∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring := fun f hf => hPV ▸ hOV f hf
  refine ⟨P, hOP, ?_⟩

  let jO : ↥O →+* ↥P.toValuationSubring :=
    (ιF.comp O.subtype).codRestrict P.toValuationSubring.toSubring (fun g => hOP _ g.2)
  have hjO : ∀ g : ↥O, ((jO g : ↥P.toValuationSubring) : ↥(fieldBar q M')) = ((g : ↥F₀) : ↥(fieldBar q M')) :=
    fun g => rfl
  let ψ : ↥O →+* AlgebraicClosure ℚ :=
    ((constEquiv P hrat).symm : P.ResidueField →+* AlgebraicClosure ℚ).comp
      ((residue ↥P.toValuationSubring).comp jO)
  have hψ_apply : ∀ g : ↥O, ψ g = (constEquiv P hrat).symm (residue ↥P.toValuationSubring (jO g)) :=
    fun g => rfl

  have heval : ∀ (f : ↥F₀) (hf : f ∈ O), P.evalAt (f : ↥(fieldBar q M')) = ψ ⟨f, hf⟩ := by
    intro f hf
    rw [evalAt_eq_symm_residue P hrat (hOP f hf), hψ_apply]
    rfl

  have hψconst : ∀ (x : ↥k₀) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O), ψ ⟨_, hxO⟩ = (x : AlgebraicClosure ℚ) := by
    intro x hxO
    rw [hψ_apply]
    apply (constEquiv P hrat).injective
    rw [RingEquiv.apply_symm_apply, constEquiv_apply]
    have hj : jO ⟨_, hxO⟩ = algebraMap (AlgebraicClosure ℚ) ↥P.toValuationSubring (x : AlgebraicClosure ℚ) :=
      Subtype.ext (by rw [hjO, hkF, Place.coe_algebraMap])
    rw [hj]
    exact (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥P.toValuationSubring P.ResidueField _).symm

  have hker : ∀ g : ↥O, ψ g = 0 → g ∈ maximalIdeal ↥O := by
    intro g hg
    have hne : RingHom.ker ψ ≠ ⊤ := RingHom.ker_ne_top ψ
    exact IsLocalRing.le_maximalIdeal hne hg

  let D : LocalSubring (AlgebraicClosure ℚ) := LocalSubring.range ψ
  have hDcarrier : D.toSubring = ψ.range := LocalSubring.range_toSubring ψ
  have hψD : ∀ g : ↥O, ψ g ∈ D.toSubring := fun g => by rw [hDcarrier]; exact ⟨g, rfl⟩
  have hnuD : ∀ g : ↥O, g ∈ maximalIdeal ↥O → ¬ IsUnit (⟨ψ g, hψD g⟩ : ↥D.toSubring) := by
    intro g hg hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwD : (w : AlgebraicClosure ℚ) ∈ ψ.range := by rw [← hDcarrier]; exact w.2
    obtain ⟨g', hg'⟩ := hwD
    have h1 : ψ (g * g') = 1 := by
      rw [map_mul, hg']
      exact congrArg Subtype.val hw
    have h2 : g * g' - 1 ∈ maximalIdeal ↥O := hker _ (by rw [map_sub, h1, map_one, sub_self])
    have h3 : g * g' ∈ maximalIdeal ↥O := Ideal.mul_mem_right _ _ hg
    have : (1 : ↥O) ∈ maximalIdeal ↥O := by
      have := (maximalIdeal ↥O).sub_mem h3 h2
      simpa using this
    exact (maximalIdeal.isMaximal ↥O).ne_top ((Ideal.eq_top_iff_one _).mpr this)

  obtain ⟨W, hW⟩ := D.exists_le_valuationSubring
  obtain ⟨hDW, hlocD⟩ := hW

  have hA₀W : ∀ x : ↥k₀, (x : AlgebraicClosure ℚ) ∈ A → (x : AlgebraicClosure ℚ) ∈ W := by
    intro x hxA
    have hxO : algebraMap ↥k₀ ↥F₀ x ∈ O := (hOA x).mp hxA
    rw [← hψconst x hxO]
    exact hDW (hψD _)

  have hπW : ¬ IsUnit (⟨(π₀ : AlgebraicClosure ℚ), hA₀W π₀ hπ⟩ : ↥W.toSubring) := by
    intro hu
    have hπD : ¬ IsUnit (⟨ψ ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩, hψD _⟩ : ↥D.toSubring) := hnuD _ hπOmax
    apply hπD
    apply hlocD.map_nonunit
    have : Subring.inclusion hDW ⟨ψ ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩, hψD _⟩ = ⟨(π₀ : AlgebraicClosure ℚ), hA₀W π₀ hπ⟩ :=
      Subtype.ext (by rw [Subring.coe_inclusion]; exact hψconst π₀ hπO)
    rw [this]
    exact hu

  have hWk : ∀ x : ↥k₀, algebraMap ↥k₀ (AlgebraicClosure ℚ) x ∈ W ↔ x ∈ A₀ := by
    intro x
    rw [hmemA₀]
    show (x : AlgebraicClosure ℚ) ∈ W ↔ (x : AlgebraicClosure ℚ) ∈ A
    refine ⟨fun hxW => ?_, hA₀W x⟩
    by_contra hxA
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxA (by simpa using A.zero_mem)
    have hxinv : (x⁻¹ : ↥k₀) ∈ A₀ := by
      rw [hmemA₀]
      rcases A.mem_or_inv_mem (x : AlgebraicClosure ℚ) with h | h
      · exact absurd h hxA
      · simpa using h

    have hxnu : (⟨x⁻¹, hxinv⟩ : ↥A₀) ∈ maximalIdeal ↥A₀ := by
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hw' : (x⁻¹ : ↥k₀) * (w : ↥A₀) = 1 := by
        have := congrArg (fun z : ↥A₀ => (z : ↥k₀)) hw
        simpa using this
      have hwx : ((w : ↥A₀) : ↥k₀) = x := by
        have := eq_inv_of_mul_eq_one_right hw'
        simpa using this
      apply hxA
      rw [← hwx]
      exact (hmemA₀ _).mp (w : ↥A₀).2
    rw [hunif, Ideal.mem_span_singleton'] at hxnu
    obtain ⟨y, hy⟩ := hxnu
    have hy' : ((y : ↥A₀) : ↥k₀) * π₀ = x⁻¹ := by
      have := congrArg (fun z : ↥A₀ => (z : ↥k₀)) hy
      simpa using this

    have hyW : ((y : ↥A₀) : AlgebraicClosure ℚ) ∈ W := hA₀W _ ((hmemA₀ _).mp (y : ↥A₀).2)
    apply hπW
    refine isUnit_iff_exists_inv.mpr ⟨⟨((y : ↥A₀) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ),
      W.mul_mem _ _ hyW hxW⟩, Subtype.ext ?_⟩
    show ((π₀ : ↥k₀) : AlgebraicClosure ℚ) * ((((y : ↥A₀) : ↥k₀) : AlgebraicClosure ℚ) *
      ((x : ↥k₀) : AlgebraicClosure ℚ)) = 1
    have hk : (π₀ : ↥k₀) * (((y : ↥A₀) : ↥k₀) * x) = 1 := by
      rw [← mul_assoc, mul_comm (π₀ : ↥k₀), hy', inv_mul_cancel₀ hx0]
    have := congrArg (fun z : ↥k₀ => (z : AlgebraicClosure ℚ)) hk
    simpa using this
  have hAk : ∀ x : ↥k₀, algebraMap ↥k₀ (AlgebraicClosure ℚ) x ∈ A ↔ x ∈ A₀ := fun x => (hmemA₀ x).symm
  haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
  have hWA : W = A :=
    (ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing A₀ A hAk).2 W hWk
  subst hWA

  intro f hfO hnu
  have hfm : (⟨f, hfO⟩ : ↥O) ∈ maximalIdeal ↥O := hnu
  have hmemA : ψ ⟨f, hfO⟩ ∈ W := hDW (hψD _)
  refine ⟨(heval f hfO).symm ▸ hmemA, ?_⟩
  have hnuW : ¬ IsUnit (Subring.inclusion hDW ⟨ψ ⟨f, hfO⟩, hψD _⟩) :=
    fun hu => hnuD _ hfm (hlocD.map_nonunit _ hu)
  have hmax : (⟨ψ ⟨f, hfO⟩, hmemA⟩ : ↥W) ∈ maximalIdeal ↥W := by
    have : Subring.inclusion hDW ⟨ψ ⟨f, hfO⟩, hψD _⟩ = (⟨ψ ⟨f, hfO⟩, hmemA⟩ : ↥W.toSubring) :=
      Subtype.ext rfl
    rw [this] at hnuW
    exact hnuW
  convert hmax using 2
  exact heval f hfO

end S_ModularCurve_FullLevel_exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel (solution)
