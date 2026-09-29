-- Prove2me | solution 1 for ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/40e80c76-35f1-5a26-a79c-a988e03221a7

import Mathlib
import Theorems.Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
import Theorems.Thm_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
import Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

universe u

namespace OrdRegAux

p2m_open "AlgebraicCurve.TwoChartIntegralModel Polynomial AlgebraicGeometry.Polynomial"

theorem essFiniteType_localization_atPrime_comap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (y : Ideal S) [y.IsPrime] :
    letI := (Localization.localRingHom (y.comap (algebraMap R S)) y (algebraMap R S) rfl).toAlgebra
    Algebra.EssFiniteType (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y) := by
  letI := (Localization.localRingHom (y.comap (algebraMap R S)) y (algebraMap R S) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]
      exact IsScalarTower.algebraMap_apply R S (Localization.AtPrime y) r
  haveI : Algebra.EssFiniteType R (Localization.AtPrime y) := inferInstance
  exact Algebra.EssFiniteType.of_comp R (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

private theorem _root_.OrdRegAux.finite_chartAlgFin_of_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'),
      ((algebraMap _ ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) =
        IntermediateField.inclusion hle (x : ↥K')) :
    Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := by
  classical
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨hfin, -⟩ := finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
  letI algP : Algebra A[X] ↥(chartAlgFin A (↥K) j) := (polynomialToChartFin A (↥K) j).toRingHom.toAlgebra
  letI algP' : Algebra A[X] ↥(chartAlgFin A (↥K') j') := (polynomialToChartFin A (↥K') j').toRingHom.toAlgebra
  haveI : Module.Finite A[X] ↥(chartAlgFin A (↥K) j) := hfin
  have key : polynomialToChartFin A (↥K) j =
      (IsScalarTower.toAlgHom A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)).comp
        (polynomialToChartFin A (↥K') j') := by
    apply Polynomial.algHom_ext
    simp only [polynomialToChartFin, AlgHom.comp_apply, Polynomial.aeval_X, IsScalarTower.coe_toAlgHom']
    apply Subtype.ext
    rw [hι, coe_jChartFin, coe_jChartFin, hjj']
  haveI : IsScalarTower A[X] ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq fun P => by
      change polynomialToChartFin A (↥K) j P = algebraMap _ _ (polynomialToChartFin A (↥K') j' P)
      rw [key]
      rfl
  exact Module.Finite.of_restrictScalars_finite A[X] _ _

p2m_export "OrdRegAux" "finite_chartAlgFin_of_floor"

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_localization_le {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) P) ?_
  refine Monotone.strictMono_of_injective (fun P Q h => ?_) (PrimeSpectrum.localization_comap_injective S M)
  change (PrimeSpectrum.comap (algebraMap R S) P).asIdeal ≤ (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal
  exact Ideal.comap_mono h

private lemma le_one_of_add_one_le {a : WithBot ℕ∞} (h : a + 1 ≤ (1 : WithBot ℕ∞) + 1) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at h
      have h3 : n + 1 ≤ 1 + 1 := by exact_mod_cast h
      have h4 : n ≤ 1 := by omega
      rw [← WithBot.coe_one, WithBot.coe_le_coe]
      exact_mod_cast h4

section DimCount

variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

private noncomputable def ψ : A[X] →ₐ[A] ↥(Algebra.adjoin A ({j} : Set K)) :=
  (Polynomial.aeval j).codRestrict (Algebra.adjoin A ({j} : Set K))
    (fun P => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨P, rfl⟩)

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in
private theorem ψ_surjective : Function.Surjective (ψ A K j) := by
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨P, rfl⟩ := hy
  exact ⟨P, Subtype.ext rfl⟩

private noncomputable def ι : ↥(Algebra.adjoin A ({j} : Set K)) →+* ↥(chartAlgFin A K j) :=
  (Subalgebra.inclusion (adjoin_le_chartAlg A K {j})).toRingHom

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in
private theorem ι_isIntegral : (ι A K j).IsIntegral := by
  intro x
  obtain ⟨P, hPm, hP⟩ := (mem_chartAlg_iff A K).mp x.2
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  have h1 := Polynomial.hom_eval₂ P (ι A K j) ((chartAlgFin A K j).val.toRingHom) x
  have h2 : ((chartAlgFin A K j).val.toRingHom).comp (ι A K j) =
      algebraMap ↥(Algebra.adjoin A ({j} : Set K)) K := rfl
  rw [h2] at h1
  exact h1.trans hP

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in

private theorem coe_polynomialToChartFin (P : A[X]) :
    ((polynomialToChartFin A K j P : ↥(chartAlgFin A K j)) : K) = Polynomial.aeval j P := by
  rw [show j = (chartAlgFin A K j).val (jChartFin A K j) from rfl, Polynomial.aeval_algHom_apply]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
omit [Fact (j ≠ 0)] in

theorem ringKrullDim_quotient_localization_eq_one (htj : Transcendental A j)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(chartAlgFin A K j)) [y.IsMaximal] (hyϖ : algebraMap A _ ϖ ∈ y) :
    ringKrullDim (Localization.AtPrime y ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y) (algebraMap A _ ϖ)}) = 1 := by
  classical

  letI algP : Algebra A[X] ↥(chartAlgFin A K j) := (polynomialToChartFin A K j).toRingHom.toAlgebra
  have halg : ∀ P : A[X], algebraMap A[X] ↥(chartAlgFin A K j) P = polynomialToChartFin A K j P := fun _ => rfl
  have hfact : algebraMap A[X] ↥(chartAlgFin A K j) = (ι A K j).comp (ψ A K j).toRingHom :=
    RingHom.ext fun P => Subtype.ext (by rw [halg, coe_polynomialToChartFin]; rfl)
  haveI hint : Algebra.IsIntegral A[X] ↥(chartAlgFin A K j) := ⟨fun b => by
    show (algebraMap A[X] ↥(chartAlgFin A K j)).IsIntegralElem b
    rw [hfact]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ (ψ_surjective A K j))
      (ι_isIntegral A K j) b⟩
  have hinjP : Function.Injective (algebraMap A[X] ↥(chartAlgFin A K j)) := fun P Q h => by
    apply transcendental_iff_injective.mp htj
    have := congrArg (fun b : ↥(chartAlgFin A K j) => (b : K)) h
    simpa only [halg, coe_polynomialToChartFin] using this
  haveI : FaithfulSMul A[X] ↥(chartAlgFin A K j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjP
  have hCϖ : algebraMap A[X] ↥(chartAlgFin A K j) (C ϖ) = algebraMap A _ ϖ := by
    rw [halg, polynomialToChartFin, Polynomial.aeval_C]

  have hϖ0 : ϖ ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field A (by rw [hϖ, Ideal.span_singleton_eq_bot]; exact h)
  have hϖB : algebraMap A ↥(chartAlgFin A K j) ϖ ≠ 0 := by
    rw [← hCϖ]
    exact fun h => (Polynomial.C_ne_zero.mpr hϖ0) (hinjP (by rw [h, map_zero]))
  have hϖS : algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y) (algebraMap A _ ϖ) ≠ 0 := fun h =>
    hϖB (IsLocalization.injective (Localization.AtPrime y) y.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))
  apply le_antisymm
  ·
    apply le_one_of_add_one_le
    calc ringKrullDim (Localization.AtPrime y ⧸ Ideal.span {algebraMap (↥(chartAlgFin A K j))
            (Localization.AtPrime y) (algebraMap A _ ϖ)}) + 1
        ≤ ringKrullDim (Localization.AtPrime y) :=
          ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hϖS)
      _ ≤ ringKrullDim ↥(chartAlgFin A K j) := ringKrullDim_localization_le y.primeCompl _
      _ ≤ ringKrullDim A[X] := by
          calc ringKrullDim ↥(chartAlgFin A K j) ≤ ringKrullDim ↥(Algebra.adjoin A ({j} : Set K)) :=
                ringKrullDim_le_of_isIntegral_ringHom (ι A K j) (ι_isIntegral A K j)
            _ ≤ ringKrullDim A[X] := ringKrullDim_le_of_isIntegral_ringHom (ψ A K j).toRingHom
                (RingHom.isIntegral_of_surjective _ (ψ_surjective A K j))
      _ = ringKrullDim A + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
      _ = 1 + 1 := by rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  ·
    let 𝔭 : Ideal A[X] := Ideal.map (C : A →+* A[X]) (IsLocalRing.maximalIdeal A)
    haveI h𝔭 : 𝔭.IsPrime := Ideal.isPrime_map_C_of_isPrime
    have hCϖ𝔭 : C ϖ ∈ 𝔭 := Ideal.mem_map_of_mem _ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
    haveI : (y.under A[X]).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
    have h𝔭le : 𝔭 ≤ y.under A[X] := by
      rw [Ideal.map_le_iff_le_comap, hϖ, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      show algebraMap A[X] ↥(chartAlgFin A K j) (C ϖ) ∈ y
      rw [hCϖ]; exact hyϖ
    have h𝔭ne : 𝔭 ≠ y.under A[X] := by
      intro h
      have hmax : 𝔭.IsMaximal := h ▸ inferInstance
      have hf : IsField (A[X] ⧸ 𝔭) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭).mp hmax
      exact Polynomial.not_isField (A ⧸ IsLocalRing.maximalIdeal A)
        (MulEquiv.isField hf (Ideal.polynomialQuotientEquivQuotientPolynomial
          (IsLocalRing.maximalIdeal A)).toMulEquiv)
    obtain ⟨Q, hQy, hQprime, hQover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔭) (q := y.under A[X]) y (lt_of_le_of_ne h𝔭le h𝔭ne)
    have hϖQ : algebraMap A ↥(chartAlgFin A K j) ϖ ∈ Q := by
      have : C ϖ ∈ Q.under A[X] := hQover.over ▸ hCϖ𝔭
      rw [← hCϖ]; exact Ideal.mem_comap.mp this

    let P₁ : Ideal (Localization.AtPrime y) := Q.map (algebraMap _ (Localization.AtPrime y))
    haveI : P₁.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime y hQy.le
    have hP₁lt : P₁ < IsLocalRing.maximalIdeal (Localization.AtPrime y) := by
      refine lt_of_le_of_ne ?_ fun h => hQy.ne ?_
      · rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.map_mono hQy.le
      · rw [← Ideal.under_map_of_isLocalizationAtPrime y (S := Localization.AtPrime y) hQy.le]
        show P₁.under _ = y
        rw [h]; exact Localization.AtPrime.under_maximalIdeal
    rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
    refine ⟨⟨⟨P₁, inferInstance⟩, ?_⟩, ⟨⟨IsLocalRing.maximalIdeal _, inferInstance⟩, ?_⟩, hP₁lt⟩
    · rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ hϖQ
    · rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      show _ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hyϖ

end DimCount

section Floor

variable (L : Type) [Field L] [CharZero L] (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
  (j : ↥K) (j' : ↥K') (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
  (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)

set_option synthInstance.maxHeartbeats 1600000 in
include hjj' hFD in
omit [CharZero L] in

theorem isIntegral_inclusion_of_finiteDimensional_adjoin :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  intro x
  haveI := hFD
  have hx : IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) x := Algebra.IsIntegral.isIntegral x
  obtain ⟨P, hPm, hP⟩ := hx

  have hrange : IntermediateField.adjoin L ({j} : Set ↥K) ≤ (IntermediateField.inclusion hle).fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨j', hjj'⟩
  set P' : Polynomial ↥K := P.map (algebraMap ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) with hP'
  have hlifts : P' ∈ Polynomial.lifts (IntermediateField.inclusion hle).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hP', Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := hrange (P.coeff n).2
    exact ⟨y, hy⟩
  obtain ⟨Q, hQP, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hPm.map _)
  refine ⟨Q, hQm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hQP, hP', Polynomial.eval_map, hP]

set_option synthInstance.maxHeartbeats 1600000 in
include hjj' hFD in

theorem isSeparable_of_inclusion :
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Algebra.IsSeparable ↥K' ↥K := by
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : Algebra.IsIntegral ↥K' ↥K :=
    ⟨fun x => isIntegral_inclusion_of_finiteDimensional_adjoin L K K' hle j j' hjj' hFD x⟩
  exact Algebra.IsSeparable.of_integral _ _

end Floor

end OrdRegAux

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL0

theorem algebraMap_stalk_eq_germ {S : Type} [CommRing S] (q : ↥(Spec (CommRingCat.of S))) (s : S) :
    letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
    algebraMap S ((Spec (CommRingCat.of S)).presheaf.stalk q) s =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := by
  show AlgebraicGeometry.StructureSheaf.toStalk S q s = _
  rfl

theorem exists_ringEquiv_stalk_localization_map_germ_eq
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) :
    ∃ E : X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal,
      ∀ a : A, E ((X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S a) := by
  have key : ∀ a : A, (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    intro a
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  let E₁ : X.presheaf.stalk (ι.base q) ≃+* (Spec (CommRingCat.of S)).presheaf.stalk q :=
    (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let E₂ : ((Spec (CommRingCat.of S)).presheaf.stalk q) ≃ₐ[S] Localization.AtPrime q.asIdeal :=
    (AlgebraicGeometry.StructureSheaf.stalkIso S q).symm
  refine ⟨E₁.trans E₂.toRingEquiv, fun a => ?_⟩
  rw [RingEquiv.trans_apply]
  change E₂ ((ι.stalkMap q).hom _) = _
  rw [key a, ← algebraMap_stalk_eq_germ q (algebraMap A S a)]
  exact E₂.commutes _

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem L0_isRegularLocalRing_fibre_of_localization
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (y : ↥(XFin A K j)) (hy : (ιFin A K j).base y = z)
    (h : IsRegularLocalRing (Localization.AtPrime y.asIdeal ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ ϖ)})) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  subst hy
  subst hϖz
  obtain ⟨E, hE⟩ := exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y
  refine @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (Ideal.quotientEquiv _ _ E.symm ?_)
  rw [Ideal.map_span, Set.image_singleton, ← hE ϖ]
  simp only [RingHom.coe_coe, RingEquiv.symm_apply_apply]

theorem exists_ringEquiv_stalk_ιFin_localization (y : ↥(XFin A K j)) :
    ∃ E : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιFin A K j).base y) ≃+*
        Localization.AtPrime y.asIdeal,
      ∀ a : A, E (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιFin A K j).base y) trivial).hom
          (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ a) :=
  exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y

theorem exists_ringEquiv_stalk_ιInf_localization (y : ↥(XInf A K j)) :
    ∃ E : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιInf A K j).base y) ≃+*
        Localization.AtPrime y.asIdeal,
      ∀ a : A, E (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιInf A K j).base y) trivial).hom
          (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap (↥(chartAlgInf A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ a) :=
  exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιInf A K j) (ιInf_toBase A K j) y

end OrdRegL0

open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL1

theorem exists_algHom_chartAlgFin
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j') :
    ∃ ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'),
      (∀ x, ((ι x : ↥(chartAlgFin R F' j')) : F') = φ x) ∧ Function.Injective ι := by
  classical

  have hadj : ∀ x ∈ Algebra.adjoin R ({j} : Set F), φ x ∈ Algebra.adjoin R ({j'} : Set F') := by
    intro x hx
    have : (Algebra.adjoin R ({j} : Set F)).map φ ≤ Algebra.adjoin R ({j'} : Set F') := by
      rw [AlgHom.map_adjoin, Set.image_singleton, hj]
    exact this ⟨x, hx, rfl⟩

  let ψ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥(Algebra.adjoin R ({j'} : Set F')) :=
    (φ.toRingHom.comp (Algebra.adjoin R ({j} : Set F)).val.toRingHom).codRestrict
      (Algebra.adjoin R ({j'} : Set F')).toSubring (fun x => hadj x x.2)

  have hint : ∀ x : F, IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x →
      IsIntegral ↥(Algebra.adjoin R ({j'} : Set F')) (φ x) := by
    intro x hx
    exact hx.map_of_comp_eq ψ φ.toRingHom (by ext y; rfl)
  let ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j') :=
    { toFun := fun x => ⟨φ (x : F), (mem_chartAlg_iff R F').mpr (hint x x.2)⟩,
      map_one' := Subtype.ext (by simp),
      map_mul' := fun x y => Subtype.ext (by simp),
      map_zero' := Subtype.ext (by simp),
      map_add' := fun x y => Subtype.ext (by simp),
      commutes' := fun r => Subtype.ext (by
        show φ (algebraMap R F r) = ((algebraMap R ↥(chartAlgFin R F' j') r : ↥(chartAlgFin R F' j')) : F')
        rw [φ.commutes]; rfl) }
  refine ⟨ι, fun x => rfl, ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact φ.toRingHom.injective (congrArg (fun z : ↥(chartAlgFin R F' j') => (z : F')) hxy :)

end OrdRegL1

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

namespace OrdRegL2

section QuotLoc

variable {B : Type} [CommRing B] (P : Ideal B) [P.IsPrime] (x : B)

@[reducible] noncomputable def quotAlg : Algebra (B ⧸ Ideal.span {x})
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x}) :=
  (Ideal.quotientMap (Ideal.span {algebraMap B (Localization.AtPrime P) x}) (algebraMap B (Localization.AtPrime P))
    (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact Ideal.subset_span rfl)).toAlgebra

theorem isLocalization_quotient_localization [IsDomain B] (Q : Ideal (B ⧸ Ideal.span {x})) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk (Ideal.span {x})) = P) :
    letI := quotAlg P x
    IsLocalization Q.primeCompl
      (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x}) := by
  letI := quotAlg P x
  have halg : ∀ b : B, algebraMap (B ⧸ Ideal.span {x}) (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x})
      (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime P) b) := fun _ => rfl
  have hmemP : ∀ b : B, Ideal.Quotient.mk (Ideal.span {x}) b ∈ Q ↔ b ∈ P := by
    intro b
    rw [← hQ, Ideal.mem_comap]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨s, hs⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hb : b ∉ P := fun h => hs ((hmemP b).mpr h)
    rw [halg]
    exact (IsLocalization.map_units (Localization.AtPrime P) (⟨b, hb⟩ : P.primeCompl)).map _
  ·
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj P.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ (t : B), fun h => t.2 ((hmemP _).mp h)⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ w * algebraMap _ _ (Ideal.Quotient.mk _ (t : B)) = algebraMap _ _ (Ideal.Quotient.mk _ b)
    rw [halg, halg, ← map_mul, hbt]
  ·
    intro a₁ a₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective a₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective a₂
    rw [halg, halg, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj P.primeCompl w

    have h1 : algebraMap B (Localization.AtPrime P) ((t : B) * (b₁ - b₂)) =
        algebraMap B (Localization.AtPrime P) (c * x) := by
      rw [map_mul, map_mul, map_sub, ← hw, ← hct]; ring
    have h2 : (t : B) * (b₁ - b₂) = c * x :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors h1
    refine ⟨⟨Ideal.Quotient.mk _ (t : B), fun h => t.2 ((hmemP _).mp h)⟩, ?_⟩
    show Ideal.Quotient.mk _ (t : B) * Ideal.Quotient.mk _ b₁ = Ideal.Quotient.mk _ (t : B) * Ideal.Quotient.mk _ b₂
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← mul_sub, h2, mul_comm]⟩

end QuotLoc

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_chartAlg_singleton_le
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (s : F) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) ≤ ringKrullDim (Polynomial R) := by
  let ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
    (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
      (fun P => by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨P, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, Subtype.ext rfl⟩
  let ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
    (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F {s})).toRingHom
  have hι : ι.IsIntegral := by
    intro x
    obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2
    refine ⟨P, hPm, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ P ι ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom) x
    have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom).comp ι =
        algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
    rw [h2] at h1
    exact h1.trans hP
  calc ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})
      ≤ ringKrullDim ↥(Algebra.adjoin R ({s} : Set F)) := ringKrullDim_le_of_isIntegral_ringHom ι hι
    _ ≤ ringKrullDim (Polynomial R) :=
        ringKrullDim_le_of_isIntegral_ringHom ψ.toRingHom (RingHom.isIntegral_of_surjective _ hψ)

theorem ringKrullDim_localization_le {R : Type} [CommRing R] (M : Submonoid R) (S : Type) [CommRing S] [Algebra R S]
    [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) P) ?_
  refine Monotone.strictMono_of_injective (fun P Q h => ?_) (PrimeSpectrum.localization_comap_injective S M)
  change (PrimeSpectrum.comap (algebraMap R S) P).asIdeal ≤ (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal
  exact Ideal.comap_mono h

theorem algebraMap_stalk_eq_germ {S : Type} [CommRing S] (q : ↥(Spec (CommRingCat.of S))) (s : S) :
    letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
    algebraMap S ((Spec (CommRingCat.of S)).presheaf.stalk q) s =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := by
  show AlgebraicGeometry.StructureSheaf.toStalk S q s = _
  rfl

theorem exists_ringEquiv_stalk_localization
    {S : Type} [CommRing S] {X : Scheme.{0}} (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (q : ↥(Spec (CommRingCat.of S))) :
    Nonempty (X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal) :=
  ⟨((asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv).trans
    (AlgebraicGeometry.StructureSheaf.stalkIso S q).toRingEquiv.symm⟩

theorem exists_maximal_ringEquiv_localization {R T : Type} [CommRing R] [CommRing T] (e : R ≃+* T)
    (P : Ideal R) [hP : P.IsMaximal] :
    ∃ (Q : Ideal T) (_ : Q.IsMaximal), Nonempty (Localization.AtPrime P ≃+* Localization.AtPrime Q) := by
  let Q : Ideal T := P.comap e.symm.toRingHom
  haveI hQ : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hMQ : P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      exact hy (by simpa [Q, Ideal.mem_comap] using hx)
    · intro hx
      refine ⟨e.symm x, fun hy => hx ?_, by simp⟩
      simp only [Q, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      simpa using hy
  exact ⟨Q, hQ, ⟨IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q) e hMQ⟩⟩

theorem isRegularLocalRing_localization_of_smooth
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    [Smooth (toBase A K j)] (y : ↥(XFin A K j)) :
    IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing A (toBase A K j) ((ιFin A K j).base y)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization (ιFin A K j) y
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ E

theorem isRegularLocalRing_localization_tensor_of_smooth
    (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    (hs : Smooth (toBase A K j)) (k : Type) [Field k] [Algebra A k]
    (Q : Ideal (↥(chartAlgFin A K j) ⊗[A] k)) [hQ : Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  obtain ⟨g, hgo, -, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin A K j k
  haveI := hgo
  haveI hsm : Smooth (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :=
    MorphismProperty.pullback_snd _ _ hs
  let q : ↥(Spec (CommRingCat.of (↥(chartAlgFin A K j) ⊗[A] k))) := ⟨Q, hQ⟩
  have hst := @AlgebraicGeometry.Smooth.isRegularLocalRing_stalk k _ _
    (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) hsm (g.base q)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization g q
  exact @IsRegularLocalRing.of_ringEquiv _ _ hst _ _ E

theorem exists_ringEquiv_fibre_localization_tensor
    (A : Type) [CommRing A] [IsLocalRing A] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (B : Type) [CommRing B] [IsDomain B] [Algebra A B]
    (y : Ideal B) [hy : y.IsMaximal] (hyϖ : algebraMap A B ϖ ∈ y) :
    ∃ (Q₁ : Ideal (B ⊗[A] (IsLocalRing.ResidueField A))) (_ : Q₁.IsMaximal)
      (Q₂ : Ideal ((IsLocalRing.ResidueField A) ⊗[A] B)) (_ : Q₂.IsMaximal),
      Nonempty ((Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) (algebraMap A B ϖ)}) ≃+*
        Localization.AtPrime Q₁) ∧
      Nonempty ((Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) (algebraMap A B ϖ)}) ≃+*
        Localization.AtPrime Q₂) := by
  classical
  set ϖ' : B := algebraMap A B ϖ with hϖ'def
  let ybar : Ideal (B ⧸ Ideal.span {ϖ'}) := y.map (Ideal.Quotient.mk _)
  haveI hybar : ybar.IsPrime := by
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem]; exact hyϖ
  have hycomap : ybar.comap (Ideal.Quotient.mk (Ideal.span {ϖ'})) = y := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left, Ideal.span_singleton_le_iff_mem]
    exact hyϖ
  haveI hybarmax : ybar.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hy).resolve_left
      (fun h => hy.ne_top (by
        have := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {ϖ'}))) h
        rw [hycomap, Ideal.comap_top] at this
        exact this))
  letI := quotAlg y ϖ'
  haveI hloc := isLocalization_quotient_localization y ϖ' ybar hycomap
  let Efib : (Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) ϖ'}) ≃+* Localization.AtPrime ybar :=
    (IsLocalization.algEquiv ybar.primeCompl
      (Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) ϖ'}) (Localization.AtPrime ybar)).toRingEquiv
  have hmapϖ : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = Ideal.span {ϖ'} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  let e₁ : (B ⧸ Ideal.span {ϖ'}) ≃+* B ⊗[A] (IsLocalRing.ResidueField A) :=
    (Ideal.quotEquivOfEq hmapϖ.symm).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv
  let e₂ : (B ⧸ Ideal.span {ϖ'}) ≃+* (IsLocalRing.ResidueField A) ⊗[A] B :=
    e₁.trans (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A)).toRingEquiv
  obtain ⟨Q₁, hQ₁, ⟨E₁⟩⟩ := exists_maximal_ringEquiv_localization e₁ ybar
  obtain ⟨Q₂, hQ₂, ⟨E₂⟩⟩ := exists_maximal_ringEquiv_localization e₂ ybar
  exact ⟨Q₁, hQ₁, Q₂, hQ₂, ⟨Efib.trans E₁⟩, ⟨Efib.trans E₂⟩⟩

set_option maxHeartbeats 3200000 in

theorem L2_floor_regular_of_smooth
    (L : Type) [Field L] [CharZero L]
    (K' : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K'] [IsScalarTower A L ↥K'] (j' : ↥K') [Fact (j' ≠ 0)]
    (htj : Transcendental A j')
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y' : Ideal ↥(chartAlgFin A (↥K') j')) [hy' : y'.IsMaximal] (hy'ϖ : algebraMap A ↥(chartAlgFin A (↥K') j') ϖ ∈ y') :
    IsRegularLocalRing (Localization.AtPrime y') ∧
    ringKrullDim (Localization.AtPrime y') ≤ 2 ∧
    IsRegularLocalRing (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) ∧
    ringKrullDim (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) = 1 ∧
    IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) := by
  classical
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsIntegral.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
  have hFT := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') j' htj hFD hsep
  haveI := hsmooth

  have hreg1 : IsRegularLocalRing (Localization.AtPrime y') :=
    isRegularLocalRing_localization_of_smooth A (↥K') j' (⟨y', hy'.isPrime⟩ : ↥(XFin A (↥K') j'))

  have hdim2 : ringKrullDim (Localization.AtPrime y') ≤ 2 := by
    refine (ringKrullDim_localization_le y'.primeCompl (Localization.AtPrime y')).trans ?_
    refine (ringKrullDim_chartAlg_singleton_le A (↥K') (j' : ↥K')).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      (IsPrincipalIdealRing.ringKrullDim_eq_one A) (IsDiscreteValuationRing.not_isField A)]
    norm_num

  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, ⟨E₁⟩, ⟨E₂⟩⟩ := exists_ringEquiv_fibre_localization_tensor A ϖ hϖ ↥(chartAlgFin A (↥K') j') y' hy'ϖ

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖκ : algebraMap A (IsLocalRing.ResidueField A) ϖ = 0 := by
    rw [show algebraMap A (IsLocalRing.ResidueField A) ϖ = IsLocalRing.residue A ϖ from rfl, IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hinj : Function.Injective (Polynomial.aeval (R := A) (j' : ↥K')) := transcendental_iff_injective.mp htj
  have hrange : (Polynomial.aeval (R := A) (j' : ↥K')).range = Algebra.adjoin A ({(j' : ↥K')} : Set ↥K') :=
    (Algebra.adjoin_singleton_eq_range_aeval A (j' : ↥K')).symm
  let eR : Polynomial A ≃ₐ[A] ↥(Algebra.adjoin A ({(j' : ↥K')} : Set ↥K')) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := A) (j' : ↥K')) hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have hdimQ₂ : ringKrullDim (Localization.AtPrime Q₂) = 1 :=
    Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hirr
      (Algebra.adjoin A ({(j' : ↥K')} : Set ↥K')) (chartAlgFin A (↥K') j') eR
      (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K') {(j' : ↥K')})
      (fun a => (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K')).mp a.2)
      hFT.1 (AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') {(j' : ↥K')})
      (IsLocalRing.ResidueField A) hϖκ Q₂

  have hregQ₁ : IsRegularLocalRing (Localization.AtPrime Q₁) :=
    isRegularLocalRing_localization_tensor_of_smooth A (↥K') j' hsmooth (IsLocalRing.ResidueField A) Q₁

  have halgϖ : algebraMap A (Localization.AtPrime y') ϖ =
      algebraMap ↥(chartAlgFin A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ) := IsScalarTower.algebraMap_apply _ _ _ _
  rw [halgϖ]
  have hregfib := @IsRegularLocalRing.of_ringEquiv _ _ hregQ₁ _ _ E₁.symm
  haveI := hregfib
  have hdom : IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap ↥(chartAlgFin A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ)}) :=
    @IsRegularLocalRing.isDomain _ _ hregfib
  exact ⟨hreg1, hdim2, hregfib, (ringKrullDim_eq_of_ringEquiv E₂).trans hdimQ₂, hdom⟩

end OrdRegL2

open _root_.Algebra _root_.CategoryTheory.Algebra _root_.TensorProduct.Algebra in

theorem L3_localization
    {A' B : Type u} [CommRing A'] [CommRing B] [IsDomain A'] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A' B] [Module.Finite A' B] [FaithfulSMul A' B] (y' : Ideal A') [y'.IsPrime] :
    Module.Finite (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsIntegrallyClosed (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    FaithfulSMul (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
  have hinj := FaithfulSMul.algebraMap_injective A' B
  have hM : algebraMapSubmonoid B y'.primeCompl ≤ nonZeroDivisors B := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨a, ha, h0⟩
    have : a = 0 := hinj (by rw [h0, map_zero])
    exact ha (this ▸ y'.zero_mem)
  haveI : IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) := IsLocalization.isDomain_localization hM
  refine ⟨Module.Finite.of_isLocalization A' B y'.primeCompl, isIntegrallyClosed_of_isLocalization (Localization (algebraMapSubmonoid B y'.primeCompl)) (algebraMapSubmonoid B y'.primeCompl) hM,
    inferInstance, ?_⟩

  rw [faithfulSMul_iff_algebraMap_injective]
  have : algebraMap (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) =
      IsLocalization.map (T := algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl))
        (algebraMap A' B) (Submonoid.le_comap_map y'.primeCompl) := by
    apply IsLocalization.ringHom_ext y'.primeCompl
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [this]
  haveI : IsLocalization (y'.primeCompl.map (algebraMap A' B)) (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
    exact (Localization.isLocalization : IsLocalization (algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl)))
  exact IsLocalization.map_injective_of_injective (M := y'.primeCompl) (S := Localization.AtPrime y')
    (Q := Localization (algebraMapSubmonoid B y'.primeCompl)) (g := algebraMap A' B) hinj

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL4

theorem mem_minimalPrimes_span_singleton_of_height_eq_one
    {B : Type u} [CommRing B] (x : B) (hx : x ∈ nonZeroDivisors B)
    (Q : Ideal B) [Q.IsPrime] (hxQ : x ∈ Q) (hQ : Q.height = 1) :
    Q ∈ (Ideal.span {x}).minimalPrimes := by
  have hle : Ideal.span {x} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hxQ
  haveI : Q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hQ]; exact ENat.one_lt_top))
  apply Ideal.mem_minimalPrimes_of_height_eq hle
  rw [hQ]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hx

end OrdRegL4

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL0

theorem germ_mem_maximalIdeal_iff_of_chart
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) (a : A) :
    (X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (ι.base q)) ↔
      algebraMap A S a ∈ q.asIdeal := by
  have key : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (ι.stalkMap q).hom, key,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk S q
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal (algebraMap A S a)

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem algebraMap_mem_asIdeal_of_germ_mem_maximalIdeal
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z))
    (y : ↥(XFin A K j)) (hy : (ιFin A K j).base y = z) :
    algebraMap A (↥(chartAlgFin A K j)) ϖ ∈ y.asIdeal := by
  subst hy
  subst hϖz
  exact (germ_mem_maximalIdeal_iff_of_chart (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y ϖ).mp hz

theorem germ_mem_maximalIdeal_of_algebraMap_mem_asIdeal
    (ϖ : A) (y : ↥(XFin A K j)) (hy : algebraMap A (↥(chartAlgFin A K j)) ϖ ∈ y.asIdeal) :
    ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιFin A K j).base y) trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιFin A K j).base y)) :=
  (germ_mem_maximalIdeal_iff_of_chart (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y ϖ).mpr hy

end OrdRegL0

p2m_open "Algebra CategoryTheory.Algebra TensorProduct.Algebra IsLocalRing"

namespace OrdRegS3

theorem L3_localization
    {A' B : Type u} [CommRing A'] [CommRing B] [IsDomain A'] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A' B] [Module.Finite A' B] [FaithfulSMul A' B] (y' : Ideal A') [y'.IsPrime] :
    Module.Finite (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsIntegrallyClosed (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    FaithfulSMul (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
  have hinj := FaithfulSMul.algebraMap_injective A' B
  have hM : algebraMapSubmonoid B y'.primeCompl ≤ nonZeroDivisors B := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨a, ha, h0⟩
    have : a = 0 := hinj (by rw [h0, map_zero])
    exact ha (this ▸ y'.zero_mem)
  haveI : IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) := IsLocalization.isDomain_localization hM
  refine ⟨Module.Finite.of_isLocalization A' B y'.primeCompl, isIntegrallyClosed_of_isLocalization (Localization (algebraMapSubmonoid B y'.primeCompl)) (algebraMapSubmonoid B y'.primeCompl) hM,
    inferInstance, ?_⟩
  rw [faithfulSMul_iff_algebraMap_injective]
  have : algebraMap (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) =
      IsLocalization.map (T := algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl))
        (algebraMap A' B) (Submonoid.le_comap_map y'.primeCompl) := by
    apply IsLocalization.ringHom_ext y'.primeCompl
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [this]
  haveI : IsLocalization (y'.primeCompl.map (algebraMap A' B)) (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
    exact (Localization.isLocalization : IsLocalization (algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl)))
  exact IsLocalization.map_injective_of_injective (M := y'.primeCompl) (S := Localization.AtPrime y')
    (Q := Localization (algebraMapSubmonoid B y'.primeCompl)) (g := algebraMap A' B) hinj

theorem formallyUnramified_localization_of_forall_height_one
    (A' : Type u) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (K' : Type u) [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A' B] [Module.Finite A' B] [FaithfulSMul A' B]
    (L' : Type u) [Field L'] [Algebra B L'] [IsFractionRing B L'] [Algebra K' L'] [Algebra A' L']
    [IsScalarTower A' K' L'] [IsScalarTower A' B L'] [Algebra.IsSeparable K' L']
    (y : Ideal B) [y.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime (y.comap (algebraMap A' B))))
    (hdim : ringKrullDim (Localization.AtPrime (y.comap (algebraMap A' B))) ≤ 2)
    (h1 : ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ y → Q.height = 1 → Algebra.IsUnramifiedAt A' Q) :
    letI := (Localization.localRingHom (y.comap (algebraMap A' B)) y (algebraMap A' B) rfl).toAlgebra
    Algebra.FormallyUnramified (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime y) := by
  classical
  haveI hyp : (y.comap (algebraMap A' B)).IsPrime := Ideal.comap_isPrime _ y
  letI algRy : Algebra (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime y) :=
    (Localization.localRingHom (y.comap (algebraMap A' B)) y (algebraMap A' B) rfl).toAlgebra

  obtain ⟨hfin, hic, hdom, hfaith⟩ := L3_localization (A' := A') (B := B) (y.comap (algebraMap A' B))
  haveI := hfin; haveI := hic; haveI := hdom; haveI := hfaith; haveI := hreg
  haveI hfree : Module.Free (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) :=
    Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two (Localization.AtPrime (y.comap (algebraMap A' B))) hdim (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl))

  have hMle : ((y.comap (algebraMap A' B))).primeCompl ≤ nonZeroDivisors A' := Ideal.primeCompl_le_nonZeroDivisors _
  have hinjAB := FaithfulSMul.algebraMap_injective A' B
  have hMBle : algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl ≤ nonZeroDivisors B := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨a, ha, h0⟩
    have : a = 0 := hinjAB (by rw [h0, map_zero])
    exact ha (this ▸ ((y.comap (algebraMap A' B))).zero_mem)
  letI algRK : Algebra (Localization.AtPrime (y.comap (algebraMap A' B))) K' :=
    (IsLocalization.map (M := ((y.comap (algebraMap A' B))).primeCompl) (T := nonZeroDivisors A') K' (RingHom.id A')
      (show ((y.comap (algebraMap A' B))).primeCompl ≤ (nonZeroDivisors A').comap (RingHom.id A') from hMle)).toAlgebra
  haveI towARK : IsScalarTower A' (Localization.AtPrime (y.comap (algebraMap A' B))) K' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A' K' a = IsLocalization.map K' (RingHom.id A') _ (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a)
    rw [IsLocalization.map_eq]; rfl)
  haveI frRK : IsFractionRing (Localization.AtPrime (y.comap (algebraMap A' B))) K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization ((y.comap (algebraMap A' B))).primeCompl (Localization.AtPrime (y.comap (algebraMap A' B))) K'
  letI algBL : Algebra (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' :=
    (IsLocalization.map (M := algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) (T := nonZeroDivisors B) L' (RingHom.id B)
      (show algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl ≤ (nonZeroDivisors B).comap (RingHom.id B) from hMBle)).toAlgebra
  haveI towBBL : IsScalarTower B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B L' b = IsLocalization.map L' (RingHom.id B) _ (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) b)
    rw [IsLocalization.map_eq]; rfl)
  haveI frBL : IsFractionRing (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L'
  letI algRL : Algebra (Localization.AtPrime (y.comap (algebraMap A' B))) L' := ((algebraMap K' L').comp (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) K')).toAlgebra
  haveI towRKL : IsScalarTower (Localization.AtPrime (y.comap (algebraMap A' B))) K' L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI towRBL : IsScalarTower (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have heq : (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) L') = (algebraMap (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L').comp (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl))) := by
      apply IsLocalization.ringHom_ext ((y.comap (algebraMap A' B))).primeCompl
      ext a
      show algebraMap K' L' (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) K' (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a)) =
        algebraMap (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a))
      rw [← IsScalarTower.algebraMap_apply A' (Localization.AtPrime (y.comap (algebraMap A' B))) K', ← IsScalarTower.algebraMap_apply A' K' L',
        ← IsScalarTower.algebraMap_apply A' (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)), IsScalarTower.algebraMap_apply A' B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)),
        ← IsScalarTower.algebraMap_apply B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L', ← IsScalarTower.algebraMap_apply A' B L']
    exact congrArg (fun f => f r) heq |>.trans rfl

  have hdisj : Disjoint (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl : Set B) (y : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsy
    exact hs hsy
  let P : Ideal (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) := y.map (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)))
  haveI hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) y inferInstance hdisj
  have hPy : P.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl))) = y :=
    IsLocalization.under_map_of_isPrime_disjoint (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) inferInstance hdisj
  haveI hicR : IsIntegrallyClosed (Localization.AtPrime (y.comap (algebraMap A' B))) := isIntegrallyClosed_of_isLocalization (Localization.AtPrime (y.comap (algebraMap A' B))) ((y.comap (algebraMap A' B))).primeCompl hMle

  have hpur : Algebra.IsUnramifiedAt (Localization.AtPrime (y.comap (algebraMap A' B))) P := by
    refine Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed (Localization.AtPrime (y.comap (algebraMap A' B))) K' (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) L' P ?_
    intro Q' _ hQ'P hQ'1

    haveI : (Q'.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)))).IsPrime := Ideal.comap_isPrime _ Q'
    have hQy : Q'.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl))) ≤ y := (Ideal.comap_mono hQ'P).trans hPy.le
    have hQ1 : (Q'.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)))).height = 1 := by
      rw [← hQ'1]; exact IsLocalization.height_under (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) Q'
    have hunr := h1 (Q'.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)))) hQy hQ1

    let e : Localization.AtPrime (Q'.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)))) ≃ₐ[B] Localization.AtPrime Q' :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) Q'
    haveI : Algebra.FormallyUnramified A' (Localization.AtPrime Q') :=
      Algebra.FormallyUnramified.of_equiv (e.restrictScalars A')
    exact Algebra.FormallyUnramified.of_restrictScalars (R := A') (A := (Localization.AtPrime (y.comap (algebraMap A' B)))) (B := Localization.AtPrime Q')

  have hsub : P.primeCompl.comap (algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl))) = y.primeCompl := by
    ext b
    show algebraMap B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) b ∉ P ↔ b ∉ y
    rw [← Ideal.mem_comap, hPy]
  haveI hlocy : IsLocalization y.primeCompl (Localization.AtPrime P) :=
    hsub ▸ (IsLocalization.localization_localization_isLocalization_of_has_all_units
      (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl) P.primeCompl (Localization.AtPrime P)
      (fun x hx hxP => hP.ne_top (P.eq_top_of_isUnit_mem hxP hx)))
  let eY : Localization.AtPrime y ≃ₐ[B] Localization.AtPrime P :=
    IsLocalization.algEquiv y.primeCompl (Localization.AtPrime y) (Localization.AtPrime P)
  haveI := hpur

  have hcomm : ∀ r : (Localization.AtPrime (y.comap (algebraMap A' B))), eY.symm (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime P) r) =
      algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime y) r := by
    intro r
    have heq : (eY.symm : Localization.AtPrime P →+* Localization.AtPrime y).comp (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime P)) =
        algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime y) := by
      apply IsLocalization.ringHom_ext ((y.comap (algebraMap A' B))).primeCompl
      ext a
      show eY.symm (algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime P) (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a)) =
        Localization.localRingHom (y.comap (algebraMap A' B)) y (algebraMap A' B) rfl (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a)
      rw [Localization.localRingHom_to_map]
      have h1 : algebraMap (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization.AtPrime P) (algebraMap A' (Localization.AtPrime (y.comap (algebraMap A' B))) a) =
          algebraMap B (Localization.AtPrime P) (algebraMap A' B a) := by
        rw [IsScalarTower.algebraMap_apply (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) (Localization.AtPrime P),
          ← IsScalarTower.algebraMap_apply A' (Localization.AtPrime (y.comap (algebraMap A' B))) (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)), IsScalarTower.algebraMap_apply A' B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)),
          ← IsScalarTower.algebraMap_apply B (Localization (algebraMapSubmonoid B ((y.comap (algebraMap A' B))).primeCompl)) (Localization.AtPrime P)]
      rw [h1]
      exact eY.symm.commutes _
    exact congrArg (fun f => f r) heq
  let eR : Localization.AtPrime P ≃ₐ[(Localization.AtPrime (y.comap (algebraMap A' B)))] Localization.AtPrime y :=
    AlgEquiv.ofRingEquiv (f := eY.symm.toRingEquiv) hcomm
  exact Algebra.FormallyUnramified.of_equiv eR

end OrdRegS3

namespace OrdRegSeams
open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

private theorem _root_.OrdRegSeams.finite_chartAlgFin_of_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)] [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'), ((algebraMap _ ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle (x : ↥K')) :
    Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
  OrdRegAux.finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hι

p2m_export "OrdRegSeams" "finite_chartAlgFin_of_floor"
end OrdRegSeams

namespace OrdRegPort

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ringLevel_of_h1
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(chartAlgFin A (↥K) j)) [hmax : y.IsMaximal]
    (hyϖ : algebraMap A (↥(chartAlgFin A (↥K) j)) ϖ ∈ y)

    (K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') [Fact (j' ≠ 0)] (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj' : Transcendental A j')
    (hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'),
      ((algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) =
        IntermediateField.inclusion hle (x : ↥K'))

    (h1 : ∀ (Q : Ideal ↥(chartAlgFin A (↥K) j)) [Q.IsPrime], Q ≤ y → Q.height = 1 →
      Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K') j') Q) :
    IsRegularLocalRing (Localization.AtPrime y ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A (↥K) j)) (Localization.AtPrime y) (algebraMap A _ ϖ)}) := by
  classical
  haveI := hFD
  haveI := hFD'
  haveI hsepj : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  have hιinj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) := by
    intro a b hab
    have h := congrArg (fun z : ↥(chartAlgFin A (↥K) j) => (z : ↥K)) hab
    simp only [hι] at h
    exact Subtype.ext ((IntermediateField.inclusion hle).injective h)
  haveI hfinAA : Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    OrdRegSeams.finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hι

  let y' : Ideal ↥(chartAlgFin A (↥K') j') := y.comap (algebraMap _ _)
  haveI : Algebra.IsIntegral ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := inferInstance
  haveI hy'max : y'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
  have hy'ϖ : algebraMap A ↥(chartAlgFin A (↥K') j') ϖ ∈ y' := by
    show algebraMap _ (↥(chartAlgFin A (↥K) j)) (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ) ∈ y
    rw [← IsScalarTower.algebraMap_apply]; exact hyϖ
  obtain ⟨hRreg, hRdim, hRfib, hRfib1, hRdom⟩ :=
    OrdRegL2.L2_floor_regular_of_smooth L K' A j' htj' hFD' hsmooth ϖ hϖ y' hy'ϖ

  letI hRS : Algebra (Localization.AtPrime y') (Localization.AtPrime y) :=
    (Localization.localRingHom y' y (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) rfl).toAlgebra
  haveI : IsLocalHom (algebraMap (Localization.AtPrime y') (Localization.AtPrime y)) :=
    Localization.isLocalHom_localRingHom y' y _ rfl
  haveI : Algebra.EssFiniteType (Localization.AtPrime y') (Localization.AtPrime y) :=
    OrdRegAux.essFiniteType_localization_atPrime_comap y

  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K') j') := by
    haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') j' htj' hFD' inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K') j') := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K) _
  haveI : FaithfulSMul ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hιinj

  letI : Algebra ↥K' ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : Algebra ↥(chartAlgFin A (↥K') j') ↥K := ((algebraMap ↥K' ↥K).comp (algebraMap ↥(chartAlgFin A (↥K') j') ↥K')).toAlgebra
  haveI : IsScalarTower ↥(chartAlgFin A (↥K') j') ↥K' ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) ↥K :=
    IsScalarTower.of_algebraMap_eq (fun x => (hι x).symm)
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgFin A (↥K') j') ↥K' := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K') _
  haveI : Algebra.IsSeparable ↥K' ↥K := OrdRegAux.isSeparable_of_inclusion L K K' hle j j' hjj' hFD
  haveI _t1 : IsScalarTower ↥(chartAlgFin A (↥K') j') ↥K' ↥K := inferInstance
  haveI _t2 : IsScalarTower ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) ↥K := inferInstance
  haveI hunr : Algebra.FormallyUnramified (Localization.AtPrime y') (Localization.AtPrime y) :=
    @OrdRegS3.formallyUnramified_localization_of_forall_height_one
      ↥(chartAlgFin A (↥K') j') _ _ _ _ ↥K' _ _ _ ↥(chartAlgFin A (↥K) j) _ _ _ _ _ _ ↥K _ _ _ _ _ _t1 _t2 _ y _ hRreg hRdim h1

  have hgen : algebraMap (Localization.AtPrime y') (Localization.AtPrime y) (algebraMap A (Localization.AtPrime y') ϖ) =
      algebraMap (↥(chartAlgFin A (↥K) j)) (Localization.AtPrime y) (algebraMap A _ ϖ) := by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K') j') (Localization.AtPrime y'),
      Localization.localRingHom_to_map]
    congr 1
    exact (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) ϖ).symm
  have hS1 : ringKrullDim (Localization.AtPrime y ⧸ Ideal.span {algebraMap (Localization.AtPrime y') (Localization.AtPrime y)
      (algebraMap A (Localization.AtPrime y') ϖ)}) = 1 := by
    rw [hgen]
    exact OrdRegAux.ringKrullDim_quotient_localization_eq_one A (↥K) j htj ϖ hϖ y hyϖ
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := by
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing (Localization.AtPrime y) := IsLocalization.isNoetherianRing y.primeCompl _ inferInstance
  have key := Algebra.FormallyUnramified.isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
    (R := Localization.AtPrime y') (S := Localization.AtPrime y) (algebraMap A (Localization.AtPrime y') ϖ) hRfib hRfib1 hS1
  rw [hgen] at key
  exact key

end OrdRegPort

namespace OrdRegPort
open scoped MatrixGroups
open CongruenceSubgroup

theorem Gamma_le_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

theorem GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

end OrdRegPort

namespace OrdRegL2
p2m_open "IsLocalRing AlgebraicCurve.TwoChartIntegralModel TensorProduct Algebra.TensorProduct"

theorem isRegularLocalRing_localization_of_smooth_inf
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    [Smooth (toBase A K j)] (y : ↥(XInf A K j)) :
    IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing A (toBase A K j) ((ιInf A K j).base y)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization (ιInf A K j) y
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ E

theorem isRegularLocalRing_localization_tensor_of_smooth_inf
    (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    (hs : Smooth (toBase A K j)) (k : Type) [Field k] [Algebra A k]
    (Q : Ideal (↥(chartAlgInf A K j) ⊗[A] k)) [hQ : Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  obtain ⟨g, hgo, -, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgInf A K j k
  haveI := hgo
  haveI hsm : Smooth (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :=
    MorphismProperty.pullback_snd _ _ hs
  let q : ↥(Spec (CommRingCat.of (↥(chartAlgInf A K j) ⊗[A] k))) := ⟨Q, hQ⟩
  have hst := @AlgebraicGeometry.Smooth.isRegularLocalRing_stalk k _ _
    (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) hsm (g.base q)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization g q
  exact @IsRegularLocalRing.of_ringEquiv _ _ hst _ _ E

set_option maxHeartbeats 3200000 in

theorem L2inf_floor_regular_of_smooth
    (L : Type) [Field L] [CharZero L]
    (K' : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K'] [IsScalarTower A L ↥K'] (j' : ↥K') [Fact (j' ≠ 0)]
    (htj : Transcendental A j')
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y' : Ideal ↥(chartAlgInf A (↥K') j')) [hy' : y'.IsMaximal] (hy'ϖ : algebraMap A ↥(chartAlgInf A (↥K') j') ϖ ∈ y') :
    IsRegularLocalRing (Localization.AtPrime y') ∧
    ringKrullDim (Localization.AtPrime y') ≤ 2 ∧
    IsRegularLocalRing (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) ∧
    ringKrullDim (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) = 1 ∧
    IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) := by
  classical
  haveI := hFD
  haveI : Fact ((j' : ↥K')⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : (j' : ↥K') ≠ 0)⟩
  have htjI : Transcendental A (j' : ↥K')⁻¹ := fun halg => htj (by simpa using halg.inv)
  have heqadj : IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K') = IntermediateField.adjoin L ({j'} : Set ↥K') := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j')
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L (j' : ↥K')⁻¹)
      rwa [inv_inv] at this
  have hFDI : FiniteDimensional ↥(IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K')) ↥K' := by rw [heqadj]; exact hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K')) ↥K' := Algebra.IsIntegral.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
  have hFT := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') (j' : ↥K')⁻¹ htjI hFDI hsep
  haveI := hsmooth

  have hreg1 : IsRegularLocalRing (Localization.AtPrime y') :=
    isRegularLocalRing_localization_of_smooth_inf A (↥K') j' (⟨y', hy'.isPrime⟩ : ↥(XInf A (↥K') j'))

  have hdim2 : ringKrullDim (Localization.AtPrime y') ≤ 2 := by
    refine (ringKrullDim_localization_le y'.primeCompl (Localization.AtPrime y')).trans ?_
    refine (ringKrullDim_chartAlg_singleton_le A (↥K') ((j' : ↥K')⁻¹)).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      (IsPrincipalIdealRing.ringKrullDim_eq_one A) (IsDiscreteValuationRing.not_isField A)]
    norm_num

  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, ⟨E₁⟩, ⟨E₂⟩⟩ := exists_ringEquiv_fibre_localization_tensor A ϖ hϖ ↥(chartAlgInf A (↥K') j') y' hy'ϖ

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖκ : algebraMap A (IsLocalRing.ResidueField A) ϖ = 0 := by
    rw [show algebraMap A (IsLocalRing.ResidueField A) ϖ = IsLocalRing.residue A ϖ from rfl, IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hinj : Function.Injective (Polynomial.aeval (R := A) ((j' : ↥K')⁻¹)) := transcendental_iff_injective.mp htjI
  have hrange : (Polynomial.aeval (R := A) ((j' : ↥K')⁻¹)).range = Algebra.adjoin A ({(j' : ↥K')⁻¹} : Set ↥K') :=
    (Algebra.adjoin_singleton_eq_range_aeval A ((j' : ↥K')⁻¹)).symm
  let eR : Polynomial A ≃ₐ[A] ↥(Algebra.adjoin A ({(j' : ↥K')⁻¹} : Set ↥K')) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := A) ((j' : ↥K')⁻¹)) hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have hdimQ₂ : ringKrullDim (Localization.AtPrime Q₂) = 1 :=
    Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hirr
      (Algebra.adjoin A ({(j' : ↥K')⁻¹} : Set ↥K')) (chartAlgInf A (↥K') j') eR
      (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K') {(j' : ↥K')⁻¹})
      (fun a => (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K')).mp a.2)
      hFT.1 (AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') {(j' : ↥K')⁻¹})
      (IsLocalRing.ResidueField A) hϖκ Q₂

  have hregQ₁ : IsRegularLocalRing (Localization.AtPrime Q₁) :=
    isRegularLocalRing_localization_tensor_of_smooth_inf A (↥K') j' hsmooth (IsLocalRing.ResidueField A) Q₁

  have halgϖ : algebraMap A (Localization.AtPrime y') ϖ =
      algebraMap ↥(chartAlgInf A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgInf A (↥K') j') ϖ) := IsScalarTower.algebraMap_apply _ _ _ _
  rw [halgϖ]
  have hregfib := @IsRegularLocalRing.of_ringEquiv _ _ hregQ₁ _ _ E₁.symm
  haveI := hregfib
  have hdom : IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap ↥(chartAlgInf A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgInf A (↥K') j') ϖ)}) :=
    @IsRegularLocalRing.isDomain _ _ hregfib
  exact ⟨hreg1, hdim2, hregfib, (ringKrullDim_eq_of_ringEquiv E₂).trans hdimQ₂, hdom⟩

end OrdRegL2

namespace OrdRegL0
open AlgebraicCurve.TwoChartIntegralModel

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem L0inf_isRegularLocalRing_fibre_of_localization
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (y : ↥(XInf A K j)) (hy : (ιInf A K j).base y = z)
    (h : IsRegularLocalRing (Localization.AtPrime y.asIdeal ⧸
      Ideal.span {algebraMap (↥(chartAlgInf A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ ϖ)})) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  subst hy
  subst hϖz
  obtain ⟨E, hE⟩ := exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιInf A K j) (ιInf_toBase A K j) y
  refine @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (Ideal.quotientEquiv _ _ E.symm ?_)
  rw [Ideal.map_span, Set.image_singleton, ← hE ϖ]
  simp only [RingHom.coe_coe, RingEquiv.symm_apply_apply]

theorem algebraMap_mem_asIdeal_of_germ_mem_maximalIdeal_inf
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z))
    (y : ↥(XInf A K j)) (hy : (ιInf A K j).base y = z) :
    algebraMap A (↥(chartAlgInf A K j)) ϖ ∈ y.asIdeal := by
  subst hy
  subst hϖz
  exact (germ_mem_maximalIdeal_iff_of_chart (toBase A K j) (ιInf A K j) (ιInf_toBase A K j) y ϖ).mp hz

end OrdRegL0

namespace OrdRegPort

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ringLevel_of_h1_inf
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(chartAlgInf A (↥K) j)) [hmax : y.IsMaximal]
    (hyϖ : algebraMap A (↥(chartAlgInf A (↥K) j)) ϖ ∈ y)

    (K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') [Fact (j' ≠ 0)] (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj' : Transcendental A j')
    (hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    [Algebra ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j)]
    [IsScalarTower A ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgInf A (↥K') j'),
      ((algebraMap ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) x : ↥(chartAlgInf A (↥K) j)) : ↥K) =
        IntermediateField.inclusion hle (x : ↥K'))

    (h1 : ∀ (Q : Ideal ↥(chartAlgInf A (↥K) j)) [Q.IsPrime], Q ≤ y → Q.height = 1 →
      Algebra.IsUnramifiedAt ↥(chartAlgInf A (↥K') j') Q) :
    IsRegularLocalRing (Localization.AtPrime y ⧸
      Ideal.span {algebraMap (↥(chartAlgInf A (↥K) j)) (Localization.AtPrime y) (algebraMap A _ ϖ)}) := by
  classical
  haveI := hFD
  haveI := hFD'
  haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : (j : ↥K) ≠ 0)⟩
  haveI : Fact ((j' : ↥K')⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : (j' : ↥K') ≠ 0)⟩
  have htjinv : Transcendental A (j : ↥K)⁻¹ := fun halg => htj (by simpa using halg.inv)
  have htj'inv : Transcendental A (j' : ↥K')⁻¹ := fun halg => htj' (by simpa using halg.inv)
  have heqadj : IntermediateField.adjoin L ({(j : ↥K)⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L (j : ↥K)⁻¹)
      rwa [inv_inv] at this
  have hFDinv : FiniteDimensional ↥(IntermediateField.adjoin L ({(j : ↥K)⁻¹} : Set ↥K)) ↥K := by rw [heqadj]; exact hFD
  have heqadj' : IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K') = IntermediateField.adjoin L ({j'} : Set ↥K') := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j')
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L (j' : ↥K')⁻¹)
      rwa [inv_inv] at this
  have hFD'inv : FiniteDimensional ↥(IntermediateField.adjoin L ({(j' : ↥K')⁻¹} : Set ↥K')) ↥K' := by rw [heqadj']; exact hFD'
  have hjj'inv : (IntermediateField.inclusion hle (j'⁻¹) : ↥K) = j⁻¹ := by rw [map_inv₀, hjj']
  haveI hsepj : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  have hιinj : Function.Injective (algebraMap ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j)) := by
    intro a b hab
    have h := congrArg (fun z : ↥(chartAlgInf A (↥K) j) => (z : ↥K)) hab
    simp only [hι] at h
    exact Subtype.ext ((IntermediateField.inclusion hle).injective h)
  haveI hfinAA : Module.Finite ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) :=
    OrdRegSeams.finite_chartAlgFin_of_floor A L K K' hle j⁻¹ j'⁻¹ hjj'inv htjinv hFDinv hι

  let y' : Ideal ↥(chartAlgInf A (↥K') j') := y.comap (algebraMap _ _)
  haveI : Algebra.IsIntegral ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) := inferInstance
  haveI hy'max : y'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
  have hy'ϖ : algebraMap A ↥(chartAlgInf A (↥K') j') ϖ ∈ y' := by
    show algebraMap _ (↥(chartAlgInf A (↥K) j)) (algebraMap A ↥(chartAlgInf A (↥K') j') ϖ) ∈ y
    rw [← IsScalarTower.algebraMap_apply]; exact hyϖ
  obtain ⟨hRreg, hRdim, hRfib, hRfib1, hRdom⟩ :=
    OrdRegL2.L2inf_floor_regular_of_smooth L K' A j' htj' hFD' hsmooth ϖ hϖ y' hy'ϖ

  letI hRS : Algebra (Localization.AtPrime y') (Localization.AtPrime y) :=
    (Localization.localRingHom y' y (algebraMap ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j)) rfl).toAlgebra
  haveI : IsLocalHom (algebraMap (Localization.AtPrime y') (Localization.AtPrime y)) :=
    Localization.isLocalHom_localRingHom y' y _ rfl
  haveI : Algebra.EssFiniteType (Localization.AtPrime y') (Localization.AtPrime y) :=
    OrdRegAux.essFiniteType_localization_atPrime_comap y

  haveI : IsNoetherianRing ↥(chartAlgInf A (↥K') j') := by
    haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
    obtain ⟨-, hft⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') j' htj' hFD' inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K') j') := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') _
  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K) _
  haveI : FaithfulSMul ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hιinj

  letI : Algebra ↥K' ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : Algebra ↥(chartAlgInf A (↥K') j') ↥K := ((algebraMap ↥K' ↥K).comp (algebraMap ↥(chartAlgInf A (↥K') j') ↥K')).toAlgebra
  haveI : IsScalarTower ↥(chartAlgInf A (↥K') j') ↥K' ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) ↥K :=
    IsScalarTower.of_algebraMap_eq (fun x => (hι x).symm)
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsFractionRing ↥(chartAlgInf A (↥K) j) ↥K := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgInf A (↥K') j') ↥K' := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K') _
  haveI : Algebra.IsSeparable ↥K' ↥K := OrdRegAux.isSeparable_of_inclusion L K K' hle j j' hjj' hFD
  haveI _t1 : IsScalarTower ↥(chartAlgInf A (↥K') j') ↥K' ↥K := inferInstance
  haveI _t2 : IsScalarTower ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) ↥K := inferInstance
  haveI hunr : Algebra.FormallyUnramified (Localization.AtPrime y') (Localization.AtPrime y) :=
    @OrdRegS3.formallyUnramified_localization_of_forall_height_one
      ↥(chartAlgInf A (↥K') j') _ _ _ _ ↥K' _ _ _ ↥(chartAlgInf A (↥K) j) _ _ _ _ _ _ ↥K _ _ _ _ _ _t1 _t2 _ y _ hRreg hRdim h1

  have hgen : algebraMap (Localization.AtPrime y') (Localization.AtPrime y) (algebraMap A (Localization.AtPrime y') ϖ) =
      algebraMap (↥(chartAlgInf A (↥K) j)) (Localization.AtPrime y) (algebraMap A _ ϖ) := by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K') j') (Localization.AtPrime y'),
      Localization.localRingHom_to_map]
    congr 1
    exact (IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K') j') ↥(chartAlgInf A (↥K) j) ϖ).symm
  have hS1 : ringKrullDim (Localization.AtPrime y ⧸ Ideal.span {algebraMap (Localization.AtPrime y') (Localization.AtPrime y)
      (algebraMap A (Localization.AtPrime y') ϖ)}) = 1 := by
    rw [hgen]
    exact OrdRegAux.ringKrullDim_quotient_localization_eq_one A (↥K) (j : ↥K)⁻¹ htjinv ϖ hϖ y hyϖ
  haveI : IsNoetherianRing ↥(chartAlgInf A (↥K) j) := by
    obtain ⟨-, hft⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing (Localization.AtPrime y) := IsLocalization.isNoetherianRing y.primeCompl _ inferInstance
  have key := Algebra.FormallyUnramified.isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
    (R := Localization.AtPrime y') (S := Localization.AtPrime y) (algebraMap A (Localization.AtPrime y') ϖ) hRfib hRfib1 hS1
  rw [hgen] at key
  exact key

end OrdRegPort

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀))
    (hfloor : Smooth (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := ι.toAlgebra

    (∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) 𝔔) →
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  intro h1
  classical
  letI algK : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle₀).toRingHom.toAlgebra
  letI algι : Algebra ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := ι.toAlgebra
  haveI := hmax

  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    OrdRegPort.GammaH_finiteIndex _ _
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) := hK
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK' j hj
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD₀ := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  have hjj' : (IntermediateField.inclusion hle₀ j₀ : ↥K) = j :=
    Subtype.ext (show ((j₀ : ↥K₀) : LaurentSeries L) = (j : LaurentSeries L) by rw [hj₀, hj])

  haveI : IsScalarTower A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    show ((algebraMap A ↥(chartAlgInf A (↥K) j) a : ↥(chartAlgInf A (↥K) j)) : ↥K) = ((ι (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) a)) : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K a) : LaurentSeries L) = ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K₀]
    rfl
  have hyϖ : algebraMap A (↥(chartAlgInf A (↥K) j)) ϖ ∈ y.asIdeal :=
    OrdRegL0.algebraMap_mem_asIdeal_of_germ_mem_maximalIdeal_inf A (↥K) j ϖ z ϖz hϖz hz y hy
  exact OrdRegL0.L0inf_isRegularLocalRing_fibre_of_localization A (↥K) j ϖ z ϖz hϖz y hy
    (OrdRegPort.ringLevel_of_h1_inf L K A j htj hFD ϖ hϖ y.asIdeal hyϖ K₀ hle₀ j₀ hjj' htj₀ hFD₀ hfloor hι h1)

end S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three (solution)
