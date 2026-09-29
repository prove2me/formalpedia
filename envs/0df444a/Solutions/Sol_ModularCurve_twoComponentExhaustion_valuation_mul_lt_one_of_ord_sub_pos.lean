-- Prove2me | solution 1 for ModularCurve.twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4230f4db-5039-5941-ab7e-bbc832ab9914

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_LevelBaseRing
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRFibreBound
p2m_open "ModularCurve"

variable {R : Type*} [CommRing R] [IsDomain R] (ϖ : R)
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {L : Type*} [AddCommGroup L] [Module K L] [Module R L] [IsScalarTower R K L]
variable {B : Type*} [CommRing B] [Algebra R B]
variable {S : Type*} [AddCommGroup S] (π : B →+ S)
variable {κ : Type*} [Field κ] [Module κ S] (ρ : R →+* κ)

omit [IsDomain R] in

private theorem exists_pow_mul_not_mem {ι : Type*} [Fintype ι] (hfin : ∀ x : R, x ≠ 0 → FiniteMultiplicity ϖ x)
    (c : ι → R) (hc : ∃ i, c i ≠ 0) :
    ∃ (m : ℕ) (c' : ι → R), (∀ i, c i = ϖ ^ m * c' i) ∧ ∃ i, c' i ∉ Ideal.span {ϖ} := by
  classical
  have hex : ∃ m : ℕ, ∃ i, ¬ ϖ ^ (m + 1) ∣ c i := by
    obtain ⟨i, hi⟩ := hc
    obtain ⟨m, hm⟩ := hfin (c i) hi
    exact ⟨m, i, hm⟩
  let m := Nat.find hex
  have hall : ∀ i, ϖ ^ m ∣ c i := by
    intro i
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero]; exact one_dvd _
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hmin := Nat.find_min hex (m := m') (by omega)
      push Not at hmin
      rw [hm']
      exact hmin i
  choose c' hc' using hall
  refine ⟨m, c', hc', ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, fun hmem => hi ?_⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨d, ?_⟩
  change c i = ϖ ^ (m + 1) * d
  rw [hc' i, hd, pow_succ, mul_assoc]

variable (φ : B →ₗ[R] L)

private theorem linearIndependent_lift (hϖ : ϖ ≠ 0) (hfin : ∀ x : R, x ≠ 0 → FiniteMultiplicity ϖ x)
    (hφ : Function.Injective φ)
    (hρ : ∀ r : R, r ∉ Ideal.span {ϖ} → ρ r ≠ 0)
    (hcompat : ∀ (r : R) (b : B), π (algebraMap R B r * b) = ρ r • π b)
    {ι : Type*} [Fintype ι] (b : ι → B) (hind : LinearIndependent κ (fun i => π (b i))) :
    LinearIndependent K (fun i => φ (b i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro k hk
  by_contra hne
  push Not at hne

  obtain ⟨⟨den, hden⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) k
  choose c hc using hint

  have hsum : ∑ i, (c i) • φ (b i) = 0 := by
    have h1 : ∑ i, ((den : R) • k i) • φ (b i) = 0 := by
      simp_rw [smul_assoc, ← Finset.smul_sum, hk, smul_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, algebraMap_smul]

  have hc0 : ∃ i, c i ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨i, fun h0 => hi ?_⟩
    have h1 : (den : R) • k i = 0 := by
      rw [← hc i, h0, map_zero]
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h (nonZeroDivisors.ne_zero hden)
    · exact h

  obtain ⟨m, c', hcc', i₀, hi₀⟩ := exists_pow_mul_not_mem ϖ hfin c hc0

  have hB : ∑ i, algebraMap R B (c' i) * b i = 0 := by
    apply hφ
    rw [map_zero]
    have hϖ0 : algebraMap R K (ϖ ^ m) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ fun h => hϖ ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
    have h2 : (ϖ ^ m) • φ (∑ i, algebraMap R B (c' i) * b i) = ∑ i, c i • φ (b i) := by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def, φ.map_smul, ← mul_smul, ← hcc' i]
    have h4 : algebraMap R K (ϖ ^ m) • φ (∑ i, algebraMap R B (c' i) * b i) = 0 := by
      rw [algebraMap_smul, h2, hsum]
    exact (smul_eq_zero.mp h4).resolve_left hϖ0

  have hS : ∑ i, ρ (c' i) • π (b i) = 0 := by
    have := congrArg π hB
    rw [map_sum, map_zero] at this
    simpa only [hcompat] using this
  exact hρ _ hi₀ ((Fintype.linearIndependent_iff.mp hind) (fun i => ρ (c' i)) hS i₀)

private theorem _root_.ModularCurve.DRFibreBound.finite_and_finrank_le [FiniteDimensional K L] (hϖ : ϖ ≠ 0) (hfin : ∀ x : R, x ≠ 0 → FiniteMultiplicity ϖ x)
    (hφ : Function.Injective φ) (hπ : Function.Surjective π)
    (hρ : ∀ r : R, r ∉ Ideal.span {ϖ} → ρ r ≠ 0)
    (hcompat : ∀ (r : R) (b : B), π (algebraMap R B r * b) = ρ r • π b) :
    Module.Finite κ S ∧ Module.finrank κ S ≤ Module.finrank K L := by
  classical
  have hrank : Module.rank κ S ≤ Module.finrank K L := by
    apply rank_le
    intro s hs
    choose b hb using fun x : s => hπ (x : S)
    have hind : LinearIndependent κ (fun x : s => π (b x)) := by
      simpa only [hb] using hs
    have hK := linearIndependent_lift (K := K) ϖ π ρ φ hϖ hfin hφ hρ hcompat b hind
    simpa using hK.fintype_card_le_finrank
  have hfinite : Module.Finite κ S :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.natCast_lt_aleph0 (n := Module.finrank K L)))
  exact ⟨hfinite, Module.finrank_le_of_rank_le hrank⟩

p2m_export "ModularCurve.DRFibreBound" "finite_and_finrank_le"
end ModularCurve.DRFibreBound

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRCount
p2m_open "ModularCurve"

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

private noncomputable def quotProd (P₁ P₂ : Ideal S) : S →ₗ[K] (S ⧸ P₁) × (S ⧸ P₂) :=
  (Ideal.Quotient.mkₐ K P₁).toLinearMap.prod (Ideal.Quotient.mkₐ K P₂).toLinearMap

@[scoped simp] private theorem quotProd_apply (P₁ P₂ : Ideal S) (x : S) :
    quotProd (K := K) P₁ P₂ x = (Ideal.Quotient.mk P₁ x, Ideal.Quotient.mk P₂ x) := rfl

private theorem quotProd_surjective (P₁ P₂ : Ideal S) (hsup : P₁ ⊔ P₂ = ⊤) :
    Function.Surjective (quotProd (K := K) P₁ P₂) := by
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p₁, hp₁, p₂, hp₂, h⟩ := Submodule.mem_sup.mp ((hsup ▸ Submodule.mem_top : (1 : S) ∈ P₁ ⊔ P₂))
  refine ⟨x * p₂ + y * p₁, Prod.ext ?_ ?_⟩
  · rw [quotProd_apply, Ideal.Quotient.eq]
    have : x * p₂ + y * p₁ - x = (y - x) * p₁ := by linear_combination x * h
    rw [this]
    exact P₁.mul_mem_left _ hp₁
  · rw [quotProd_apply, Ideal.Quotient.eq]
    have : x * p₂ + y * p₁ - y = (x - y) * p₂ := by linear_combination y * h
    rw [this]
    exact P₂.mul_mem_left _ hp₂

private theorem ker_quotProd (P₁ P₂ : Ideal S) :
    LinearMap.ker (quotProd (K := K) P₁ P₂) = (P₁ ⊓ P₂).restrictScalars K := by
  ext x
  simp only [LinearMap.mem_ker, quotProd_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.restrictScalars_mem, Ideal.mem_inf]

private theorem inf_eq_bot_of_finrank_le_add [Module.Finite K S] (P₁ P₂ : Ideal S) (hsup : P₁ ⊔ P₂ = ⊤)
    (hdim : Module.finrank K S ≤ Module.finrank K (S ⧸ P₁) + Module.finrank K (S ⧸ P₂)) :
    P₁ ⊓ P₂ = ⊥ := by
  haveI : Module.Finite K (S ⧸ P₁) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K P₁).toLinearMap (Ideal.Quotient.mkₐ_surjective K P₁)
  haveI : Module.Finite K (S ⧸ P₂) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K P₂).toLinearMap (Ideal.Quotient.mkₐ_surjective K P₂)
  have hrn := LinearMap.finrank_range_add_finrank_ker (quotProd (K := K) P₁ P₂)
  rw [LinearMap.range_eq_top.mpr (quotProd_surjective P₁ P₂ hsup), finrank_top, Module.finrank_prod,
    ker_quotProd] at hrn
  have h0 : Module.finrank K ((P₁ ⊓ P₂).restrictScalars K) = 0 := by omega
  have hbot : (P₁ ⊓ P₂).restrictScalars K = ⊥ := Submodule.finrank_eq_zero.mp h0
  exact (Submodule.restrictScalars_eq_bot_iff _ _ _).mp hbot

private theorem finrank_eq_add_of_finrank_le_add [Module.Finite K S] (P₁ P₂ : Ideal S) (hsup : P₁ ⊔ P₂ = ⊤)
    (hdim : Module.finrank K S ≤ Module.finrank K (S ⧸ P₁) + Module.finrank K (S ⧸ P₂)) :
    Module.finrank K S = Module.finrank K (S ⧸ P₁) + Module.finrank K (S ⧸ P₂) := by
  haveI : Module.Finite K (S ⧸ P₁) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K P₁).toLinearMap (Ideal.Quotient.mkₐ_surjective K P₁)
  haveI : Module.Finite K (S ⧸ P₂) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K P₂).toLinearMap (Ideal.Quotient.mkₐ_surjective K P₂)
  have hrn := LinearMap.finrank_range_add_finrank_ker (quotProd (K := K) P₁ P₂)
  rw [LinearMap.range_eq_top.mpr (quotProd_surjective P₁ P₂ hsup), finrank_top, Module.finrank_prod,
    ker_quotProd] at hrn
  omega

private theorem inf_eq_bot_of_isMaximal_of_finrank_le_add [Module.Finite K S] (P₁ P₂ : Ideal S) [P₁.IsMaximal]
    [P₂.IsMaximal] (hne : P₁ ≠ P₂)
    (hdim : Module.finrank K S ≤ Module.finrank K (S ⧸ P₁) + Module.finrank K (S ⧸ P₂)) :
    P₁ ⊓ P₂ = ⊥ :=
  inf_eq_bot_of_finrank_le_add P₁ P₂ (Ideal.IsMaximal.coprime_of_ne ‹_› ‹_› hne) hdim

end ModularCurve.DRCount
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRACE
p2m_open "ModularCurve"

open IsLocalization

universe uR uB uP uL uΩ

variable {R : Type uR} [CommRing R] [IsDomain R] (ϖ : R)

private abbrev pIdeal : Ideal R := Ideal.span {ϖ}

variable [hp : (pIdeal ϖ).IsPrime]

private def locSubmonoid (B : Type uB) [CommRing B] [Algebra R B] : Submonoid B := (pIdeal ϖ).primeCompl.map (algebraMap R B)

omit [IsDomain R] in
private theorem mem_locSubmonoid_iff (B : Type uB) [CommRing B] [Algebra R B] {m : B} :
    m ∈ locSubmonoid ϖ B ↔ ∃ s : R, s ∉ pIdeal ϖ ∧ algebraMap R B s = m := by
  simp only [locSubmonoid, Submonoid.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

omit [IsDomain R] in
private theorem algebraMap_mem_locSubmonoid (B : Type uB) [CommRing B] [Algebra R B] {s : R} (hs : s ∉ pIdeal ϖ) :
    algebraMap R B s ∈ locSubmonoid ϖ B :=
  (mem_locSubmonoid_iff ϖ B).mpr ⟨s, hs, rfl⟩

omit [IsDomain R] in

private theorem isUnit_algebraMap_Bp (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] {s : R} (hs : s ∉ pIdeal ϖ) : IsUnit (algebraMap R Bp s) := by
  rw [IsScalarTower.algebraMap_apply R B Bp s]
  exact IsLocalization.map_units Bp ⟨algebraMap R B s, algebraMap_mem_locSubmonoid ϖ B hs⟩

private abbrev fibIdeal (Bp : Type uP) [CommRing Bp] [Algebra R Bp] : Ideal Bp := Ideal.span {algebraMap R Bp ϖ}

private abbrev Fib (Bp : Type uP) [CommRing Bp] [Algebra R Bp] : Type uP := Bp ⧸ fibIdeal ϖ Bp

private abbrev κ : Type uR := (pIdeal ϖ).ResidueField

private def RToFib (Bp : Type uP) [CommRing Bp] [Algebra R Bp] : R →+* Fib ϖ Bp :=
  (Ideal.Quotient.mk (fibIdeal ϖ Bp)).comp (algebraMap R Bp)

omit [IsDomain R] hp in
private theorem RToFib_apply (Bp : Type uP) [CommRing Bp] [Algebra R Bp] (r : R) :
    RToFib ϖ Bp r = Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap R Bp r) := rfl

omit [IsDomain R] hp in
private theorem pIdeal_le_ker (Bp : Type uP) [CommRing Bp] [Algebra R Bp] : pIdeal ϖ ≤ RingHom.ker (RToFib ϖ Bp) := by
  intro r hr
  rw [RingHom.mem_ker, RToFib_apply, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [IsDomain R] in
private theorem primeCompl_le (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] : (pIdeal ϖ).primeCompl ≤ (IsUnit.submonoid (Fib ϖ Bp)).comap (RToFib ϖ Bp) := by
  intro s hs
  exact (isUnit_algebraMap_Bp ϖ B Bp hs).map (Ideal.Quotient.mk (fibIdeal ϖ Bp))

private noncomputable def κToFib (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] : κ ϖ →+* Fib ϖ Bp :=
  Ideal.ResidueField.lift (S := Fib ϖ Bp) (pIdeal ϖ) (RToFib ϖ Bp) (pIdeal_le_ker ϖ Bp) (primeCompl_le ϖ B Bp)

omit [IsDomain R] in
private theorem κToFib_algebraMap (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (r : R) :
    κToFib ϖ B Bp (algebraMap R (κ ϖ) r) = Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap R Bp r) :=
  Ideal.ResidueField.lift_algebraMap (S := Fib ϖ Bp) (pIdeal ϖ) (RToFib ϖ Bp) (pIdeal_le_ker ϖ Bp)
    (primeCompl_le ϖ B Bp) r

@[reducible] private noncomputable def algebraκFib (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] : Algebra (κ ϖ) (Fib ϖ Bp) := (κToFib ϖ B Bp).toAlgebra

omit [IsDomain R] in
private theorem algebraMap_κ_ne_zero {r : R} (hr : r ∉ pIdeal ϖ) : algebraMap R (κ ϖ) r ≠ 0 := by
  rwa [Ne, Ideal.algebraMap_residueField_eq_zero]

omit [IsDomain R] in
private theorem compat (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (r : R) (b : Bp) :
    letI := algebraκFib ϖ B Bp
    Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap R Bp r * b) =
      algebraMap R (κ ϖ) r • (Ideal.Quotient.mk (fibIdeal ϖ Bp) b : Fib ϖ Bp) := by
  letI := algebraκFib ϖ B Bp
  rw [Algebra.smul_def, map_mul]
  exact congrArg (· * _) (κToFib_algebraMap ϖ B Bp r).symm

private theorem _root_.ModularCurve.DRACE.finite_and_finrank_le (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type uL} [AddCommGroup L] [Module K L] [Module R L] [IsScalarTower R K L] [FiniteDimensional K L]
    (φ : Bp →ₗ[R] L) (hϖ : ϖ ≠ 0) (hfin : ∀ x : R, x ≠ 0 → FiniteMultiplicity ϖ x)
    (hφ : Function.Injective φ) :
    letI := algebraκFib ϖ B Bp
    Module.Finite (κ ϖ) (Fib ϖ Bp) ∧ Module.finrank (κ ϖ) (Fib ϖ Bp) ≤ Module.finrank K L :=
  letI := algebraκFib ϖ B Bp
  DRFibreBound.finite_and_finrank_le (K := K) ϖ (Ideal.Quotient.mk (fibIdeal ϖ Bp)).toAddMonoidHom
    (algebraMap R (κ ϖ)) φ hϖ hfin hφ Ideal.Quotient.mk_surjective (fun _ hr => algebraMap_κ_ne_zero ϖ hr)
    (fun r b => compat ϖ B Bp r b)

p2m_export "ModularCurve.DRACE" "finite_and_finrank_le"

section Reduction
variable {Ω : Type uΩ} [Field Ω]

omit [IsDomain R] in
private theorem isUnit_πB (B : Type uB) [CommRing B] [Algebra R B] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (m : locSubmonoid ϖ B) : IsUnit (πB m) := by
  obtain ⟨s, hs, hsm⟩ := (mem_locSubmonoid_iff ϖ B).mp m.2
  rw [← hsm]
  exact IsUnit.mk0 _ (hunit s hs)

private noncomputable def πp (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0) :
    Bp →+* Ω :=
  IsLocalization.lift (M := locSubmonoid ϖ B) (g := πB) (isUnit_πB ϖ B πB hunit)

omit [IsDomain R] in
private theorem πp_algebraMap (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0) (b : B) :
    πp ϖ B Bp πB hunit (algebraMap B Bp b) = πB b :=
  IsLocalization.lift_eq _ b

omit [IsDomain R] in
private theorem πp_algebraMap_R (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (r : R) : πp ϖ B Bp πB hunit (algebraMap R Bp r) = πB (algebraMap R B r) := by
  rw [IsScalarTower.algebraMap_apply R B Bp r, πp_algebraMap]

omit [IsDomain R] in
private theorem πp_vanishes (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) (x : Bp) (hx : x ∈ fibIdeal ϖ Bp) : πp ϖ B Bp πB hunit x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, πp_algebraMap_R, hϖ0, mul_zero]

private noncomputable def πS (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) : Fib ϖ Bp →+* Ω :=
  Ideal.Quotient.lift _ (πp ϖ B Bp πB hunit) (πp_vanishes ϖ B Bp πB hunit hϖ0)

omit [IsDomain R] in
private theorem πS_mk (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) (x : Bp) :
    πS ϖ B Bp πB hunit hϖ0 (Ideal.Quotient.mk (fibIdeal ϖ Bp) x) = πp ϖ B Bp πB hunit x :=
  Ideal.Quotient.lift_mk _ _ _

omit [IsDomain R] in
private theorem πS_mk_algebraMap (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) (b : B) :
    πS ϖ B Bp πB hunit hϖ0 (Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap B Bp b)) = πB b := by
  rw [πS_mk, πp_algebraMap]

omit [IsDomain R] in

private theorem ker_πS_isPrime (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) : (RingHom.ker (πS ϖ B Bp πB hunit hϖ0)).IsPrime :=
  RingHom.ker_isPrime (πS ϖ B Bp πB hunit hϖ0)

omit [IsDomain R] in

private theorem le_finrank_quotient_ker (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp] (πB : B →+* Ω) (hunit : ∀ s : R, s ∉ pIdeal ϖ → πB (algebraMap R B s) ≠ 0)
    (hϖ0 : πB (algebraMap R B ϖ) = 0) {ι : Type*} [Fintype ι] (b : ι → B)
    (hind : ∀ c : ι → R, (∑ i, πB (algebraMap R B (c i)) * πB (b i)) = 0 → ∀ i, c i ∈ pIdeal ϖ) :
    letI := algebraκFib ϖ B Bp
    ∀ [Module.Finite (κ ϖ) (Fib ϖ Bp)],
      Fintype.card ι ≤ Module.finrank (κ ϖ) (Fib ϖ Bp ⧸ RingHom.ker (πS ϖ B Bp πB hunit hϖ0)) := by
  letI := algebraκFib ϖ B Bp
  intro _
  classical
  set P := RingHom.ker (πS ϖ B Bp πB hunit hϖ0)
  let x : ι → Fib ϖ Bp ⧸ P := fun i =>
    Ideal.Quotient.mk P (Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap B Bp (b i)))
  suffices hli : LinearIndependent (κ ϖ) x by
    simpa using hli.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro k hk

  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (R ⧸ pIdeal ϖ)) k
  choose cbar hcbar using hint
  choose c hc using fun i => Ideal.Quotient.mk_surjective (cbar i)

  have hsum : ∑ i, algebraMap R (κ ϖ) (c i) • x i = 0 := by
    have h1 : ∑ i, (algebraMap (R ⧸ pIdeal ϖ) (κ ϖ) d * k i) • x i = 0 := by
      simp_rw [mul_smul, ← Finset.smul_sum, hk, smul_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, ← hcbar i, ← hc i, Ideal.algebraMap_quotient_residueField_mk]

  have hx : ∀ i, algebraMap R (κ ϖ) (c i) • x i =
      Ideal.Quotient.mk P (Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap R Bp (c i) * algebraMap B Bp (b i))) := by
    intro i
    rw [compat ϖ B Bp, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  have hz : Ideal.Quotient.mk P (Ideal.Quotient.mk (fibIdeal ϖ Bp)
      (∑ i, algebraMap R Bp (c i) * algebraMap B Bp (b i))) = 0 := by
    rw [map_sum, map_sum, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hx i).symm
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hΩ : (∑ i, πB (algebraMap R B (c i)) * πB (b i)) = 0 := by
    rw [RingHom.mem_ker, πS_mk, map_sum] at hmem
    rw [← hmem]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, πp_algebraMap_R, πp_algebraMap]
  have hci : ∀ i, c i ∈ pIdeal ϖ := hind c hΩ
  intro i
  have hcbar0 : cbar i = 0 := by
    rw [← hc i, Ideal.Quotient.eq_zero_iff_mem]; exact hci i
  have hdk : algebraMap (R ⧸ pIdeal ϖ) (κ ϖ) d * k i = 0 := by
    rw [← Algebra.smul_def, ← hcbar i, hcbar0, map_zero]
  rcases mul_eq_zero.mp hdk with h | h
  · exact absurd h (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  · exact h

omit [IsDomain R] in

private theorem exists_mul_mul_eq_mul (B : Type uB) [CommRing B] [Algebra R B]
    (Bp : Type uP) [CommRing Bp] [Algebra B Bp] [Algebra R Bp] [IsScalarTower R B Bp]
    [IsLocalization (locSubmonoid ϖ B) Bp]
    (hM : locSubmonoid ϖ B ≤ nonZeroDivisors B)
    {Ω₁ : Type*} [Field Ω₁] (π₁ : B →+* Ω₁) (hu₁ : ∀ s : R, s ∉ pIdeal ϖ → π₁ (algebraMap R B s) ≠ 0)
    (hz₁ : π₁ (algebraMap R B ϖ) = 0)
    {Ω₂ : Type*} [Field Ω₂] (π₂ : B →+* Ω₂) (hu₂ : ∀ s : R, s ∉ pIdeal ϖ → π₂ (algebraMap R B s) ≠ 0)
    (hz₂ : π₂ (algebraMap R B ϖ) = 0)
    (x : B) (hx₁ : π₁ x = 0) (hx₂ : π₂ x ≠ 0)
    {ι₁ : Type*} [Fintype ι₁] (b₁ : ι₁ → B)
    (hind₁ : ∀ c : ι₁ → R, (∑ i, π₁ (algebraMap R B (c i)) * π₁ (b₁ i)) = 0 → ∀ i, c i ∈ pIdeal ϖ)
    {ι₂ : Type*} [Fintype ι₂] (b₂ : ι₂ → B)
    (hind₂ : ∀ c : ι₂ → R, (∑ i, π₂ (algebraMap R B (c i)) * π₂ (b₂ i)) = 0 → ∀ i, c i ∈ pIdeal ϖ) :
    letI := algebraκFib ϖ B Bp
    ∀ [Module.Finite (κ ϖ) (Fib ϖ Bp)], Module.finrank (κ ϖ) (Fib ϖ Bp) ≤ Fintype.card ι₁ + Fintype.card ι₂ →
      ∀ e f : B, π₁ e = 0 → π₂ f = 0 →
        ∃ s : R, s ∉ pIdeal ϖ ∧ ∃ a : B, algebraMap R B s * (e * f) = algebraMap R B ϖ * a := by
  letI := algebraκFib ϖ B Bp
  intro _ hdim e f he hf
  set P₁ := RingHom.ker (πS ϖ B Bp π₁ hu₁ hz₁)
  set P₂ := RingHom.ker (πS ϖ B Bp π₂ hu₂ hz₂)

  haveI : IsArtinianRing (Fib ϖ Bp) := IsArtinianRing.of_finite (κ ϖ) (Fib ϖ Bp)
  haveI hP₁ : P₁.IsPrime := ker_πS_isPrime ϖ B Bp π₁ hu₁ hz₁
  haveI hP₂ : P₂.IsPrime := ker_πS_isPrime ϖ B Bp π₂ hu₂ hz₂
  haveI : P₁.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P₁
  haveI : P₂.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P₂
  have hne : P₁ ≠ P₂ := by
    intro h
    have h1 : Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap B Bp x) ∈ P₁ := by
      rw [RingHom.mem_ker, πS_mk_algebraMap, hx₁]
    rw [h, RingHom.mem_ker, πS_mk_algebraMap] at h1
    exact hx₂ h1

  have h₁ := le_finrank_quotient_ker ϖ B Bp π₁ hu₁ hz₁ b₁ hind₁
  have h₂ := le_finrank_quotient_ker ϖ B Bp π₂ hu₂ hz₂ b₂ hind₂
  have hbot : P₁ ⊓ P₂ = ⊥ :=
    DRCount.inf_eq_bot_of_isMaximal_of_finrank_le_add (K := κ ϖ) P₁ P₂ hne (hdim.trans (add_le_add h₁ h₂))

  have hy : Ideal.Quotient.mk (fibIdeal ϖ Bp) (algebraMap B Bp (e * f)) = 0 := by
    rw [← Ideal.mem_bot, ← hbot, Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker, πS_mk_algebraMap,
      πS_mk_algebraMap, map_mul, map_mul, he, hf, zero_mul, mul_zero]
    exact ⟨rfl, rfl⟩

  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hy)
  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj (locSubmonoid ϖ B) z
  obtain ⟨s, hs, hsm⟩ := (mem_locSubmonoid_iff ϖ B).mp m.2
  refine ⟨s, hs, a, IsLocalization.injective Bp hM ?_⟩
  rw [map_mul, hsm, ← hz, map_mul, ← IsScalarTower.algebraMap_apply R B Bp ϖ, ← mul_assoc, mul_comm _ z, ham]
  exact mul_comm _ _

end Reduction
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

end ModularCurve.DRACE
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRFraction
p2m_open "ModularCurve"

variable (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪]
variable (E : Type*) [Field E] [Algebra 𝒪 E] [IsFractionRing 𝒪 E]
variable {L : Type*} [Field L] [Algebra E L]
variable (f : L)

private noncomputable def evalRange : Subring L :=
  (eval₂RingHom ((algebraMap E L).comp (algebraMap 𝒪 E)) f).range

omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in
private theorem eval₂_mem_evalRange (p : 𝒪[X]) : eval₂ ((algebraMap E L).comp (algebraMap 𝒪 E)) f p ∈ evalRange 𝒪 E f :=
  ⟨p, rfl⟩

omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in
private theorem eval₂_eq_aeval_map (p : 𝒪[X]) :
    eval₂ ((algebraMap E L).comp (algebraMap 𝒪 E)) f p = aeval f (p.map (algebraMap 𝒪 E)) := by
  rw [aeval_def, eval₂_map]

omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in
private theorem aeval_mem_adjoin (p : E[X]) : aeval f p ∈ E⟮f⟯ :=
  algebra_adjoin_le_adjoin E {f} (aeval_mem_adjoin_singleton E f)

variable {𝒪} in
omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in
private theorem eval₂_mem_adjoin (p : 𝒪[X]) : eval₂ ((algebraMap E L).comp (algebraMap 𝒪 E)) f p ∈ E⟮f⟯ := by
  rw [eval₂_eq_aeval_map]
  exact aeval_mem_adjoin E f _

omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in

private theorem evalRange_le : evalRange 𝒪 E f ≤ (E⟮f⟯).toSubring := by
  rintro _ ⟨p, rfl⟩
  exact eval₂_mem_adjoin E f p

section
variable (R : Subring L)

omit [IsDomain 𝒪] [IsFractionRing 𝒪 E] in
private theorem le_adjoin (hR : R = evalRange 𝒪 E f) : R ≤ (E⟮f⟯).toSubring := hR ▸ evalRange_le 𝒪 E f

variable {E} in

@[reducible] private def algebraOfLE {R : Subring L} {K : IntermediateField E L} (h : R ≤ K.toSubring) : Algebra R K :=
  (Subring.inclusion h).toAlgebra

variable {E} in
private theorem algebraOfLE_algebraMap_apply {R : Subring L} {K : IntermediateField E L} (h : R ≤ K.toSubring) (x : R) :
    ((@algebraMap R K _ _ (algebraOfLE h)) x : L) = x :=
  rfl

private theorem isFractionRing (hR : R = evalRange 𝒪 E f) (hf : Transcendental E f) :
    @IsFractionRing R _ E⟮f⟯ _ (algebraOfLE (le_adjoin 𝒪 E f R hR)) := by
  letI : Algebra R E⟮f⟯ := algebraOfLE (le_adjoin 𝒪 E f R hR)
  haveI : FaithfulSMul R E⟮f⟯ :=
    (faithfulSMul_iff_algebraMap_injective R E⟮f⟯).mpr fun x y h =>
      Subtype.ext (congrArg (fun z : E⟮f⟯ => (z : L)) h)
  refine IsFractionRing.of_field R E⟮f⟯ fun z => ?_

  let e := RatFunc.algEquivOfTranscendental f hf
  obtain ⟨u, rfl⟩ : ∃ u, e u = z := ⟨e.symm z, e.apply_symm_apply z⟩
  have hz : ((e u : E⟮f⟯) : L) = aeval f u.num / aeval f u.denom := RatFunc.algEquivOfTranscendental_apply f hf u

  obtain ⟨b₁, hb₁, h₁⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) u.num
  obtain ⟨b₂, hb₂, h₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) u.denom
  set pn : 𝒪[X] := IsLocalization.integerNormalization (nonZeroDivisors 𝒪) u.num
  set pd : 𝒪[X] := IsLocalization.integerNormalization (nonZeroDivisors 𝒪) u.denom

  let φ : 𝒪[X] →+* L := eval₂RingHom ((algebraMap E L).comp (algebraMap 𝒪 E)) f
  have hmem : ∀ p : 𝒪[X], φ p ∈ R := fun p => hR ▸ ⟨p, rfl⟩
  refine ⟨⟨φ (C b₂ * pn), hmem _⟩, ⟨φ (C b₁ * pd), hmem _⟩, ?_⟩
  apply Subtype.ext
  rw [hz, IntermediateField.coe_div, algebraOfLE_algebraMap_apply, algebraOfLE_algebraMap_apply]
  change _ = φ (C b₂ * pn) / φ (C b₁ * pd)
  have hφ : ∀ p : 𝒪[X], φ p = aeval f (p.map (algebraMap 𝒪 E)) := eval₂_eq_aeval_map 𝒪 E f
  have hsm : ∀ (b : 𝒪) (p : E[X]), (b • p : E[X]) = C (algebraMap 𝒪 E b) * p := fun b p => by
    rw [← algebraMap_smul E b p, smul_eq_C_mul]
  rw [map_mul, map_mul, hφ, hφ, hφ, hφ, h₁, h₂]
  simp only [map_C, aeval_C, hsm, map_mul]

  have hden : aeval f u.denom ≠ 0 := fun h0 =>
    (RatFunc.denom_ne_zero u) ((injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hf) _ h0)
  have hb₁0 : algebraMap E L (algebraMap 𝒪 E b₁) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₁)
  have hb₂0 : algebraMap E L (algebraMap 𝒪 E b₂) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₂)
  field_simp

end
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

end ModularCurve.DRFraction
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

open IntermediateField Module

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRRelfinrank
p2m_open "ModularCurve"

variable {F X : Type*} [Field F] [Field X] [Algebra F X] (B : IntermediateField F X) (a : B)

private theorem comap_val_adjoin_singleton : (adjoin F {(a : X)}).comap B.val = adjoin F {a} := by
  apply le_antisymm
  · intro x hx
    change B.val x ∈ adjoin F {(a : X)} at hx
    have hmap : adjoin F {(a : X)} = (adjoin F ({a} : Set B)).map B.val := by
      rw [adjoin_map, Set.image_singleton]
      rfl
    rw [hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    change B.val a ∈ adjoin F {(a : X)}
    exact mem_adjoin_simple_self F (a : X)

private theorem finrank_adjoin_eq_relfinrank :
    finrank (adjoin F ({a} : Set B)) B = relfinrank (adjoin F {(a : X)}) B := by
  rw [← comap_val_adjoin_singleton, IntermediateField.finrank_comap, fieldRange_val]

private theorem finite_of_relfinrank_pos (h : 0 < relfinrank (adjoin F {(a : X)}) B) :
    Module.Finite (adjoin F ({a} : Set B)) B :=
  Module.finite_of_finrank_pos (by rwa [finrank_adjoin_eq_relfinrank])

end ModularCurve.DRRelfinrank
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRHind
p2m_open "ModularCurve"

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (t : F)

private theorem eq_zero_of_sum_aeval_mul_eq_zero (ht : Transcendental k t) {ι : Type*} [Fintype ι] (m : ι → F)
    (hm : LinearIndependent k⟮t⟯ m) (q : ι → k[X]) (h : ∑ i, aeval t (q i) * m i = 0) : ∀ i, q i = 0 := by
  have hmem : ∀ i, aeval t (q i) ∈ k⟮t⟯ := fun i =>
    algebra_adjoin_le_adjoin k {t} (aeval_mem_adjoin_singleton k t)
  have h' : ∑ i, (⟨aeval t (q i), hmem i⟩ : k⟮t⟯) • m i = 0 := by
    rw [← h]
    rfl
  have hzero := Fintype.linearIndependent_iff.mp hm _ h'
  intro i
  have hi : aeval t (q i) = 0 := congrArg Subtype.val (hzero i)
  exact (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp ht) _ hi

omit [Algebra k F] in

private theorem eq_zero_of_sum_expand_mul_X_pow_eq_zero {ℓ : ℕ} (hℓ : 0 < ℓ) (p : Fin ℓ → k[X])
    (h : ∑ a : Fin ℓ, expand k ℓ (p a) * X ^ (a : ℕ) = 0) : ∀ a, p a = 0 := by
  intro a
  ext n

  have hc := congrArg (fun f : k[X] => f.coeff (n * ℓ + a)) h
  simp only [finsetSum_coeff, coeff_zero] at hc
  rw [Finset.sum_eq_single a] at hc
  · rwa [coeff_mul_X_pow, coeff_expand_mul hℓ] at hc
  · intro b _ hba
    rw [coeff_mul_X_pow', coeff_expand hℓ]
    split_ifs with hle hdvd
    · exfalso
      apply hba

      apply Fin.ext
      obtain ⟨c, hc'⟩ := hdvd
      have hb := b.2
      have ha := a.2
      have h1 : n * ℓ + a = ℓ * c + b := by omega

      have h2 : (n * ℓ + (a : ℕ)) % ℓ = (a : ℕ) := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
      have h3 : (ℓ * c + (b : ℕ)) % ℓ = (b : ℕ) := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      rw [h1] at h2
      rw [h2] at h3
      exact h3.symm
    · rfl
    · rfl
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private theorem eq_zero_of_sum_sum_aeval_expand_mul_eq_zero (ht : Transcendental k t) {ι : Type*} [Fintype ι] (m : ι → F)
    (hm : LinearIndependent k⟮t⟯ m) {ℓ : ℕ} (hℓ : 0 < ℓ) (p : Fin ℓ → ι → k[X])
    (h : ∑ a : Fin ℓ, ∑ i, aeval t (expand k ℓ (p a i)) * (t ^ (a : ℕ) * m i) = 0) : ∀ a i, p a i = 0 := by

  have h' : ∑ i, aeval t (∑ a : Fin ℓ, expand k ℓ (p a i) * X ^ (a : ℕ)) * m i = 0 := by
    rw [← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_pow, aeval_X, mul_assoc]
  have hq := eq_zero_of_sum_aeval_mul_eq_zero t ht m hm _ h'
  intro a i
  exact eq_zero_of_sum_expand_mul_X_pow_eq_zero hℓ (fun a => p a i) (hq i) a

end ModularCurve.DRHind
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRPullback
p2m_open "ModularCurve"

open Polynomial

section Scale

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem minpoly_mul_eq_scaleRoots {c : K} (hc : c ≠ 0) {x : F} (hx : IsIntegral K x) :
    minpoly K (algebraMap K F c * x) = (minpoly K x).scaleRoots c := by
  symm
  refine minpoly.unique K (algebraMap K F c * x) ((monic_scaleRoots_iff c).mpr (minpoly.monic hx))
    (scaleRoots_aeval_eq_zero (minpoly.aeval K x)) fun q hq hq0 => ?_
  have h' : aeval x (q.scaleRoots c⁻¹) = 0 := by
    have h := scaleRoots_aeval_eq_zero (r := c⁻¹) hq0
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h
  calc ((minpoly K x).scaleRoots c).degree = (minpoly K x).degree := degree_scaleRoots _
    _ ≤ (q.scaleRoots c⁻¹).degree := minpoly.min K x ((monic_scaleRoots_iff _).mpr hq) h'
    _ = q.degree := degree_scaleRoots _

end Scale
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

section Pullback

variable {R F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F] [Algebra R F]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K F] [IsScalarTower R K F]

private theorem coeff_minpoly_mul_pow_mem_range {c : R} (hc : c ≠ 0) {x : F} (hx : IsIntegral K x)
    (hcx : IsIntegral R (algebraMap R F c * x)) (i : ℕ) :
    (minpoly K x).coeff i * algebraMap R K c ^ ((minpoly K x).natDegree - i) ∈ (algebraMap R K).range := by
  have hcK : algebraMap R K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc
  have hsc : minpoly K (algebraMap R F c * x) = (minpoly K x).scaleRoots (algebraMap R K c) := by
    rw [IsScalarTower.algebraMap_apply R K F c]
    exact minpoly_mul_eq_scaleRoots hcK hx
  have hcoeff := congrArg (fun P => P.coeff i) hsc
  simp only [minpoly.isIntegrallyClosed_eq_field_fractions' K hcx, coeff_map, coeff_scaleRoots] at hcoeff
  exact ⟨_, hcoeff⟩

include K in

private theorem isIntegral_of_prime_of_not_dvd {ℓ p : R} (hℓ : Prime ℓ) (hp : ¬ ℓ ∣ p) {x : F}
    (h1 : IsIntegral R (algebraMap R F ℓ * x)) (h2 : IsIntegral R (algebraMap R F p * x)) :
    IsIntegral R x := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hℓK : algebraMap R K ℓ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hℓ.ne_zero
  have hp0 : p ≠ 0 := fun h => hp (h ▸ dvd_zero ℓ)

  have hxK : IsIntegral K x := by
    have h1K : IsIntegral K (algebraMap R F ℓ * x) := h1.tower_top
    have hx : x = algebraMap K F (algebraMap R K ℓ)⁻¹ * (algebraMap R F ℓ * x) := by
      rw [← mul_assoc, IsScalarTower.algebraMap_apply R K F ℓ, ← map_mul, inv_mul_cancel₀ hℓK, map_one, one_mul]
    rw [hx]
    exact isIntegral_algebraMap.mul h1K

  set μ := minpoly K x with hμ
  have hlift : μ ∈ Polynomial.lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    obtain ⟨a, ha⟩ := coeff_minpoly_mul_pow_mem_range K hℓ.ne_zero hxK h1 i
    obtain ⟨b, hb⟩ := coeff_minpoly_mul_pow_mem_range K hp0 hxK h2 i
    set m := μ.natDegree - i with hm

    have hab : a * p ^ m = b * ℓ ^ m := hinj (by
      rw [map_mul, map_mul, map_pow, map_pow, ha, hb]; ring)
    have hdvd : ℓ ^ m ∣ a * p ^ m := ⟨b, by rw [hab, mul_comm]⟩
    have hnot : ¬ ℓ ∣ p ^ m := fun h => hp (hℓ.dvd_of_dvd_pow h)
    obtain ⟨a', rfl⟩ := hℓ.pow_dvd_of_dvd_mul_right m hnot hdvd
    refine ⟨a', ?_⟩
    have hpow : algebraMap R K ℓ ^ m ≠ 0 := pow_ne_zero _ hℓK
    apply mul_right_cancel₀ hpow
    rw [← ha, map_mul, map_pow, mul_comm]
  obtain ⟨q, hqμ, -, hqmonic⟩ := lifts_and_degree_eq_and_monic hlift (minpoly.monic hxK)
  refine ⟨q, hqmonic, ?_⟩
  change aeval x q = 0
  rw [← aeval_map_algebraMap K, hqμ]
  exact minpoly.aeval K x

include K in

private theorem exists_eq_mul_of_mul_eq_mul {ℓ p : R} (hℓ : Prime ℓ) (hp : ¬ ℓ ∣ p) {e g : F}
    (he : IsIntegral R e) (hg : IsIntegral R g) (h : algebraMap R F p * e = algebraMap R F ℓ * g) :
    ∃ e' : F, IsIntegral R e' ∧ e = algebraMap R F ℓ * e' := by
  have hℓF : algebraMap R F ℓ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K F]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hℓ.ne_zero)
  refine ⟨(algebraMap R F ℓ)⁻¹ * e, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hℓF, one_mul]⟩
  refine isIntegral_of_prime_of_not_dvd K hℓ hp ?_ ?_
  · rwa [← mul_assoc, mul_inv_cancel₀ hℓF, one_mul]
  · rw [mul_left_comm, h, ← mul_assoc, inv_mul_cancel₀ hℓF, one_mul]
    exact hg

end Pullback
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

end ModularCurve.DRPullback
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

open NumberField IsDedekindDomain

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRNumberField
p2m_open "ModularCurve"

variable {K : Type*} [Field K] (𝒪 : ValuationSubring K)

private theorem coe_ringOfIntegers_mem (x : 𝓞 K) : (x : K) ∈ 𝒪 := by
  have hx : IsIntegral 𝒪 (x : K) := (RingOfIntegers.isIntegral_coe x).tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪) (K := K)).mp hx
  rw [← hy]
  exact y.2

private noncomputable def ofIntegers : 𝓞 K →+* 𝒪 :=
  (algebraMap (𝓞 K) K).codRestrict 𝒪 (coe_ringOfIntegers_mem 𝒪)

@[scoped simp]
private theorem coe_ofIntegers (x : 𝓞 K) : (ofIntegers 𝒪 x : K) = x :=
  rfl

private noncomputable def centre : Ideal (𝓞 K) :=
  (IsLocalRing.maximalIdeal 𝒪).comap (ofIntegers 𝒪)

private scoped instance centre_isPrime : (centre 𝒪).IsPrime :=
  Ideal.comap_isPrime _ _

private theorem mem_centre_iff (x : 𝓞 K) : x ∈ centre 𝒪 ↔ ofIntegers 𝒪 x ∈ IsLocalRing.maximalIdeal 𝒪 :=
  Iff.rfl

private theorem centre_ne_bot [NumberField K] (h𝒪 : 𝒪 ≠ ⊤) : centre 𝒪 ≠ ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ 𝒪 := by
    by_contra h
    push Not at h
    exact h𝒪 (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  set xa : K := algebraMap (𝓞 K) K a with hxa
  set xb : K := algebraMap (𝓞 K) K b with hxb
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : xa ≠ 0 := by
    intro ha
    exact hx (by rw [ha, zero_div]; exact zero_mem _)

  have hx1 : 1 < 𝒪.valuation (xa / xb) := by
    rw [← not_le, 𝒪.valuation_le_one_iff]; exact hx
  have hinv : (xa / xb)⁻¹ ∈ 𝒪 := (𝒪.mem_or_inv_mem _).resolve_left hx
  have hmax : (⟨(xa / xb)⁻¹, hinv⟩ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [𝒪.valuation_lt_one_iff]
    change 𝒪.valuation (xa / xb)⁻¹ < 1
    rw [map_inv₀, inv_lt_one₀ (zero_lt_one.trans hx1)]
    exact hx1

  intro hbot
  have hbmem : b ∈ centre 𝒪 := by
    rw [mem_centre_iff]
    have : ofIntegers 𝒪 b = ofIntegers 𝒪 a * ⟨(xa / xb)⁻¹, hinv⟩ := by
      apply Subtype.ext
      change xb = xa * (xa / xb)⁻¹
      rw [inv_div, mul_div_cancel₀ _ ha0]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmax
  rw [hbot, Ideal.mem_bot] at hbmem
  exact hb0 hbmem

private noncomputable def centrePt [NumberField K] (h𝒪 : 𝒪 ≠ ⊤) : HeightOneSpectrum (𝓞 K) :=
  ⟨centre 𝒪, inferInstance, centre_ne_bot 𝒪 h𝒪⟩

private theorem valuationSubringAtPrime_le [NumberField K] (h𝒪 : 𝒪 ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime K (centrePt 𝒪 h𝒪) ≤ 𝒪 := by
  rintro x ⟨a, s, hs, rfl⟩
  refine 𝒪.mul_mem _ _ (coe_ringOfIntegers_mem 𝒪 a) ?_

  have hs' : ofIntegers 𝒪 s ∉ IsLocalRing.maximalIdeal 𝒪 := hs
  rw [𝒪.valuation_lt_one_iff, not_lt] at hs'
  have hs1 : 𝒪.valuation (s : K) = 1 :=
    le_antisymm ((𝒪.valuation_le_one_iff _).mpr (coe_ringOfIntegers_mem 𝒪 s)) hs'
  apply 𝒪.mem_of_valuation_le_one
  rw [map_inv₀]
  change (𝒪.valuation (s : K))⁻¹ ≤ 1
  rw [hs1, inv_one]

private theorem valuationSubringAtPrime_eq [NumberField K] (h𝒪 : 𝒪 ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime K (centrePt 𝒪 h𝒪) = 𝒪 :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le 𝒪 h𝒪) h𝒪

private theorem isDiscreteValuationRing [NumberField K] (h𝒪 : 𝒪 ≠ ⊤) : IsDiscreteValuationRing 𝒪 := by
  rw [← valuationSubringAtPrime_eq 𝒪 h𝒪]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (A := 𝓞 K)
    (centrePt 𝒪 h𝒪).ne_bot (HeightOneSpectrum.valuationSubringAtPrime K (centrePt 𝒪 h𝒪))

end ModularCurve.DRNumberField
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount"

noncomputable section

p2m_open "Polynomial IntermediateField ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve ModularCurve.CharPModel"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRMainBound
p2m_open "ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

section LevelField

variable (s : Finset ℚ̄)

private abbrev LevelField : IntermediateField ℚ ℚ̄ := IntermediateField.adjoin ℚ (s : Set ℚ̄)

private scoped instance finiteDimensional_levelField : FiniteDimensional ℚ (LevelField s) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

private scoped instance numberField_levelField : NumberField (LevelField s) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := inferInstance

private scoped instance isAlgebraic_levelField : Algebra.IsAlgebraic ℚ (LevelField s) := Algebra.IsAlgebraic.of_finite ℚ _

private theorem subset_range_algebraMap_levelField : (s : Set ℚ̄) ⊆ Set.range (algebraMap (LevelField s) ℚ̄) := by
  intro x hx
  exact ⟨⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩, rfl⟩

end LevelField
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"

section DVR

variable {E : Type} [Field E] [NumberField E] (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄)

private abbrev 𝒪v : ValuationSubring E := A.comap ι

omit [NumberField E] in
private theorem 𝒪v_toSubring : (𝒪v ι A).toSubring = A.toSubring.comap ι := rfl

omit [NumberField E] in
private theorem 𝒪v_ne_top {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓA : A.valuation ((ℓ : ℕ) : ℚ̄) < 1) : 𝒪v ι A ≠ ⊤ := by
  intro h
  have hℓ0 : ((ℓ : ℕ) : ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero
  have hmem : ((ℓ : ℕ) : E)⁻¹ ∈ 𝒪v ι A := h.symm ▸ Subring.mem_top _
  rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hmem
  have h1 := (A.valuation_le_one_iff _).mpr hmem
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hℓ0))] at h1
  exact absurd hℓA (not_lt_of_ge h1)

private scoped instance isDiscreteValuationRing_𝒪v' : ∀ [Fact (𝒪v ι A ≠ ⊤)], IsDiscreteValuationRing (𝒪v ι A) :=
  fun {h} => DRNumberField.isDiscreteValuationRing (𝒪v ι A) h.out

omit [NumberField E] in

private theorem mem_maximalIdeal_𝒪v_iff (x : 𝒪v ι A) :
    x ∈ IsLocalRing.maximalIdeal (𝒪v ι A) ↔ A.valuation (ι x) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff ι ι.injective]

omit [NumberField E] in
private theorem valuation_lt_one_of_mem_span {ϖ : 𝒪v ι A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (𝒪v ι A)) {x : 𝒪v ι A}
    (hx : x ∈ Ideal.span {ϖ}) : A.valuation (ι x) < 1 :=
  (mem_maximalIdeal_𝒪v_iff ι A x).mp (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖ) hx)

end DVR
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"

section Base

variable {E : Type} [Field E] [Algebra ℚ E] (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (M : ℕ) [NeZero M]

private abbrev F₀ : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull M

private def jF : F₀ M := ⟨jq, modularFunctionField_le_full M (jq_mem M)⟩

private abbrev 𝒪s : Subring E := A.toSubring.comap ι

private abbrev LF (E : Type) [Field E] [Algebra ℚ E] : IntermediateField E (LaurentSeries E) := laurentBaseChange E (F₀ M)

private abbrev Rj : Subring (LF M E) := levelBaseRing (𝒪s ι A) (F₀ M) {jF M}

private abbrev Tj (E : Type) [Field E] [Algebra ℚ E] : LF M E := levelGen₁ (F₀ M) (jF M) E

private theorem transcendental_Tj : Transcendental E (Tj M E) := transcendental_coeffEmb_jq E M

private abbrev ϖR (ϖ : 𝒪s ι A) : Rj ι A M := ⟨levelConst (𝒪s ι A) (F₀ M) ϖ, levelConst_mem _ _ {jF M} ϖ⟩

private theorem prime_ϖR {ϖ : 𝒪s ι A} (hϖ : Prime ϖ) : Prime (ϖR ι A M ϖ) :=
  prime_levelConst (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M) hϖ

private theorem isPrime_span_ϖR {ϖ : 𝒪s ι A} (hϖ : Prime ϖ) : (Ideal.span {ϖR ι A M ϖ}).IsPrime :=
  (Ideal.span_singleton_prime (prime_ϖR ι A M hϖ).ne_zero).mpr (prime_ϖR ι A M hϖ)

section Structure
variable [IsDiscreteValuationRing (𝒪s ι A)]

private theorem uniqueFactorizationMonoid_Rj : UniqueFactorizationMonoid (Rj ι A M) :=
  uniqueFactorizationMonoid_levelBaseRing (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M)

private theorem isIntegrallyClosed_Rj : IsIntegrallyClosed (Rj ι A M) :=
  isIntegrallyClosed_levelBaseRing (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M)

private theorem finiteMultiplicity_ϖR {ϖ : 𝒪s ι A} (hϖ : Prime ϖ) (x : Rj ι A M) (hx : x ≠ 0) :
    FiniteMultiplicity (ϖR ι A M ϖ) x :=
  haveI := uniqueFactorizationMonoid_Rj ι A M
  FiniteMultiplicity.of_prime_left (prime_ϖR ι A M hϖ) hx

end Structure
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"

private abbrev Kj : IntermediateField E (LF M E) := E⟮Tj M E⟯

private theorem Rj_eq_evalRange : Rj ι A M = DRFraction.evalRange (𝒪s ι A) E (Tj M E) := by
  change levelBaseRing (𝒪s ι A) (F₀ M) {jF M} = _
  rw [levelBaseRing_singleton_eq_range]
  rfl

private scoped instance isFractionRing_𝒪s : IsFractionRing (𝒪s ι A) E :=
  IsFractionRing.of_field (𝒪s ι A) E fun z => by
    rcases (𝒪v ι A).mem_or_inv_mem z with h | h
    · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
    · refine ⟨1, ⟨z⁻¹, h⟩, ?_⟩
      rw [map_one, one_div]
      exact (inv_inv z).symm

private theorem Rj_le_Kj : Rj ι A M ≤ (Kj M).toSubring :=
  DRFraction.le_adjoin (𝒪s ι A) E (Tj M E) (Rj ι A M) (Rj_eq_evalRange ι A M)

private scoped instance algebraRjKj : Algebra (Rj ι A M) (Kj M (E := E)) := DRFraction.algebraOfLE (Rj_le_Kj ι A M)

private scoped instance isScalarTower_Rj_Kj : IsScalarTower (Rj ι A M) (Kj M (E := E)) (LF M E) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance isFractionRing_Rj_Kj : IsFractionRing (Rj ι A M) (Kj M (E := E)) :=
  DRFraction.isFractionRing (𝒪s ι A) E (Tj M E) (Rj ι A M) (Rj_eq_evalRange ι A M) (transcendental_Tj M)

private theorem finrank_Kj : Module.finrank (Kj M (E := E)) (LF M E) = dedekindPsi M := by
  refine (DRRelfinrank.finrank_adjoin_eq_relfinrank (LF M E) (Tj M E)).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin E {coeffEmb E jq}) _ = _
  rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi]

private scoped instance finiteDimensional_Kj : FiniteDimensional (Kj M (E := E)) (LF M E) :=
  Module.finite_of_finrank_pos (by rw [finrank_Kj]; exact dedekindPsi_pos M (NeZero.ne M))

private abbrev Bint : Subalgebra (Rj ι A M) (LF M E) := integralClosure (Rj ι A M) (LF M E)

variable (ϖ : 𝒪s ι A) [hϖ : Fact (Prime ϖ)]

private scoped instance isPrime_pIdeal_ϖR : (DRACE.pIdeal (ϖR ι A M ϖ)).IsPrime := isPrime_span_ϖR ι A M hϖ.out

private abbrev locM : Submonoid (Bint ι A M) := DRACE.locSubmonoid (ϖR ι A M ϖ) (Bint ι A M)

private abbrev Bp : Type := Localization (locM ι A M ϖ)

private theorem locM_le_nonZeroDivisors : locM ι A M ϖ ≤ nonZeroDivisors (Bint ι A M) := by
  intro m hm
  obtain ⟨s, hs, hsm⟩ := (DRACE.mem_locSubmonoid_iff (ϖR ι A M ϖ) (Bint ι A M)).mp hm
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
  rw [h0] at hsm
  have : s = 0 := by
    have h1 : ((algebraMap (Rj ι A M) (Bint ι A M) s : Bint ι A M) : LF M E) = 0 := by rw [hsm]; rfl
    exact Subtype.ext h1
  rw [this]; exact Ideal.zero_mem _

private theorem isUnit_val_of_mem_locM (m : locM ι A M ϖ) : IsUnit ((Bint ι A M).val m) := by
  refine IsUnit.mk0 _ fun h0 => ?_
  have := locM_le_nonZeroDivisors ι A M ϖ m.2
  exact nonZeroDivisors.ne_zero this (Subtype.ext h0)

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance moduleBint : Module (Bint ι A M) (Bint ι A M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance algebraBintBp : Algebra (Bint ι A M) (Bp ι A M ϖ) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance isLocalization_Bp : IsLocalization (locM ι A M ϖ) (Bp ι A M ϖ) := inferInstance

private scoped instance smulBintBp : SMul (Bint ι A M) (Bp ι A M ϖ) := Algebra.toSMul

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance distribMulActionBint : DistribMulAction (Bint ι A M) (Bint ι A M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance isScalarTower_Bint : IsScalarTower (Bint ι A M) (Bint ι A M) (Bint ι A M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance algebraRjBint : Algebra (Rj ι A M) (Bint ι A M) := inferInstance

private scoped instance smulRjBint : SMul (Rj ι A M) (Bint ι A M) := Algebra.toSMul

private scoped instance algebraRjBp : Algebra (Rj ι A M) (Bp ι A M ϖ) :=
  ((algebraMap (Bint ι A M) (Bp ι A M ϖ)).comp (algebraMap (Rj ι A M) (Bint ι A M))).toAlgebra

private scoped instance smulRjBp : SMul (Rj ι A M) (Bp ι A M ϖ) := Algebra.toSMul

private theorem algebraMap_Rj_Bp (r : Rj ι A M) :
    algebraMap (Rj ι A M) (Bp ι A M ϖ) r = algebraMap (Bint ι A M) (Bp ι A M ϖ) (algebraMap (Rj ι A M) (Bint ι A M) r) :=
  rfl

private scoped instance isScalarTower_Rj_Bint_Bp : IsScalarTower (Rj ι A M) (Bint ι A M) (Bp ι A M ϖ) :=
  IsScalarTower.of_algebraMap_eq (algebraMap_Rj_Bp ι A M ϖ)

private def φL : Bp ι A M ϖ →ₐ[Rj ι A M] LF M E :=
  { IsLocalization.lift (M := locM ι A M ϖ) (g := (Bint ι A M).val.toRingHom) (isUnit_val_of_mem_locM ι A M ϖ) with
    commutes' := fun r => by
      change IsLocalization.lift _ (algebraMap (Bint ι A M) (Bp ι A M ϖ) (algebraMap (Rj ι A M) (Bint ι A M) r)) = _
      rw [IsLocalization.lift_eq]
      rfl }

private theorem φL_injective : Function.Injective (φL ι A M ϖ) := by
  intro x y hxy
  change IsLocalization.lift (M := locM ι A M ϖ) _ x = IsLocalization.lift (M := locM ι A M ϖ) _ y at hxy
  exact (IsLocalization.lift_injective_iff _).mpr
    (fun a b => ⟨fun h => congrArg _ ((IsLocalization.injective (Bp ι A M ϖ) (locM_le_nonZeroDivisors ι A M ϖ)) h),
      fun h => congrArg _ (Subtype.ext h)⟩) hxy

end Base
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"

end ModularCurve.DRMainBound
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField"

p2m_open "Polynomial IntermediateField ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRMainBound
p2m_open "ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {E : Type} [Field E] [Algebra ℚ E] (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (M : ℕ) [NeZero M]

private theorem affineBaseFin_eq_levelBaseRing : affineBaseFin M A = levelBaseRing A.toSubring (F₀ M) {jF M} := by
  unfold affineBaseFin levelBaseRing
  rw [range_levelGen_singleton]
  rfl

private theorem algebraMap_Rj_eq_subtype : algebraMap (Rj ι A M) (LF M E) = (Rj ι A M).subtype := RingHom.ext fun _ => rfl

private theorem isIntegral_iff_exists_monic (x : LF M E) :
    IsIntegral (Rj ι A M) x ↔
      ∃ q : Polynomial (Rj ι A M), q.Monic ∧ Polynomial.eval₂ (Rj ι A M).subtype x q = 0 := by
  unfold IsIntegral RingHom.IsIntegralElem
  rw [algebraMap_Rj_eq_subtype]

private theorem coeff_mem_𝒪s (b : LF M E) (hb : IsIntegral (Rj ι A M) b) (n : ℤ) : (b : LaurentSeries E).coeff n ∈ 𝒪s ι A := by
  have h1 := integral_laurentDescent_of_integral (F₀ M) ({jF M} : Set (F₀ M)) ι A.toSubring b
    ((isIntegral_iff_exists_monic ι A M b).mp hb)
  rw [← affineBaseFin_eq_levelBaseRing] at h1
  have h2 := mem_integralCoeffs_of_integral_affineBaseFin A M (laurentDescent ι (F₀ M) b) h1
  exact (laurentDescent_mem_integralCoeffs_iff (F₀ M) ι A.toSubring b).mp h2 n

private def toIC : Bint ι A M →+* integralCoeffs (𝒪s ι A) where
  toFun b := ⟨((b : LF M E) : LaurentSeries E), coeff_mem_𝒪s ι A M b b.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[scoped simp] private theorem coe_toIC (b : Bint ι A M) : (toIC ι A M b : LaurentSeries E) = ((b : LF M E) : LaurentSeries E) := rfl

section Reduction

variable [IsDiscreteValuationRing (𝒪s ι A)]

private abbrev k₀ : Type := IsLocalRing.ResidueField (𝒪s ι A)

private abbrev red₀ : 𝒪s ι A →+* k₀ ι A := IsLocalRing.residue (𝒪s ι A)

private def π₁ : Bint ι A M →+* LaurentSeries (k₀ ι A) := (coeffRed (𝒪s ι A) (red₀ ι A)).comp (toIC ι A M)

private theorem π₁_coeff (b : Bint ι A M) (n : ℤ) :
    (π₁ ι A M b).coeff n = red₀ ι A ⟨((b : LF M E) : LaurentSeries E).coeff n, (toIC ι A M b).2 n⟩ :=
  rfl

private theorem π₁_eq_map_of_coe_eq (b : Bint ι A M) (y : LaurentSeries (𝒪s ι A))
    (h : ((b : LF M E) : LaurentSeries E) = y.map (𝒪s ι A).subtype) : π₁ ι A M b = y.map (red₀ ι A) := by
  ext n
  rw [π₁_coeff, HahnSeries.map_coeff]
  congr 1
  apply Subtype.ext
  change ((b : LF M E) : LaurentSeries E).coeff n = _
  rw [h, HahnSeries.map_coeff]
  rfl

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] [Algebra ℚ E] in

private theorem C_map_eq {S : Type*} [CommRing S] (f : 𝒪s ι A →+* S) (c : 𝒪s ι A) :
    (HahnSeries.C c : LaurentSeries (𝒪s ι A)).map f = HahnSeries.C (f c) := by
  ext n
  rw [HahnSeries.map_coeff]
  change f ((HahnSeries.single 0 c).coeff n) = (HahnSeries.single 0 (f c)).coeff n
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f, map_zero]

private theorem π₁_const (c : 𝒪s ι A) (b : Bint ι A M) (hb : ((b : LF M E) : LaurentSeries E) = HahnSeries.C (c : E)) :
    π₁ ι A M b = HahnSeries.C (red₀ ι A c) := by
  rw [π₁_eq_map_of_coe_eq ι A M b (HahnSeries.C c) (hb.trans (C_map_eq ι A (𝒪s ι A).subtype c).symm), C_map_eq]

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] in

private theorem coeffEmb_qExpand_jq_eq_map (d : ℕ) [NeZero d] :
    coeffEmb E (qExpand ℚ d jq) = (jqNModC (𝒪s ι A) d).map (𝒪s ι A).subtype := by
  rw [coeffEmb_qExpand, show jq = jqModC ℚ from rfl, coeffEmb]
  change qExpand E d ((jqModC ℚ).map (algebraMap ℚ E)) = coeffMap (𝒪s ι A).subtype (qExpand _ d (jqModC _))
  rw [map_jqModC, coeffMap_qExpand]
  change _ = qExpand E d ((jqModC (𝒪s ι A)).map (𝒪s ι A).subtype)
  rw [map_jqModC]

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] in
private theorem coeffEmb_jq_eq_map : coeffEmb E jq = (jqModC (𝒪s ι A)).map (𝒪s ι A).subtype := by
  have h := coeffEmb_qExpand_jq_eq_map (E := E) ι A 1
  rwa [qExpand_one_apply, jqNModC_one] at h

private theorem π₁_gen (d : ℕ) [NeZero d] (b : Bint ι A M) (hb : ((b : LF M E) : LaurentSeries E) = coeffEmb E (qExpand ℚ d jq)) :
    π₁ ι A M b = jqNModC (k₀ ι A) d := by
  rw [π₁_eq_map_of_coe_eq ι A M b (jqNModC (𝒪s ι A) d) (hb.trans (coeffEmb_qExpand_jq_eq_map ι A d))]
  change coeffMap (red₀ ι A) (qExpand _ d (jqModC _)) = qExpand _ d (jqModC _)
  rw [coeffMap_qExpand]
  exact congrArg _ (map_jqModC (red₀ ι A))

private theorem π₁_Tj (b : Bint ι A M) (hb : ((b : LF M E) : LaurentSeries E) = coeffEmb E jq) : π₁ ι A M b = jqModC (k₀ ι A) := by
  have h := π₁_gen ι A M 1 b (by rwa [qExpand_one_apply])
  rwa [jqNModC_one] at h

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] in
private theorem coe_levelConst (c : 𝒪s ι A) :
    ((levelConst (𝒪s ι A) (F₀ M) c : LF M E) : LaurentSeries E) = HahnSeries.C (c : E) := by
  rw [levelConst_apply]
  change algebraMap E (LaurentSeries E) (c : E) = _
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] [Algebra ℚ E] in

private theorem algebraMap_laurentSeries_eq_C (K : Type*) [Field K] :
    (algebraMap K (LaurentSeries K) : K →+* LaurentSeries K) = HahnSeries.C := by
  refine RingHom.ext fun c => ?_
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

omit [IsDiscreteValuationRing (𝒪s ι A)] in

private theorem coe_levelEval (p : Polynomial (𝒪s ι A)) :
    ((levelEval (𝒪s ι A) (F₀ M) (jF M) p : LF M E) : LaurentSeries E) =
      (p.eval₂ HahnSeries.C (jqModC (𝒪s ι A))).map (𝒪s ι A).subtype := by
  change (LF M E).val.toRingHom (Polynomial.eval₂RingHom (levelConst (𝒪s ι A) (F₀ M)) (levelGen₁ (F₀ M) (jF M) E) p) =
    coeffMap (𝒪s ι A).subtype (p.eval₂ HahnSeries.C (jqModC (𝒪s ι A)))
  rw [Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, Polynomial.hom_eval₂]
  congr 1
  · exact RingHom.ext fun c => (coe_levelConst ι A M c).trans (C_map_eq ι A (𝒪s ι A).subtype c).symm
  · exact coeffEmb_jq_eq_map ι A

omit [NeZero M] [IsDiscreteValuationRing (𝒪s ι A)] [Algebra ℚ E] in
private theorem map_eval₂_C {S : Type*} [CommRing S] (f : 𝒪s ι A →+* S) (p : Polynomial (𝒪s ι A)) (y : LaurentSeries (𝒪s ι A)) :
    (p.eval₂ HahnSeries.C y).map f = (p.map f).eval₂ HahnSeries.C (y.map f) := by
  change coeffMap f (p.eval₂ HahnSeries.C y) = _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext fun c => C_map_eq ι A f c

private theorem π₁_levelEval (p : Polynomial (𝒪s ι A)) (b : Bint ι A M)
    (hb : (b : LF M E) = (levelEval (𝒪s ι A) (F₀ M) (jF M) p : LF M E)) :
    π₁ ι A M b = (p.map (red₀ ι A)).eval₂ HahnSeries.C (jqModC (k₀ ι A)) := by
  rw [π₁_eq_map_of_coe_eq ι A M b _ ((congrArg Subtype.val hb).trans (coe_levelEval ι A M p)), map_eval₂_C,
    map_jqModC]

omit [Algebra ℚ E] in

private theorem map_eq_zero_of_eval₂_eq_zero (p : Polynomial (𝒪s ι A))
    (h : (p.map (red₀ ι A)).eval₂ HahnSeries.C (jqModC (k₀ ι A)) = 0) : p.map (red₀ ι A) = 0 := by
  have ht := transcendental_jqModC (k₀ ι A)
  rw [transcendental_iff_injective] at ht
  refine (injective_iff_map_eq_zero _).mp ht _ ?_
  rwa [Polynomial.aeval_def, algebraMap_laurentSeries_eq_C]

omit [Algebra ℚ E] in

private theorem C_dvd_of_map_eq_zero {ϖ : 𝒪s ι A} (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (p : Polynomial (𝒪s ι A)) (h : p.map (red₀ ι A) = 0) : Polynomial.C ϖ ∣ p := by
  rw [← Ideal.mem_span_singleton, show Ideal.span {Polynomial.C ϖ} = (Ideal.span {ϖ}).map Polynomial.C from by
    rw [Ideal.map_span, Set.image_singleton], Ideal.mem_map_C_iff]
  intro n
  rw [← hmax, ← IsLocalRing.residue_eq_zero_iff]
  have := congrArg (fun q => Polynomial.coeff q n) h
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this

private theorem π₁_ϖR {ϖ : 𝒪s ι A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (𝒪s ι A)) :
    π₁ ι A M (algebraMap (Rj ι A M) (Bint ι A M) (ϖR ι A M ϖ)) = 0 := by
  rw [π₁_const ι A M ϖ]
  · rw [(IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ, map_zero]
  · exact coe_levelConst ι A M ϖ

private theorem π₁_ne_zero_of_not_mem {ϖ : 𝒪s ι A} (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (s : Rj ι A M) (hs : s ∉ DRACE.pIdeal (ϖR ι A M ϖ)) :
    π₁ ι A M (algebraMap (Rj ι A M) (Bint ι A M) s) ≠ 0 := by
  obtain ⟨p, rfl⟩ := (levelPolynomialEquiv (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M)).surjective s
  rw [π₁_levelEval ι A M p _ rfl]
  intro h
  apply hs
  have hdvd := C_dvd_of_map_eq_zero ι A hmax p (map_eq_zero_of_eval₂_eq_zero ι A p h)
  rw [DRACE.pIdeal, Ideal.mem_span_singleton]
  have hC : levelPolynomialEquiv (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M) (Polynomial.C ϖ) = ϖR ι A M ϖ :=
    Subtype.ext (levelPolynomialEquiv_C _ _ _ _ ϖ)
  rw [← hC]
  exact map_dvd (levelPolynomialEquiv (𝒪s ι A) (F₀ M) (jF M) (transcendental_Tj M)) hdvd

end Reduction
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Generators

private def gE (E : Type) [Field E] [Algebra ℚ E] (d : ℕ) [NeZero d] (hd : d ∣ M) : LF M E :=
  ⟨coeffEmb E (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange E (jqd_mem_full M hd)⟩

omit [NeZero M] in
private theorem qExpand_eq_of_eq {R : Type*} [CommRing R] {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (f : LaurentSeries R) :
    qExpand R a f = qExpand R b f := by
  subst h
  rfl

omit [NeZero M] in
@[scoped simp] private theorem coe_gE (d : ℕ) [NeZero d] (hd : d ∣ M) : (gE M E d hd : LaurentSeries E) = coeffEmb E (qExpand ℚ d jq) := rfl

private theorem gE_one : gE M E 1 (one_dvd M) = Tj M E :=
  Subtype.ext (by rw [coe_gE, qExpand_one_apply]; rfl)

omit [Algebra ℚ E] [NeZero M] in

private theorem ringHom_int_eq (f : Polynomial ℤ →+* LaurentSeries E) :
    f = Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries E)) (f Polynomial.X) :=
  Polynomial.ringHom_ext (fun a => by simp) (by simp)

omit [NeZero M] in

private theorem modular_equation (d p : ℕ) [NeZero d] [NeZero p] (hdp : d * p ∣ M) (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries E)) (gE M E d (dvd_of_mul_right_dvd hdp) : LaurentSeries E))
      (gE M E (d * p) hdp : LaurentSeries E) = 0 := by
  have h0 := congrArg (fun y => coeffEmb E (qExpand ℚ d y)) data.eval_eq_zero
  simp only [map_zero] at h0
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂] at h0
  rw [coe_gE, coe_gE, ← qExpand_qExpand, ringHom_int_eq ((coeffEmb E).comp ((qExpand ℚ d).comp evalAtJ))] at *
  convert h0 using 2 <;> first | rfl | (congr 1; simp [evalAtJ])

private theorem isIntegral_gE_mul {d p : ℕ} [NeZero d] [Fact p.Prime] (hdp : d * p ∣ M)
    (hd : IsIntegral (Rj ι A M) (gE M E d (dvd_of_mul_right_dvd hdp))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsIntegral (Rj ι A M) (gE M E (d * p) hdp) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨data, -⟩ := exists_modularPolynomialData_evalSymm p

  set x : Bint ι A M := ⟨gE M E d (dvd_of_mul_right_dvd hdp), hd⟩
  let ψ : Polynomial ℤ →+* Bint ι A M := Polynomial.eval₂RingHom (algebraMap ℤ (Bint ι A M)) x
  have hint : IsIntegral (Bint ι A M) (gE M E (d * p) hdp) := by
    refine ⟨data.Φ.map ψ, data.monic.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    apply Subtype.val_injective
    change (LF M E).val.toRingHom (Polynomial.eval₂ ((algebraMap (Bint ι A M) (LF M E)).comp ψ) (gE M E (d * p) hdp) data.Φ) =
      ((0 : LF M E) : LaurentSeries E)
    rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero, ← modular_equation M d p hdp data]
    congr 1
    rw [ringHom_int_eq (((LF M E).val.toRingHom.comp ((algebraMap (Bint ι A M) (LF M E)).comp ψ)))]
    congr 1
    change (((ψ Polynomial.X : Bint ι A M) : LF M E) : LaurentSeries E) = _
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  exact isIntegral_trans _ hint

private theorem isIntegral_gE : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ M), IsIntegral (Rj ι A M) (gE M E d hd) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd0 hd
    by_cases h1 : d = 1
    · subst h1
      rw [gE_one, isIntegral_iff_exists_monic]
      refine ⟨Polynomial.X - Polynomial.C ⟨Tj M E, levelGen_mem (𝒪s ι A) (F₀ M) {jF M} ⟨jF M, rfl⟩⟩,
        Polynomial.monic_X_sub_C _, ?_⟩
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact sub_self _
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨d', rfl⟩ := hpd
      haveI := Fact.mk hp
      have hd'0 : NeZero d' := ⟨fun h => hd0.out (by rw [h, mul_zero])⟩
      have hlt : d' < p * d' := lt_mul_left (Nat.pos_of_ne_zero hd'0.out) hp.one_lt
      have hd' : d' * p ∣ M := by rwa [mul_comm] at hd
      have key := isIntegral_gE_mul ι A M hd' (ih d' hlt hd'0 (dvd_of_mul_right_dvd hd'))
      have heq : gE M E (p * d') hd = gE M E (d' * p) hd' := Subtype.ext (by rw [coe_gE, coe_gE, qExpand_eq_of_eq (mul_comm p d')])
      rwa [heq]

private theorem gE_mem_Bint (d : ℕ) [NeZero d] (hd : d ∣ M) : gE M E d hd ∈ Bint ι A M := isIntegral_gE ι A M d inferInstance hd

end Generators
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section AtkinLehner

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) (hσ : IsAtkinLehnerAutFull N ℓ σ)

private scoped instance neZero_ℓ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

private abbrev wE (E : Type) [Field E] [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E] :
    LF (N * ℓ) E ≃ₐ[E] LF (N * ℓ) E :=
  geomAut E (F₀ (N * ℓ)) σ

variable [Algebra.IsAlgebraic ℚ E]

include hσ in

private theorem σ_jF : (σ (jF (N * ℓ)) : LaurentSeries ℚ) = qExpand ℚ ℓ jq ∧
    (σ ⟨qExpand ℚ ℓ jq, jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N)⟩ : LaurentSeries ℚ) = jq := by
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have e1 : (⟨qExpand ℚ 1 jq, jqd_mem_full (N * ℓ) (Dvd.dvd.mul_right (one_dvd N) ℓ)⟩ : F₀ (N * ℓ)) = jF (N * ℓ) :=
    Subtype.ext (qExpand_one_apply jq)
  have e2 : (⟨qExpand ℚ (1 * ℓ) jq, jqd_mem_full (N * ℓ) (Nat.mul_dvd_mul_right (one_dvd N) ℓ)⟩ : F₀ (N * ℓ)) =
      ⟨qExpand ℚ ℓ jq, jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N)⟩ :=
    Subtype.ext (qExpand_eq_of_eq (one_mul ℓ) jq)
  rw [e1, e2] at h1 h2
  exact ⟨(congrArg Subtype.val h1).trans rfl, (congrArg Subtype.val h2).trans rfl⟩

include hσ in

private theorem wE_Tj : wE N ℓ σ E (Tj (N * ℓ) E) = gE (N * ℓ) E ℓ (dvd_mul_left ℓ N) := by
  apply Subtype.ext
  change ((geomAut E (F₀ (N * ℓ)) σ ⟨coeffEmb E (jF (N * ℓ) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange E (jF (N * ℓ)).2⟩ : LF (N * ℓ) E) : LaurentSeries E) = _
  rw [coe_geomAut_coeffEmb, (σ_jF N ℓ σ hσ).1, coe_gE]

include hσ in

private theorem wE_symm_Tj : (wE N ℓ σ E).symm (Tj (N * ℓ) E) = gE (N * ℓ) E ℓ (dvd_mul_left ℓ N) := by
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  change _ = ((geomAut E (F₀ (N * ℓ)) σ ⟨coeffEmb E ((⟨qExpand ℚ ℓ jq, jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N)⟩ :
      F₀ (N * ℓ)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange E (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N))⟩ :
    LF (N * ℓ) E) : LaurentSeries E)
  rw [coe_geomAut_coeffEmb, (σ_jF N ℓ σ hσ).2]
  rfl

omit [Fact ℓ.Prime] [Algebra.IsAlgebraic ℚ E] in

private theorem map_Rj_le_Bint [NeZero ℓ] (w : LF (N * ℓ) E ≃ₐ[E] LF (N * ℓ) E) (hw : w (Tj (N * ℓ) E) ∈ Bint ι A (N * ℓ)) :
    (Rj ι A (N * ℓ)).map w.toRingEquiv.toRingHom ≤ (Bint ι A (N * ℓ)).toSubring := by
  rw [Subring.map_le_iff_le_comap]
  change Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro x (⟨c, rfl⟩ | ⟨g, rfl⟩)
  · change w (levelConst (𝒪s ι A) (F₀ (N * ℓ)) c) ∈ Bint ι A (N * ℓ)
    have hc : w (levelConst (𝒪s ι A) (F₀ (N * ℓ)) c) = levelConst (𝒪s ι A) (F₀ (N * ℓ)) c := by
      rw [levelConst_apply, AlgEquiv.commutes]
    rw [hc]
    exact (Bint ι A (N * ℓ)).algebraMap_mem (⟨_, levelConst_mem (𝒪s ι A) (F₀ (N * ℓ)) {jF (N * ℓ)} c⟩ : Rj ι A (N * ℓ))
  · obtain ⟨g, hg⟩ := g
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hw

omit [Fact ℓ.Prime] [Algebra.IsAlgebraic ℚ E] in

private theorem map_mem_Bint [NeZero ℓ] (w : LF (N * ℓ) E ≃ₐ[E] LF (N * ℓ) E) (hw : w (Tj (N * ℓ) E) ∈ Bint ι A (N * ℓ))
    (b : LF (N * ℓ) E) (hb : b ∈ Bint ι A (N * ℓ)) : w b ∈ Bint ι A (N * ℓ) := by

  let ψ : Rj ι A (N * ℓ) →+* Bint ι A (N * ℓ) :=
    { toFun := fun r => ⟨w r, map_Rj_le_Bint ι A N ℓ w hw ⟨r, r.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one w)
      map_mul' := fun _ _ => Subtype.ext (map_mul w _ _)
      map_zero' := Subtype.ext (map_zero w)
      map_add' := fun _ _ => Subtype.ext (map_add w _ _) }
  obtain ⟨p, hp, hpb⟩ := hb
  have hint : IsIntegral (Bint ι A (N * ℓ)) (w b) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Bint ι A (N * ℓ)) (LF (N * ℓ) E)).comp ψ =
        w.toRingEquiv.toRingHom.comp (algebraMap (Rj ι A (N * ℓ)) (LF (N * ℓ) E)) := RingHom.ext fun _ => rfl
    rw [hcomp, show w b = w.toRingEquiv.toRingHom b from rfl, ← Polynomial.hom_eval₂, hpb, map_zero]
  exact isIntegral_trans _ hint

private theorem wE_mem_Bint (hσ : IsAtkinLehnerAutFull N ℓ σ) (b : LF (N * ℓ) E) (hb : b ∈ Bint ι A (N * ℓ)) :
    wE N ℓ σ E b ∈ Bint ι A (N * ℓ) :=
  map_mem_Bint ι A N ℓ _ (by rw [wE_Tj N ℓ σ hσ]; exact gE_mem_Bint ι A (N * ℓ) ℓ _) b hb

private theorem wE_symm_mem_Bint (hσ : IsAtkinLehnerAutFull N ℓ σ) (b : LF (N * ℓ) E) (hb : b ∈ Bint ι A (N * ℓ)) :
    (wE N ℓ σ E).symm b ∈ Bint ι A (N * ℓ) :=
  map_mem_Bint ι A N ℓ _ (by rw [wE_symm_Tj N ℓ σ hσ]; exact gE_mem_Bint ι A (N * ℓ) ℓ _) b hb

private def wB (hσ : IsAtkinLehnerAutFull N ℓ σ) : Bint ι A (N * ℓ) →+* Bint ι A (N * ℓ) where
  toFun b := ⟨wE N ℓ σ E b, wE_mem_Bint ι A N ℓ σ hσ b b.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] private theorem coe_wB (hσ : IsAtkinLehnerAutFull N ℓ σ) (b : Bint ι A (N * ℓ)) :
    (wB ι A N ℓ σ hσ b : LF (N * ℓ) E) = wE N ℓ σ E b := rfl

section Pi2
variable [IsDiscreteValuationRing (𝒪s ι A)]

private def π₂ (hσ : IsAtkinLehnerAutFull N ℓ σ) : Bint ι A (N * ℓ) →+* LaurentSeries (k₀ ι A) :=
  (π₁ ι A (N * ℓ)).comp (wB ι A N ℓ σ hσ)

private theorem π₂_apply (hσ : IsAtkinLehnerAutFull N ℓ σ) (b : Bint ι A (N * ℓ)) :
    π₂ ι A N ℓ σ hσ b = π₁ ι A (N * ℓ) (wB ι A N ℓ σ hσ b) := rfl

omit [IsDiscreteValuationRing (𝒪s ι A)] in

private theorem coe_wE_levelEval (hσ : IsAtkinLehnerAutFull N ℓ σ) (p : Polynomial (𝒪s ι A)) :
    ((wE N ℓ σ E (levelEval (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) p) : LF (N * ℓ) E) : LaurentSeries E) =
      (p.eval₂ HahnSeries.C (jqNModC (𝒪s ι A) ℓ)).map (𝒪s ι A).subtype := by
  change ((LF (N * ℓ) E).val.toRingHom.comp (wE N ℓ σ E).toRingEquiv.toRingHom)
      (Polynomial.eval₂RingHom (levelConst (𝒪s ι A) (F₀ (N * ℓ))) (levelGen₁ (F₀ (N * ℓ)) (jF (N * ℓ)) E) p) =
    coeffMap (𝒪s ι A).subtype (p.eval₂ HahnSeries.C (jqNModC (𝒪s ι A) ℓ))
  rw [Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, Polynomial.hom_eval₂]
  congr 1
  · refine RingHom.ext fun c => ?_
    change ((wE N ℓ σ E (levelConst (𝒪s ι A) (F₀ (N * ℓ)) c) : LF (N * ℓ) E) : LaurentSeries E) = _
    rw [levelConst_apply, AlgEquiv.commutes, ← levelConst_apply, coe_levelConst]
    exact (C_map_eq ι A (𝒪s ι A).subtype c).symm
  · change ((wE N ℓ σ E (Tj (N * ℓ) E) : LF (N * ℓ) E) : LaurentSeries E) = _
    rw [wE_Tj N ℓ σ hσ, coe_gE]
    exact coeffEmb_qExpand_jq_eq_map ι A ℓ

private theorem π₂_levelEval (hσ : IsAtkinLehnerAutFull N ℓ σ) (p : Polynomial (𝒪s ι A)) (b : Bint ι A (N * ℓ))
    (hb : (b : LF (N * ℓ) E) = (levelEval (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) p : LF (N * ℓ) E)) :
    π₂ ι A N ℓ σ hσ b = qExpand (k₀ ι A) ℓ ((p.map (red₀ ι A)).eval₂ HahnSeries.C (jqModC (k₀ ι A))) := by
  rw [π₂_apply, π₁_eq_map_of_coe_eq ι A (N * ℓ) _ _ (by rw [coe_wB, hb]; exact coe_wE_levelEval ι A N ℓ σ hσ p),
    map_eval₂_C]
  change _ = qExpand (k₀ ι A) ℓ (Polynomial.eval₂ HahnSeries.C (jqModC (k₀ ι A)) (p.map (red₀ ι A)))
  rw [Polynomial.hom_eval₂]
  congr 1
  · exact (RingHom.ext fun c => qExpand_C ℓ c).symm
  · change coeffMap (red₀ ι A) (qExpand _ ℓ (jqModC _)) = _
    rw [coeffMap_qExpand]
    exact congrArg _ (map_jqModC (red₀ ι A))

private theorem π₂_ϖR (hσ : IsAtkinLehnerAutFull N ℓ σ) {ϖ : 𝒪s ι A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (𝒪s ι A)) :
    π₂ ι A N ℓ σ hσ (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (ϖR ι A (N * ℓ) ϖ)) = 0 := by
  have h := π₂_levelEval ι A N ℓ σ hσ (Polynomial.C ϖ) (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (ϖR ι A (N * ℓ) ϖ))
    (by rw [levelEval_C]; rfl)
  rw [h, Polynomial.map_C, Polynomial.eval₂_C, (IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ, map_zero, map_zero]

private theorem π₂_ne_zero_of_not_mem (hσ : IsAtkinLehnerAutFull N ℓ σ) {ϖ : 𝒪s ι A}
    (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ}) (s : Rj ι A (N * ℓ))
    (hs : s ∉ DRACE.pIdeal (ϖR ι A (N * ℓ) ϖ)) :
    π₂ ι A N ℓ σ hσ (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) s) ≠ 0 := by
  obtain ⟨p, rfl⟩ := (levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ))).surjective s
  rw [π₂_levelEval ι A N ℓ σ hσ p _ rfl, Ne, map_eq_zero_iff _ (qExpand_injective ℓ)]
  have h := π₁_ne_zero_of_not_mem ι A (N * ℓ) hmax _ hs
  rwa [π₁_levelEval ι A (N * ℓ) p _ rfl] at h

end Pi2
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

end AtkinLehner
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

end ModularCurve.DRMainBound
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

p2m_open "Polynomial IntermediateField ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRMainBound
p2m_open "ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

section Residue

variable (k : Type) [Field k] (N : ℕ) [NeZero N]

private abbrev K₁ : IntermediateField k (LaurentSeries k) := k⟮jqModC k⟯

private theorem K₁_le : K₁ k ≤ modularFunctionFieldC k N :=
  IntermediateField.adjoin_simple_le_iff.mpr (jqModC_mem k N)

private abbrev V : IntermediateField (K₁ k) (LaurentSeries k) := IntermediateField.extendScalars (K₁_le k N)

private theorem adjoin_jqN_eq_V : (K₁ k)⟮jqNModC k N⟯ = V k N := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr (jqNModC_mem k N)
  · intro x hx
    change x ∈ (modularFunctionFieldC k N).toSubfield at hx
    rw [modularFunctionFieldC, IntermediateField.adjoin_toSubfield] at hx
    refine (Subfield.closure_le.mpr ?_) hx
    rintro y (⟨c, rfl⟩ | hy)
    · exact ((K₁ k)⟮jqNModC k N⟯).algebraMap_mem ⟨algebraMap k _ c, (K₁ k).algebraMap_mem c⟩
    · rcases hy with rfl | hy
      · exact ((K₁ k)⟮jqNModC k N⟯).algebraMap_mem ⟨jqModC k, mem_adjoin_simple_self k (jqModC k)⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact mem_adjoin_simple_self _ (jqNModC k N)

variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]

private theorem finrank_V (hℓN : ¬ ℓ ∣ N) : Module.finrank (K₁ k) (V k N) = dedekindPsi N :=
  (IntermediateField.relfinrank_eq_finrank_of_le (K₁_le k N)).symm.trans
    (relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N ℓ hℓN)

private theorem natDegree_minpoly_jqN (hℓN : ¬ ℓ ∣ N) : (minpoly (K₁ k) (jqNModC k N)).natDegree = dedekindPsi N := by
  haveI : FiniteDimensional (K₁ k) (V k N) :=
    Module.finite_of_finrank_pos (by rw [finrank_V k N ℓ hℓN]; exact dedekindPsi_pos N (NeZero.ne N))
  have hint : IsIntegral (K₁ k) (jqNModC k N) :=
    (IsIntegral.of_finite (K₁ k) (⟨jqNModC k N, jqNModC_mem k N⟩ : V k N)).algebraMap
  rw [← IntermediateField.adjoin.finrank hint, adjoin_jqN_eq_V, finrank_V k N ℓ hℓN]

private theorem linearIndependent_pow_jqN (hℓN : ¬ ℓ ∣ N) :
    LinearIndependent (K₁ k) fun b : Fin (dedekindPsi N) => jqNModC k N ^ (b : ℕ) :=
  (linearIndependent_pow (K := K₁ k) (jqNModC k N)).comp (Fin.cast (natDegree_minpoly_jqN k N ℓ hℓN).symm)
    (Fin.cast_injective _)

omit [Fact ℓ.Prime] [CharP k ℓ] [NeZero N] in
private theorem aeval_eq_eval₂_C (x : LaurentSeries k) (p : k[X]) : aeval x p = p.eval₂ HahnSeries.C x := by
  rw [aeval_def, algebraMap_laurentSeries_eq_C]

private theorem rel₁ (hℓN : ¬ ℓ ∣ N) (q : Fin (dedekindPsi N) → k[X])
    (h : ∑ b, (q b).eval₂ HahnSeries.C (jqModC k) * jqNModC k N ^ (b : ℕ) = 0) : ∀ b, q b = 0 := by
  refine DRHind.eq_zero_of_sum_aeval_mul_eq_zero (jqModC k) (transcendental_jqModC k) _
    (linearIndependent_pow_jqN k N ℓ hℓN) q ?_
  rw [← h]
  exact Finset.sum_congr rfl fun b _ => by rw [aeval_eq_eval₂_C]

private theorem rel₂ (hℓN : ¬ ℓ ∣ N) (q : Fin ℓ → Fin (dedekindPsi N) → k[X])
    (h : ∑ a, ∑ b, (expand k ℓ (q a b)).eval₂ HahnSeries.C (jqModC k) * (jqModC k ^ (a : ℕ) * jqNModC k N ^ (b : ℕ)) = 0) :
    ∀ a b, q a b = 0 := by
  refine DRHind.eq_zero_of_sum_sum_aeval_expand_mul_eq_zero (jqModC k) (transcendental_jqModC k) _
    (linearIndependent_pow_jqN k N ℓ hℓN) (Fact.out : ℓ.Prime).pos q ?_
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [aeval_eq_eval₂_C]

omit [NeZero N] in

private theorem qExpand_eval₂_C (p : k[X]) :
    qExpand k ℓ (p.eval₂ HahnSeries.C (jqModC k)) = (expand k ℓ p).eval₂ HahnSeries.C (jqModC k) := by
  rw [Polynomial.hom_eval₂, ← aeval_eq_eval₂_C, expand_aeval, aeval_eq_eval₂_C,
    ← frobenius_identity_geom_unconditional k (ℓ := ℓ)]
  congr 1
  · exact RingHom.ext fun c => qExpand_C ℓ c

omit [CharP k ℓ] [NeZero N] in

private theorem jqModC_ne_pow : jqModC k - (jqModC k ^ ℓ) ^ ℓ ≠ 0 := by
  have h := transcendental_iff_injective.mp (transcendental_jqModC k)
  intro h0
  have h1 : aeval (jqModC k) (X - (X ^ ℓ) ^ ℓ : k[X]) = 0 := by simp [h0]
  have h2 : (X - (X ^ ℓ) ^ ℓ : k[X]) = 0 := (injective_iff_map_eq_zero _).mp h _ h1
  have hℓ := (Fact.out : ℓ.Prime).two_le
  have h3 := congrArg (fun p : k[X] => p.coeff 1) h2
  simp only [coeff_sub, coeff_X_one, ← pow_mul, coeff_X_pow, coeff_zero] at h3
  rw [if_neg (by nlinarith)] at h3
  simp at h3

end Residue
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Families

variable {E : Type} [Field E] [Algebra ℚ E] (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private def TB : Bint ι A (N * ℓ) :=
  ⟨Tj (N * ℓ) E, (Bint ι A (N * ℓ)).algebraMap_mem
    (⟨Tj (N * ℓ) E, levelGen_mem (𝒪s ι A) (F₀ (N * ℓ)) {jF (N * ℓ)} ⟨jF (N * ℓ), rfl⟩⟩ : Rj ι A (N * ℓ))⟩

@[scoped simp] private theorem coe_TB : (TB ι A N ℓ : LF (N * ℓ) E) = Tj (N * ℓ) E := rfl

private def gB (d : ℕ) [NeZero d] (hd : d ∣ N * ℓ) : Bint ι A (N * ℓ) := ⟨gE (N * ℓ) E d hd, gE_mem_Bint ι A (N * ℓ) d hd⟩

@[scoped simp] private theorem coe_gB (d : ℕ) [NeZero d] (hd : d ∣ N * ℓ) : (gB ι A N ℓ d hd : LF (N * ℓ) E) = gE (N * ℓ) E d hd := rfl

section Values
variable [IsDiscreteValuationRing (𝒪s ι A)]

private theorem π₁_TB : π₁ ι A (N * ℓ) (TB ι A N ℓ) = jqModC (k₀ ι A) := π₁_Tj ι A (N * ℓ) _ rfl

private theorem π₁_gB (d : ℕ) [NeZero d] (hd : d ∣ N * ℓ) : π₁ ι A (N * ℓ) (gB ι A N ℓ d hd) = jqNModC (k₀ ι A) d :=
  π₁_gen ι A (N * ℓ) d _ rfl

private theorem mem_pIdeal_of_map_eq_zero {ϖ : 𝒪s ι A} (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (p : Polynomial (𝒪s ι A)) (h : p.map (red₀ ι A) = 0) :
    levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ)) p ∈
      DRACE.pIdeal (ϖR ι A (N * ℓ) ϖ) := by
  rw [DRACE.pIdeal, Ideal.mem_span_singleton]
  have hC : levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ)) (Polynomial.C ϖ) =
      ϖR ι A (N * ℓ) ϖ :=
    Subtype.ext (levelPolynomialEquiv_C _ _ _ _ ϖ)
  rw [← hC]
  exact map_dvd (levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ))) (C_dvd_of_map_eq_zero ι A hmax p h)

end Values
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

private def b₁ (b : Fin (dedekindPsi N)) : Bint ι A (N * ℓ) := gB ι A N ℓ N (dvd_mul_right N ℓ) ^ (b : ℕ)

section Hind1
variable [IsDiscreteValuationRing (𝒪s ι A)] [CharP (k₀ ι A) ℓ]

private theorem hind₁ (hℓN : ¬ ℓ ∣ N) {ϖ : 𝒪s ι A} (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (c : Fin (dedekindPsi N) → Rj ι A (N * ℓ))
    (h : (∑ b, π₁ ι A (N * ℓ) (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (c b)) * π₁ ι A (N * ℓ) (b₁ ι A N ℓ b)) = 0) :
    ∀ b, c b ∈ DRACE.pIdeal (ϖR ι A (N * ℓ) ϖ) := by
  set eqv := levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ))
  choose p hp using fun b => eqv.surjective (c b)
  have hπ : ∀ b, π₁ ι A (N * ℓ) (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (c b)) =
      ((p b).map (red₀ ι A)).eval₂ HahnSeries.C (jqModC (k₀ ι A)) := fun b =>
    π₁_levelEval ι A (N * ℓ) (p b) _ (by rw [← hp b]; rfl)
  have hzero := rel₁ (k₀ ι A) N ℓ hℓN (fun b => (p b).map (red₀ ι A)) (by
    rw [← h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hπ, b₁, map_pow, π₁_gB])
  intro b
  rw [← hp b]
  exact mem_pIdeal_of_map_eq_zero ι A N ℓ hmax (p b) (hzero b)

end Hind1
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Hind2

variable (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) [Algebra.IsAlgebraic ℚ E]

private def wBs (hσ : IsAtkinLehnerAutFull N ℓ σ) : Bint ι A (N * ℓ) →+* Bint ι A (N * ℓ) where
  toFun b := ⟨(wE N ℓ σ E).symm b, wE_symm_mem_Bint ι A N ℓ σ hσ b b.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem wB_wBs (hσ : IsAtkinLehnerAutFull N ℓ σ) (b : Bint ι A (N * ℓ)) : wB ι A N ℓ σ hσ (wBs ι A N ℓ σ hσ b) = b :=
  Subtype.ext ((wE N ℓ σ E).apply_symm_apply _)

private theorem wE_gEℓ (hσ : IsAtkinLehnerAutFull N ℓ σ) : wE N ℓ σ E (gE (N * ℓ) E ℓ (dvd_mul_left ℓ N)) = Tj (N * ℓ) E := by
  rw [← wE_symm_Tj N ℓ σ hσ, AlgEquiv.apply_symm_apply]

private def b₂ (hσ : IsAtkinLehnerAutFull N ℓ σ) (ab : Fin ℓ × Fin (dedekindPsi N)) : Bint ι A (N * ℓ) :=
  wBs ι A N ℓ σ hσ (TB ι A N ℓ ^ (ab.1 : ℕ) * gB ι A N ℓ N (dvd_mul_right N ℓ) ^ (ab.2 : ℕ))

private def xB : Bint ι A (N * ℓ) := gB ι A N ℓ ℓ (dvd_mul_left ℓ N) - TB ι A N ℓ ^ ℓ

variable [IsDiscreteValuationRing (𝒪s ι A)] [CharP (k₀ ι A) ℓ]

omit [CharP (k₀ ι A) ℓ] in
private theorem π₂_b₂ (hσ : IsAtkinLehnerAutFull N ℓ σ) (ab : Fin ℓ × Fin (dedekindPsi N)) :
    π₂ ι A N ℓ σ hσ (b₂ ι A N ℓ σ hσ ab) = jqModC (k₀ ι A) ^ (ab.1 : ℕ) * jqNModC (k₀ ι A) N ^ (ab.2 : ℕ) := by
  rw [π₂_apply, b₂, wB_wBs, map_mul, map_pow, map_pow, π₁_TB, π₁_gB]

private theorem hind₂ (hσ : IsAtkinLehnerAutFull N ℓ σ) (hℓN : ¬ ℓ ∣ N) {ϖ : 𝒪s ι A}
    (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (c : Fin ℓ × Fin (dedekindPsi N) → Rj ι A (N * ℓ))
    (h : (∑ ab, π₂ ι A N ℓ σ hσ (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (c ab)) * π₂ ι A N ℓ σ hσ (b₂ ι A N ℓ σ hσ ab))
      = 0) :
    ∀ ab, c ab ∈ DRACE.pIdeal (ϖR ι A (N * ℓ) ϖ) := by
  set eqv := levelPolynomialEquiv (𝒪s ι A) (F₀ (N * ℓ)) (jF (N * ℓ)) (transcendental_Tj (N * ℓ))
  choose p hp using fun ab => eqv.surjective (c ab)
  have hπ : ∀ ab, π₂ ι A N ℓ σ hσ (algebraMap (Rj ι A (N * ℓ)) (Bint ι A (N * ℓ)) (c ab)) =
      (expand (k₀ ι A) ℓ ((p ab).map (red₀ ι A))).eval₂ HahnSeries.C (jqModC (k₀ ι A)) := fun ab => by
    rw [π₂_levelEval ι A N ℓ σ hσ (p ab) _ (by rw [← hp ab]; rfl), qExpand_eval₂_C]
  have hzero := rel₂ (k₀ ι A) N ℓ hℓN (fun a b => (p (a, b)).map (red₀ ι A)) (by
    rw [← h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hπ, π₂_b₂])
  rintro ⟨a, b⟩
  rw [← hp (a, b)]
  exact mem_pIdeal_of_map_eq_zero ι A N ℓ hmax (p (a, b)) (hzero a b)

omit [Algebra.IsAlgebraic ℚ E] in
private theorem π₁_xB : π₁ ι A (N * ℓ) (xB ι A N ℓ) = 0 := by
  rw [xB, map_sub, map_pow, π₁_gB, π₁_TB, frobenius_identity_geom_unconditional (k₀ ι A) (ℓ := ℓ), sub_self]

private theorem π₂_xB (hσ : IsAtkinLehnerAutFull N ℓ σ) : π₂ ι A N ℓ σ hσ (xB ι A N ℓ) ≠ 0 := by
  rw [xB, map_sub, map_pow, π₂_apply, π₂_apply]
  have h1 : wB ι A N ℓ σ hσ (gB ι A N ℓ ℓ (dvd_mul_left ℓ N)) = TB ι A N ℓ := Subtype.ext (wE_gEℓ N ℓ σ hσ)
  have h2 : wB ι A N ℓ σ hσ (TB ι A N ℓ) = gB ι A N ℓ ℓ (dvd_mul_left ℓ N) := Subtype.ext (wE_Tj N ℓ σ hσ)
  rw [h1, h2, π₁_TB, π₁_gB, frobenius_identity_geom_unconditional (k₀ ι A) (ℓ := ℓ)]
  exact jqModC_ne_pow (k₀ ι A) ℓ

end Hind2
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

end Families
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

end ModularCurve.DRMainBound
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

p2m_open "Polynomial IntermediateField AlgebraicCurve ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"

namespace ModularCurve
p2m_export "ModularCurve" "IsAtkinLehnerAutFull qExpand qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand jq dedekindPsi evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full geomAut coe_geomAut_coeffEmb coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem levelConst levelConst_apply levelBaseRing levelConst_mem levelGen_mem exists_finset_forall_integral_laurentDescent integral_laurentDescent_of_integral laurentDescent_mem_integralCoeffs_iff levelGen₁ range_levelGen_singleton levelEval levelEval_C levelBaseRing_singleton_eq_range levelPolynomialEquiv levelPolynomialEquiv_C isIntegrallyClosed_levelBaseRing uniqueFactorizationMonoid_levelBaseRing prime_levelConst laurentDescent laurentDescent_algebraMap laurentDescent_geomAut transcendental_coeffEmb_jq relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi dedekindPsi_pos mem_integralCoeffs_of_integral_affineBaseFin coeffEmb_qExpand coeffMap_qExpand transcendental_jqModC frobenius_identity_geom_unconditional exists_modularPolynomialData_evalSymm relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_ord_sub_pos_of_integral_affineBaseFin dedekindPsi_mul_of_coprime dedekindPsi_prime"
namespace DRMainBound
p2m_open "ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

section PlaceOrgans

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_nonunits_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : f ∈ v.toValuationSubring.nonunits := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at h
    exact lt_irrefl 0 h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h.le
  have hn0 : n ≠ 0 := by rintro rfl; rw [hn] at h; exact lt_irrefl _ h
  rw [hn, zpow_natCast] at hu
  have hmem : f = (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) := by rw [hu]; rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_lt_one_iff]
  have hπ𝔪 : π ∈ IsLocalRing.maximalIdeal v.toValuationSubring := hπ.not_isUnit
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ𝔪 n (Nat.pos_of_ne_zero hn0))

private theorem mem_of_ord_sub_algebraMap_pos (v : Place K F) {f : F} {c : K} (h : 0 < v.ord (f - algebraMap K F c)) :
    f ∈ v.toValuationSubring := by
  have h1 : f - algebraMap K F c ∈ v.toValuationSubring :=
    v.toValuationSubring.nonunits_subset (mem_nonunits_of_ord_pos v h)
  have := add_mem h1 (v.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

private theorem eq_zero_of_algebraMap_mem_nonunits (v : Place K F) {c : K} (hc : algebraMap K F c ∈ v.toValuationSubring.nonunits) :
    c = 0 := by
  by_contra h0
  rw [ValuationSubring.mem_nonunits_iff_or] at hc
  rcases hc with hc | hc
  · exact h0 ((map_eq_zero_iff _ (algebraMap K F).injective).mp hc)
  · exact hc (by rw [← map_inv₀]; exact v.algebraMap_mem' _)

private theorem mem_of_integral (v : Place K F) (S : Subring F) (hS : S ≤ v.toValuationSubring.toSubring) {b : F}
    (hb : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) : b ∈ v.toValuationSubring := by
  obtain ⟨p, hp, hpb⟩ := hb
  have hint : IsIntegral v.toValuationSubring b := by
    refine ⟨p.map (Subring.inclusion hS), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := F)).mp hint
  rw [← hy]
  exact y.2

end PlaceOrgans
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Count

variable {E : Type} [Field E] [Algebra ℚ E] (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

private theorem finrank_le_card (hℓN : ¬ ℓ ∣ N) :
    Module.finrank (Kj (N * ℓ) (E := E)) (LF (N * ℓ) E) ≤
      Fintype.card (Fin (dedekindPsi N)) + Fintype.card (Fin ℓ × Fin (dedekindPsi N)) := by
  have hcop : Nat.Coprime N ℓ := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hℓN))
  rw [finrank_Kj, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, dedekindPsi_mul_of_coprime N ℓ hcop,
    dedekindPsi_prime hℓ.out, Nat.mul_add_one]
  linarith [Nat.mul_comm (dedekindPsi N) ℓ]

end Count
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section LevelE

variable {E : Type} [Field E] [Algebra ℚ E] [NumberField E] [Algebra.IsAlgebraic ℚ E]
  (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
  [IsDiscreteValuationRing (𝒪s ι A)] [CharP (k₀ ι A) ℓ]
  (ϖ : 𝒪s ι A) [hϖ : Fact (Prime ϖ)]

omit [NumberField E] in

private theorem exists_integral_mul_eq (hσ : IsAtkinLehnerAutFull N ℓ σ) (hℓN : ¬ ℓ ∣ N)
    (hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ})
    (eB fB : Bint ι A (N * ℓ)) (he : π₁ ι A (N * ℓ) eB = 0) (hf : π₂ ι A N ℓ σ hσ fB = 0) :
    ∃ y : LF (N * ℓ) E, IsIntegral (Rj ι A (N * ℓ)) y ∧
      ((ϖR ι A (N * ℓ) ϖ : Rj ι A (N * ℓ)) : LF (N * ℓ) E) * y = (eB : LF (N * ℓ) E) * (fB : LF (N * ℓ) E) := by
  have hϖ𝔪 : ϖ ∈ IsLocalRing.maximalIdeal (𝒪s ι A) := hmax ▸ Ideal.mem_span_singleton_self ϖ
  have hϖR0 : ϖR ι A (N * ℓ) ϖ ≠ 0 := (prime_ϖR ι A (N * ℓ) hϖ.out).ne_zero

  have hcount := DRACE.finite_and_finrank_le (ϖR ι A (N * ℓ) ϖ) (Bint ι A (N * ℓ)) (Bp ι A (N * ℓ) ϖ)
    (Kj (N * ℓ) (E := E)) ((φL ι A (N * ℓ) ϖ).toLinearMap) hϖR0 (finiteMultiplicity_ϖR ι A (N * ℓ) hϖ.out)
    (φL_injective ι A (N * ℓ) ϖ)
  letI := DRACE.algebraκFib (ϖR ι A (N * ℓ) ϖ) (Bint ι A (N * ℓ)) (Bp ι A (N * ℓ) ϖ)
  haveI := hcount.1

  obtain ⟨s, hs, a, hsa⟩ := DRACE.exists_mul_mul_eq_mul (ϖR ι A (N * ℓ) ϖ) (Bint ι A (N * ℓ)) (Bp ι A (N * ℓ) ϖ)
    (locM_le_nonZeroDivisors ι A (N * ℓ) ϖ)
    (π₁ ι A (N * ℓ)) (fun s hs => π₁_ne_zero_of_not_mem ι A (N * ℓ) hmax s hs) (π₁_ϖR ι A (N * ℓ) hϖ𝔪)
    (π₂ ι A N ℓ σ hσ) (fun s hs => π₂_ne_zero_of_not_mem ι A N ℓ σ hσ hmax s hs) (π₂_ϖR ι A N ℓ σ hσ hϖ𝔪)
    (xB ι A N ℓ) (π₁_xB ι A N ℓ) (π₂_xB ι A N ℓ σ hσ)
    (b₁ ι A N ℓ) (hind₁ ι A N ℓ hℓN hmax) (b₂ ι A N ℓ σ hσ) (hind₂ ι A N ℓ σ hσ hℓN hmax)
    (hcount.2.trans (finrank_le_card N ℓ hℓN)) eB fB he hf

  set ϖL : LF (N * ℓ) E := ((ϖR ι A (N * ℓ) ϖ : Rj ι A (N * ℓ)) : LF (N * ℓ) E)
  have hϖL0 : ϖL ≠ 0 := fun h => hϖR0 (Subtype.ext h)
  refine ⟨ϖL⁻¹ * ((eB : LF (N * ℓ) E) * (fB : LF (N * ℓ) E)), ?_, by rw [mul_inv_cancel_left₀ hϖL0]⟩
  haveI := isIntegrallyClosed_Rj ι A (N * ℓ)
  have hsaL : ((s : Rj ι A (N * ℓ)) : LF (N * ℓ) E) * ((eB : LF (N * ℓ) E) * (fB : LF (N * ℓ) E)) =
      ϖL * (a : LF (N * ℓ) E) := by
    have := congrArg (fun b : Bint ι A (N * ℓ) => (b : LF (N * ℓ) E)) hsa
    first | exact this | (simp at this; exact this) | (simp at this ⊢; exact this)
  refine DRPullback.isIntegral_of_prime_of_not_dvd (Kj (N * ℓ) (E := E)) (prime_ϖR ι A (N * ℓ) hϖ.out)
    (fun hdvd => hs (Ideal.mem_span_singleton.mpr hdvd)) ?_ ?_
  · rw [algebraMap_Rj_eq_subtype, Subring.coe_subtype, mul_inv_cancel_left₀ hϖL0]
    exact (eB * fB).2
  · rw [algebraMap_Rj_eq_subtype, Subring.coe_subtype, ← mul_assoc, mul_comm _ ϖL⁻¹, mul_assoc, hsaL,
      inv_mul_cancel_left₀ hϖL0]
    exact a.2

end LevelE
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Value

variable {E : Type} [Field E] [Algebra ℚ E] [NumberField E] [Algebra.IsAlgebraic ℚ E]
  (ι : E →+* ℚ̄) (A : ValuationSubring ℚ̄) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]
  (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))

omit [NumberField E] [Algebra.IsAlgebraic ℚ E] in

private theorem π₁_eq_zero_of_valuation_lt [IsDiscreteValuationRing (𝒪s ι A)] (b : Bint ι A (N * ℓ))
    (h : ∀ n : ℤ, A.valuation (ι (((b : LF (N * ℓ) E) : LaurentSeries E).coeff n)) < 1) : π₁ ι A (N * ℓ) b = 0 := by
  ext n
  rw [π₁_coeff, HahnSeries.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  exact (mem_maximalIdeal_𝒪v_iff ι A _).mpr (h n)

private theorem valuation_mul_lt_one_level (hℓA : A.valuation ((ℓ : ℕ) : ℚ̄) < 1) (hℓN : ¬ ℓ ∣ N)
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (W : Place ℚ̄ (laurentBaseChange ℚ̄ (F₀ (N * ℓ)))) (c : A)
    (hj : 0 < W.ord (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩
      - algebraMap ℚ̄ (laurentBaseChange ℚ̄ (F₀ (N * ℓ))) (c : ℚ̄)))
    (eE fE : LF (N * ℓ) E) (heI : IsIntegral (Rj ι A (N * ℓ)) eE) (hfI : IsIntegral (Rj ι A (N * ℓ)) fE) (a b : A)
    (hea : 0 < W.ord (laurentDescent ι (F₀ (N * ℓ)) eE - algebraMap ℚ̄ (laurentBaseChange ℚ̄ (F₀ (N * ℓ))) (a : ℚ̄)))
    (hfb : 0 < W.ord (laurentDescent ι (F₀ (N * ℓ)) fE - algebraMap ℚ̄ (laurentBaseChange ℚ̄ (F₀ (N * ℓ))) (b : ℚ̄)))
    (heInf : ∀ n : ℤ, A.valuation (ι ((eE : LaurentSeries E).coeff n)) < 1)
    (hfZero : ∀ n : ℤ, A.valuation (ι ((wE N ℓ σ E fE : LaurentSeries E).coeff n)) < 1) :
    A.valuation ((a : ℚ̄) * (b : ℚ̄)) < 1 := by
  classical

  haveI hdvr : IsDiscreteValuationRing (𝒪s ι A) := DRNumberField.isDiscreteValuationRing (𝒪v ι A) (𝒪v_ne_top ι A hℓA)
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪s ι A)
  have hmax : IsLocalRing.maximalIdeal (𝒪s ι A) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  haveI : Fact (Prime ϖ) := ⟨hirr.prime⟩
  have hϖ𝔪 : ϖ ∈ IsLocalRing.maximalIdeal (𝒪s ι A) := hmax ▸ Ideal.mem_span_singleton_self ϖ
  have hϖv : A.valuation (ι ϖ) < 1 := (mem_maximalIdeal_𝒪v_iff ι A _).mp hϖ𝔪
  have hℓ𝔪 : ((ℓ : ℕ) : 𝒪s ι A) ∈ IsLocalRing.maximalIdeal (𝒪s ι A) :=
    (mem_maximalIdeal_𝒪v_iff ι A _).mpr (by rw [Subring.coe_natCast, map_natCast]; exact hℓA)
  haveI : CharP (k₀ ι A) ℓ := (CharP.charP_iff_prime_eq_zero hℓ.out).mpr (by
    rw [← map_natCast (red₀ ι A), IsLocalRing.residue_eq_zero_iff]; exact hℓ𝔪)

  set eB : Bint ι A (N * ℓ) := ⟨eE, heI⟩
  set fB : Bint ι A (N * ℓ) := ⟨fE, hfI⟩
  have he0 : π₁ ι A (N * ℓ) eB = 0 := π₁_eq_zero_of_valuation_lt ι A N ℓ eB heInf
  have hf0 : π₂ ι A N ℓ σ hσ fB = 0 := by
    rw [π₂_apply]
    exact π₁_eq_zero_of_valuation_lt ι A N ℓ _ hfZero

  obtain ⟨y, hyI, hy⟩ := exists_integral_mul_eq ι A N ℓ σ ϖ hσ hℓN hmax eB fB he0 hf0

  set d := laurentDescent ι (F₀ (N * ℓ))
  have hyI' := integral_laurentDescent_of_integral (F₀ (N * ℓ)) ({jF (N * ℓ)} : Set (F₀ (N * ℓ))) ι A.toSubring y
    ((isIntegral_iff_exists_monic ι A (N * ℓ) y).mp hyI)
  rw [← affineBaseFin_eq_levelBaseRing] at hyI'
  obtain ⟨c', hc'⟩ := exists_ord_sub_pos_of_integral_affineBaseFin A (N * ℓ) W (d y) hyI' c hj

  set α := algebraMap ℚ̄ (laurentBaseChange ℚ̄ (F₀ (N * ℓ)))
  have hdϖ : d (((ϖR ι A (N * ℓ) ϖ : Rj ι A (N * ℓ)) : LF (N * ℓ) E)) = α (ι ϖ) := by
    change d (levelConst (𝒪s ι A) (F₀ (N * ℓ)) ϖ) = _
    rw [levelConst_apply]
    exact laurentDescent_algebraMap ι (F₀ (N * ℓ)) (ϖ : E)
  have hprod : α (ι ϖ) * d y = d eE * d fE := by rw [← hdϖ, ← map_mul, hy, map_mul]

  set O := W.toValuationSubring
  have meme : d eE ∈ O := mem_of_ord_sub_algebraMap_pos W hea
  have memf : d fE ∈ O := mem_of_ord_sub_algebraMap_pos W hfb
  have memy : d y ∈ O := by
    have h1 : d y - α c' ∈ O := O.nonunits_subset hc'
    have := add_mem h1 (W.algebraMap_mem' (c' : ℚ̄))
    rwa [sub_add_cancel] at this
  have memα : ∀ t : ℚ̄, α t ∈ O := W.algebraMap_mem'

  have tomax : ∀ {x : laurentBaseChange ℚ̄ (F₀ (N * ℓ))} (hx : x ∈ O), x ∈ O.nonunits →
      (⟨x, hx⟩ : O) ∈ IsLocalRing.maximalIdeal O := fun hx hn => by
    obtain ⟨_, h⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hn
    exact h
  have m₁ : (⟨d eE, meme⟩ - ⟨α a, memα a⟩ : O) ∈ IsLocalRing.maximalIdeal O :=
    tomax (sub_mem meme (memα a)) (mem_nonunits_of_ord_pos W hea)
  have m₂ : (⟨d fE, memf⟩ - ⟨α b, memα b⟩ : O) ∈ IsLocalRing.maximalIdeal O :=
    tomax (sub_mem memf (memα b)) (mem_nonunits_of_ord_pos W hfb)
  have m₃ : (⟨d y, memy⟩ - ⟨α c', memα c'⟩ : O) ∈ IsLocalRing.maximalIdeal O :=
    tomax (sub_mem memy (memα c')) hc'

  have key : (⟨α a, memα a⟩ * ⟨α b, memα b⟩ - ⟨α (ι ϖ), memα _⟩ * ⟨α c', memα c'⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    have hid : (⟨α a, memα a⟩ * ⟨α b, memα b⟩ - ⟨α (ι ϖ), memα _⟩ * ⟨α c', memα c'⟩ : O) =
        -((⟨d eE, meme⟩ - ⟨α a, memα a⟩) * ⟨α b, memα b⟩) - ⟨d eE, meme⟩ * (⟨d fE, memf⟩ - ⟨α b, memα b⟩)
          + ⟨α (ι ϖ), memα _⟩ * (⟨d y, memy⟩ - ⟨α c', memα c'⟩) := by
      have hPY : (⟨α (ι ϖ), memα _⟩ * ⟨d y, memy⟩ : O) = ⟨d eE, meme⟩ * ⟨d fE, memf⟩ := Subtype.ext hprod
      linear_combination (-1 : O) * hPY
    rw [hid]
    exact add_mem (sub_mem (neg_mem (Ideal.mul_mem_right _ _ m₁)) (Ideal.mul_mem_left _ _ m₂)) (Ideal.mul_mem_left _ _ m₃)

  have hzero : (a : ℚ̄) * b - ι ϖ * c' = 0 := by
    apply eq_zero_of_algebraMap_mem_nonunits W
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_mul, map_mul]; exact sub_mem (mul_mem (memα a) (memα b)) (mul_mem (memα _) (memα c'))
    · convert key using 1
      apply Subtype.ext
      simp only [map_sub, map_mul]
      rfl
  rw [sub_eq_zero] at hzero
  rw [hzero, map_mul]
  calc A.valuation (ι ϖ) * A.valuation (c' : ℚ̄) ≤ A.valuation (ι ϖ) * 1 :=
        mul_le_mul_of_nonneg_left (A.valuation_le_one c') zero_le'
    _ < 1 := by rw [mul_one]; exact hϖv

end Value
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

section Main

open AlgebraicCurve ModularCurve.CharPModel

private theorem main_bound
    (A : ValuationSubring (ℚ̄)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : ℚ̄) < 1) (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (W : Place (ℚ̄)
      (laurentBaseChange (ℚ̄) (modularFunctionFieldFull (N * ℓ))))
    (c : A)
    (hj : 0 < W.ord (⟨coeffEmb (ℚ̄) jq,
        coeffEmb_mem_laurentBaseChange (ℚ̄)
          (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩
      - algebraMap (ℚ̄)
        (laurentBaseChange (ℚ̄) (modularFunctionFieldFull (N * ℓ)))
        (c : ℚ̄)))
    (e f : laurentBaseChange (ℚ̄) (modularFunctionFieldFull (N * ℓ)))
    (he : ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype e p = 0)
    (hf : ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype f p = 0)
    (a b : A)
    (hea : 0 < W.ord (e - algebraMap (ℚ̄)
      (laurentBaseChange (ℚ̄) (modularFunctionFieldFull (N * ℓ)))
      (a : ℚ̄)))
    (hfb : 0 < W.ord (f - algebraMap (ℚ̄)
      (laurentBaseChange (ℚ̄) (modularFunctionFieldFull (N * ℓ)))
      (b : ℚ̄)))
    (heInf : ∀ n : ℤ,
      A.valuation ((e : LaurentSeries (ℚ̄)).coeff n) < 1)
    (hfZero : ∀ n : ℤ,
      A.valuation (((geomAut (ℚ̄) _ σ) f : LaurentSeries (ℚ̄)).coeff n) < 1) :
    A.valuation ((a : ℚ̄) * (b : ℚ̄)) < 1 := by
  classical

  rw [affineBaseFin_eq_levelBaseRing] at he hf
  obtain ⟨s₁, hs₁⟩ := exists_finset_forall_integral_laurentDescent (F₀ (N * ℓ)) ({jF (N * ℓ)} : Set (F₀ (N * ℓ)))
    A.toSubring e he
  obtain ⟨s₂, hs₂⟩ := exists_finset_forall_integral_laurentDescent (F₀ (N * ℓ)) ({jF (N * ℓ)} : Set (F₀ (N * ℓ)))
    A.toSubring f hf
  have hsub := subset_range_algebraMap_levelField (s₁ ∪ s₂)
  rw [Finset.coe_union, Set.union_subset_iff] at hsub
  set ι : LevelField (s₁ ∪ s₂) →+* ℚ̄ := (algebraMap (LevelField (s₁ ∪ s₂)) ℚ̄ : LevelField (s₁ ∪ s₂) →+* ℚ̄)
  obtain ⟨eE, heE, heI⟩ := hs₁ (LevelField (s₁ ∪ s₂)) ι hsub.1
  obtain ⟨fE, hfE, hfI⟩ := hs₂ (LevelField (s₁ ∪ s₂)) ι hsub.2
  subst heE hfE
  refine valuation_mul_lt_one_level ι A N ℓ σ hℓA hlN hσ W c hj eE fE
    ((isIntegral_iff_exists_monic ι A (N * ℓ) eE).mpr heI) ((isIntegral_iff_exists_monic ι A (N * ℓ) fE).mpr hfI)
    a b hea hfb heInf fun n => ?_
  have h := hfZero n
  rwa [← laurentDescent_geomAut] at h

end Main
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

end ModularCurve.DRMainBound
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"
p2m_reactivate "P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRCount P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRNumberField P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve.DRMainBound"

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos.ModularCurve ModularCurve.CharPModel in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1) (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    (c : A)
    (hj : 0 < W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (N * ℓ) (jq_mem (N * ℓ)))⟩
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
        (c : AlgebraicClosure ℚ)))
    (e f : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
    (he : ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype e p = 0)
    (hf : ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype f p = 0)
    (a b : A)
    (hea : 0 < W.ord (e - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (a : AlgebraicClosure ℚ)))
    (hfb : 0 < W.ord (f - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))
      (b : AlgebraicClosure ℚ)))
    (heInf : ∀ n : ℤ,
      A.valuation ((e : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1)
    (hfZero : ∀ n : ℤ,
      A.valuation (((geomAut (AlgebraicClosure ℚ) _ σ) f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) :
    A.valuation ((a : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ)) < 1 :=
  ModularCurve.DRMainBound.main_bound A N ℓ hℓA hlN σ hσ W c hj e f he hf a b hea hfb heInf hfZero

end
end S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos
end P2MW
export P2MW.S_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos (solution)
