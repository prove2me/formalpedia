-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d6_frobenius_of_cuspChart_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c251bacd-4bec-5eb8-bd61-efaf3d35b1c9

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Algebra.Ring.GeomSum
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll
import Theorems.Thm_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place SemilinearAut SemilinearAut.toRingAut SemilinearAut.smul_algebraMap SemilinearAut.ord_smul"
namespace PlaceCentre
p2m_open "AlgebraicCurve"

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_nonunits_pointwise_smul_iff {G : Type*} [Group G] [MulSemiringAction G F]
    (g : G) (S : ValuationSubring F) (x : F) :
    x ∈ (g • S).nonunits ↔ g⁻¹ • x ∈ S.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

private theorem mem_nonunits_smul_place_iff (g : SemilinearAut K F) (w : Place K F) (x : F) :
    x ∈ (g • w).toValuationSubring.nonunits ↔ g⁻¹ • x ∈ w.toValuationSubring.nonunits := by
  exact mem_nonunits_pointwise_smul_iff g w.toValuationSubring x

private def Centre (M : AddSubgroup F) (w : Place K F) (b : F) : Prop :=
  ∃ m ∈ M, b - m ∈ w.toValuationSubring.nonunits

private theorem centre_smul_iff (M : AddSubgroup F) (g : SemilinearAut K F) (hM : ∀ m ∈ M, g • m ∈ M)
    (hM' : ∀ m ∈ M, g⁻¹ • m ∈ M) (w : Place K F) (b : F)
    (hkey : ∃ m₀ ∈ M, (g⁻¹ • b - b) - m₀ ∈ w.toValuationSubring.nonunits) :
    Centre M (g • w) b ↔ Centre M w b := by
  obtain ⟨m₀, hm₀, hk⟩ := hkey
  constructor
  · rintro ⟨m, hm, h⟩
    rw [mem_nonunits_smul_place_iff, smul_sub] at h
    refine ⟨g⁻¹ • m - m₀, M.sub_mem (hM' m hm) hm₀, ?_⟩
    have : b - (g⁻¹ • m - m₀) = (g⁻¹ • b - g⁻¹ • m) - ((g⁻¹ • b - b) - m₀) := by abel
    rw [this]
    exact (w.toValuationSubring.nonunits).sub_mem h hk
  · rintro ⟨m, hm, h⟩
    refine ⟨g • (m₀ + m), hM _ (M.add_mem hm₀ hm), ?_⟩
    rw [mem_nonunits_smul_place_iff, smul_sub, inv_smul_smul]
    have : g⁻¹ • b - (m₀ + m) = ((g⁻¹ • b - b) - m₀) + (b - m) := by abel
    rw [this]
    exact (w.toValuationSubring.nonunits).add_mem hk h

private theorem centre_smul_iff' (M : AddSubgroup F) (g : SemilinearAut K F) (hM : ∀ m ∈ M, g • m ∈ M)
    (hM' : ∀ m ∈ M, g⁻¹ • m ∈ M) (w : Place K F) (b : F)
    (hkey : ∃ m₀ ∈ M, (b - g⁻¹ • b) - m₀ ∈ w.toValuationSubring.nonunits) :
    Centre M (g • w) b ↔ Centre M w b := by
  refine centre_smul_iff M g hM hM' w b ?_
  obtain ⟨m₀, hm₀, hk⟩ := hkey
  refine ⟨-m₀, M.neg_mem hm₀, ?_⟩
  have : g⁻¹ • b - b - -m₀ = -((b - g⁻¹ • b) - m₀) := by abel
  rw [this]
  exact (w.toValuationSubring.nonunits).neg_mem hk

private theorem d6f_mul_mem_nonunits (O : ValuationSubring F) {n o : F} (hn : n ∈ O.nonunits) (ho : o ∈ O) :
    n * o ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn ⊢
  rw [map_mul]
  exact mul_lt_of_lt_of_le_one hn ((O.valuation_le_one_iff o).mpr ho)

private theorem pow_sub_pow_mem_nonunits (O : ValuationSubring F) {x a : F} (ha : a ∈ O) (h : x - a ∈ O.nonunits)
    (n : ℕ) : x ^ n - a ^ n ∈ O.nonunits := by
  have hx : x ∈ O := by
    have hxa : x - a ∈ O := O.nonunits_subset h
    have := O.add_mem _ _ hxa ha
    rwa [sub_add_cancel] at this
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (⟨x, hx⟩ : O) ⟨a, ha⟩ n
  have hS' : x ^ n - a ^ n = (x - a) * (S : F) := by
    have := congrArg (fun z : O => (z : F)) hS
    simpa using this
  rw [hS']
  exact d6f_mul_mem_nonunits O h S.2

private theorem centre_pow_iff (M : AddSubgroup F) (Aset : Subring F) (w : Place K F) (ℓ : ℕ)
    (hAO : ∀ a ∈ Aset, a ∈ w.toValuationSubring)
    (hconst : ∀ c ∈ Aset, c ∈ w.toValuationSubring.nonunits → c ∈ M)
    (hMA : ∀ m ∈ M, m ∈ Aset) (hMpow : ∀ m ∈ M, m ^ ℓ ∈ M) (hprime : ∀ a ∈ Aset, a ^ ℓ ∈ M → a ∈ M)
    {x : F} (hx : ∃ a ∈ Aset, x - a ∈ w.toValuationSubring.nonunits) :
    Centre M w (x ^ ℓ) ↔ Centre M w x := by
  obtain ⟨a, haA, ha⟩ := hx
  have hpow : x ^ ℓ - a ^ ℓ ∈ w.toValuationSubring.nonunits :=
    pow_sub_pow_mem_nonunits _ (hAO a haA) ha ℓ
  constructor
  · rintro ⟨m, hm, h⟩

    have hdiff : a ^ ℓ - m ∈ w.toValuationSubring.nonunits := by
      have : a ^ ℓ - m = (x ^ ℓ - m) - (x ^ ℓ - a ^ ℓ) := by abel
      rw [this]
      exact (w.toValuationSubring.nonunits).sub_mem h hpow
    have haℓ : a ^ ℓ ∈ M := by
      have h1 : a ^ ℓ - m ∈ M := hconst _ (Aset.sub_mem (Aset.pow_mem haA ℓ) (hMA m hm)) hdiff
      have := M.add_mem h1 hm
      rwa [sub_add_cancel] at this
    exact ⟨a, hprime a haA haℓ, ha⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m ^ ℓ, hMpow m hm, pow_sub_pow_mem_nonunits _ (hAO m (hMA m hm)) h ℓ⟩

private theorem centre_frob_iff (M : AddSubgroup F) (Aset : Subring F) (w : Place K F) (ℓ : ℕ)
    (hAO : ∀ a ∈ Aset, a ∈ w.toValuationSubring)
    (hconst : ∀ c ∈ Aset, c ∈ w.toValuationSubring.nonunits → c ∈ M)
    (hMA : ∀ m ∈ M, m ∈ Aset) (hMpow : ∀ m ∈ M, m ^ ℓ ∈ M) (hprime : ∀ a ∈ Aset, a ^ ℓ ∈ M → a ∈ M)
    {x b'' : F} (hx : ∃ a ∈ Aset, x - a ∈ w.toValuationSubring.nonunits)
    (hkey : ∃ m₀ ∈ M, b'' - x ^ ℓ - m₀ ∈ w.toValuationSubring.nonunits) :
    Centre M w b'' ↔ Centre M w x := by
  rw [← centre_pow_iff M Aset w ℓ hAO hconst hMA hMpow hprime hx]
  obtain ⟨m₀, hm₀, hk⟩ := hkey
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m - m₀, M.sub_mem hm hm₀, ?_⟩
    have : x ^ ℓ - (m - m₀) = (b'' - m) - (b'' - x ^ ℓ - m₀) := by abel
    rw [this]
    exact (w.toValuationSubring.nonunits).sub_mem h hk
  · rintro ⟨m, hm, h⟩
    refine ⟨m₀ + m, M.add_mem hm₀ hm, ?_⟩
    have : b'' - (m₀ + m) = (b'' - x ^ ℓ - m₀) + (x ^ ℓ - m) := by abel
    rw [this]
    exact (w.toValuationSubring.nonunits).add_mem hk h

private theorem centre_inv_smul_iff (M : AddSubgroup F) (g : SemilinearAut K F) (hM : ∀ m ∈ M, g • m ∈ M)
    (hM' : ∀ m ∈ M, g⁻¹ • m ∈ M) (w : Place K F) (b : F) :
    Centre M (g • w) b ↔ Centre M w (g⁻¹ • b) := by
  constructor
  · rintro ⟨m, hm, h⟩
    rw [mem_nonunits_smul_place_iff, smul_sub] at h
    exact ⟨g⁻¹ • m, hM' m hm, h⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨g • m, hM m hm, ?_⟩
    rw [mem_nonunits_smul_place_iff, smul_sub, inv_smul_smul]
    exact h

end AlgebraicCurve.PlaceCentre

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem qExpand ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap coeffMap_coeffMap laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_injective frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll coeffMap_pow_char_eq_qExpand_of_frobenius"
namespace GaloisActionOnPlaces
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"
open scoped Pointwise

private abbrev FN (N : ℕ) [NeZero N] : Type :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem smul_const (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ • algebraMap (AlgebraicClosure ℚ) (FN N) c
      = algebraMap (AlgebraicClosure ℚ) (FN N) (σ c) := by
  rw [SemilinearAut.smul_algebraMap]
  rfl

private theorem smul_jBar' (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ • jBar N = jBar N :=
  arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ (modularFunctionField_le_full N (jq_mem N))

private theorem ord_smul_chart (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : Place (AlgebraicClosure ℚ) (FN N))
    (a : AlgebraicClosure ℚ) :
    (arithmeticGalois (modularFunctionFieldFull N) σ • w).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (σ a))
      = w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) a) := by
  conv_lhs => rw [← smul_jBar' N σ, ← smul_const N σ a, ← smul_sub]
  exact SemilinearAut.ord_smul _ _ _

private theorem pole_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσA : ∀ a ∈ A, σ.symm a ∈ A)
    (w : Place (AlgebraicClosure ℚ) (FN N))
    (hpole : ∀ a : A, w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∀ a : A, (arithmeticGalois (modularFunctionFieldFull N) σ • w).ord
      (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
  intro a
  have h := ord_smul_chart N σ w (σ.symm a)
  rw [σ.apply_symm_apply] at h
  rw [h]
  exact hpole ⟨σ.symm a, hσA a a.2⟩

private noncomputable def maxIdealImage : AddSubgroup (FN N) :=
  (IsLocalRing.maximalIdeal A).toAddSubgroup.map (constantsHom N A).toAddMonoidHom

private theorem mem_maxIdealImage {x : FN N} :
    x ∈ maxIdealImage N A ↔ ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ) = x := by
  simp only [maxIdealImage, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  rfl

private theorem algebraMap_mem_maxIdealImage {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ) ∈ maxIdealImage N A :=
  (mem_maxIdealImage N A).mpr ⟨a, ha, rfl⟩

end ModularCurve.GaloisActionOnPlaces

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem qExpand ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap coeffMap_coeffMap laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_injective frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll coeffMap_pow_char_eq_qExpand_of_frobenius"
namespace GaloisActionOnPlaces
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"
open scoped Pointwise

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem smul_mem_affineBaseFin {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτA : ∀ a ∈ A, τ a ∈ A)
    {x : FN N} (hx : x ∈ affineBaseFin N A) :
    arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ affineBaseFin N A := by
  change SemilinearAut.toRingAut (arithmeticGalois (modularFunctionFieldFull N) τ) x ∈ affineBaseFin N A
  have hle : affineBaseFin N A ≤ (affineBaseFin N A).comap
      (SemilinearAut.toRingAut (arithmeticGalois (modularFunctionFieldFull N) τ)).toRingHom := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · change arithmeticGalois (modularFunctionFieldFull N) τ •
          algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ) ∈ affineBaseFin N A
      rw [smul_const]
      exact Subring.subset_closure (Or.inl ⟨⟨τ a, hτA a a.2⟩, rfl⟩)
    · change arithmeticGalois (modularFunctionFieldFull N) τ • jBar N ∈ affineBaseFin N A
      rw [smul_jBar']
      exact Subring.subset_closure (Or.inr rfl)
  exact hle hx

private theorem smul_jBar_inv (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) τ • (jBar N)⁻¹ = (jBar N)⁻¹ := by
  rw [smul_inv'', smul_jBar']

private theorem smul_mem_affineBaseInf {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτA : ∀ a ∈ A, τ a ∈ A)
    {x : FN N} (hx : x ∈ affineBaseInf N A) :
    arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ affineBaseInf N A := by
  change SemilinearAut.toRingAut (arithmeticGalois (modularFunctionFieldFull N) τ) x ∈ affineBaseInf N A
  have hle : affineBaseInf N A ≤ (affineBaseInf N A).comap
      (SemilinearAut.toRingAut (arithmeticGalois (modularFunctionFieldFull N) τ)).toRingHom := by
    rw [affineBaseInf, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · change arithmeticGalois (modularFunctionFieldFull N) τ •
          algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ) ∈ affineBaseInf N A
      rw [smul_const]
      exact Subring.subset_closure (Or.inl ⟨⟨τ a, hτA a a.2⟩, rfl⟩)
    · change arithmeticGalois (modularFunctionFieldFull N) τ • (jBar N)⁻¹ ∈ affineBaseInf N A
      rw [smul_jBar_inv]
      exact Subring.subset_closure (Or.inr rfl)
  exact hle hx

private theorem integral_smul (S : Subring (FN N)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hS : ∀ x ∈ S, arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ S)
    {b : FN N} (hb : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) :
    ∃ p : Polynomial S, p.Monic ∧
      Polynomial.eval₂ S.subtype (arithmeticGalois (modularFunctionFieldFull N) τ • b) p = 0 := by
  obtain ⟨p, hp, hpb⟩ := hb
  set φ := (SemilinearAut.toRingAut (arithmeticGalois (modularFunctionFieldFull N) τ)).toRingHom with hφ
  let ψ : S →+* S := φ.restrict S S (fun x hx => hS x hx)
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  have hcomp : S.subtype.comp ψ = φ.comp S.subtype := RingHom.ext fun _ => rfl
  rw [Polynomial.eval₂_map, hcomp]
  change Polynomial.eval₂ (φ.comp S.subtype) (φ b) p = 0
  rw [← Polynomial.hom_eval₂, hpb, map_zero]

private theorem d6i_mem_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) {f : F}
    (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

private theorem d6i_mem_of_ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) {f : F}
    {c : K} (h : 0 < w.ord (f - algebraMap K F c)) : f ∈ w.toValuationSubring := by
  have h1 := d6i_mem_of_ord_pos w h
  have h2 : algebraMap K F c ∈ w.toValuationSubring := w.algebraMap_mem' c
  have := w.toValuationSubring.add_mem _ _ h1 h2
  rwa [sub_add_cancel] at this

private theorem centre_iff (v : Place (AlgebraicClosure ℚ) (FN N)) (x : FN N) :
    PlaceCentre.Centre (maxIdealImage N A) v x ↔
      ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        (x - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) ∈ v.toValuationSubring.nonunits := by
  constructor
  · rintro ⟨m, hm, h⟩
    obtain ⟨a, ha, rfl⟩ := (mem_maxIdealImage N A).mp hm
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨_, algebraMap_mem_maxIdealImage N A ha, h⟩

end ModularCurve.GaloisActionOnPlaces

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem qExpand ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap coeffMap_coeffMap laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_injective frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll coeffMap_pow_char_eq_qExpand_of_frobenius"
namespace GaloisActionOnPlaces
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"
open scoped Pointwise

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

section FrobAt
variable {A}
variable {ℓ : ℕ} {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}

private theorem mem_of_mem_decomp {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hτ : τ ∈ A.decompositionSubgroup ℚ) {a : AlgebraicClosure ℚ} (ha : a ∈ A) : τ a ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul τ a A ha
  rw [MulAction.mem_stabilizer_iff.mp hτ] at h
  exact h

private theorem frob_mem (hφ : A.IsFrobeniusAt φ ℓ) {a : AlgebraicClosure ℚ} (ha : a ∈ A) : φ a ∈ A :=
  mem_of_mem_decomp hφ.mem_decompositionSubgroup ha

private theorem frob_inv_mem (hφ : A.IsFrobeniusAt φ ℓ) {a : AlgebraicClosure ℚ} (ha : a ∈ A) : φ⁻¹ a ∈ A :=
  mem_of_mem_decomp (Subgroup.inv_mem _ hφ.mem_decompositionSubgroup) ha

private theorem ker_red_eq {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red) :
    RingHom.ker red = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)

private theorem valuation_lt_one_of_red_eq_zero {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red)
    {a : A} (ha : red a = 0) : A.valuation (a : AlgebraicClosure ℚ) < 1 := by
  rw [← ValuationSubring.valuation_lt_one_iff, ← ker_red_eq red hred]
  exact ha

private theorem frob_sub_pow_mem (hφ : A.IsFrobeniusAt φ ℓ) (a : A) :
    (⟨φ a, frob_mem hφ a.2⟩ : A) - a ^ ℓ ∈ IsLocalRing.maximalIdeal A := by
  rw [← Ideal.Quotient.eq]
  change IsLocalRing.residue A _ = IsLocalRing.residue A _
  have h := hφ.smul_residue_eq (IsLocalRing.residue A a)
  rw [← IsLocalRing.ResidueField.residue_smul] at h
  rw [map_pow, ← h]
  rfl

private theorem red_frob {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red)
    (hφ : A.IsFrobeniusAt φ ℓ) (a : A) : red ⟨φ a, frob_mem hφ a.2⟩ = red a ^ ℓ := by
  have h := frob_sub_pow_mem hφ a
  rw [← ker_red_eq red hred, RingHom.mem_ker, map_sub, sub_eq_zero, map_pow] at h
  exact h

private theorem frob_mem_maximalIdeal (hφ : A.IsFrobeniusAt φ ℓ) (hℓ : ℓ ≠ 0) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    (⟨φ a, frob_mem hφ a.2⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have h := frob_sub_pow_mem hφ a
  have hp : a ^ ℓ ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ ha ℓ (Nat.pos_of_ne_zero hℓ)
  have := Ideal.add_mem _ h hp
  rwa [sub_add_cancel] at this

private theorem frob_inv_mem_maximalIdeal (hφ : A.IsFrobeniusAt φ ℓ) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    (⟨φ⁻¹ a, frob_inv_mem hφ a.2⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have h := frob_sub_pow_mem hφ ⟨φ⁻¹ a, frob_inv_mem hφ a.2⟩
  have he : (⟨φ (φ⁻¹ a), frob_mem hφ (frob_inv_mem hφ a.2)⟩ : A) = a := Subtype.ext (by simp)
  rw [he] at h
  have hp : (⟨φ⁻¹ a, frob_inv_mem hφ a.2⟩ : A) ^ ℓ ∈ IsLocalRing.maximalIdeal A := by
    have := Ideal.sub_mem _ ha h
    rwa [sub_sub_cancel] at this
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance ℓ hp

private noncomputable def frobInvRes (hφ : A.IsFrobeniusAt φ ℓ) : A →+* A where
  toFun a := ⟨φ⁻¹ a, frob_inv_mem hφ a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem frobInvRes_apply (hφ : A.IsFrobeniusAt φ ℓ) (a : A) :
    ((frobInvRes hφ a : A) : AlgebraicClosure ℚ) = φ⁻¹ a := rfl

private theorem red_frobInvRes_pow {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red)
    (hφ : A.IsFrobeniusAt φ ℓ) (a : A) : red (frobInvRes hφ a) ^ ℓ = red a := by
  rw [← red_frob red hred hφ]
  congr 1
  exact Subtype.ext (by simp [frobInvRes])

end FrobAt

private theorem mem_nonunits_frob_iff {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (v : Place k (modularFunctionFieldC k N)) (x : modularFunctionFieldC k N) :
    x ∈ (frobOnPlacesGeomLevel k N data hKr v).toValuationSubring.nonunits ↔
      frobeniusGeomLevel k N data hKr x ∈ v.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_frobOnPlacesGeomLevel_iff, map_inv₀,
    map_eq_zero_iff _ (frobeniusGeomLevel_injective k N data hKr)]

private noncomputable def pack (e : FN N) (he : ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) :
    LaurentSeries A where
  coeff n := ⟨(e : LaurentSeries (AlgebraicClosure ℚ)).coeff n, he n⟩
  isPWO_support' := by
    refine (e : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono ?_
    intro n hn
    rw [Function.mem_support] at hn
    rw [HahnSeries.mem_support]
    exact fun h => hn (Subtype.ext h)

private theorem coeffMap_subtype_pack (e : FN N) (he : ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) :
    coeffMap A.subtype (pack N A e he) = (e : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n; rfl

private theorem coeffMap_pack_coeff {k : Type*} [Field k] (red : A →+* k) (e : FN N)
    (he : ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) (n : ℤ) :
    (coeffMap red (pack N A e he)).coeff n = red ⟨(e : LaurentSeries (AlgebraicClosure ℚ)).coeff n, he n⟩ := rfl

private theorem key_frob_at {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (S : Subring (FN N)) {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : A.IsFrobeniusAt φ ℓ)
    (hS : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ a ∈ A, τ a ∈ A) →
      ∀ x ∈ S, arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ S)
    (w : Place (AlgebraicClosure ℚ) (FN N))
    (hS3 : ∀ (τ : A →+* A), (∀ a : A, red (τ a) ^ ℓ = red a) → ∀ x : LaurentSeries A,
      coeffMap red (coeffMap τ x) ^ ℓ = qExpand k ℓ (coeffMap red x))
    (hT1w : ∀ b : FN N, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) →
      ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits)
    (hT2w : ∀ b : FN N, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) →
      (∀ n : ℤ, A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) →
      ∀ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits → A.valuation (a : AlgebraicClosure ℚ) < 1)
    (b b'' : FN N) (hb : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0)
    (hb'' : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b'' p = 0)
    (hbA : ∀ n : ℤ, (b : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hb''A : ∀ n : ℤ, (b'' : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hrel : ∀ n : ℤ, red ⟨(b'' : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hb''A n⟩
      = (qExpand k ℓ (coeffMap red (pack N A b hbA))).coeff n) :
    ∃ m₀ ∈ maxIdealImage N A,
      b'' - ((arithmeticGalois (modularFunctionFieldFull N) φ)⁻¹ • b) ^ ℓ - m₀ ∈ w.toValuationSubring.nonunits := by
  have hφ'A : ∀ a ∈ A, φ⁻¹ a ∈ A := fun a ha => frob_inv_mem hφ ha
  rw [← map_inv]
  set x : FN N := arithmeticGalois (modularFunctionFieldFull N) φ⁻¹ • b with hx
  set y : FN N := b'' - x ^ ℓ with hy

  have hyint : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype y p = 0 := by
    have h1 : IsIntegral S x := integral_smul N S φ⁻¹ (hS φ⁻¹ hφ'A) hb
    have h2 : IsIntegral S b'' := hb''
    exact h2.sub (h1.pow ℓ)

  set τ := frobInvRes hφ with hτ
  have hxq : ((x ^ ℓ : FN N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (coeffMap τ (pack N A b hbA) ^ ℓ) := by
    rw [map_pow, coeffMap_coeffMap, show A.subtype.comp τ = ((φ⁻¹ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype from RingHom.ext fun _ => rfl,
      ← coeffMap_coeffMap, coeffMap_subtype_pack]
    rfl

  have hcoeff : ∀ n : ℤ, A.valuation ((y : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1 := by
    intro n
    have hS3' := hS3 τ (fun a => red_frobInvRes_pow red hred hφ a) (pack N A b hbA)
    have hyn : (y : LaurentSeries (AlgebraicClosure ℚ)).coeff n
        = ((⟨(b'' : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hb''A n⟩ - (coeffMap τ (pack N A b hbA) ^ ℓ).coeff n
            : A) : AlgebraicClosure ℚ) := by
      change (((b'' : FN N) : LaurentSeries (AlgebraicClosure ℚ)) - ((x ^ ℓ : FN N) : LaurentSeries _)).coeff n = _
      rw [HahnSeries.coeff_sub, hxq]
      rfl
    rw [hyn]
    refine valuation_lt_one_of_red_eq_zero red hred ?_
    rw [map_sub, sub_eq_zero, hrel n, ← hS3']
    change _ = (coeffMap red (coeffMap τ (pack N A b hbA) ^ ℓ)).coeff n
    rw [map_pow]
  obtain ⟨a, ha⟩ := hT1w y hyint
  have ha𝔪 : a ∈ IsLocalRing.maximalIdeal A :=
    (ValuationSubring.valuation_lt_one_iff A a).mpr (hT2w y hyint hcoeff a ha)
  exact ⟨_, algebraMap_mem_maxIdealImage N A ha𝔪, ha⟩

section BPrimePrime
variable {N A}
variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

private theorem affineBaseFin_le (fm : FibreModel N A ℓ k red) : affineBaseFin N A ≤ fm.BFin := by
  rw [affineBaseFin, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl)
  exacts [fm.constFin_mem a, fm.jBar_mem]

private theorem affineBaseInf_le (fm : FibreModel N A ℓ k red) : affineBaseInf N A ≤ fm.BInf := by
  rw [affineBaseInf, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl)
  exacts [fm.constInf_mem a, fm.jInvBar_mem]

private theorem frob_mem_range_of (B : Subring (FN N)) (S : Subring (FN N)) (hSB : S ≤ B)
    (π : B →+* modularFunctionFieldC k N) (Fr : modularFunctionFieldC k N →+* modularFunctionFieldC k N)
    (hint : ∀ x : modularFunctionFieldC k N,
      (∃ p : Polynomial π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype x p = 0) → x ∈ π.range)
    (hgen : ∀ (x : FN N) (hx : x ∈ S), Fr (π ⟨x, hSB hx⟩) ∈ π.range)
    (b : B) (hb : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype (b : FN N) p = 0) :
    Fr (π b) ∈ π.range := by
  obtain ⟨p, hp, hpb⟩ := hb
  let Φ : B →+* modularFunctionFieldC k N := Fr.comp π
  let ι : S →+* B := Subring.inclusion hSB
  let ψ : S →+* π.range := (Φ.comp ι).codRestrict π.range (fun x => hgen x.1 x.2)
  refine hint _ ⟨p.map ψ, hp.map ψ, ?_⟩
  have h1 : π.range.subtype.comp ψ = Φ.comp ι := RingHom.ext fun _ => rfl
  have h2 : Polynomial.eval₂ ι b p = 0 := by
    apply Subtype.val_injective
    change B.subtype (Polynomial.eval₂ ι b p) = ((0 : B) : FN N)
    rw [Polynomial.hom_eval₂, show B.subtype.comp ι = S.subtype from RingHom.ext fun _ => rfl]
    exact hpb
  rw [Polynomial.eval₂_map, h1]
  change Polynomial.eval₂ (Φ.comp ι) (Φ b) p = 0
  rw [← Polynomial.hom_eval₂, h2, map_zero]

private theorem piFin_frob_gen_mem (fm : FibreModel N A ℓ k red) (x : FN N) (hx : x ∈ affineBaseFin N A) :
    (frobeniusGeomLevel k N data hKr).toRingHom (fm.piFin ⟨x, affineBaseFin_le fm hx⟩) ∈ fm.piFin.range := by
  have hle : affineBaseFin N A ≤ ((fm.piFin.range.comap
      ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piFin)).map fm.BFin.subtype) := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, ?_, rfl⟩
      change ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piFin) _ ∈ fm.piFin.range
      refine ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, ?_⟩
      change _ = frobeniusGeomLevel k N data hKr (fm.piFin ⟨constantsHom N A a, fm.constFin_mem a⟩)
      rw [fm.piFin_const, AlgHom.commutes]
    · refine ⟨⟨jBar N, fm.jBar_mem⟩, ?_, rfl⟩
      change ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piFin) _ ∈ fm.piFin.range
      refine ⟨⟨jBar N, fm.jBar_mem⟩ ^ ℓ, ?_⟩
      change _ = frobeniusGeomLevel k N data hKr (fm.piFin ⟨jBar N, fm.jBar_mem⟩)
      rw [map_pow fm.piFin, fm.piFin_j, frobeniusGeomLevel_jq]
  obtain ⟨z, hz, hzx⟩ := Subring.mem_map.mp (hle hx)
  rw [Subring.mem_comap] at hz
  have hzx' : (⟨x, affineBaseFin_le fm hx⟩ : fm.BFin) = z := Subtype.ext hzx.symm
  rw [hzx']
  exact hz

private theorem piInf_frob_gen_mem (fm : FibreModel N A ℓ k red) (x : FN N) (hx : x ∈ affineBaseInf N A) :
    (frobeniusGeomLevel k N data hKr).toRingHom (fm.piInf ⟨x, affineBaseInf_le fm hx⟩) ∈ fm.piInf.range := by
  have hle : affineBaseInf N A ≤ ((fm.piInf.range.comap
      ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piInf)).map fm.BInf.subtype) := by
    rw [affineBaseInf, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, ?_, rfl⟩
      change ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piInf) _ ∈ fm.piInf.range
      refine ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, ?_⟩
      change _ = frobeniusGeomLevel k N data hKr (fm.piInf ⟨constantsHom N A a, fm.constInf_mem a⟩)
      rw [fm.piInf_const, AlgHom.commutes]
    · refine ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, ?_, rfl⟩
      change ((frobeniusGeomLevel k N data hKr).toRingHom.comp fm.piInf) _ ∈ fm.piInf.range
      refine ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩ ^ ℓ, ?_⟩
      change _ = frobeniusGeomLevel k N data hKr (fm.piInf ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩)
      rw [map_pow fm.piInf, fm.piInf_jInv, map_inv₀, frobeniusGeomLevel_jq, inv_pow]
  obtain ⟨z, hz, hzx⟩ := Subring.mem_map.mp (hle hx)
  rw [Subring.mem_comap] at hz
  have hzx' : (⟨x, affineBaseInf_le fm hx⟩ : fm.BInf) = z := Subtype.ext hzx.symm
  rw [hzx']
  exact hz

private theorem exists_piFin_eq_frob (fm : FibreModel N A ℓ k red) (b : fm.BFin) :
    ∃ b'' : fm.BFin, fm.piFin b'' = frobeniusGeomLevel k N data hKr (fm.piFin b) :=
  frob_mem_range_of fm.BFin (affineBaseFin N A) (affineBaseFin_le fm) fm.piFin
    (frobeniusGeomLevel k N data hKr).toRingHom fm.intClosed_piFin (piFin_frob_gen_mem data hKr fm) b
    (fm.integralFin b)

private theorem exists_piInf_eq_frob (fm : FibreModel N A ℓ k red) (b : fm.BInf) :
    ∃ b'' : fm.BInf, fm.piInf b'' = frobeniusGeomLevel k N data hKr (fm.piInf b) :=
  frob_mem_range_of fm.BInf (affineBaseInf N A) (affineBaseInf_le fm) fm.piInf
    (frobeniusGeomLevel k N data hKr).toRingHom fm.intClosed_piInf (piInf_frob_gen_mem data hKr fm) b
    (fm.integralInf b)

end BPrimePrime

set_option maxHeartbeats 3200000 in

private theorem spPlace_smul_eq_frob (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (hred : Function.Surjective red)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data) (hlN : ¬ ℓ ∣ N)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    (hPI : ∀ (b : fm.BFin) (hmem : ((b : FN N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring),
      ((fm.piFin b : modularFunctionFieldC k N) : LaurentSeries k) = coeffRed A.toSubring red ⟨_, hmem⟩)
    (hPIP : ∀ (b : fm.BInf) (hmem : ((b : FN N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring),
      ((fm.piInf b : modularFunctionFieldC k N) : LaurentSeries k) = coeffRed A.toSubring red ⟨_, hmem⟩)
    (hS2 : ∀ e : FN N, (∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (affineBaseFin N A).subtype e p = 0) →
      (e : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring)
    (hT1 : ∀ (w : Place (AlgebraicClosure ℚ) (FN N)) (b : FN N),
      (∃ p : Polynomial (affineBaseFin N A), p.Monic ∧ Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0) →
      ∀ a₀ : A, 0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ)) →
      ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits)
    (hT2 : ∀ (w : Place (AlgebraicClosure ℚ) (FN N)) (a₀ : A),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ)) →
      ∀ b : FN N, (∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0) →
      (∀ n : ℤ, A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) →
      ∀ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits → A.valuation (a : AlgebraicClosure ℚ) < 1)
    (hS2P : ∀ e : FN N, (∃ p : Polynomial (affineBaseInf N A), p.Monic ∧
        Polynomial.eval₂ (affineBaseInf N A).subtype e p = 0) →
      (e : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring)
    (hT1P : ∀ (w : Place (AlgebraicClosure ℚ) (FN N)) (b : FN N),
      (∃ p : Polynomial (affineBaseInf N A), p.Monic ∧ Polynomial.eval₂ (affineBaseInf N A).subtype b p = 0) →
      ∀ a₀ : A, 0 < w.ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ)) →
      ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits)
    (hT2P : ∀ (w : Place (AlgebraicClosure ℚ) (FN N)) (a₀ : A),
      0 < w.ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ)) →
      ∀ b : FN N, (∃ p : Polynomial (affineBaseInf N A), p.Monic ∧
        Polynomial.eval₂ (affineBaseInf N A).subtype b p = 0) →
      (∀ n : ℤ, A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) →
      ∀ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits → A.valuation (a : AlgebraicClosure ℚ) < 1)
    (hCH : ∀ w : Place (AlgebraicClosure ℚ) (FN N),
      (∃ a : A, 0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))) ∨
      (∃ a : A, 0 < w.ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))))
    (hEXTFIN : ∀ v₁ v₂ : Place k (modularFunctionFieldC k N),
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v₁.toValuationSubring →
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v₂.toValuationSubring →
      (∀ b : fm.BFin,
        ((fm.piFin b : modularFunctionFieldC k N) ∈ v₁.toValuationSubring.nonunits ↔
          (fm.piFin b : modularFunctionFieldC k N) ∈ v₂.toValuationSubring.nonunits)) →
      v₁ = v₂)
    (hS3 : ∀ (τ : A →+* A), (∀ a : A, red (τ a) ^ ℓ = red a) → ∀ x : LaurentSeries A,
      coeffMap red (coeffMap τ x) ^ ℓ = qExpand k ℓ (coeffMap red x))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : A.IsFrobeniusAt φ ℓ)
    (w : Place (AlgebraicClosure ℚ) (FN N)) :
    fm.spPlace hred dataAll hsep (arithmeticGalois (modularFunctionFieldFull N) φ • w)
      = frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w) := by
  set g := arithmeticGalois (modularFunctionFieldFull N) φ with hg
  have hℓA := valuation_lt_one_of_red_eq_zero red hred (a := (ℓ : A)) (by rw [map_natCast, CharP.cast_eq_zero])
  have _hℓA' : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := by simpa using hℓA
  have _ := hlN
  have hφA : ∀ a ∈ A, φ a ∈ A := fun a ha => frob_mem hφ ha
  have hφA' : ∀ a ∈ A, φ.symm a ∈ A := fun a ha => frob_inv_mem hφ ha
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hM : ∀ m ∈ maxIdealImage N A, g • m ∈ maxIdealImage N A := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := (mem_maxIdealImage N A).mp hm
    rw [hg, smul_const]
    exact algebraMap_mem_maxIdealImage N A (a := ⟨φ a, hφA a a.2⟩) (frob_mem_maximalIdeal hφ hℓ0 ha)
  have hM' : ∀ m ∈ maxIdealImage N A, g⁻¹ • m ∈ maxIdealImage N A := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := (mem_maxIdealImage N A).mp hm
    rw [hg, ← map_inv, smul_const]
    exact algebraMap_mem_maxIdealImage N A (a := ⟨φ⁻¹ a, frob_inv_mem hφ a.2⟩) (frob_inv_mem_maximalIdeal hφ ha)

  set Aset : Subring (FN N) := (constantsHom N A).range with hAset
  have hAO : ∀ a ∈ Aset, a ∈ w.toValuationSubring := by
    rintro _ ⟨a, rfl⟩; exact w.algebraMap_mem' _
  have hconst : ∀ c ∈ Aset, c ∈ w.toValuationSubring.nonunits → c ∈ maxIdealImage N A := by
    rintro _ ⟨a, rfl⟩ hc
    refine algebraMap_mem_maxIdealImage N A ?_
    by_contra ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
    obtain ⟨u, rfl⟩ := ha
    rw [ValuationSubring.mem_nonunits_iff_or] at hc
    rcases hc with hc | hc
    · exact (Units.ne_zero u) (Subtype.ext ((algebraMap (AlgebraicClosure ℚ) (FN N)).injective
        (by change constantsHom N A u = algebraMap _ _ ((0 : A) : AlgebraicClosure ℚ)
            rw [ZeroMemClass.coe_zero, map_zero]; exact hc)))
    · apply hc
      have : (constantsHom N A (u : A))⁻¹ = constantsHom N A ((u⁻¹ : Aˣ) : A) :=
        inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
      rw [this]
      exact w.algebraMap_mem' _
  have hMA : ∀ m ∈ maxIdealImage N A, m ∈ Aset := by
    intro m hm
    obtain ⟨a, _, rfl⟩ := (mem_maxIdealImage N A).mp hm
    exact ⟨a, rfl⟩
  have hMpow : ∀ m ∈ maxIdealImage N A, m ^ ℓ ∈ maxIdealImage N A := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := (mem_maxIdealImage N A).mp hm
    rw [← map_pow]
    exact algebraMap_mem_maxIdealImage N A (a := a ^ ℓ) (Ideal.pow_mem_of_mem _ ha ℓ (Nat.pos_of_ne_zero hℓ0))
  have hprime : ∀ a ∈ Aset, a ^ ℓ ∈ maxIdealImage N A → a ∈ maxIdealImage N A := by
    rintro _ ⟨a, rfl⟩ h
    obtain ⟨m, hm, hma⟩ := (mem_maxIdealImage N A).mp h
    refine algebraMap_mem_maxIdealImage N A (Ideal.IsPrime.mem_of_pow_mem inferInstance ℓ ?_)
    have : m = a ^ ℓ := by
      apply Subtype.ext
      apply (algebraMap (AlgebraicClosure ℚ) (FN N)).injective
      rw [hma, SubmonoidClass.coe_pow, map_pow]
      rfl
    exact this ▸ hm

  have hS2c : ∀ e : FN N, (∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype e p = 0) →
      ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    fun e he n => (mem_integralCoeffs A.toSubring).mp (hS2 e he) n
  have hS2Pc : ∀ e : FN N, (∃ p : Polynomial (affineBaseInf N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf N A).subtype e p = 0) →
      ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    fun e he n => (mem_integralCoeffs A.toSubring).mp (hS2P e he) n

  have hrel_of : ∀ (B : Subring (FN N)) (π : B → modularFunctionFieldC k N) (b b'' : B)
      (hbA : ∀ n : ℤ, (((b : FN N)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
      (hb''A : ∀ n : ℤ, (((b'' : FN N)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A),
      ((π b : modularFunctionFieldC k N) : LaurentSeries k)
        = coeffRed A.toSubring red ⟨_, (mem_integralCoeffs A.toSubring).mpr hbA⟩ →
      ((π b'' : modularFunctionFieldC k N) : LaurentSeries k)
        = coeffRed A.toSubring red ⟨_, (mem_integralCoeffs A.toSubring).mpr hb''A⟩ →
      π b'' = frobeniusGeomLevel k N data hKr (π b) →
      ∀ n : ℤ, red ⟨(((b'' : FN N)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hb''A n⟩
        = (qExpand k ℓ (coeffMap red (pack N A (b : FN N) hbA))).coeff n := by
    intro B π b b'' hbA hb''A hπb hπb'' hF n
    have h1 : red ⟨(((b'' : FN N)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hb''A n⟩
        = (((π b'' : modularFunctionFieldC k N) : LaurentSeries k)).coeff n := by
      rw [hπb'']; rfl
    have h2 : coeffMap red (pack N A (b : FN N) hbA) = ((π b : modularFunctionFieldC k N) : LaurentSeries k) := by
      rw [hπb]; ext m; rfl
    rw [h1, h2, hF, frobeniusGeomLevel_apply_coe]
  by_cases hfin : ∃ a₀ : A, 0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ))
  ·
    obtain ⟨a₀, ha₀⟩ := hfin
    set a₀φ : A := ⟨φ a₀, hφA a₀ a₀.2⟩ with ha₀φ_def
    have ha₀φ : 0 < (g • w).ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀φ : AlgebraicClosure ℚ)) := by
      rw [hg, show ((a₀φ : A) : AlgebraicClosure ℚ) = φ a₀ from rfl, ord_smul_chart]
      exact ha₀
    have hFin : ∀ b : fm.BFin,
        ((fm.piFin b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring.nonunits ↔
          (fm.piFin b : modularFunctionFieldC k N) ∈
            (frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w)).toValuationSubring.nonunits) := by
      intro b
      obtain ⟨b'', hb''⟩ := exists_piFin_eq_frob data hKr fm b
      have hbA := hS2c (b : FN N) (fm.integralFin b)
      have hb''A := hS2c (b'' : FN N) (fm.integralFin b'')
      rw [fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep (g • w) a₀φ ha₀φ b, mem_nonunits_frob_iff, ← hb'',
        fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀ b'', ← centre_iff N A, ← centre_iff N A,
        PlaceCentre.centre_inv_smul_iff (maxIdealImage N A) g hM hM' w (b : FN N)]
      symm
      refine PlaceCentre.centre_frob_iff (maxIdealImage N A) Aset w ℓ hAO hconst hMA hMpow hprime ?_ ?_
      ·
        have hint := integral_smul N (affineBaseFin N A) φ⁻¹
          (fun x hx => smul_mem_affineBaseFin N A (fun a ha => frob_inv_mem hφ ha) hx) (fm.integralFin b)
        rw [← map_inv]
        obtain ⟨a, ha⟩ := hT1 w _ hint a₀ ha₀
        exact ⟨_, ⟨a, rfl⟩, ha⟩
      · exact key_frob_at N A red hred (affineBaseFin N A) hφ
          (fun τ hτ x hx => smul_mem_affineBaseFin N A hτ hx) w hS3
          (fun b' hb' => hT1 w b' hb' a₀ ha₀)
          (fun b' hb' hc a hv => hT2 w a₀ ha₀ b' hb' hc a hv)
          (b : FN N) (b'' : FN N) (fm.integralFin b) (fm.integralFin b'') hbA hb''A
          (hrel_of fm.BFin (fun e => fm.piFin e) b b'' hbA hb''A (hPI b _) (hPI b'' _) hb'')
    have hjw : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep w).toValuationSubring :=
      d6i_mem_of_ord_sub_algebraMap_pos _ (FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep w a₀ ha₀)
    have hj₁ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring :=
      d6i_mem_of_ord_sub_algebraMap_pos _ (FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep (g • w) a₀φ ha₀φ)
    have hj₂ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈
        (frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w)).toValuationSubring := by
      rw [mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq]
      exact pow_mem hjw ℓ
    exact hEXTFIN _ _ hj₁ hj₂ hFin
  ·
    have hpole : ∀ a : A, w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
      intro a
      by_contra h
      exact hfin ⟨a, lt_of_not_ge h⟩
    have hpoleφ := pole_smul N A φ hφA' w hpole
    obtain ⟨a₁, ha₁⟩ : ∃ a : A,
        0 < w.ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) :=
      (hCH w).resolve_left hfin
    have hInf : ∀ b : fm.BInf,
        ((fm.piInf b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring.nonunits ↔
          (fm.piInf b : modularFunctionFieldC k N) ∈
            (frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w)).toValuationSubring.nonunits) := by
      intro b
      obtain ⟨b'', hb''⟩ := exists_piInf_eq_frob data hKr fm b
      have hbA := hS2Pc (b : FN N) (fm.integralInf b)
      have hb''A := hS2Pc (b'' : FN N) (fm.integralInf b'')
      rw [fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep (g • w) hpoleφ b, mem_nonunits_frob_iff, ← hb'',
        fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole b'', ← centre_iff N A, ← centre_iff N A,
        PlaceCentre.centre_inv_smul_iff (maxIdealImage N A) g hM hM' w (b : FN N)]
      symm
      refine PlaceCentre.centre_frob_iff (maxIdealImage N A) Aset w ℓ hAO hconst hMA hMpow hprime ?_ ?_
      · have hint := integral_smul N (affineBaseInf N A) φ⁻¹
          (fun x hx => smul_mem_affineBaseInf N A (fun a ha => frob_inv_mem hφ ha) hx) (fm.integralInf b)
        rw [← map_inv]
        obtain ⟨a, ha⟩ := hT1P w _ hint a₁ ha₁
        exact ⟨_, ⟨a, rfl⟩, ha⟩
      · exact key_frob_at N A red hred (affineBaseInf N A) hφ
          (fun τ hτ x hx => smul_mem_affineBaseInf N A hτ hx) w hS3
          (fun b' hb' => hT1P w b' hb' a₁ ha₁)
          (fun b' hb' hc a hv => hT2P w a₁ ha₁ b' hb' hc a hv)
          (b : FN N) (b'' : FN N) (fm.integralInf b) (fm.integralInf b'') hbA hb''A
          (hrel_of fm.BInf (fun e => fm.piInf e) b b'' hbA hb''A (hPIP b _) (hPIP b'' _) hb'')
    have h₁ := fm.jLineInv_mem_spPlace hred dataAll hsep (g • w) hpoleφ
    have h₂ : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹) ∈
        (frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w)).toValuationSubring := by
      rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀, frobeniusGeomLevel_jq, ← inv_pow]
      exact pow_mem (fm.jLineInv_mem_spPlace hred dataAll hsep w hpole) ℓ
    exact FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff N ℓ A k red fm hred dataAll hsep _ _ h₁ h₂ hInf

end ModularCurve.GaloisActionOnPlaces

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.ModularCurve _root_.ModularCurve.CharPModel in
theorem solution (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    A.IsFrobeniusAt σ ℓ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w)
        = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) w) := by
  intro σ hσ w
  have _ := halpha
  have _ := hbeta
  have _ := hsym
  have hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := by
    simpa using ModularCurve.GaloisActionOnPlaces.valuation_lt_one_of_red_eq_zero red hred (a := (ℓ : A))
      (by rw [map_natCast, CharP.cast_eq_zero])
  exact ModularCurve.GaloisActionOnPlaces.spPlace_smul_eq_frob N A ℓ k red hred data hKr hlN dataAll hsep fm
    (fun b hmem => FibreModel.coe_piFin_eq_coeffRed N A ℓ k red fm b hmem)
    (fun b hmem => FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A ℓ k red fm cc (dataAll N (dvd_refl N)) hsep b hmem)
    (fun e he => ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin A N e he)
    (fun w b hb a₀ hj => ModularCurve.exists_ord_sub_pos_of_integral_affineBaseFin A N w b hb a₀ hj)
    (fun w a₀ hj b hb hc a hv =>
      ModularCurve.valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one A N ℓ hℓA hlN w a₀ hj b hb hc a hv)
    (fun e he => ModularCurve.mem_integralCoeffs_of_integral_affineBaseInf A N e he)
    (fun w b hb a₀ hj => ModularCurve.exists_sub_mem_nonunits_of_integral_affineBaseInf A N w b hb a₀ hj)
    (fun w a₀ hj b hb hc a hv =>
      ModularCurve.valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf A N ℓ hℓA hlN w a₀ hj b hb hc a hv)
    (fun w => ModularCurve.exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll A N dataAll w)
    (fun v₁ v₂ h₁ h₂ hF =>
      FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff N ℓ A k red fm hred dataAll hsep v₁ v₂ h₁ h₂ hF)
    (fun τ hτ x => ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius ℓ red τ hτ x)
    hσ w

end S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level (solution)
