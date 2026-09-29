-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d6_inertia_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c26d76f9-6878-5893-bc79-7d6dc2ea7329

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"

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

end AlgebraicCurve.PlaceCentre

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll"
namespace GaloisActionOnPlaces
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"
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

private theorem mem_maximalIdeal_of_inertia {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    ∃ h : σ a ∈ A, (⟨σ a, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨hmem, hlt⟩ := ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hσ a.2
  refine ⟨hmem, ?_⟩
  rw [ValuationSubring.valuation_lt_one_iff] at ha ⊢
  have h : (σ a : AlgebraicClosure ℚ) = (σ a - a) + a := by ring
  change A.valuation (σ a) < 1
  rw [h]
  exact Valuation.map_add_lt _ hlt ha

private theorem smul_mem_maxIdealImage {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {m : FN N} (hm : m ∈ maxIdealImage N A) :
    arithmeticGalois (modularFunctionFieldFull N) σ • m ∈ maxIdealImage N A := by
  obtain ⟨a, ha, rfl⟩ := (mem_maxIdealImage N A).mp hm
  obtain ⟨h, h𝔪⟩ := mem_maximalIdeal_of_inertia A hσ ha
  rw [smul_const]
  exact algebraMap_mem_maxIdealImage N A (a := ⟨σ a, h⟩) h𝔪

private theorem inv_smul_mem_maxIdealImage {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {m : FN N} (hm : m ∈ maxIdealImage N A) :
    (arithmeticGalois (modularFunctionFieldFull N) σ)⁻¹ • m ∈ maxIdealImage N A := by
  rw [← map_inv]
  exact smul_mem_maxIdealImage N A (Subgroup.inv_mem _ hσ) hm

end ModularCurve.GaloisActionOnPlaces

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll"
namespace GaloisActionOnPlaces
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction"
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

private theorem key_at (S : Subring (FN N)) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (hS : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ a ∈ A, τ a ∈ A) →
      ∀ x ∈ S, arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ S)
    (w : Place (AlgebraicClosure ℚ) (FN N))
    (hS2 : ∀ e : FN N, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype e p = 0) →
      ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hT1w : ∀ b : FN N, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) →
      ∃ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits)
    (hT2w : ∀ b : FN N, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) →
      (∀ n : ℤ, A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1) →
      ∀ a : A, (b - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ))
        ∈ w.toValuationSubring.nonunits → A.valuation (a : AlgebraicClosure ℚ) < 1)
    (b : FN N) (hb : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0) :
    ∃ m₀ ∈ maxIdealImage N A,
      (arithmeticGalois (modularFunctionFieldFull N) σ)⁻¹ • b - b - m₀ ∈ w.toValuationSubring.nonunits := by
  have hσ' : σ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hσ
  have hσ'A : ∀ a ∈ A, σ⁻¹ a ∈ A := fun a ha =>
    (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hσ' ha).1
  rw [← map_inv]
  set x : FN N := arithmeticGalois (modularFunctionFieldFull N) σ⁻¹ • b - b with hx
  have hgb := integral_smul N S σ⁻¹ (hS σ⁻¹ hσ'A) hb
  have hxint : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0 := by
    have h1 : IsIntegral S (arithmeticGalois (modularFunctionFieldFull N) σ⁻¹ • b) := hgb
    have h2 : IsIntegral S b := hb
    exact h1.sub h2
  have hcoeff : ∀ n : ℤ, A.valuation ((x : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1 := by
    intro n
    have hbn : (b : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := hS2 b hb n
    have hcoe : (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n
        = σ⁻¹ ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n)
          - (b : LaurentSeries (AlgebraicClosure ℚ)).coeff n := rfl
    rw [hcoe]
    exact (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hσ' hbn).2
  obtain ⟨a, ha⟩ := hT1w x hxint
  have ha𝔪 : a ∈ IsLocalRing.maximalIdeal A :=
    (ValuationSubring.valuation_lt_one_iff A a).mpr (hT2w x hxint hcoeff a ha)
  exact ⟨_, algebraMap_mem_maxIdealImage N A ha𝔪, ha⟩

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

set_option maxHeartbeats 3200000 in

private theorem spPlace_smul_eq_of_inertia (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)

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
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : Place (AlgebraicClosure ℚ) (FN N)) :
    fm.spPlace hred dataAll hsep (arithmeticGalois (modularFunctionFieldFull N) σ • w)
      = fm.spPlace hred dataAll hsep w := by

  set g := arithmeticGalois (modularFunctionFieldFull N) σ with hg
  have hσA : ∀ a ∈ A, σ a ∈ A := fun a ha =>
    (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hσ ha).1
  have hσ' : σ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hσ
  have hσA' : ∀ a ∈ A, σ.symm a ∈ A := fun a ha =>
    (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hσ' ha).1
  have hM := fun m (hm : m ∈ maxIdealImage N A) => smul_mem_maxIdealImage N A hσ hm
  have hM' := fun m (hm : m ∈ maxIdealImage N A) => inv_smul_mem_maxIdealImage N A hσ hm
  have hS2c : ∀ e : FN N, (∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype e p = 0) →
      ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    fun e he n => (mem_integralCoeffs A.toSubring).mp (hS2 e he) n
  have hS2Pc : ∀ e : FN N, (∃ p : Polynomial (affineBaseInf N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf N A).subtype e p = 0) →
      ∀ n : ℤ, (e : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    fun e he n => (mem_integralCoeffs A.toSubring).mp (hS2P e he) n
  by_cases hfin : ∃ a₀ : A, 0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀ : AlgebraicClosure ℚ))
  ·
    obtain ⟨a₀, ha₀⟩ := hfin
    set a₀σ : A := ⟨σ a₀, hσA a₀ a₀.2⟩ with ha₀σ_def
    have ha₀σ : 0 < (g • w).ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a₀σ : AlgebraicClosure ℚ)) := by
      rw [hg, show ((a₀σ : A) : AlgebraicClosure ℚ) = σ a₀ from rfl, ord_smul_chart]
      exact ha₀

    have hFin : ∀ b : fm.BFin,
        ((fm.piFin b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring.nonunits ↔
          (fm.piFin b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep w).toValuationSubring.nonunits) := by
      intro b
      rw [fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep (g • w) a₀σ ha₀σ b,
        fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀ b,
        ← centre_iff N A, ← centre_iff N A]
      refine PlaceCentre.centre_smul_iff (maxIdealImage N A) g hM hM' w (b : FN N) ?_
      exact key_at N A (affineBaseFin N A) hσ (fun τ hτ x hx => smul_mem_affineBaseFin N A hτ hx) w hS2c
        (fun b' hb' => hT1 w b' hb' a₀ ha₀) (fun b' hb' => hT2 w a₀ ha₀ b' hb') (b : FN N) (fm.integralFin b)

    have hj₂ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep w).toValuationSubring :=
      d6i_mem_of_ord_sub_algebraMap_pos _ (FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep w a₀ ha₀)
    have hj₁ : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring :=
      d6i_mem_of_ord_sub_algebraMap_pos _ (FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep (g • w) a₀σ ha₀σ)
    exact hEXTFIN _ _ hj₁ hj₂ hFin
  ·
    have hpole : ∀ a : A, w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
      intro a
      by_contra h
      exact hfin ⟨a, lt_of_not_ge h⟩
    have hpoleσ := pole_smul N A σ hσA' w hpole

    obtain ⟨a₁, ha₁⟩ : ∃ a : A,
        0 < w.ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a : AlgebraicClosure ℚ)) :=
      (hCH w).resolve_left hfin
    set a₁σ : A := ⟨σ a₁, hσA a₁ a₁.2⟩ with ha₁σ_def
    have ha₁σ : 0 < (g • w).ord ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a₁σ : AlgebraicClosure ℚ)) := by
      have h := SemilinearAut.ord_smul g w ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FN N) (a₁ : AlgebraicClosure ℚ))
      rw [smul_sub, hg, smul_jBar_inv, smul_const] at h
      rw [hg, show ((a₁σ : A) : AlgebraicClosure ℚ) = σ a₁ from rfl, h]
      exact ha₁

    have hInf : ∀ b : fm.BInf,
        ((fm.piInf b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep (g • w)).toValuationSubring.nonunits ↔
          (fm.piInf b : modularFunctionFieldC k N) ∈
            (fm.spPlace hred dataAll hsep w).toValuationSubring.nonunits) := by
      intro b
      rw [fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep (g • w) hpoleσ b,
        fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole b,
        ← centre_iff N A, ← centre_iff N A]
      refine PlaceCentre.centre_smul_iff (maxIdealImage N A) g hM hM' w (b : FN N) ?_
      exact key_at N A (affineBaseInf N A) hσ (fun τ hτ x hx => smul_mem_affineBaseInf N A hτ hx) w hS2Pc
        (fun b' hb' => hT1P w b' hb' a₁ ha₁) (fun b' hb' => hT2P w a₁ ha₁ b' hb') (b : FN N) (fm.integralInf b)
    have h₂ := fm.jLineInv_mem_spPlace hred dataAll hsep w hpole
    have h₁ := fm.jLineInv_mem_spPlace hred dataAll hsep (g • w) hpoleσ
    exact FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff N ℓ A k red fm hred dataAll hsep _ _ h₁ h₂ hInf

end ModularCurve.GaloisActionOnPlaces

namespace ModularCurve p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full laurentBaseChange EvalSymm arithmeticGalois modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence arithmeticGalois_smul_coeffEmb mem_integralCoeffs_of_integral_affineBaseFin exists_ord_sub_pos_of_integral_affineBaseFin valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one mem_integralCoeffs_of_integral_affineBaseInf exists_sub_mem_nonunits_of_integral_affineBaseInf valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf exists_ord_sub_pos_or_exists_ord_inv_sub_pos_of_dataAll" namespace GaloisActionOnPlaces end ModularCurve.GaloisActionOnPlaces
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.GaloisActionOnPlaces.valuation_natCast_lt_one (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) :
    A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := by
  have h : ((ℓ : A) : AlgebraicClosure ℚ) = ((ℓ : ℕ) : AlgebraicClosure ℚ) := by simp
  rw [← h, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 : red (ℓ : A) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  exact not_isUnit_zero (h0 ▸ hu.map red)

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.ModularCurve _root_.ModularCurve.CharPModel in
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
    (fm : FibreModel N A ℓ k red) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w) =
          (fm.spPlace hred dataAll hsep) w := by
  intro σ hσ w
  have _ := hKr
  have _ := halpha
  have _ := hbeta
  have _ := hsym
  have hℓA := ModularCurve.GaloisActionOnPlaces.valuation_natCast_lt_one A ℓ k red
  exact ModularCurve.GaloisActionOnPlaces.spPlace_smul_eq_of_inertia N A ℓ k red hred dataAll hsep fm
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
    hσ w

end S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level (solution)
