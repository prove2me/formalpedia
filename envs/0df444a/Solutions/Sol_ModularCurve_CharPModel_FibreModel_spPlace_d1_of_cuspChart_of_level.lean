-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d1_of_cuspChart_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e7cf57b7-8cfc-55c0-8861-c145183939f7

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos
import Theorems.Thm_ModularCurve_twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_sub_mem_nonunits_of_integral_affineBaseInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.ModularCurve.CharPModel ModularCurve.CharPReduction"
open scoped Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange EvalSymm heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff mem_restrictAlong_iff KroneckerCongruence geomAut IsAtkinLehnerAutFull coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs mem_integralCoeffs_of_integral_affineBaseFin mem_integralCoeffs_of_integral_affineBaseInf exists_ord_sub_pos_of_integral_affineBaseFin exists_sub_mem_nonunits_of_integral_affineBaseInf"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseFin affineBaseInf FibreModel FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff FibreModel.coe_piFin_eq_coeffRed FibreModel.coe_piInf_eq_coeffRed_of_cuspChart"
namespace HeckeSpecialization
p2m_open "ModularCurve.CharPModel ModularCurve"

section PlaceGeneral

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_nonunits_iff_ord_pos (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring.nonunits ↔ 0 < v.ord f := by
  constructor
  · intro h
    have hmem : f ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : v.toValuationSubring) : F) ∈ v.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (v.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg hf h.le
    have h' := (v.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

private theorem zero_mem_nonunits (v : Place K F) : (0 : F) ∈ v.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

private theorem mem_nonunits_iff_mem_and {L : Type*} [Field L] (B : ValuationSubring L) (x : L) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  constructor
  · intro h
    refine ⟨B.nonunits_subset h, ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    · right
      intro hinv
      rw [ValuationSubring.mem_nonunits_iff] at h
      have h1 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hinv
      have h2 : B.valuation (x * x⁻¹) < 1 := by
        rw [map_mul]
        calc B.valuation x * B.valuation x⁻¹ ≤ B.valuation x * 1 := by gcongr
          _ = B.valuation x := mul_one _
          _ < 1 := h
      rw [mul_inv_cancel₀ hx, map_one] at h2
      exact lt_irrefl _ h2
  · rintro ⟨hx, h⟩
    rcases h with h | h
    · subst h
      rw [ValuationSubring.mem_nonunits_iff, map_zero]
      exact zero_lt_one
    · rw [ValuationSubring.mem_nonunits_iff]
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact h (by rw [inv_zero]; exact zero_mem _)
      rcases lt_or_ge (B.valuation x) 1 with hlt | hle
      · exact hlt
      · exfalso
        apply h
        rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hle

private theorem mem_nonunits_iff_map_mem_nonunits {L L' : Type*} [Field L] [Field L']
    (B : ValuationSubring L) (B' : ValuationSubring L') (φ : L →+* L')
    (hmem : ∀ y, y ∈ B ↔ φ y ∈ B') (x : L) :
    x ∈ B.nonunits ↔ φ x ∈ B'.nonunits := by
  rw [mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and, ← hmem,
    map_eq_zero_iff φ φ.injective, ← map_inv₀, ← hmem]

private theorem _root_.AlgebraicCurve.Place.HasValue.sub {v : Place K F} {g h : F} {a b : K}
    (hg : v.HasValue g a) (hh : v.HasValue h b) : v.HasValue (g - h) (a - b) := by
  obtain ⟨hgm, hga⟩ := hg
  obtain ⟨hhm, hhb⟩ := hh
  refine ⟨sub_mem hgm hhm, ?_⟩
  have : (⟨g - h, sub_mem hgm hhm⟩ : v.toValuationSubring) = ⟨g, hgm⟩ - ⟨h, hhm⟩ := rfl
  rw [this, map_sub, hga, hhb, map_sub]

p2m_alias "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.AlgebraicCurve.Place.HasValue.sub" "AlgebraicCurve.Place.HasValue.sub"
private theorem _root_.AlgebraicCurve.Place.HasValue.neg {v : Place K F} {g : F} {a : K}
    (hg : v.HasValue g a) : v.HasValue (-g) (-a) := by
  have := (Place.hasValue_algebraMap v (0 : K)).sub hg
  simpa using this

p2m_alias "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.AlgebraicCurve.Place.HasValue.neg" "AlgebraicCurve.Place.HasValue.neg"
private theorem _root_.AlgebraicCurve.Place.HasValue.add {v : Place K F} {g h : F} {a b : K}
    (hg : v.HasValue g a) (hh : v.HasValue h b) : v.HasValue (g + h) (a + b) := by
  have := hg.sub hh.neg
  simpa [sub_neg_eq_add] using this

p2m_alias "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.AlgebraicCurve.Place.HasValue.add" "AlgebraicCurve.Place.HasValue.add"

private theorem hasValue_iff_sub_mem_nonunits (v : Place K F) (g : F) (a : K) :
    v.HasValue g a ↔ g - algebraMap K F a ∈ v.toValuationSubring.nonunits := by
  constructor
  · rintro ⟨hg, hga⟩
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring :=
      sub_mem hg (v.algebraMap_mem' a)
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := rfl
    have key : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [this, ← IsLocalRing.residue_eq_zero_iff, map_sub, hga, Place.residue_algebraMap,
        sub_self]
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mpr key
  · intro h
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring :=
      v.toValuationSubring.nonunits_subset h
    have hg : g ∈ v.toValuationSubring := by
      have := add_mem hmem (v.algebraMap_mem' a)
      simpa using this
    refine ⟨hg, ?_⟩
    have h' : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mp h
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := rfl
    rw [this, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero,
      Place.residue_algebraMap] at h'
    exact h'

private theorem sub_mem_nonunits_iff_eq {v : Place K F} {g : F} {a : K} (hg : v.HasValue g a)
    (a' : K) : g - algebraMap K F a' ∈ v.toValuationSubring.nonunits ↔ a' = a := by
  rw [← hasValue_iff_sub_mem_nonunits]
  exact ⟨fun h => Place.HasValue.unique h hg, fun h => h ▸ hg⟩

end PlaceGeneral

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (x : F) :
    x ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ W.toValuationSubring := Iff.rfl

private theorem mem_restrictAlong_nonunits_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (x : F) :
    x ∈ (W.restrictAlong φ hφ).toValuationSubring.nonunits ↔
      φ x ∈ W.toValuationSubring.nonunits :=
  mem_nonunits_iff_map_mem_nonunits _ _ φ.toRingHom (fun _ => Iff.rfl) x

private theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') : 0 < Place.ramificationIndexAlong φ W := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := F)

private theorem ord_restrictAlong_pos_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (x : F) :
    0 < (W.restrictAlong φ hφ).ord x ↔ 0 < W.ord (φ x) := by
  have he := ramificationIndexAlong_pos φ hφ W
  rw [Place.ord_restrictAlong φ hφ W x]
  constructor
  · intro h; positivity
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have : (Place.ramificationIndexAlong φ W : ℤ) * (W.restrictAlong φ hφ).ord x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast he.le) hle
    omega

private theorem ord_restrictAlong_nonpos_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (x : F) :
    (W.restrictAlong φ hφ).ord x ≤ 0 ↔ W.ord (φ x) ≤ 0 := by
  have := (ord_restrictAlong_pos_iff φ hφ W x).not
  simp only [not_lt] at this
  exact this

private theorem ord_inv_smul (σ : F' ≃ₐ[K] F') (W : Place K F') (f : F') :
    (σ⁻¹ • W).ord f = W.ord (σ f) := by
  have h := Place.ord_smul σ (σ⁻¹ • W) f
  rw [smul_smul, mul_inv_cancel, one_smul] at h
  exact h.symm

end Along

section Frob

variable (k : Type*) [Field k] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

private theorem mem_frobOnPlaces_nonunits_iff (P : Place k (modularFunctionFieldC k N))
    (x : modularFunctionFieldC k N) :
    x ∈ (frobOnPlacesGeomLevel k N data hKr P).toValuationSubring.nonunits ↔
      frobeniusGeomLevel k N data hKr x ∈ P.toValuationSubring.nonunits :=
  mem_nonunits_iff_map_mem_nonunits _ _ (frobeniusGeomLevel k N data hKr).toRingHom
    (fun y => mem_frobOnPlacesGeomLevel_iff k N data hKr P y) x

end Frob

section Red

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private theorem red_eq_zero_iff (hred : Function.Surjective red) (a : A) :
    red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := by
  have hmax : (RingHom.ker red).IsMaximal := RingHom.ker_isMaximal_of_surjective red hred
  rw [← IsLocalRing.eq_maximalIdeal hmax, RingHom.mem_ker]

private theorem valuation_lt_one_of_red_eq_zero (hred : Function.Surjective red) {a : A}
    (ha : red a = 0) : A.valuation (a : AlgebraicClosure ℚ) < 1 :=
  (ValuationSubring.valuation_lt_one_iff A a).mp ((red_eq_zero_iff hred a).mp ha)

include red in
private theorem valuation_natCast_lt_one (hred : Function.Surjective red) :
    A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := by
  have h : red (ℓ : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero k ℓ
  have := valuation_lt_one_of_red_eq_zero hred h
  simpa using this

private theorem valuation_coe_lt_one_iff (a : A) :
    A.valuation (a : AlgebraicClosure ℚ) < 1 ↔ a ∈ IsLocalRing.maximalIdeal A :=
  (ValuationSubring.valuation_lt_one_iff A a).symm

private theorem exists_coe_eq_of_valuation_lt_one {x : AlgebraicClosure ℚ} (hx : A.valuation x < 1) :
    ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧ (a : AlgebraicClosure ℚ) = x :=
  ⟨⟨x, (A.valuation_le_one_iff x).mp hx.le⟩,
    (ValuationSubring.valuation_lt_one_iff A _).mpr hx, rfl⟩

end Red

section PlaceGeneral2

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem hasValue_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (g : F) (a : K) :
    (W.restrictAlong φ hφ).HasValue g a ↔ W.HasValue (φ g) a := by
  rw [hasValue_iff_sub_mem_nonunits, hasValue_iff_sub_mem_nonunits,
    mem_restrictAlong_nonunits_iff, map_sub, AlgHom.commutes]

private theorem ord_sub_pos_of_hasValue {W : Place K F} {g : F} {a : K} (hg : W.HasValue g a)
    (hne : g ≠ algebraMap K F a) : 0 < W.ord (g - algebraMap K F a) :=
  (mem_nonunits_iff_ord_pos W (sub_ne_zero.mpr hne)).mp
    ((hasValue_iff_sub_mem_nonunits W g a).mp hg)

private theorem hasValue_of_ord_sub_pos {W : Place K F} {g : F} {a : K}
    (h : 0 < W.ord (g - algebraMap K F a)) (hne : g ≠ algebraMap K F a) : W.HasValue g a :=
  (hasValue_iff_sub_mem_nonunits W g a).mpr
    ((mem_nonunits_iff_ord_pos W (sub_ne_zero.mpr hne)).mpr h)

private theorem mem_iff_mem_of_sub_mem {R : Type*} [CommRing R] (I : Ideal R) {x y : R}
    (h : x - y ∈ I) : x ∈ I ↔ y ∈ I := by
  constructor
  · intro hx
    have : y = x - (x - y) := by ring
    rw [this]
    exact I.sub_mem hx h
  · intro hy
    have : x = x - y + y := by ring
    rw [this]
    exact I.add_mem h hy

end PlaceGeneral2

section Modular

local notation "ℚ̄" => AlgebraicClosure ℚ

private abbrev FF (M : ℕ) : Type := ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))

variable (M : ℕ) [NeZero M]

private theorem residue_surjective (W : Place ℚ̄ (FF M)) :
    Function.Surjective (algebraMap ℚ̄ W.ResidueField) := by
  haveI := isCurveOver_laurentBaseChange_modularFunctionFieldFull ℚ̄ M
  haveI : Module.Finite ℚ̄ W.ResidueField := IsCurveOver.finite_residueField W
  haveI : Algebra.IsIntegral ℚ̄ W.ResidueField := Algebra.IsIntegral.of_finite ℚ̄ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℚ̄) (K := W.ResidueField)).surjective

private theorem exists_hasValue (W : Place ℚ̄ (FF M)) {g : (FF M)} (hg : g ∈ W.toValuationSubring) :
    ∃ a : ℚ̄, W.HasValue g a := by
  obtain ⟨a, ha, -⟩ := W.exists_hasValue_of_surjective (residue_surjective M W) hg
  exact ⟨a, ha⟩

private theorem coe_jBar : ((jBar M : (FF M)) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ jq := rfl

private theorem coe_algebraMap' (c : ℚ̄) :
    ((algebraMap ℚ̄ (FF M) c : (FF M)) : LaurentSeries ℚ̄) = HahnSeries.single 0 c := by
  rw [← algebraMap_laurentSeries_eq_single]
  rfl

private theorem jBar_ne_algebraMap (c : ℚ̄) : (jBar M : (FF M)) ≠ algebraMap ℚ̄ (FF M) c := by
  intro h
  have h1 := congrArg (fun x : (FF M) => (x : LaurentSeries ℚ̄).coeff (-1)) h
  simp only [coe_jBar, coeffEmb_coeff, coeff_jq_neg_one, map_one, coe_algebraMap'] at h1
  rw [HahnSeries.coeff_single_of_ne (by norm_num)] at h1
  exact one_ne_zero h1

private theorem jBar_ne_zero : (jBar M : (FF M)) ≠ 0 := by
  simpa using jBar_ne_algebraMap M 0

private theorem jBar_inv_ne_algebraMap (c : ℚ̄) : (jBar M : (FF M))⁻¹ ≠ algebraMap ℚ̄ (FF M) c := by
  intro h
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, inv_eq_zero] at h
    exact jBar_ne_zero M h
  · apply jBar_ne_algebraMap M c⁻¹
    rw [map_inv₀, ← h, inv_inv]

private theorem exists_mem_maximalIdeal_sub_mem_nonunits_iff (A : ValuationSubring ℚ̄)
    {F : Type*} [Field F] [Algebra ℚ̄ F] {w : Place ℚ̄ F} {g : F} {x : ℚ̄}
    (hg : w.HasValue g x) :
    (∃ a ∈ IsLocalRing.maximalIdeal A,
        g - algebraMap ℚ̄ F (a : ℚ̄) ∈ w.toValuationSubring.nonunits) ↔ A.valuation x < 1 := by
  constructor
  · rintro ⟨a, ha, h⟩
    have hax : (a : ℚ̄) = x := (sub_mem_nonunits_iff_eq hg (a : ℚ̄)).mp h
    rw [← hax]
    exact (valuation_coe_lt_one_iff a).mpr ha
  · intro hx
    obtain ⟨a, ha, hax⟩ := exists_coe_eq_of_valuation_lt_one hx
    exact ⟨a, ha, (sub_mem_nonunits_iff_eq hg _).mpr hax⟩

private theorem valuation_lt_one_or_of_mul (A : ValuationSubring ℚ̄) (a b : A)
    (h : A.valuation ((a : ℚ̄) * b) < 1) :
    A.valuation (a : ℚ̄) < 1 ∨ A.valuation (b : ℚ̄) < 1 := by
  rw [valuation_coe_lt_one_iff, valuation_coe_lt_one_iff]
  have hab : a * b ∈ IsLocalRing.maximalIdeal A := by
    rw [← valuation_coe_lt_one_iff]
    push_cast
    exact h
  exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_or_mem hab

private theorem exists_ord_inv_sub_pos (A : ValuationSubring ℚ̄) (W : Place ℚ̄ (FF M)) (g : (FF M))
    (hg : ∀ c : ℚ̄, g ≠ algebraMap ℚ̄ (FF M) c)
    (hpole : ∀ a : A, W.ord (g - algebraMap ℚ̄ (FF M) (a : ℚ̄)) ≤ 0) :
    ∃ c : A, 0 < W.ord (g⁻¹ - algebraMap ℚ̄ (FF M) (c : ℚ̄)) := by
  have hginv : ∀ c : ℚ̄, g⁻¹ ≠ algebraMap ℚ̄ (FF M) c := by
    intro c h
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, inv_eq_zero] at h
      exact hg 0 (by rw [h, map_zero])
    · exact hg c⁻¹ (by rw [map_inv₀, ← h, inv_inv])
  by_cases hinv : g⁻¹ ∈ W.toValuationSubring
  · obtain ⟨c, hc⟩ := exists_hasValue M W hinv
    by_cases hcA : c ∈ A
    · exact ⟨⟨c, hcA⟩, ord_sub_pos_of_hasValue hc (hginv c)⟩
    · exfalso
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hcA A.zero_mem
      have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hval : W.HasValue g c⁻¹ := by simpa using hc.inv hc0
      have hpos := ord_sub_pos_of_hasValue hval (hg c⁻¹)
      exact absurd (hpole ⟨c⁻¹, hcinv⟩) (not_le.mpr hpos)
  · exfalso
    have hgO : g ∈ W.toValuationSubring := (W.toValuationSubring.mem_or_inv_mem g).resolve_right hinv
    have hg0 : g ≠ 0 := fun h => hg 0 (by rw [h, map_zero])
    have hnu : g ∈ W.toValuationSubring.nonunits :=
      (mem_nonunits_iff_mem_and _ g).mpr ⟨hgO, Or.inr hinv⟩
    have hpos : 0 < W.ord g := (mem_nonunits_iff_ord_pos W hg0).mp hnu
    have := hpole 0
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero] at this
    exact absurd this (not_le.mpr hpos)

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private theorem heckeAlphaBar_jBar : heckeAlphaBar ℚ̄ N ℓ (jBar N) = jBar (N * ℓ) := by
  apply Subtype.ext
  rw [coe_heckeAlphaBar]
  rfl

private theorem coe_heckeBetaBar_jBar :
    ((heckeBetaBar ℚ̄ N ℓ (jBar N) : (FF (N * ℓ))) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (jqN ℓ) := by
  rw [coe_heckeBetaBar, coe_jBar, jqN, coeffEmb, coeffSemilinearAut.coeffMap_qExpand]

private theorem heckeBetaBar_jBar_ne_algebraMap (c : ℚ̄) :
    heckeBetaBar ℚ̄ N ℓ (jBar N) ≠ algebraMap ℚ̄ (FF (N * ℓ)) c := by
  intro h
  apply jBar_ne_algebraMap N c
  apply (heckeBetaBar ℚ̄ N ℓ).toRingHom.injective
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h, AlgHom.commutes]

private theorem heckeAlphaBar_jBar_ne_algebraMap (c : ℚ̄) :
    heckeAlphaBar ℚ̄ N ℓ (jBar N) ≠ algebraMap ℚ̄ (FF (N * ℓ)) c := by
  rw [heckeAlphaBar_jBar]
  exact jBar_ne_algebraMap _ c

end Modular

section Partners

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
  (fm : FibreModel N A ℓ k red)

private theorem affineBaseFin_le_BFin : affineBaseFin N A ≤ fm.BFin := by
  rw [affineBaseFin, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact fm.constFin_mem a
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fm.jBar_mem

private theorem affineBaseInf_le_BInf : affineBaseInf N A ≤ fm.BInf := by
  rw [affineBaseInf, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact fm.constInf_mem a
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fm.jInvBar_mem

private theorem exists_partner_aux (B R : Subring (FF N)) (hRB : R ≤ B)
    (π : B →+* modularFunctionFieldC k N)
    (g : modularFunctionFieldC k N →+* modularFunctionFieldC k N)
    (hint : ∀ b : B, ∃ p : Polynomial R, p.Monic ∧ Polynomial.eval₂ R.subtype (b : FF N) p = 0)
    (hclosed : ∀ x, (∃ p : Polynomial π.range, p.Monic ∧
      Polynomial.eval₂ π.range.subtype x p = 0) → x ∈ π.range)
    (hgen : R ≤ (π.range.comap (g.comp π)).map B.subtype) (b : B) :
    ∃ b' : B, π b' = g (π b) := by
  obtain ⟨p₀, hp₀, hb⟩ := hint b
  let ι : R →+* B := Subring.inclusion hRB
  have hψ : ∀ y : R, ((g.comp π).comp ι) y ∈ π.range := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hgen y.2
    have hz' : z = ι y := Subtype.ext hzy
    subst hz'
    exact hz
  let ψ : R →+* π.range := ((g.comp π).comp ι).codRestrict π.range hψ
  have h2 : Polynomial.eval₂ ι b p₀ = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ p₀ ι B.subtype b
    have hcomp : B.subtype.comp ι = R.subtype := RingHom.ext fun _ => rfl
    rw [hcomp] at h
    change B.subtype (Polynomial.eval₂ ι b p₀) = 0
    rw [h]
    exact hb
  have hroot : Polynomial.eval₂ π.range.subtype (g (π b)) (p₀.map ψ) = 0 := by
    rw [Polynomial.eval₂_map]
    have h1 : π.range.subtype.comp ψ = (g.comp π).comp ι := RingHom.ext fun _ => rfl
    rw [h1]
    calc Polynomial.eval₂ ((g.comp π).comp ι) (g (π b)) p₀
        = (g.comp π) (Polynomial.eval₂ ι b p₀) := (Polynomial.hom_eval₂ p₀ ι (g.comp π) b).symm
      _ = 0 := by rw [h2, map_zero]
  obtain ⟨b', hb'⟩ := RingHom.mem_range.mp (hclosed _ ⟨p₀.map ψ, hp₀.map ψ, hroot⟩)
  exact ⟨b', hb'⟩

private theorem exists_partner_fin (b : fm.BFin) :
    ∃ b' : fm.BFin, fm.piFin b' = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  refine exists_partner_aux fm.BFin (affineBaseFin N A) (affineBaseFin_le_BFin fm) fm.piFin
    (frobeniusGeomLevel k N data hKr).toRingHom fm.integralFin fm.intClosed_piFin ?_ b
  rw [affineBaseFin, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · refine ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, ?_, rfl⟩
    change frobeniusGeomLevel k N data hKr (fm.piFin ⟨constantsHom N A a, fm.constFin_mem a⟩)
      ∈ fm.piFin.range
    rw [fm.piFin_const, AlgHom.commutes]
    exact ⟨_, fm.piFin_const a⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨⟨jBar N, fm.jBar_mem⟩, ?_, rfl⟩
    change frobeniusGeomLevel k N data hKr (fm.piFin ⟨jBar N, fm.jBar_mem⟩) ∈ fm.piFin.range
    rw [fm.piFin_j, frobeniusGeomLevel_jq, ← fm.piFin_j, ← map_pow]
    exact ⟨_, rfl⟩

private theorem exists_partner_inf (b : fm.BInf) :
    ∃ b' : fm.BInf, fm.piInf b' = frobeniusGeomLevel k N data hKr (fm.piInf b) := by
  refine exists_partner_aux fm.BInf (affineBaseInf N A) (affineBaseInf_le_BInf fm) fm.piInf
    (frobeniusGeomLevel k N data hKr).toRingHom fm.integralInf fm.intClosed_piInf ?_ b
  rw [affineBaseInf, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · refine ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, ?_, rfl⟩
    change frobeniusGeomLevel k N data hKr (fm.piInf ⟨constantsHom N A a, fm.constInf_mem a⟩)
      ∈ fm.piInf.range
    rw [fm.piInf_const, AlgHom.commutes]
    exact ⟨_, fm.piInf_const a⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, ?_, rfl⟩
    change frobeniusGeomLevel k N data hKr (fm.piInf ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩)
      ∈ fm.piInf.range
    rw [fm.piInf_jInv, map_inv₀, frobeniusGeomLevel_jq, ← inv_pow, ← fm.piInf_jInv, ← map_pow]
    exact ⟨_, rfl⟩

private theorem valuation_coeff_qExpand_sub_lt_one (hred : Function.Surjective red)
    {x y : LaurentSeries ℚ̄} (hx : x ∈ integralCoeffs A.toSubring)
    (hy : y ∈ integralCoeffs A.toSubring)
    (h : coeffRed A.toSubring red ⟨y, hy⟩ = qExpand k ℓ (coeffRed A.toSubring red ⟨x, hx⟩))
    (n : ℤ) : A.valuation ((qExpand ℚ̄ ℓ x - y).coeff n) < 1 := by
  rw [HahnSeries.coeff_sub]
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [qExpand_coeff_mul]
    have hxm : x.coeff m ∈ A := hx m
    have hym : y.coeff (ℓ * m) ∈ A := hy (ℓ * m)
    have hred0 : red (⟨x.coeff m, hxm⟩ - ⟨y.coeff (ℓ * m), hym⟩) = 0 := by
      rw [map_sub]
      have h1 : red ⟨y.coeff (ℓ * m), hym⟩ = (coeffRed A.toSubring red ⟨y, hy⟩).coeff (ℓ * m) :=
        (coeffRed_coeff A.toSubring red ⟨y, hy⟩ (ℓ * m)).symm
      have h2 : red ⟨x.coeff m, hxm⟩ = (coeffRed A.toSubring red ⟨x, hx⟩).coeff m :=
        (coeffRed_coeff A.toSubring red ⟨x, hx⟩ m).symm
      rw [h1, h2, h, qExpand_coeff_mul, sub_self]
    have := valuation_lt_one_of_red_eq_zero hred hred0
    simpa using this
  · rw [qExpand_coeff_of_not_dvd ℓ x hn, zero_sub]
    have hyn : y.coeff n ∈ A := hy n
    have hred0 : red (-⟨y.coeff n, hyn⟩) = 0 := by
      rw [map_neg, neg_eq_zero]
      have h1 : red ⟨y.coeff n, hyn⟩ = (coeffRed A.toSubring red ⟨y, hy⟩).coeff n :=
        (coeffRed_coeff A.toSubring red ⟨y, hy⟩ n).symm
      rw [h1, h, qExpand_coeff_of_not_dvd ℓ _ hn]
    have := valuation_lt_one_of_red_eq_zero hred hred0
    simpa using this

end Partners

section Integrality

variable {F F' : Type*} [Field F] [Field F']

private theorem isIntegral_iff_exists (R : Subring F) (x : F) :
    IsIntegral R x ↔ ∃ p : Polynomial R, p.Monic ∧ Polynomial.eval₂ R.subtype x p = 0 :=
  Iff.rfl

private theorem exists_monic_map (R : Subring F) (R' : Subring F') (φ : F →+* F')
    (hR : R ≤ R'.comap φ) {x : F}
    (hx : ∃ p : Polynomial R, p.Monic ∧ Polynomial.eval₂ R.subtype x p = 0) :
    ∃ p : Polynomial R', p.Monic ∧ Polynomial.eval₂ R'.subtype (φ x) p = 0 := by
  obtain ⟨p, hp, hx⟩ := hx
  let ψ : R →+* R' := (φ.comp R.subtype).codRestrict R' (fun y => hR y.2)
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  rw [Polynomial.eval₂_map]
  have h1 : R'.subtype.comp ψ = φ.comp R.subtype := RingHom.ext fun _ => rfl
  rw [h1, ← Polynomial.hom_eval₂, hx, map_zero]

private theorem exists_monic_of_integral (R S : Subring F) (hS : ∀ s ∈ S, IsIntegral R s) {x : F}
    (hx : ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0) :
    ∃ p : Polynomial R, p.Monic ∧ Polynomial.eval₂ R.subtype x p = 0 := by
  rw [← isIntegral_iff_exists] at hx ⊢
  have hle : ∀ s : S, (s : F) ∈ integralClosure R F :=
    fun s => (mem_integralClosure_iff _ _).mpr (hS s s.2)
  let ψ : S →+* integralClosure R F := S.subtype.codRestrict (integralClosure R F) hle
  have hx' : IsIntegral (integralClosure R F) x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have h1 : (algebraMap (integralClosure R F) F).comp ψ = algebraMap S F :=
      RingHom.ext fun _ => rfl
    rw [h1]
    exact hpx
  exact isIntegral_trans x hx'

end Integrality

section ModularIntegrality

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private theorem heckeAlphaBar_constantsHom (a : A) :
    heckeAlphaBar ℚ̄ N ℓ (constantsHom N A a) = constantsHom (N * ℓ) A a := by
  rw [constantsHom, RingHom.comp_apply, AlgHom.commutes]
  rfl

private theorem heckeBetaBar_constantsHom (a : A) :
    heckeBetaBar ℚ̄ N ℓ (constantsHom N A a) = constantsHom (N * ℓ) A a := by
  rw [constantsHom, RingHom.comp_apply, AlgHom.commutes]
  rfl

private theorem affineBaseFin_le_comap_alpha :
    affineBaseFin N A ≤ (affineBaseFin (N * ℓ) A).comap (heckeAlphaBar ℚ̄ N ℓ).toRingHom := by
  rw [affineBaseFin, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      heckeAlphaBar_constantsHom]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      heckeAlphaBar_jBar]
    exact Subring.subset_closure (Or.inr rfl)

private abbrev adjJ' : Subring (FF (N * ℓ)) :=
  Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪ {heckeBetaBar ℚ̄ N ℓ (jBar N)})

private theorem affineBaseFin_le_comap_beta :
    affineBaseFin N A ≤ (adjJ' A N ℓ).comap (heckeBetaBar ℚ̄ N ℓ).toRingHom := by
  rw [affineBaseFin, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      heckeBetaBar_constantsHom]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact Subring.subset_closure (Or.inr rfl)

private abbrev RInf : Subring (FF (N * ℓ)) :=
  Subring.closure (Set.range (constantsHom (N * ℓ) A) ∪
    {(jBar (N * ℓ))⁻¹, (heckeBetaBar ℚ̄ N ℓ (jBar N))⁻¹})

private theorem affineBaseInf_le_comap_alpha :
    affineBaseInf N A ≤ (RInf A N ℓ).comap (heckeAlphaBar ℚ̄ N ℓ).toRingHom := by
  rw [affineBaseInf, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      heckeAlphaBar_constantsHom]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_inv₀, heckeAlphaBar_jBar]
    exact Subring.subset_closure (Or.inr (Or.inl rfl))

private theorem affineBaseInf_le_comap_beta :
    affineBaseInf N A ≤ (RInf A N ℓ).comap (heckeBetaBar ℚ̄ N ℓ).toRingHom := by
  rw [affineBaseInf, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      heckeBetaBar_constantsHom]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_inv₀]
    exact Subring.subset_closure (Or.inr (Or.inr rfl))

private theorem isIntegral_heckeBetaBar_jBar (data : ModularPolynomialData ℓ) :
    IsIntegral (affineBaseFin (N * ℓ) A) (heckeBetaBar ℚ̄ N ℓ (jBar N)) := by
  have hJ : jBar (N * ℓ) ∈ affineBaseFin (N * ℓ) A := Subring.subset_closure (Or.inr rfl)
  let θ : Polynomial ℤ →+* affineBaseFin (N * ℓ) A :=
    (Polynomial.aeval (R := ℤ) (⟨jBar (N * ℓ), hJ⟩ : affineBaseFin (N * ℓ) A)).toRingHom
  refine ⟨data.Φ.map θ, data.monic.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  let χ : FF (N * ℓ) →+* LaurentSeries ℚ̄ :=
    (laurentBaseChange ℚ̄ (modularFunctionFieldFull (N * ℓ))).val.toRingHom
  have hχ : Function.Injective χ := Subtype.val_injective
  apply hχ
  rw [map_zero, Polynomial.hom_eval₂]
  have hθX : ((θ Polynomial.X : affineBaseFin (N * ℓ) A) : FF (N * ℓ)) = jBar (N * ℓ) := by
    have : θ Polynomial.X = ⟨jBar (N * ℓ), hJ⟩ := Polynomial.aeval_X _
    rw [this]
  have h1 : χ.comp ((algebraMap (affineBaseFin (N * ℓ) A) (FF (N * ℓ))).comp θ)
      = (coeffEmb ℚ̄).comp evalAtJ := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext_int
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X,
        Algebra.algebraMap_ofSubsemiring_apply, hθX]
      rfl
  have h2 : χ (heckeBetaBar ℚ̄ N ℓ (jBar N)) = coeffEmb ℚ̄ (jqN ℓ) := coe_heckeBetaBar_jBar N ℓ
  rw [h1, h2, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]

private theorem isIntegral_of_mem_adjJ' (data : ModularPolynomialData ℓ) (s : FF (N * ℓ))
    (hs : s ∈ adjJ' A N ℓ) : IsIntegral (affineBaseFin (N * ℓ) A) s := by
  have hle : adjJ' A N ℓ ≤ (integralClosure (affineBaseFin (N * ℓ) A) (FF (N * ℓ))).toSubring := by
    rw [Subring.closure_le]
    rintro x (⟨a, rfl⟩ | hx)
    · have hmem : constantsHom (N * ℓ) A a ∈ affineBaseFin (N * ℓ) A :=
        Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      exact (mem_integralClosure_iff _ _).mpr
        (isIntegral_algebraMap (R := affineBaseFin (N * ℓ) A) (x := ⟨_, hmem⟩))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (mem_integralClosure_iff _ _).mpr (isIntegral_heckeBetaBar_jBar A N ℓ data)
  exact (mem_integralClosure_iff _ _).mp (hle hs)

end ModularIntegrality

section Charts

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
  (fm : FibreModel N A ℓ k red) (hred : Function.Surjective red)
  (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
  (hsep : (((dataAll N (dvd_refl N)).Φ.map
      (Polynomial.mapRingHom (Int.castRingHom k))).map
    (algebraMap (Polynomial k) (RatFunc k))).Separable)

private theorem jLine_mem_spPlace (w : Place ℚ̄ (FF N)) (a₀ : A)
    (ha₀ : 0 < w.ord (jBar N - algebraMap ℚ̄ (FF N) (a₀ : ℚ̄))) :
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      ∈ (fm.spPlace hred dataAll hsep w).toValuationSubring := by
  have hb : (⟨jBar N - constantsHom N A a₀, sub_mem fm.jBar_mem (fm.constFin_mem a₀)⟩ : fm.BFin)
      = ⟨jBar N, fm.jBar_mem⟩ - ⟨constantsHom N A a₀, fm.constFin_mem a₀⟩ := rfl
  have hnu : (fm.piFin ⟨jBar N - constantsHom N A a₀, sub_mem fm.jBar_mem (fm.constFin_mem a₀)⟩
      : modularFunctionFieldC k N) ∈ (fm.spPlace hred dataAll hsep w).toValuationSubring.nonunits := by
    rw [fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀]
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    exact (mem_nonunits_iff_ord_pos w (sub_ne_zero.mpr (jBar_ne_algebraMap N _))).mpr ha₀
  rw [hb, map_sub, fm.piFin_j, fm.piFin_const] at hnu
  have hmem := (fm.spPlace hred dataAll hsep w).toValuationSubring.nonunits_subset hnu
  have := add_mem hmem ((fm.spPlace hred dataAll hsep w).algebraMap_mem' (red a₀))
  rwa [sub_add_cancel] at this

private theorem jLine_mem_frob_iff (P : Place k (modularFunctionFieldC k N)) :
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        ∈ (frobOnPlacesGeomLevel k N data hKr P).toValuationSubring ↔
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ ℓ ∈ P.toValuationSubring := by
  rw [mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq]

private theorem jLineInv_mem_frob_iff (P : Place k (modularFunctionFieldC k N)) :
    ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹
        ∈ (frobOnPlacesGeomLevel k N data hKr P).toValuationSubring ↔
      (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹) ^ ℓ
        ∈ P.toValuationSubring := by
  rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀, frobeniusGeomLevel_jq, inv_pow]

private theorem pow_mem_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) (x : F)
    {n : ℕ} (hn : n ≠ 0) : x ^ n ∈ P.toValuationSubring ↔ x ∈ P.toValuationSubring := by
  rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

private theorem frob_spPlace_eq_of_fin (w₁ w₂ : Place ℚ̄ (FF N)) (a₁ a₂ : A)
    (h₁ : 0 < w₁.ord (jBar N - algebraMap ℚ̄ (FF N) (a₁ : ℚ̄)))
    (h₂ : 0 < w₂.ord (jBar N - algebraMap ℚ̄ (FF N) (a₂ : ℚ̄)))
    (hsmall : ∀ b b' : fm.BFin, fm.piFin b' = frobeniusGeomLevel k N data hKr (fm.piFin b) →
      ∀ x y : A, w₂.HasValue (b : FF N) (x : ℚ̄) → w₁.HasValue (b' : FF N) (y : ℚ̄) →
        x - y ∈ IsLocalRing.maximalIdeal A) :
    frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w₁)
      = fm.spPlace hred dataAll hsep w₂ := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  apply FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff N ℓ A k red fm hred dataAll hsep
  · rw [jLine_mem_frob_iff, pow_mem_iff _ _ hℓ0]
    exact jLine_mem_spPlace fm hred dataAll hsep w₁ a₁ h₁
  · exact jLine_mem_spPlace fm hred dataAll hsep w₂ a₂ h₂
  · intro b
    obtain ⟨b', hb'⟩ := exists_partner_fin data hKr fm b
    obtain ⟨x, hx⟩ := exists_ord_sub_pos_of_integral_affineBaseFin A N w₂ b (fm.integralFin b) a₂ h₂
    obtain ⟨y, hy⟩ := exists_ord_sub_pos_of_integral_affineBaseFin A N w₁ b' (fm.integralFin b')
      a₁ h₁
    have hxv : w₂.HasValue (b : FF N) (x : ℚ̄) := (hasValue_iff_sub_mem_nonunits w₂ _ _).mpr hx
    have hyv : w₁.HasValue (b' : FF N) (y : ℚ̄) := (hasValue_iff_sub_mem_nonunits w₁ _ _).mpr hy
    rw [mem_frobOnPlaces_nonunits_iff, ← hb',
      fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w₁ a₁ h₁,
      fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w₂ a₂ h₂,
      exists_mem_maximalIdeal_sub_mem_nonunits_iff A hyv,
      exists_mem_maximalIdeal_sub_mem_nonunits_iff A hxv,
      valuation_coe_lt_one_iff, valuation_coe_lt_one_iff]
    exact (mem_iff_mem_of_sub_mem _ (hsmall b b' hb' x y hxv hyv)).symm

private theorem frob_spPlace_eq_of_inf (w₁ w₂ : Place ℚ̄ (FF N))
    (hp₁ : ∀ a : A, w₁.ord (jBar N - algebraMap ℚ̄ (FF N) (a : ℚ̄)) ≤ 0)
    (hp₂ : ∀ a : A, w₂.ord (jBar N - algebraMap ℚ̄ (FF N) (a : ℚ̄)) ≤ 0)
    (hsmall : ∀ b b' : fm.BInf, fm.piInf b' = frobeniusGeomLevel k N data hKr (fm.piInf b) →
      ∀ x y : A, w₂.HasValue (b : FF N) (x : ℚ̄) → w₁.HasValue (b' : FF N) (y : ℚ̄) →
        x - y ∈ IsLocalRing.maximalIdeal A) :
    frobOnPlacesGeomLevel k N data hKr (fm.spPlace hred dataAll hsep w₁)
      = fm.spPlace hred dataAll hsep w₂ := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨c₁, hc₁⟩ := exists_ord_inv_sub_pos N A w₁ (jBar N) (jBar_ne_algebraMap N) hp₁
  obtain ⟨c₂, hc₂⟩ := exists_ord_inv_sub_pos N A w₂ (jBar N) (jBar_ne_algebraMap N) hp₂
  apply FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff N ℓ A k red fm hred dataAll hsep
  · rw [jLineInv_mem_frob_iff, pow_mem_iff _ _ hℓ0]
    exact fm.jLineInv_mem_spPlace hred dataAll hsep w₁ hp₁
  · exact fm.jLineInv_mem_spPlace hred dataAll hsep w₂ hp₂
  · intro b
    obtain ⟨b', hb'⟩ := exists_partner_inf data hKr fm b
    obtain ⟨x, hx⟩ := exists_sub_mem_nonunits_of_integral_affineBaseInf A N w₂ b
      (fm.integralInf b) c₂ hc₂
    obtain ⟨y, hy⟩ := exists_sub_mem_nonunits_of_integral_affineBaseInf A N w₁ b'
      (fm.integralInf b') c₁ hc₁
    have hxv : w₂.HasValue (b : FF N) (x : ℚ̄) := (hasValue_iff_sub_mem_nonunits w₂ _ _).mpr hx
    have hyv : w₁.HasValue (b' : FF N) (y : ℚ̄) := (hasValue_iff_sub_mem_nonunits w₁ _ _).mpr hy
    rw [mem_frobOnPlaces_nonunits_iff, ← hb',
      fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w₁ hp₁,
      fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w₂ hp₂,
      exists_mem_maximalIdeal_sub_mem_nonunits_iff A hyv,
      exists_mem_maximalIdeal_sub_mem_nonunits_iff A hxv,
      valuation_coe_lt_one_iff, valuation_coe_lt_one_iff]
    exact (mem_iff_mem_of_sub_mem _ (hsmall b b' hb' x y hxv hyv)).symm

end Charts

section Small

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
  (fm : FibreModel N A ℓ k red)

private theorem coe_beta_sub_alpha (b b' : FF N) :
    ((heckeBetaBar ℚ̄ N ℓ b - heckeAlphaBar ℚ̄ N ℓ b' : FF (N * ℓ)) : LaurentSeries ℚ̄)
      = qExpand ℚ̄ ℓ (b : LaurentSeries ℚ̄) - (b' : LaurentSeries ℚ̄) := by
  rw [AddSubgroupClass.coe_sub, coe_heckeBetaBar, coe_heckeAlphaBar]

private theorem valuation_coeff_fin_lt_one (hred : Function.Surjective red) (b b' : fm.BFin)
    (hb' : fm.piFin b' = frobeniusGeomLevel k N data hKr (fm.piFin b)) (n : ℤ) :
    A.valuation (((heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)
      : FF (N * ℓ)) : LaurentSeries ℚ̄).coeff n) < 1 := by
  have hx := mem_integralCoeffs_of_integral_affineBaseFin A N (b : FF N) (fm.integralFin b)
  have hy := mem_integralCoeffs_of_integral_affineBaseFin A N (b' : FF N) (fm.integralFin b')
  have h : coeffRed A.toSubring red ⟨_, hy⟩ = qExpand k ℓ (coeffRed A.toSubring red ⟨_, hx⟩) := by
    rw [← FibreModel.coe_piFin_eq_coeffRed N A ℓ k red fm b' hy,
      ← FibreModel.coe_piFin_eq_coeffRed N A ℓ k red fm b hx, hb', frobeniusGeomLevel_apply_coe]
  rw [coe_beta_sub_alpha]
  exact valuation_coeff_qExpand_sub_lt_one hred hx hy h n

private theorem valuation_coeff_inf_lt_one (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (cc : fm.CuspChart) (b b' : fm.BInf)
    (hb' : fm.piInf b' = frobeniusGeomLevel k N data hKr (fm.piInf b)) (n : ℤ) :
    A.valuation (((heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)
      : FF (N * ℓ)) : LaurentSeries ℚ̄).coeff n) < 1 := by
  have hx := mem_integralCoeffs_of_integral_affineBaseInf A N (b : FF N) (fm.integralInf b)
  have hy := mem_integralCoeffs_of_integral_affineBaseInf A N (b' : FF N) (fm.integralInf b')
  have h : coeffRed A.toSubring red ⟨_, hy⟩ = qExpand k ℓ (coeffRed A.toSubring red ⟨_, hx⟩) := by
    rw [← FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A ℓ k red fm cc (dataAll N (dvd_refl N))
        hsep b' hy,
      ← FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A ℓ k red fm cc (dataAll N (dvd_refl N))
        hsep b hx, hb', frobeniusGeomLevel_apply_coe]
  rw [coe_beta_sub_alpha]
  exact valuation_coeff_qExpand_sub_lt_one hred hx hy h n

include data in

private theorem integral_fin (b b' : fm.BFin) :
    ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype
        (heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)) p = 0 := by
  have h1 : IsIntegral (affineBaseFin (N * ℓ) A) (heckeBetaBar ℚ̄ N ℓ (b : FF N)) :=
    (isIntegral_iff_exists _ _).mpr (exists_monic_of_integral (affineBaseFin (N * ℓ) A)
      (adjJ' A N ℓ) (isIntegral_of_mem_adjJ' A N ℓ data)
      (exists_monic_map (affineBaseFin N A) (adjJ' A N ℓ) (heckeBetaBar ℚ̄ N ℓ).toRingHom
        (affineBaseFin_le_comap_beta A N ℓ) (fm.integralFin b)))
  have h2 : IsIntegral (affineBaseFin (N * ℓ) A) (heckeAlphaBar ℚ̄ N ℓ (b' : FF N)) :=
    (isIntegral_iff_exists _ _).mpr
      (exists_monic_map (affineBaseFin N A) (affineBaseFin (N * ℓ) A)
        (heckeAlphaBar ℚ̄ N ℓ).toRingHom (affineBaseFin_le_comap_alpha A N ℓ) (fm.integralFin b'))
  exact (isIntegral_iff_exists _ _).mp (h1.sub h2)

include data in
private theorem integral_fin' (c c' : fm.BFin) :
    ∃ p : Polynomial (affineBaseFin (N * ℓ) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * ℓ) A).subtype
        (heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N)) p = 0 := by
  obtain ⟨p, hp, h⟩ := integral_fin data fm c' c
  have : IsIntegral (affineBaseFin (N * ℓ) A)
      (heckeBetaBar ℚ̄ N ℓ (c' : FF N) - heckeAlphaBar ℚ̄ N ℓ (c : FF N)) := ⟨p, hp, h⟩
  have := this.neg
  rw [neg_sub] at this
  exact (isIntegral_iff_exists _ _).mp this

private theorem integral_inf (b b' : fm.BInf) :
    ∃ p : Polynomial (RInf A N ℓ), p.Monic ∧
      Polynomial.eval₂ (RInf A N ℓ).subtype
        (heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)) p = 0 := by
  have h1 : IsIntegral (RInf A N ℓ) (heckeBetaBar ℚ̄ N ℓ (b : FF N)) :=
    (isIntegral_iff_exists _ _).mpr
      (exists_monic_map (affineBaseInf N A) (RInf A N ℓ)
        (heckeBetaBar ℚ̄ N ℓ).toRingHom (affineBaseInf_le_comap_beta A N ℓ) (fm.integralInf b))
  have h2 : IsIntegral (RInf A N ℓ) (heckeAlphaBar ℚ̄ N ℓ (b' : FF N)) :=
    (isIntegral_iff_exists _ _).mpr
      (exists_monic_map (affineBaseInf N A) (RInf A N ℓ)
        (heckeAlphaBar ℚ̄ N ℓ).toRingHom (affineBaseInf_le_comap_alpha A N ℓ) (fm.integralInf b'))
  exact (isIntegral_iff_exists _ _).mp (h1.sub h2)

private theorem integral_inf' (c c' : fm.BInf) :
    ∃ p : Polynomial (RInf A N ℓ), p.Monic ∧
      Polynomial.eval₂ (RInf A N ℓ).subtype
        (heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N)) p = 0 := by
  obtain ⟨p, hp, h⟩ := integral_inf fm c' c
  have : IsIntegral (RInf A N ℓ)
      (heckeBetaBar ℚ̄ N ℓ (c' : FF N) - heckeAlphaBar ℚ̄ N ℓ (c : FF N)) := ⟨p, hp, h⟩
  have := this.neg
  rw [neg_sub] at this
  exact (isIntegral_iff_exists _ _).mp this

private theorem valuation_lt_one_of_coeff_algebraMap (M : ℕ) [NeZero M] (z : ℚ̄)
    (h : A.valuation (((algebraMap ℚ̄ (FF M) z : FF M) : LaurentSeries ℚ̄).coeff 0) < 1) :
    A.valuation z < 1 := by
  rw [coe_algebraMap', HahnSeries.coeff_single_same] at h
  exact h

private theorem geomAut_algebraMap (M : ℕ) (σ : modularFunctionFieldFull M ≃ₐ[ℚ] modularFunctionFieldFull M)
    (z : ℚ̄) : geomAut ℚ̄ _ σ (algebraMap ℚ̄ (FF M) z) = algebraMap ℚ̄ (FF M) z :=
  AlgEquiv.commutes _ _

private theorem small_or_small_fin (hred : Function.Surjective red) (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (hσα : ∀ x, geomAut ℚ̄ _ σ (heckeAlphaBar ℚ̄ N ℓ x) = heckeBetaBar ℚ̄ N ℓ x)
    (hσβ : ∀ x, geomAut ℚ̄ _ σ (heckeBetaBar ℚ̄ N ℓ x) = heckeAlphaBar ℚ̄ N ℓ x)
    (W : Place ℚ̄ (FF (N * ℓ))) (c₀ : A)
    (hc₀ : 0 < W.ord (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) (c₀ : ℚ̄))) :
    (∀ b b' : fm.BFin, fm.piFin b' = frobeniusGeomLevel k N data hKr (fm.piFin b) →
      ∀ z : A, W.HasValue (heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N))
        (z : ℚ̄) → A.valuation (z : ℚ̄) < 1) ∨
    (∀ c c' : fm.BFin, fm.piFin c' = frobeniusGeomLevel k N data hKr (fm.piFin c) →
      ∀ z : A, W.HasValue (heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N))
        (z : ℚ̄) → A.valuation (z : ℚ̄) < 1) := by
  rw [or_iff_not_imp_left]
  intro hnot c c' hc z hz
  simp only [not_forall, exists_prop] at hnot
  obtain ⟨b, b', hb, x, hx, hxv⟩ := hnot
  have heInf := valuation_coeff_fin_lt_one data hKr fm hred b b' hb
  have hfZero : ∀ n : ℤ, A.valuation (((geomAut ℚ̄ _ σ) (heckeAlphaBar ℚ̄ N ℓ (c : FF N)
      - heckeBetaBar ℚ̄ N ℓ (c' : FF N)) : LaurentSeries ℚ̄).coeff n) < 1 := by
    intro n
    rw [map_sub, hσα, hσβ]
    exact valuation_coeff_fin_lt_one data hKr fm hred c c' hc n
  by_cases hfc : heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N)
      = algebraMap ℚ̄ (FF (N * ℓ)) (z : ℚ̄)
  · have h0 := hfZero 0
    rw [hfc, geomAut_algebraMap] at h0
    exact valuation_lt_one_of_coeff_algebraMap (N * ℓ) _ h0
  by_cases hbe : heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)
      = algebraMap ℚ̄ (FF (N * ℓ)) (x : ℚ̄)
  · have h0 := heInf 0
    rw [hbe] at h0
    exact absurd (valuation_lt_one_of_coeff_algebraMap (N * ℓ) _ h0) hxv
  have hmul := twoComponentExhaustion_valuation_mul_lt_one_of_ord_sub_pos A N ℓ
    (valuation_natCast_lt_one hred) hlN σ hσ W c₀ hc₀ _ _ (integral_fin data fm b b')
    (integral_fin' data fm c c') x z (ord_sub_pos_of_hasValue hx hbe)
    (ord_sub_pos_of_hasValue hz hfc) heInf hfZero
  exact (valuation_lt_one_or_of_mul A x z hmul).resolve_left hxv

private theorem small_or_small_inf (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (cc : fm.CuspChart) (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ)
    (hσα : ∀ x, geomAut ℚ̄ _ σ (heckeAlphaBar ℚ̄ N ℓ x) = heckeBetaBar ℚ̄ N ℓ x)
    (hσβ : ∀ x, geomAut ℚ̄ _ σ (heckeBetaBar ℚ̄ N ℓ x) = heckeAlphaBar ℚ̄ N ℓ x)
    (W : Place ℚ̄ (FF (N * ℓ))) (c₁ c₂ : A)
    (hc₁ : 0 < W.ord ((jBar (N * ℓ))⁻¹ - algebraMap ℚ̄ (FF (N * ℓ)) (c₁ : ℚ̄)))
    (hc₂ : 0 < W.ord ((heckeBetaBar ℚ̄ N ℓ (jBar N))⁻¹
      - algebraMap ℚ̄ (FF (N * ℓ)) (c₂ : ℚ̄))) :
    (∀ b b' : fm.BInf, fm.piInf b' = frobeniusGeomLevel k N data hKr (fm.piInf b) →
      ∀ z : A, W.HasValue (heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N))
        (z : ℚ̄) → A.valuation (z : ℚ̄) < 1) ∨
    (∀ c c' : fm.BInf, fm.piInf c' = frobeniusGeomLevel k N data hKr (fm.piInf c) →
      ∀ z : A, W.HasValue (heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N))
        (z : ℚ̄) → A.valuation (z : ℚ̄) < 1) := by
  rw [or_iff_not_imp_left]
  intro hnot c c' hc z hz
  simp only [not_forall, exists_prop] at hnot
  obtain ⟨b, b', hb, x, hx, hxv⟩ := hnot
  have heInf := valuation_coeff_inf_lt_one data hKr fm hred dataAll hsep cc b b' hb
  have hfZero : ∀ n : ℤ, A.valuation (((geomAut ℚ̄ _ σ) (heckeAlphaBar ℚ̄ N ℓ (c : FF N)
      - heckeBetaBar ℚ̄ N ℓ (c' : FF N)) : LaurentSeries ℚ̄).coeff n) < 1 := by
    intro n
    rw [map_sub, hσα, hσβ]
    exact valuation_coeff_inf_lt_one data hKr fm hred dataAll hsep cc c c' hc n
  by_cases hfc : heckeAlphaBar ℚ̄ N ℓ (c : FF N) - heckeBetaBar ℚ̄ N ℓ (c' : FF N)
      = algebraMap ℚ̄ (FF (N * ℓ)) (z : ℚ̄)
  · have h0 := hfZero 0
    rw [hfc, geomAut_algebraMap] at h0
    exact valuation_lt_one_of_coeff_algebraMap (N * ℓ) _ h0
  by_cases hbe : heckeBetaBar ℚ̄ N ℓ (b : FF N) - heckeAlphaBar ℚ̄ N ℓ (b' : FF N)
      = algebraMap ℚ̄ (FF (N * ℓ)) (x : ℚ̄)
  · have h0 := heInf 0
    rw [hbe] at h0
    exact absurd (valuation_lt_one_of_coeff_algebraMap (N * ℓ) _ h0) hxv
  have hmul := twoComponentExhaustion_valuation_mul_lt_one_of_ord_inv_sub_pos A N ℓ
    (valuation_natCast_lt_one hred) hlN σ hσ W c₁ hc₁ c₂ hc₂ _ _ (integral_inf fm b b')
    (integral_inf' fm c c') x z (ord_sub_pos_of_hasValue hx hbe)
    (ord_sub_pos_of_hasValue hz hfc) heInf hfZero
  exact (valuation_lt_one_or_of_mul A x z hmul).resolve_left hxv

end Small

section Transfer

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private theorem ord_alpha_pos_iff (halpha : HeckeAlphaBarIntegral ℚ̄ N ℓ) (W : Place ℚ̄ (FF (N * ℓ)))
    (a : ℚ̄) :
    0 < (W.restrictAlong (heckeAlphaBar ℚ̄ N ℓ) halpha).ord (jBar N - algebraMap ℚ̄ (FF N) a) ↔
      0 < W.ord (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) a) := by
  rw [ord_restrictAlong_pos_iff, map_sub, AlgHom.commutes, heckeAlphaBar_jBar]

private theorem ord_beta_pos_iff (hbeta : HeckeBetaBarIntegral ℚ̄ N ℓ) (W : Place ℚ̄ (FF (N * ℓ)))
    (a : ℚ̄) :
    0 < (W.restrictAlong (heckeBetaBar ℚ̄ N ℓ) hbeta).ord (jBar N - algebraMap ℚ̄ (FF N) a) ↔
      0 < W.ord (heckeBetaBar ℚ̄ N ℓ (jBar N) - algebraMap ℚ̄ (FF (N * ℓ)) a) := by
  rw [ord_restrictAlong_pos_iff, map_sub, AlgHom.commutes]

private theorem ord_alpha_nonpos_iff (halpha : HeckeAlphaBarIntegral ℚ̄ N ℓ) (W : Place ℚ̄ (FF (N * ℓ)))
    (a : ℚ̄) :
    (W.restrictAlong (heckeAlphaBar ℚ̄ N ℓ) halpha).ord (jBar N - algebraMap ℚ̄ (FF N) a) ≤ 0 ↔
      W.ord (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) a) ≤ 0 := by
  rw [ord_restrictAlong_nonpos_iff, map_sub, AlgHom.commutes, heckeAlphaBar_jBar]

private theorem ord_beta_nonpos_iff (hbeta : HeckeBetaBarIntegral ℚ̄ N ℓ) (W : Place ℚ̄ (FF (N * ℓ)))
    (a : ℚ̄) :
    (W.restrictAlong (heckeBetaBar ℚ̄ N ℓ) hbeta).ord (jBar N - algebraMap ℚ̄ (FF N) a) ≤ 0 ↔
      W.ord (heckeBetaBar ℚ̄ N ℓ (jBar N) - algebraMap ℚ̄ (FF (N * ℓ)) a) ≤ 0 := by
  rw [ord_restrictAlong_nonpos_iff, map_sub, AlgHom.commutes]

private theorem exists_ord_J'_sub_pos (data : ModularPolynomialData ℓ) (W : Place ℚ̄ (FF (N * ℓ)))
    (a₀ : A) (ha₀ : 0 < W.ord (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) (a₀ : ℚ̄))) :
    ∃ a₁ : A, 0 < W.ord (heckeBetaBar ℚ̄ N ℓ (jBar N) - algebraMap ℚ̄ (FF (N * ℓ)) (a₁ : ℚ̄)) := by
  obtain ⟨a₁, ha₁⟩ := exists_ord_sub_pos_of_integral_affineBaseFin A (N * ℓ) W
    (heckeBetaBar ℚ̄ N ℓ (jBar N))
    ((isIntegral_iff_exists _ _).mp (isIntegral_heckeBetaBar_jBar A N ℓ data)) a₀ ha₀
  exact ⟨a₁, (mem_nonunits_iff_ord_pos W
    (sub_ne_zero.mpr (heckeBetaBar_jBar_ne_algebraMap N ℓ _))).mp ha₁⟩

private theorem forall_ord_J'_sub_nonpos (data : ModularPolynomialData ℓ)
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσα : ∀ x, geomAut ℚ̄ _ σ (heckeAlphaBar ℚ̄ N ℓ x) = heckeBetaBar ℚ̄ N ℓ x)
    (hσβ : ∀ x, geomAut ℚ̄ _ σ (heckeBetaBar ℚ̄ N ℓ x) = heckeAlphaBar ℚ̄ N ℓ x)
    (W : Place ℚ̄ (FF (N * ℓ)))
    (hpole : ∀ a : A, W.ord (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) (a : ℚ̄)) ≤ 0) :
    ∀ a : A, W.ord (heckeBetaBar ℚ̄ N ℓ (jBar N) - algebraMap ℚ̄ (FF (N * ℓ)) (a : ℚ̄)) ≤ 0 := by
  intro a
  by_contra h
  rw [not_le] at h
  have h' : 0 < ((geomAut ℚ̄ _ σ)⁻¹ • W).ord
      (jBar (N * ℓ) - algebraMap ℚ̄ (FF (N * ℓ)) (a : ℚ̄)) := by
    rw [ord_inv_smul, map_sub, geomAut_algebraMap, ← heckeAlphaBar_jBar, hσα]
    exact h
  obtain ⟨a', ha'⟩ := exists_ord_J'_sub_pos A N ℓ data _ a h'
  rw [ord_inv_smul, map_sub, geomAut_algebraMap, hσβ, heckeAlphaBar_jBar] at ha'
  exact absurd (hpole a') (not_le.mpr ha')

end Transfer

end ModularCurve.CharPModel.HeckeSpecialization

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.ModularCurve.CharPModel ModularCurve.CharPModel.HeckeSpecialization in
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
    ∀ W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
    (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) halpha)
        = frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
                hbeta))
      ∨ frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N
                ℓ) halpha))
        = (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
            hbeta) := by
  have _ := hsym
  intro W

  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N ℓ Fact.out hlN
  have hlegs := geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N ℓ σ hσ
  have hσα : ∀ x, geomAut (AlgebraicClosure ℚ) _ σ (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x)
      = heckeBetaBar (AlgebraicClosure ℚ) N ℓ x := fun x => AlgHom.congr_fun hlegs.1 x
  have hσβ : ∀ x, geomAut (AlgebraicClosure ℚ) _ σ (heckeBetaBar (AlgebraicClosure ℚ) N ℓ x)
      = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ x := fun x => AlgHom.congr_fun hlegs.2 x
  set wα := W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) halpha with hwα
  set wβ := W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hbeta with hwβ
  rcases em (∃ a₀ : A, 0 < wα.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FF N)
      (a₀ : AlgebraicClosure ℚ))) with ⟨a₀, ha₀⟩ | hpole
  ·
    have hJ := (ord_alpha_pos_iff N ℓ halpha W _).mp ha₀
    obtain ⟨a₁, ha₁W⟩ := exists_ord_J'_sub_pos A N ℓ data W a₀ hJ
    have ha₁ := (ord_beta_pos_iff N ℓ hbeta W _).mpr ha₁W
    rcases small_or_small_fin data hKr fm hred hlN σ hσ hσα hσβ W a₀ hJ with hE | hF
    · right
      refine frob_spPlace_eq_of_fin data hKr fm hred dataAll hsep wα wβ a₀ a₁ ha₀ ha₁ ?_
      intro b b' hb x y hx hy
      have hv := ((hasValue_restrictAlong_iff _ hbeta W _ _).mp hx).sub
        ((hasValue_restrictAlong_iff _ halpha W _ _).mp hy)
      rw [← AddSubgroupClass.coe_sub] at hv
      exact (valuation_coe_lt_one_iff (x - y)).mp (hE b b' hb (x - y) hv)
    · left
      refine (frob_spPlace_eq_of_fin data hKr fm hred dataAll hsep wβ wα a₁ a₀ ha₁ ha₀ ?_).symm
      intro b b' hb x y hx hy
      have hv := ((hasValue_restrictAlong_iff _ halpha W _ _).mp hx).sub
        ((hasValue_restrictAlong_iff _ hbeta W _ _).mp hy)
      rw [← AddSubgroupClass.coe_sub] at hv
      exact (valuation_coe_lt_one_iff (x - y)).mp (hF b b' hb (x - y) hv)
  ·
    simp only [not_exists] at hpole
    have hpα : ∀ a : A, wα.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FF N)
        (a : AlgebraicClosure ℚ)) ≤ 0 := fun a => not_lt.mp (hpole a)
    have hpW : ∀ a : A, W.ord (jBar (N * ℓ) - algebraMap (AlgebraicClosure ℚ) (FF (N * ℓ))
        (a : AlgebraicClosure ℚ)) ≤ 0 := fun a => (ord_alpha_nonpos_iff N ℓ halpha W _).mp (hpα a)
    have hpW' := forall_ord_J'_sub_nonpos A N ℓ data σ hσα hσβ W hpW
    have hpβ : ∀ a : A, wβ.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (FF N)
        (a : AlgebraicClosure ℚ)) ≤ 0 := fun a => (ord_beta_nonpos_iff N ℓ hbeta W _).mpr (hpW' a)
    obtain ⟨c₁, hc₁⟩ := exists_ord_inv_sub_pos (N * ℓ) A W (jBar (N * ℓ))
      (jBar_ne_algebraMap (N * ℓ)) hpW
    obtain ⟨c₂, hc₂⟩ := exists_ord_inv_sub_pos (N * ℓ) A W
      (heckeBetaBar (AlgebraicClosure ℚ) N ℓ (jBar N)) (heckeBetaBar_jBar_ne_algebraMap N ℓ) hpW'
    rcases small_or_small_inf data hKr fm hred dataAll hsep cc hlN σ hσ hσα hσβ W c₁ c₂ hc₁ hc₂
      with hE | hF
    · right
      refine frob_spPlace_eq_of_inf data hKr fm hred dataAll hsep wα wβ hpα hpβ ?_
      intro b b' hb x y hx hy
      have hv := ((hasValue_restrictAlong_iff _ hbeta W _ _).mp hx).sub
        ((hasValue_restrictAlong_iff _ halpha W _ _).mp hy)
      rw [← AddSubgroupClass.coe_sub] at hv
      exact (valuation_coe_lt_one_iff (x - y)).mp (hE b b' hb (x - y) hv)
    · left
      refine (frob_spPlace_eq_of_inf data hKr fm hred dataAll hsep wβ wα hpβ hpα ?_).symm
      intro b b' hb x y hx hy
      have hv := ((hasValue_restrictAlong_iff _ halpha W _ _).mp hx).sub
        ((hasValue_restrictAlong_iff _ hbeta W _ _).mp hy)
      rw [← AddSubgroupClass.coe_sub] at hv
      exact (valuation_coe_lt_one_iff (x - y)).mp (hF b b' hb (x - y) hv)

end

end S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level (solution)
