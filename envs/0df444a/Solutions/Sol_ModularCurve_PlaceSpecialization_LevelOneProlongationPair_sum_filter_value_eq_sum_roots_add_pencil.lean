-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencil
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e1b2eb71-3aa2-5192-a2a1-92e990f0c20b

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_GaussPencilAdapter
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add
import Theorems.Thm_ValuationSubring_isIntegral_of_forall_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
import Theorems.Thm_ModularCurve_finrank_adjoin_aeval_jqModC
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_forall_mem_iff_pencil
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section

set_option autoImplicit false

open Polynomial

namespace GaussPencil

section GaussTransport

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
  (A : ValuationSubring L) (O : ValuationSubring F)

theorem exists_C_mul_primitive {R : L[X]} (hR : R ≠ 0) :
    ∃ (c : L) (P : Polynomial A), c ≠ 0 ∧ (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) ∧
      R = C c * P.map (algebraMap A L) := by
  classical
  have hinj : Function.Injective (algebraMap A L) := fun x y h => Subtype.ext h
  obtain ⟨i₀, hi₀, hmax⟩ := R.support.exists_max_image (fun i => A.valuation (R.coeff i))
    (Polynomial.nonempty_support_iff.mpr hR)
  set c := R.coeff i₀ with hc_def
  have hc : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hcoef : ∀ n, (C c⁻¹ * R).coeff n ∈ Set.range (algebraMap A L) := by
    intro n
    rw [coeff_C_mul]
    by_cases hn : n ∈ R.support
    · obtain ⟨a, ha⟩ := (A.valuation_le_iff _ _).mp (hmax n hn)
      refine ⟨a, ?_⟩
      rw [ValuationSubring.algebraMap_apply, ← ha, mul_comm (a : L) c, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, map_zero _⟩
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp ((Polynomial.lifts_iff_coeff_lifts _).mpr hcoef)
  refine ⟨c, P, hc, ⟨i₀, ?_⟩, ?_⟩
  · intro hmem
    have h1 : algebraMap A L (P.coeff i₀) = 1 := by
      rw [← coeff_map, hP, coeff_C_mul, ← hc_def, inv_mul_cancel₀ hc]
    have h1' : P.coeff i₀ = 1 := hinj (by rw [h1, map_one])
    rw [h1'] at hmem
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  · rw [hP, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

theorem valuation_aeval_map_eq_one_of_transcendental
    {κ k₀ : Type*} [Field κ] [Field k₀] [Algebra k₀ κ]
    (hO : ∀ a : A, algebraMap L F a ∈ O)
    (res : O →+* κ) (hunit : ∀ z : O, res z ≠ 0 → IsUnit z)
    (red : A →+* k₀) (hred : ∀ a : A, a ∉ IsLocalRing.maximalIdeal A → red a ≠ 0)
    (hcomp : ∀ a : A, res ⟨algebraMap L F a, hO a⟩ = algebraMap k₀ κ (red a))
    {y : F} (hy : y ∈ O) (htr : Transcendental k₀ (res ⟨y, hy⟩))
    (P : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) :
    O.valuation (aeval y (P.map (algebraMap A L))) = 1 := by
  let toO : A →+* O := ((algebraMap L F).comp (algebraMap A L)).codRestrict O fun a => hO a
  let ev : Polynomial A →+* O := eval₂RingHom toO ⟨y, hy⟩
  have hev : ((ev P : O) : F) = aeval y (P.map (algebraMap A L)) := by
    have h : O.subtype.comp ev = (aeval y).toRingHom.comp (mapRingHom (algebraMap A L)) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C, coe_mapRingHom,
          map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, ev, toO]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X, coe_mapRingHom,
          map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, ev]
        rfl
    exact RingHom.congr_fun h P
  have hres : res (ev P) = aeval (res ⟨y, hy⟩) (P.map red) := by
    have h : res.comp ev = (aeval (res ⟨y, hy⟩)).toRingHom.comp (mapRingHom red) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C, coe_mapRingHom,
          map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, ev]
        rw [← hcomp a]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X, coe_mapRingHom,
          map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, ev]
    exact RingHom.congr_fun h P
  have hPbar : P.map red ≠ 0 := by
    obtain ⟨i, hi⟩ := hP
    intro h
    exact hred _ hi (by rw [← coeff_map, h, coeff_zero])
  have hne : res (ev P) ≠ 0 := by
    rw [hres]
    exact fun h => htr ⟨P.map red, hPbar, h⟩
  rw [← hev]
  exact (O.valuation_eq_one_iff _).mp (hunit _ hne)

theorem valuation_algHom_eq_of_primitive_isUnit
    {K₁ : Type*} [Field K₁] [Algebra L K₁] (t : K₁) (φ ψ : K₁ →ₐ[L] F)
    (hφ : ∀ P : Polynomial A, (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) →
      O.valuation (aeval (φ t) (P.map (algebraMap A L))) = 1)
    (hψ : ∀ P : Polynomial A, (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) →
      O.valuation (aeval (ψ t) (P.map (algebraMap A L))) = 1)
    {x : K₁} (hx : x ∈ IntermediateField.adjoin L {t}) :
    O.valuation (φ x) = O.valuation (ψ x) := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, rfl⟩ := hx
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  obtain ⟨c₁, P, -, hP, rfl⟩ := exists_C_mul_primitive A hr
  obtain ⟨c₂, Q, -, hQ, rfl⟩ := exists_C_mul_primitive A hs
  have key : ∀ χ : K₁ →ₐ[L] F,
      (∀ P : Polynomial A, (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) →
        O.valuation (aeval (χ t) (P.map (algebraMap A L))) = 1) →
      O.valuation (χ (aeval t (C c₁ * P.map (algebraMap A L)) /
          aeval t (C c₂ * Q.map (algebraMap A L))))
        = O.valuation (algebraMap L F c₁) / O.valuation (algebraMap L F c₂) := by
    intro χ hχ
    rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, map_mul, map_mul, aeval_C, aeval_C,
      map_div₀, map_mul, map_mul, hχ P hP, hχ Q hQ, mul_one, mul_one]
  rw [key φ hφ, key ψ hψ]

theorem algHom_mem_iff_of_primitive_isUnit
    {K₁ : Type*} [Field K₁] [Algebra L K₁] (t : K₁) (φ ψ : K₁ →ₐ[L] F)
    (hφ : ∀ P : Polynomial A, (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) →
      O.valuation (aeval (φ t) (P.map (algebraMap A L))) = 1)
    (hψ : ∀ P : Polynomial A, (∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) →
      O.valuation (aeval (ψ t) (P.map (algebraMap A L))) = 1)
    {x : K₁} (hx : x ∈ IntermediateField.adjoin L {t}) :
    φ x ∈ O ↔ ψ x ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff,
    valuation_algHom_eq_of_primitive_isUnit A O t φ ψ hφ hψ hx]

end GaussTransport

section GaussResidue

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
  (A : ValuationSubring L) (O : ValuationSubring F)

noncomputable def toIntegersO (hO : ∀ a : A, algebraMap L F a ∈ O) : A →+* O :=
  ((algebraMap L F).comp (algebraMap A L)).codRestrict O fun a => hO a

@[scoped simp] theorem coe_toIntegersO (hO : ∀ a : A, algebraMap L F a ∈ O) (a : A) :
    ((toIntegersO A O hO a : O) : F) = algebraMap L F a := rfl

noncomputable def evalO (hO : ∀ a : A, algebraMap L F a ∈ O) (y : F) (hy : y ∈ O) :
    Polynomial A →+* O :=
  eval₂RingHom (toIntegersO A O hO) ⟨y, hy⟩

theorem coe_evalO (hO : ∀ a : A, algebraMap L F a ∈ O) (y : F) (hy : y ∈ O) (P : Polynomial A) :
    ((evalO A O hO y hy P : O) : F) = aeval y (P.map (algebraMap A L)) := by
  have h : O.subtype.comp (evalO A O hO y hy)
      = (aeval y).toRingHom.comp (mapRingHom (algebraMap A L)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, evalO, coe_eval₂RingHom, eval₂_C,
        coe_mapRingHom, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, evalO, coe_eval₂RingHom, eval₂_X,
        coe_mapRingHom, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun h P

theorem res_evalO {κ k₀ : Type*} [Field κ] [Field k₀] [Algebra k₀ κ]
    (hO : ∀ a : A, algebraMap L F a ∈ O) (res : O →+* κ) (red : A →+* k₀)
    (hcomp : ∀ a : A, res ⟨algebraMap L F a, hO a⟩ = algebraMap k₀ κ (red a))
    (y : F) (hy : y ∈ O) (P : Polynomial A) :
    res (evalO A O hO y hy P) = aeval (res ⟨y, hy⟩) (P.map red) := by
  have h : res.comp (evalO A O hO y hy) = (aeval (res ⟨y, hy⟩)).toRingHom.comp (mapRingHom red) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, evalO, coe_eval₂RingHom, eval₂_C,
        coe_mapRingHom, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [← hcomp a]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, evalO, coe_eval₂RingHom, eval₂_X,
        coe_mapRingHom, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  exact RingHom.congr_fun h P

theorem res_algHom_mem_adjoin_of_transcendental
    {κ k₀ : Type*} [Field κ] [Field k₀] [Algebra k₀ κ]
    (hOA : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A)
    (res : O →+* κ) (hunit : ∀ z : O, res z ≠ 0 → IsUnit z)
    (red : A →+* k₀) (hred : ∀ a : A, a ∉ IsLocalRing.maximalIdeal A → red a ≠ 0)
    (hcomp : ∀ a : A, res ⟨algebraMap L F a, (hOA a).mpr a.2⟩ = algebraMap k₀ κ (red a))
    {K₁ : Type*} [Field K₁] [Algebra L K₁] (t : K₁) (φ : K₁ →ₐ[L] F)
    (ht : φ t ∈ O) (htr : Transcendental k₀ (res ⟨φ t, ht⟩))
    {x : K₁} (hx : x ∈ IntermediateField.adjoin L {t}) (hφx : φ x ∈ O) :
    res ⟨φ x, hφx⟩ ∈ IntermediateField.adjoin k₀ {res ⟨φ t, ht⟩} := by
  have hO : ∀ a : A, algebraMap L F a ∈ O := fun a => (hOA a).mpr a.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, hrs⟩ := hx

  by_cases hr : r = 0
  · have h0 : (⟨φ x, hφx⟩ : O) = 0 := Subtype.ext (by simp [hrs, hr])
    rw [h0, map_zero]; exact zero_mem _
  by_cases hs : s = 0
  · have h0 : (⟨φ x, hφx⟩ : O) = 0 := Subtype.ext (by simp [hrs, hs])
    rw [h0, map_zero]; exact zero_mem _
  obtain ⟨c₁, P, hc₁, hP, rfl⟩ := exists_C_mul_primitive A hr
  obtain ⟨c₂, Q, hc₂, hQ, rfl⟩ := exists_C_mul_primitive A hs
  set z : κ := res ⟨φ t, ht⟩ with hz

  have hbar : ∀ R : Polynomial A, (∃ i, R.coeff i ∉ IsLocalRing.maximalIdeal A) →
      aeval z (R.map red) ≠ 0 := by
    intro R hR h
    obtain ⟨i, hi⟩ := hR
    refine htr ⟨R.map red, fun h0 => hred _ hi ?_, h⟩
    rw [← coeff_map, h0, coeff_zero]
  have hresP : res (evalO A O hO (φ t) ht P) = aeval z (P.map red) := res_evalO A O hO res red hcomp _ _ P
  have hresQ : res (evalO A O hO (φ t) ht Q) = aeval z (Q.map red) := res_evalO A O hO res red hcomp _ _ Q
  have huP : IsUnit (evalO A O hO (φ t) ht P) := hunit _ (by rw [hresP]; exact hbar P hP)
  have huQ : IsUnit (evalO A O hO (φ t) ht Q) := hunit _ (by rw [hresQ]; exact hbar Q hQ)
  have hvP : O.valuation (aeval (φ t) (P.map (algebraMap A L))) = 1 := by
    rw [← coe_evalO A O hO (φ t) ht]; exact (O.valuation_eq_one_iff _).mp huP
  have hvQ : O.valuation (aeval (φ t) (Q.map (algebraMap A L))) = 1 := by
    rw [← coe_evalO A O hO (φ t) ht]; exact (O.valuation_eq_one_iff _).mp huQ
  have hQ0 : aeval (φ t) (Q.map (algebraMap A L)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hvQ]; exact one_ne_zero)
  have hc₂' : algebraMap L F c₂ ≠ 0 := (map_ne_zero_iff _ (algebraMap L F).injective).mpr hc₂

  have hφx_eq : φ x = algebraMap L F (c₁ / c₂) * aeval (φ t) (P.map (algebraMap A L))
      / aeval (φ t) (Q.map (algebraMap A L)) := by
    rw [hrs, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, map_mul, map_mul, aeval_C, aeval_C,
      map_div₀]
    field_simp

  have hcA : c₁ / c₂ ∈ A := by
    rw [← hOA, ← O.valuation_le_one_iff]
    have hv : O.valuation (φ x) = O.valuation (algebraMap L F (c₁ / c₂)) := by
      rw [hφx_eq, map_div₀ O.valuation, map_mul, hvP, hvQ, mul_one, div_one]
    rw [← hv]
    exact (O.valuation_le_one_iff _).mpr hφx

  have hidO : (⟨φ x, hφx⟩ : O) * evalO A O hO (φ t) ht Q
      = toIntegersO A O hO ⟨c₁ / c₂, hcA⟩ * evalO A O hO (φ t) ht P := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, coe_evalO, coe_toIntegersO]
    rw [hφx_eq]
    field_simp
  have hidκ := congrArg res hidO
  rw [map_mul, map_mul, hresP, hresQ] at hidκ
  have hresc : res (toIntegersO A O hO ⟨c₁ / c₂, hcA⟩) = algebraMap k₀ κ (red ⟨c₁ / c₂, hcA⟩) :=
    hcomp ⟨c₁ / c₂, hcA⟩
  rw [hresc] at hidκ
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨C (red ⟨c₁ / c₂, hcA⟩) * P.map red, Q.map red, ?_⟩
  rw [map_mul, aeval_C, eq_div_iff (hbar Q hQ), hidκ]

end GaussResidue

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

namespace GaussPencil

open Polynomial

section GaussLine

variable {L K₁ : Type*} [Field L] [Field K₁] [Algebra L K₁]
  (A : ValuationSubring L) (V : ValuationSubring K₁)
  (hVA : ∀ c : L, algebraMap L K₁ c ∈ V ↔ c ∈ A)
  (e₁ : RatFunc L ≃ₐ[L] K₁) (hX : e₁ RatFunc.X ∈ V)
  [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)]
  (hψ : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) (IsLocalRing.residue A a)
    = IsLocalRing.residue V ⟨algebraMap L K₁ a, (hVA a).mpr a.2⟩)
  (htr : Transcendental (IsLocalRing.ResidueField A) (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩))

theorem mem_adjoin_X (K₀ : Type*) [Field K₀] [Algebra L K₀] [Algebra K₀ (RatFunc L)] [IsScalarTower L K₀ (RatFunc L)]
    (f : RatFunc L) : f ∈ IntermediateField.adjoin K₀ {(RatFunc.X : RatFunc L)} := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    have hmem : ∀ s : L[X], algebraMap L[X] (RatFunc L) s ∈ IntermediateField.adjoin K₀ {(RatFunc.X : RatFunc L)} := by
      intro s
      rw [← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_map_algebraMap K₀]
      exact IntermediateField.algebra_adjoin_le_adjoin K₀ _ (Polynomial.aeval_mem_adjoin_singleton K₀ _)
    exact div_mem (hmem p) (hmem q)

include hVA hψ htr in

theorem adjoin_residue_X_eq_top :
    IntermediateField.adjoin (IsLocalRing.ResidueField A) {IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨f, hf⟩ : ∃ f : RatFunc L, e₁ f = v := e₁.surjective v
  have hv : (⟨e₁ f, hf ▸ v.2⟩ : V) = v := Subtype.ext hf
  rw [← hv]
  exact res_algHom_mem_adjoin_of_transcendental A V hVA (IsLocalRing.residue V)
    (fun z hz => (IsLocalRing.residue_ne_zero_iff_isUnit z).mp hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) (fun a => (hψ a).symm)
    RatFunc.X (e₁ : RatFunc L →ₐ[L] K₁) hX htr (mem_adjoin_X L f) _

include hVA hψ htr in

noncomputable def thetaEquiv : RatFunc (IsLocalRing.ResidueField A) ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField V :=
  (RatFunc.algEquivOfTranscendental _ htr).trans
    ((IntermediateField.equivOfEq (adjoin_residue_X_eq_top A V hVA e₁ hX hψ htr)).trans IntermediateField.topEquiv)

@[scoped simp] theorem thetaEquiv_X : thetaEquiv A V hVA e₁ hX hψ htr RatFunc.X = IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩ := by
  simp [thetaEquiv]

theorem thetaEquiv_algebraMap (p : Polynomial (IsLocalRing.ResidueField A)) :
    thetaEquiv A V hVA e₁ hX hψ htr (algebraMap _ (RatFunc _) p)
      = aeval (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩) p := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algHom_apply, thetaEquiv_X]

include hVA hψ htr in

theorem residue_e₁_C_mul_div (c : A) (P Q : Polynomial A)
    (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A) :
    ∃ hv : e₁ (algebraMap L (RatFunc L) c *
        (algebraMap L[X] (RatFunc L) (P.map (algebraMap A L)) / algebraMap L[X] (RatFunc L) (Q.map (algebraMap A L)))) ∈ V,
      IsLocalRing.residue V ⟨_, hv⟩
        = thetaEquiv A V hVA e₁ hX hψ htr
            (algebraMap _ (RatFunc _) (IsLocalRing.residue A c) *
              (algebraMap _ (RatFunc _) (P.map (IsLocalRing.residue A))
                / algebraMap _ (RatFunc _) (Q.map (IsLocalRing.residue A)))) := by
  have hO : ∀ a : A, algebraMap L K₁ a ∈ V := fun a => (hVA a).mpr a.2
  set z := IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩ with hz

  have hbar : ∀ R : Polynomial A, (∃ i, R.coeff i ∉ IsLocalRing.maximalIdeal A) →
      aeval z (R.map (IsLocalRing.residue A)) ≠ 0 := by
    intro R hR h
    obtain ⟨i, hi⟩ := hR
    refine htr ⟨R.map (IsLocalRing.residue A), fun h0 => hi ?_, h⟩
    rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_map, h0, coeff_zero]
  have hresQ : IsLocalRing.residue V (evalO A V hO (e₁ RatFunc.X) hX Q) = aeval z (Q.map (IsLocalRing.residue A)) :=
    res_evalO A V hO _ _ (fun a => (hψ a).symm) _ _ Q
  have hresP : IsLocalRing.residue V (evalO A V hO (e₁ RatFunc.X) hX P) = aeval z (P.map (IsLocalRing.residue A)) :=
    res_evalO A V hO _ _ (fun a => (hψ a).symm) _ _ P
  have huQ : IsUnit (evalO A V hO (e₁ RatFunc.X) hX Q) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hresQ]; exact hbar Q hQ)

  have helt : e₁ (algebraMap L (RatFunc L) c *
        (algebraMap L[X] (RatFunc L) (P.map (algebraMap A L)) / algebraMap L[X] (RatFunc L) (Q.map (algebraMap A L))))
      = ((toIntegersO A V hO c * evalO A V hO (e₁ RatFunc.X) hX P * ↑(huQ.unit⁻¹) : V) : K₁) := by
    rw [map_mul, map_div₀, AlgEquiv.commutes, ← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algHom_apply,
      ← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algHom_apply]
    simp only [MulMemClass.coe_mul, coe_toIntegersO, coe_evalO]
    rw [div_eq_mul_inv, mul_assoc]
    congr 2
    have h1 : ((evalO A V hO (e₁ RatFunc.X) hX Q : V) : K₁) * ((↑(huQ.unit⁻¹) : V) : K₁) = 1 := by
      rw [← MulMemClass.coe_mul, IsUnit.mul_val_inv, OneMemClass.coe_one]
    rw [coe_evalO] at h1
    exact (eq_inv_of_mul_eq_one_right h1).symm
  refine ⟨helt ▸ SetLike.coe_mem _, ?_⟩
  have hsub : (⟨_, helt ▸ SetLike.coe_mem _⟩ : V) = toIntegersO A V hO c * evalO A V hO (e₁ RatFunc.X) hX P * ↑(huQ.unit⁻¹) :=
    Subtype.ext helt
  have hinv : IsLocalRing.residue V (↑(huQ.unit⁻¹) : V) = (aeval z (Q.map (IsLocalRing.residue A)))⁻¹ := by
    rw [← hresQ]
    have h1 : IsLocalRing.residue V (↑(huQ.unit⁻¹) : V) * IsLocalRing.residue V (evalO A V hO (e₁ RatFunc.X) hX Q) = 1 := by
      have h := congrArg (IsLocalRing.residue V) huQ.val_inv_mul
      simp only [map_mul, map_one] at h
      exact h
    exact eq_inv_of_mul_eq_one_left h1
  have hconst : IsLocalRing.residue V (toIntegersO A V hO c)
      = algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) (IsLocalRing.residue A c) :=
    (hψ c).symm
  rw [hsub, map_mul, map_mul, hresP, hinv, hconst, map_mul, map_div₀, thetaEquiv_algebraMap,
    thetaEquiv_algebraMap, AlgEquiv.commutes, ← hz, div_eq_mul_inv, mul_assoc]

end GaussLine
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section Theta

variable {L K₁ : Type*} [Field L] [Field K₁] [Algebra L K₁]
  (A : ValuationSubring L) (V : ValuationSubring K₁)
  (hVA : ∀ c : L, algebraMap L K₁ c ∈ V ↔ c ∈ A)
  (e₁ : RatFunc L ≃ₐ[L] K₁) (hX : e₁ RatFunc.X ∈ V)
  [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)]
  (hψ : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) (IsLocalRing.residue A a)
    = IsLocalRing.residue V ⟨algebraMap L K₁ a, (hVA a).mpr a.2⟩)
  (htr : Transcendental (IsLocalRing.ResidueField A) (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩))
  {k : Type*} [Field k] (σ : IsLocalRing.ResidueField A →+* k)

noncomputable def ratFuncMap : RatFunc (IsLocalRing.ResidueField A) →+* RatFunc k :=
  RatFunc.liftRingHom ((algebraMap k[X] (RatFunc k)).comp (mapRingHom σ)) (by
    intro p hp
    simp only [Submonoid.mem_comap, RingHom.coe_comp, Function.comp_apply, mem_nonZeroDivisors_iff_ne_zero]
    exact RatFunc.algebraMap_ne_zero ((Polynomial.map_ne_zero_iff σ.injective).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hp)))

theorem ratFuncMap_div (p q : Polynomial (IsLocalRing.ResidueField A)) :
    ratFuncMap A σ (algebraMap _ (RatFunc _) p / algebraMap _ (RatFunc _) q)
      = algebraMap k[X] (RatFunc k) (p.map σ) / algebraMap k[X] (RatFunc k) (q.map σ) := by
  rw [ratFuncMap, RatFunc.liftRingHom_apply_div]
  rfl

noncomputable def Theta : IsLocalRing.ResidueField V →+* RatFunc k :=
  (ratFuncMap A σ).comp (thetaEquiv A V hVA e₁ hX hψ htr).symm.toAlgHom.toRingHom

theorem Theta_thetaEquiv (f : RatFunc (IsLocalRing.ResidueField A)) :
    Theta A V hVA e₁ hX hψ htr σ (thetaEquiv A V hVA e₁ hX hψ htr f) = ratFuncMap A σ f := by
  simp [Theta]

theorem Theta_residue_X : Theta A V hVA e₁ hX hψ htr σ (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩) = RatFunc.X := by
  rw [← thetaEquiv_X A V hVA e₁ hX hψ htr, Theta_thetaEquiv]
  have : (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))
      = algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)) Polynomial.X
        / algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_X]
  rw [this, ratFuncMap_div, Polynomial.map_X, Polynomial.map_one, map_one, div_one, RatFunc.algebraMap_X]

theorem Theta_algebraMap (a : IsLocalRing.ResidueField A) :
    Theta A V hVA e₁ hX hψ htr σ (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) a)
      = RatFunc.C (σ a) := by
  have : algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) a
      = thetaEquiv A V hVA e₁ hX hψ htr (algebraMap _ (RatFunc _) (Polynomial.C a)) := by
    rw [thetaEquiv_algebraMap, aeval_C]
  rw [this, Theta_thetaEquiv]
  have h1 : (algebraMap _ (RatFunc (IsLocalRing.ResidueField A)) (Polynomial.C a))
      = algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)) (Polynomial.C a)
        / algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)) 1 := by
    rw [map_one, div_one]
  rw [h1, ratFuncMap_div, Polynomial.map_C, Polynomial.map_one, map_one, div_one, RatFunc.algebraMap_C]

theorem Theta_residue_e₁_C_mul_div (c : A) (P Q : Polynomial A)
    (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A) :
    ∃ hv : e₁ (algebraMap L (RatFunc L) c *
        (algebraMap L[X] (RatFunc L) (P.map (algebraMap A L)) / algebraMap L[X] (RatFunc L) (Q.map (algebraMap A L)))) ∈ V,
      Theta A V hVA e₁ hX hψ htr σ (IsLocalRing.residue V ⟨_, hv⟩)
        = RatFunc.C (σ (IsLocalRing.residue A c)) *
            (algebraMap k[X] (RatFunc k) (P.map (σ.comp (IsLocalRing.residue A)))
              / algebraMap k[X] (RatFunc k) (Q.map (σ.comp (IsLocalRing.residue A)))) := by
  obtain ⟨hv, hres⟩ := residue_e₁_C_mul_div A V hVA e₁ hX hψ htr c P Q hP hQ
  refine ⟨hv, ?_⟩
  rw [hres, Theta_thetaEquiv, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← mul_div_assoc, ← map_mul,
    ratFuncMap_div, Polynomial.map_mul, Polynomial.map_C, map_mul, RatFunc.algebraMap_C, Polynomial.map_map,
    Polynomial.map_map, mul_div_assoc]

end Theta
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section Presentation

variable {L K₁ : Type*} [Field L] [Field K₁] [Algebra L K₁]
  (A : ValuationSubring L) (V : ValuationSubring K₁)
  (hVA : ∀ c : L, algebraMap L K₁ c ∈ V ↔ c ∈ A)
  (e₁ : RatFunc L ≃ₐ[L] K₁) (hX : e₁ RatFunc.X ∈ V)
  [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)]
  (hψ : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) (IsLocalRing.residue A a)
    = IsLocalRing.residue V ⟨algebraMap L K₁ a, (hVA a).mpr a.2⟩)
  (htr : Transcendental (IsLocalRing.ResidueField A) (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩))

include hVA hψ htr in

theorem exists_eq_e₁_C_mul_div (v : V) (hv0 : IsLocalRing.residue V v ≠ 0) :
    ∃ (c : A) (_ : c ∉ IsLocalRing.maximalIdeal A) (P Q : Polynomial A)
      (_ : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) (_ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A),
      (v : K₁) = e₁ (algebraMap L (RatFunc L) c *
        (algebraMap L[X] (RatFunc L) (P.map (algebraMap A L)) / algebraMap L[X] (RatFunc L) (Q.map (algebraMap A L)))) := by
  have hO : ∀ a : A, algebraMap L K₁ a ∈ V := fun a => (hVA a).mpr a.2
  have hvunit : IsUnit v := (IsLocalRing.residue_ne_zero_iff_isUnit v).mp hv0
  have hv0' : (v : K₁) ≠ 0 := fun h => hvunit.ne_zero (Subtype.ext h)

  set f := e₁.symm v with hf
  have hfv : e₁ f = v := e₁.apply_symm_apply v
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp (mem_adjoin_X L f)
  rw [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap] at hrs
  have hr : r ≠ 0 := by
    rintro rfl; apply hv0'; rw [← hfv, hrs, map_zero, zero_div, map_zero]
  have hs : s ≠ 0 := by
    rintro rfl; apply hv0'; rw [← hfv, hrs, map_zero, div_zero, map_zero]
  obtain ⟨c₁, P, hc₁, hP, rfl⟩ := exists_C_mul_primitive A hr
  obtain ⟨c₂, Q, hc₂, hQ, rfl⟩ := exists_C_mul_primitive A hs

  have hvalP := valuation_aeval_map_eq_one_of_transcendental A V hO (IsLocalRing.residue V)
    (fun z hz => (IsLocalRing.residue_ne_zero_iff_isUnit z).mp hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) (fun a => (hψ a).symm) hX htr P hP
  have hvalQ := valuation_aeval_map_eq_one_of_transcendental A V hO (IsLocalRing.residue V)
    (fun z hz => (IsLocalRing.residue_ne_zero_iff_isUnit z).mp hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) (fun a => (hψ a).symm) hX htr Q hQ
  have hc₂K : algebraMap L K₁ c₂ ≠ 0 := (map_ne_zero_iff _ (algebraMap L K₁).injective).mpr hc₂
  have hQ0 : aeval (e₁ RatFunc.X) (Q.map (algebraMap A L)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hvalQ]; exact one_ne_zero)
  have he₁C : ∀ c : L, e₁ (algebraMap L[X] (RatFunc L) (C c)) = algebraMap L K₁ c := by
    intro c; rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, AlgEquiv.commutes]
  have he₁P : ∀ S : L[X], aeval (e₁ RatFunc.X) S = e₁ (algebraMap L[X] (RatFunc L) S) := by
    intro S; rw [aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]
  have hvK : (v : K₁) = algebraMap L K₁ (c₁ / c₂) * aeval (e₁ RatFunc.X) (P.map (algebraMap A L))
      / aeval (e₁ RatFunc.X) (Q.map (algebraMap A L)) := by
    rw [← hfv, hrs, map_div₀, map_mul, map_mul, map_mul, map_mul, he₁C, he₁C, ← he₁P, ← he₁P,
      map_div₀ (algebraMap L K₁)]
    field_simp
  have hval_v : V.valuation (v : K₁) = V.valuation (algebraMap L K₁ (c₁ / c₂)) := by
    rw [hvK, map_div₀ V.valuation, map_mul, hvalP, hvalQ, mul_one, div_one]

  have hcA : c₁ / c₂ ∈ A := by
    rw [← hVA, ← V.valuation_le_one_iff, ← hval_v]; exact V.valuation_le_one v
  have hcunit : (⟨c₁ / c₂, hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := by
    intro hmem
    have h1 : V.valuation (v : K₁) = 1 := (V.valuation_eq_one_iff v).mp hvunit
    have h2 : V.valuation (algebraMap L K₁ (c₁ / c₂)) < 1 := by
      have : (⟨algebraMap L K₁ (c₁ / c₂), (hVA _).mpr hcA⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
        have hloc := (IsLocalRing.mem_maximalIdeal _).mp hmem
        refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hloc ?_

        obtain ⟨w, hw⟩ := hu.exists_right_inv
        have hwL : ((w : V) : K₁) = algebraMap L K₁ (c₁ / c₂)⁻¹ := by
          have := congrArg Subtype.val hw
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
          rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right this
        have hinvA : (c₁ / c₂)⁻¹ ∈ A := by rw [← hVA, ← hwL]; exact w.2
        exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA⟩, Subtype.ext (mul_inv_cancel₀ (div_ne_zero hc₁ hc₂))⟩
      exact (V.valuation_lt_one_iff _).mp this
    rw [hval_v] at h1
    rw [h1] at h2
    exact lt_irrefl _ h2
  refine ⟨⟨c₁ / c₂, hcA⟩, hcunit, P, Q, hP, hQ, ?_⟩
  change (v : K₁) = e₁ (algebraMap L (RatFunc L) (c₁ / c₂) * _)
  rw [map_mul, AlgEquiv.commutes, map_div₀ e₁, ← he₁P, ← he₁P, hvK, mul_div_assoc]

end Presentation
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
section
p2m_open "Polynomial ModularCurve~adjoin_jqModC_eq_top P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve"

set_option autoImplicit false

namespace GaussPencil

theorem finrank_adjoin_X_pow_ratFunc' (k₀ : Type*) [Field k₀] (q : ℕ) :
    Module.finrank ↥(IntermediateField.adjoin k₀ ({(RatFunc.X : RatFunc k₀) ^ q} : Set (RatFunc k₀)))
      (RatFunc k₀) = q := by
  have hXq : (RatFunc.X : RatFunc k₀) ^ q = algebraMap k₀[X] (RatFunc k₀) (Polynomial.X ^ q) := by
    rw [map_pow, RatFunc.algebraMap_X]
  rw [RatFunc.finrank_eq_max_natDegree, hXq, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    natDegree_X_pow, natDegree_one, max_eq_left (Nat.zero_le _)]

theorem finrank_map_algEquiv {F L L' : Type*} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (S : IntermediateField F L) :
    Module.finrank ↥(S.map (e : L →ₐ[F] L')) L' = Module.finrank ↥S L := by
  refine (Algebra.finrank_eq_of_equiv_equiv (S.equivMap (e : L →ₐ[F] L')).toRingEquiv e.toRingEquiv ?_).symm
  ext x
  rfl

theorem finrank_adjoin_pow_of_transcendental {k₀ L' : Type*} [Field k₀] [Field L'] [Algebra k₀ L']
    (s : L') (hs : Transcendental k₀ s) (hgen : IntermediateField.adjoin k₀ {s} = ⊤) (q : ℕ) :
    Module.finrank ↥(IntermediateField.adjoin k₀ ({s ^ q} : Set L')) L' = q := by
  obtain ⟨e, heX⟩ : ∃ e : RatFunc k₀ ≃ₐ[k₀] L', e RatFunc.X = s :=
    ⟨(RatFunc.algEquivOfTranscendental s hs).trans
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), by simp⟩
  have hmap : (IntermediateField.adjoin k₀ ({(RatFunc.X : RatFunc k₀) ^ q} : Set (RatFunc k₀))).map
      (e : RatFunc k₀ →ₐ[k₀] L') = IntermediateField.adjoin k₀ ({s ^ q} : Set L') := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    show IntermediateField.adjoin k₀ ({e (RatFunc.X ^ q)} : Set L') = _
    rw [map_pow, heX]
  rw [← hmap, finrank_map_algEquiv, finrank_adjoin_X_pow_ratFunc']

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

namespace GaussPencil

theorem modularFunctionFieldFullC_one_eq_adjoin (k₀ : Type*) [Field k₀] :
    modularFunctionFieldFullC k₀ 1 = IntermediateField.adjoin k₀ {jqModC k₀} := by
  have hS : divisorExpansionsC k₀ 1 = {jqModC k₀} := by
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨d, _, hd, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
    · rintro rfl
      exact ⟨1, inferInstance, dvd_refl 1, (qExpand_one_apply _).symm⟩
  show IntermediateField.adjoin k₀ (divisorExpansionsC k₀ 1) = _
  rw [hS]

theorem adjoin_jqModC_eq_top (k₀ : Type*) [Field k₀] :
    IntermediateField.adjoin k₀
      ({⟨jqModC k₀, jqModC_mem_full k₀ 1⟩} : Set ↥(modularFunctionFieldFullC k₀ 1)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : LaurentSeries k₀) ∈ IntermediateField.adjoin k₀ {jqModC k₀} := by
    rw [← modularFunctionFieldFullC_one_eq_adjoin]; exact x.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, t, hrt⟩ := hx
  refine ⟨r, t, Subtype.ext ?_⟩
  have hval : ∀ p : k₀[X], aeval (jqModC k₀) p
      = ((aeval (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) p :
          ↥(modularFunctionFieldFullC k₀ 1)) : LaurentSeries k₀) :=
    fun p => aeval_algHom_apply (IntermediateField.val (modularFunctionFieldFullC k₀ 1))
      (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) p
  rw [hrt, hval r, hval t]
  exact (map_div₀ (IntermediateField.val (modularFunctionFieldFullC k₀ 1)) _ _).symm

theorem transcendental_jqModC_full (k₀ : Type*) [Field k₀] :
    Transcendental k₀ (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) :=
  fun h => ModularCurve.transcendental_jqModC k₀ (h.algHom (IntermediateField.val _))

theorem finrank_adjoin_jqModC_pow (k₀ : Type*) [Field k₀] (q : ℕ) [Fact q.Prime] [CharP k₀ q] :
    Module.finrank
      ↥(IntermediateField.adjoin k₀ ({⟨jqModC k₀ ^ q, pow_mem (jqModC_mem_full k₀ 1) q⟩} :
          Set ↥(modularFunctionFieldFullC k₀ 1)))
      ↥(modularFunctionFieldFullC k₀ 1) = q := by
  have h : (⟨jqModC k₀ ^ q, pow_mem (jqModC_mem_full k₀ 1) q⟩ : ↥(modularFunctionFieldFullC k₀ 1))
      = ⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ ^ q := Subtype.ext rfl
  rw [h]
  exact finrank_adjoin_pow_of_transcendental _ (transcendental_jqModC_full k₀) (adjoin_jqModC_eq_top k₀) q

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
section
p2m_open "Polynomial ModularCurve~adjoin_jqModC_eq_top P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve"
namespace GaussPencil
namespace B6

theorem coe_ratFuncEquivCharLOneC_X (k : Type*) [Field k] :
    ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k := by
  change (((RatFunc.algEquivOfTranscendental (jqModC k) (ModularCurve.transcendental_jqModC k)) RatFunc.X :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k) = jqModC k
  exact RatFunc.algEquivOfTranscendental_X _ _

end GaussPencil.B6
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~adjoin_jqModC_eq_top P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve"

section
open Polynomial

namespace GaussPencil

theorem mem_adjoin_simple_gen {L F : Type*} [Field L] [Field F] [Algebra L F] (g : F)
    (x : IntermediateField.adjoin L ({g} : Set F)) :
    x ∈ IntermediateField.adjoin L
      ({(⟨g, IntermediateField.mem_adjoin_simple_self L g⟩ : IntermediateField.adjoin L ({g} : Set F))} :
        Set (IntermediateField.adjoin L ({g} : Set F))) := by
  have hx : (x : F) ∈ IntermediateField.adjoin L ({g} : Set F) := x.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, s, hrs⟩ := hx
  refine ⟨r, s, Subtype.ext ?_⟩
  have hval : ∀ p : L[X], aeval g p
      = ((aeval (⟨g, IntermediateField.mem_adjoin_simple_self L g⟩ : IntermediateField.adjoin L ({g} : Set F)) p :
          IntermediateField.adjoin L ({g} : Set F)) : F) :=
    fun p => aeval_algHom_apply (IntermediateField.val (IntermediateField.adjoin L ({g} : Set F)))
      (⟨g, IntermediateField.mem_adjoin_simple_self L g⟩ : IntermediateField.adjoin L ({g} : Set F)) p
  rw [hrs, hval r, hval s]
  exact (map_div₀ (IntermediateField.val (IntermediateField.adjoin L ({g} : Set F))) _ _).symm

theorem transcendental_aeval_of_natDegree_ne_zero {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {t : A} (ht : Transcendental K t) (p : K[X]) (hp : p.natDegree ≠ 0) :
    Transcendental K (aeval t p) :=
  ht.aeval p hp (mem_nonZeroDivisors_of_ne_zero
    (leadingCoeff_ne_zero.mpr fun h => hp (by rw [h, natDegree_zero])))

theorem natDegree_X_add_C_mul_X_pow_ne_zero {K : Type*} [Field K] (c : K) {n : ℕ} (hn : n ≠ 1) :
    (X + C c * X ^ n : K[X]).natDegree ≠ 0 := by
  have h1 : (X + C c * X ^ n : K[X]).coeff 1 = 1 := by
    rw [coeff_add, coeff_X_one, coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hn), mul_zero, add_zero]
  intro h0
  have := le_natDegree_of_ne_zero (p := (X + C c * X ^ n : K[X])) (n := 1) (by rw [h1]; exact one_ne_zero)
  omega

theorem natDegree_X_pow_add_C_mul_X_ne_zero {K : Type*} [Field K] (c : K) {n : ℕ} (hn0 : n ≠ 0) (hn : n ≠ 1) :
    (X ^ n + C c * X : K[X]).natDegree ≠ 0 := by
  have h1 : (X ^ n + C c * X : K[X]).coeff n = 1 := by
    rw [coeff_add, coeff_X_pow_self, coeff_C_mul, coeff_X, if_neg (Ne.symm hn), mul_zero, add_zero]
  intro h0
  have := le_natDegree_of_ne_zero (p := (X ^ n + C c * X : K[X])) (n := n) (by rw [h1]; exact one_ne_zero)
  omega

theorem transcendental_add_C_mul_pow {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {t : A} (ht : Transcendental K t) (c : K) {n : ℕ} (hn : n ≠ 1) :
    Transcendental K (t + algebraMap K A c * t ^ n) := by
  have e : t + algebraMap K A c * t ^ n = aeval t (X + C c * X ^ n) := by
    rw [map_add, map_mul, aeval_X, aeval_C, map_pow, aeval_X]
  rw [e]
  exact transcendental_aeval_of_natDegree_ne_zero ht _ (natDegree_X_add_C_mul_X_pow_ne_zero c hn)

theorem transcendental_pow_add_C_mul {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {t : A} (ht : Transcendental K t) (c : K) {n : ℕ} (hn0 : n ≠ 0) (hn : n ≠ 1) :
    Transcendental K (t ^ n + algebraMap K A c * t) := by
  have e : t ^ n + algebraMap K A c * t = aeval t (X ^ n + C c * X) := by
    rw [map_add, map_mul, map_pow, aeval_X, aeval_C]
  rw [e]
  exact transcendental_aeval_of_natDegree_ne_zero ht _ (natDegree_X_pow_add_C_mul_X_ne_zero c hn0 hn)

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section
open Polynomial

namespace GaussPencil
namespace Mu

theorem natDegree_C_mul_X_pow_add_X {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 1 < n) :
    (C c * X ^ n + X : K[X]).natDegree = n := by
  have h1 : (C c * X ^ n : K[X]).natDegree = n := natDegree_C_mul_X_pow n c hc
  rw [natDegree_add_eq_left_of_natDegree_lt, h1]
  rw [h1, natDegree_X]; exact hn

theorem natDegree_X_add_C_mul_X_pow {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 1 < n) :
    (X + C c * X ^ n : K[X]).natDegree = n := by
  rw [add_comm]; exact natDegree_C_mul_X_pow_add_X hc hn

theorem natDegree_X_pow_add_C_mul_X {K : Type*} [Field K] (c : K) {n : ℕ} (hn : 1 < n) :
    (X ^ n + C c * X : K[X]).natDegree = n := by
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  exact lt_of_le_of_lt ((natDegree_C_mul_le c X).trans natDegree_X_le) hn

end GaussPencil.Mu
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_injective qExpand_one_apply qExpand_congr jq ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar isFrickeAutFull_frickeInvolutionFull jq_mem_full coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModC_mem_full coeffMap_qExpand frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero adjoin_jBar_jNBar_eq_top qExpand_jqModC_eq_pow_unconditional PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun finrank_adjoin_aeval_jqModC PlaceSpecialization.gPencil PlaceSpecialization.KPencil PlaceSpecialization.gPencilGen PlaceSpecialization.coe_gPencilGen PlaceSpecialization.algebraMap_gPencilGen PlaceSpecialization.algebraMap_KPencil_apply PlaceSpecialization.mem_adjoin_gPencilGen PlaceSpecialization.jTilde PlaceSpecialization.transcendental_jTilde PlaceSpecialization.resGen₁ PlaceSpecialization.resGen₂ PlaceSpecialization.resGen₁_eq_aeval PlaceSpecialization.resGen₂_eq_aeval PlaceSpecialization.resField₁ PlaceSpecialization.resField₂ PlaceSpecialization.fricVal PlaceSpecialization.fricVal_apply"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun mk finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun gPencil KPencil gPencilGen coe_gPencilGen algebraMap_gPencilGen algebraMap_KPencil_apply mem_adjoin_gPencilGen jTilde transcendental_jTilde resGen₁ resGen₂ resGen₁_eq_aeval resGen₂_eq_aeval resField₁ resField₂ fricVal fricVal_apply"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₂ residue₁_apply residue₂_apply mem_integers₂_iff residue₂_eq R₂ residue₁_coeffMap redBar ι_coe ι mk R₁ redBar_residue gaussBase mem_gaussBase_iff algebraMap_mem_gaussBase_iff HasGaussTransport algGaussBase isScalarTower_gaussBase algebraMap_gaussBase_apply toIntegers₁ coe_toIntegers₁ gaussOrder gen_mem_gaussOrder ResOne ResTwo ResOne.val ResTwo.val ResOne.mk ResTwo.mk resBase₁ isLocalHom_resBase₁ isScalarTower_resOne resBase₁_algebraMap gaussOrderToIntegers₁ coe_gaussOrderToIntegers₁ rho₁ rho₁_apply isLocalHom_constToGaussBase algResidueConst algebraMap_residueConst algebraMap_mem_integers₂_of_mem_gaussBase toIntegers₂ coe_toIntegers₂ resBase₂ isLocalHom_resBase₂ isScalarTower_resTwo resBase₂_algebraMap gaussOrderToIntegers₂ coe_gaussOrderToIntegers₂ rho₂ rho₂_apply sum_filter_value_eq_sum_roots_add integers_eq_or_eq_of_forall_mem_iff_pencil"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~adjoin_jqModC_eq_top"

section RFacts

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

theorem coeffMap_subtype_jqModC :
    coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq := by
  rw [coeffMap_jqModC, coeffEmb, ← jqModC_rat, coeffMap_jqModC]

theorem coeffMap_subtype_qExpand_jqModC :
    coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := by
  rw [coeffMap_qExpand, coeffMap_jqModC, coeffEmb, coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jFun_mem_integers₁ : jFun (q := q) ∈ R.R₁.integers ∧
    ∃ h : jFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = jqModC (ResidueField A) := by
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_jqModC]; exact (jFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (jqModC A) hy
  have hj : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext coeffMap_subtype_jqModC
  obtain ⟨h', e'⟩ : ∃ h' : jFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (jqModC A) := by
    rw [← hj]; exact ⟨h, e⟩
  exact ⟨h', h', e'.trans (coeffMap_jqModC _)⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_integers₁ : jqFun (q := q) ∈ R.R₁.integers ∧
    ∃ h : jqFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
  have hy : coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_qExpand_jqModC]; exact (jqFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (qExpand A (1 * q) (jqModC A)) hy
  have hj : (⟨coeffMap A.subtype (qExpand A (1 * q) (jqModC A)), hy⟩ : modularFunctionFieldBar (1 * q))
      = jqFun (q := q) :=
    Subtype.ext coeffMap_subtype_qExpand_jqModC
  obtain ⟨h', e'⟩ : ∃ h' : jqFun (q := q) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (qExpand A (1 * q) (jqModC A)) := by
    rw [← hj]; exact ⟨h, e⟩
  exact ⟨h', h', e'.trans (by rw [coeffMap_qExpand, coeffMap_jqModC])⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_integers₂ : jqFun (q := q) ∈ R.R₂.integers := by
  rw [R.mem_integers₂_iff]
  have e : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
    (frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)).trans
      (Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
        congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq)))
  rw [e]; exact R.jFun_mem_integers₁.1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_integers₂"
include R in
theorem charP_residueField : CharP (ResidueField A) q := RingHom.charP R.redBar R.redBar.injective q

include R in

theorem qExpand_one_mul_jqModC :
    qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) = jqModC (ResidueField A) ^ q := by
  haveI := charP_residueField R
  rw [qExpand_congr (one_mul q)]
  exact qExpand_jqModC_eq_pow_unconditional (ResidueField A)

theorem coe_residue₂_jqFun (h : jqFun (q := q) ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
  rw [R.residue₂_eq]
  obtain ⟨h₁, e₁⟩ := R.jFun_mem_integers₁.2
  have hw : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
    (frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)).trans
      (Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
        congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq)))
  obtain ⟨h', e'⟩ : ∃ h' : frickeInvolutionBar (1 * q) (jqFun (q := q)) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = jqModC (ResidueField A) := by
    rw [hw]; exact ⟨h₁, e₁⟩
  exact e'

theorem frickeInvolutionBar_jFun' :
    frickeInvolutionBar (1 * q) (jFun (q := q)) = jqFun (q := q) := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q)
    (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) 1 (1 * q) (one_mul _)
  have e : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩
        : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext (show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq from
      congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [e] at h
  exact h

theorem coe_residue₂_jFun (h : jFun (q := q) ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) ^ q := by
  rw [R.residue₂_eq]
  obtain ⟨h₁, e₁⟩ := R.jqFun_mem_integers₁.2
  obtain ⟨h', e'⟩ : ∃ h' : frickeInvolutionBar (1 * q) (jFun (q := q)) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
    rw [frickeInvolutionBar_jFun']; exact ⟨h₁, e₁⟩
  rw [e', qExpand_one_mul_jqModC R]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jFun_mem_integers₂ : jFun (q := q) ∈ R.R₂.integers := by
  rw [R.mem_integers₂_iff, frickeInvolutionBar_jFun']; exact R.jqFun_mem_integers₁.1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jFun_mem_integers₂"
end RFacts
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"
section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
  {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
  [Algebra K₁ (modularFunctionFieldBar (1 * q))]
  [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]

variable (R : LevelOneProlongationPair P)

variable [R.HasGaussTransport K₁]

end Core
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section OnePlus

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

attribute [local instance] algGaussBase isScalarTower_gaussBase isLocalHom_resBase₁ isLocalHom_resBase₂
  isScalarTower_resOne isScalarTower_resTwo

theorem coeffMap_subtype_jqModC' :
    coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq := by
  rw [coeffMap_jqModC, coeffEmb, ← jqModC_rat, coeffMap_jqModC]

theorem coeffMap_subtype_qExpand_jqModC' :
    coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := by
  rw [coeffMap_qExpand, coeffMap_jqModC, coeffEmb, coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_jFun_mem_integers₁ : ∃ h : jFun (q := q) ∈ R.R₁.integers,
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_jqModC']; exact (jFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (jqModC A) hy
  have hj : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext coeffMap_subtype_jqModC'
  have key : ∀ (z : modularFunctionFieldBar (1 * q)) (hz : z ∈ R.R₁.integers), z = jFun (q := q) →
      ((R.R₁.residue ⟨z, hz⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (jqModC A) →
      ∃ h : jFun (q := q) ∈ R.R₁.integers,
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) := by
    rintro z hz rfl e'
    exact ⟨hz, e'.trans (coeffMap_jqModC _)⟩
  exact key _ h hj e

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_jFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_jqFun_mem_integers₁ : ∃ h : jqFun (q := q) ∈ R.R₁.integers,
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
  have hy : coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [coeffMap_subtype_qExpand_jqModC']; exact (jqFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (qExpand A (1 * q) (jqModC A)) hy
  have hj : (⟨coeffMap A.subtype (qExpand A (1 * q) (jqModC A)), hy⟩ : modularFunctionFieldBar (1 * q))
      = jqFun (q := q) :=
    Subtype.ext coeffMap_subtype_qExpand_jqModC'
  have key : ∀ (z : modularFunctionFieldBar (1 * q)) (hz : z ∈ R.R₁.integers), z = jqFun (q := q) →
      ((R.R₁.residue ⟨z, hz⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (qExpand A (1 * q) (jqModC A)) →
      ∃ h : jqFun (q := q) ∈ R.R₁.integers,
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
    rintro z hz rfl e'
    refine ⟨hz, e'.trans ?_⟩
    rw [coeffMap_qExpand, coeffMap_jqModC]
  exact key _ h hj e

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_jqFun_mem_integers₁"

theorem valuation_aeval_jFun_eq_one (Q : Polynomial A) (hQ : ∃ i, Q.coeff i ∉ maximalIdeal A) :
    R.R₁.integers.valuation
      (Polynomial.aeval (jFun (q := q)) (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 := by
  obtain ⟨h, e⟩ := R.exists_jFun_mem_integers₁
  refine GaussPencil.valuation_aeval_map_eq_one_of_transcendental A R.R₁.integers
    (fun a => (R.R₁.algebraMap_mem_iff a).mpr a.2) R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap h ?_ Q hQ
  intro halg
  apply ModularCurve.transcendental_jqModC (ResidueField A)
  rw [← e]
  exact halg.algHom (IntermediateField.val _)

theorem valuation_aeval_jqFun_eq_one (Q : Polynomial A) (hQ : ∃ i, Q.coeff i ∉ maximalIdeal A) :
    R.R₁.integers.valuation
      (Polynomial.aeval (jqFun (q := q)) (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 := by
  obtain ⟨h, e⟩ := R.exists_jqFun_mem_integers₁
  refine GaussPencil.valuation_aeval_map_eq_one_of_transcendental A R.R₁.integers
    (fun a => (R.R₁.algebraMap_mem_iff a).mpr a.2) R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap h ?_ Q hQ
  intro halg
  apply ModularCurve.transcendental_jqModC (ResidueField A)
  have h2 : IsAlgebraic (ResidueField A) (qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A))) := by
    rw [← e]
    exact halg.algHom (IntermediateField.val _)
  rw [← qExpandAlgHomC_apply] at h2
  exact (isAlgebraic_algHom_iff (qExpandAlgHomC (ResidueField A) (1 * q))
    (qExpand_injective (1 * q))).mp h2

theorem frickeInvolutionBar_jqFun' :
    frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
  frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)
    |>.trans (Subtype.ext (congrArg (fun x => coeffEmb (AlgebraicClosure ℚ) x) (qExpand_one_apply jq)))

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_jqFun :
    ((R.R₂.residue ⟨jqFun (q := q), R.jqFun_mem_integers₂⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
        LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
  rw [R.residue₂_eq]
  obtain ⟨h, e⟩ := R.jFun_mem_integers₁.2
  have hsub : (⟨frickeInvolutionBar (1 * q) (jqFun (q := q)),
      (R.mem_integers₂_iff _).mp R.jqFun_mem_integers₂⟩ : R.R₁.integers) = ⟨jFun (q := q), h⟩ :=
    Subtype.ext frickeInvolutionBar_jqFun'
  rw [hsub]
  exact e

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₂_jqFun"
end OnePlus
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section RFacts2

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

theorem redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext R.redBar_residue

include R in
theorem red_eq_zero_of_mem (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  rw [← R.redBar_residue, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ι_algebraMap (a : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) a)
      = algebraMap k (modularFunctionFieldC k 1) (R.redBar a) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) a)
    = algebraMap k (LaurentSeries k) (R.redBar a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ι_algebraMap"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ι_eq_ratFuncEquivCharLOneC_X (x : modularFunctionFieldFullC (ResidueField A) 1)
    (hx : (x : LaurentSeries (ResidueField A)) = jqModC (ResidueField A)) :
    R.ι x = ratFuncEquivCharLOneC k RatFunc.X := by
  apply Subtype.ext
  rw [R.ι_coe, hx, coeffMap_jqModC, GaussPencil.B6.coe_ratFuncEquivCharLOneC_X]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ι_eq_ratFuncEquivCharLOneC_X"
end RFacts2
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section GPencilDef

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

private noncomputable def _root_.ModularCurve.PlaceSpecialization.gPencil (μ : A) : ↥(modularFunctionFieldBar (1 * q)) :=
  jFun (q := q) + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.gPencil" "ModularCurve.PlaceSpecialization.gPencil"
end GPencilDef
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil"

section PencilLine

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

private noncomputable abbrev _root_.ModularCurve.PlaceSpecialization.KPencil (μ : A) :
    IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) {PlaceSpecialization.gPencil (q := q) μ}

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.KPencil" "ModularCurve.PlaceSpecialization.KPencil"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.gPencilGen (μ : A) :
    ↥(PlaceSpecialization.KPencil (q := q) μ) :=
  ⟨PlaceSpecialization.gPencil (q := q) μ, IntermediateField.mem_adjoin_simple_self _ _⟩

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.gPencilGen" "ModularCurve.PlaceSpecialization.gPencilGen"
@[scoped simp] private theorem _root_.ModularCurve.PlaceSpecialization.coe_gPencilGen (μ : A) :
    ((PlaceSpecialization.gPencilGen (q := q) μ : PlaceSpecialization.KPencil (q := q) μ) :
      modularFunctionFieldBar (1 * q)) = PlaceSpecialization.gPencil (q := q) μ := rfl

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.coe_gPencilGen" "ModularCurve.PlaceSpecialization.coe_gPencilGen"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"
private theorem _root_.ModularCurve.PlaceSpecialization.algebraMap_gPencilGen (μ : A) :
    algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
      (PlaceSpecialization.gPencilGen (q := q) μ) = PlaceSpecialization.gPencil (q := q) μ := rfl

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.algebraMap_gPencilGen" "ModularCurve.PlaceSpecialization.algebraMap_gPencilGen"
private theorem _root_.ModularCurve.PlaceSpecialization.algebraMap_KPencil_apply (μ : A)
    (x : PlaceSpecialization.KPencil (q := q) μ) :
    algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q)) x = (x : _) := rfl

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.algebraMap_KPencil_apply" "ModularCurve.PlaceSpecialization.algebraMap_KPencil_apply"

theorem finiteDimensional_KPencil (μ : A) (hμ : (μ : AlgebraicClosure ℚ) ≠ 0) :
    FiniteDimensional (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q)) :=
  (ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun (q := q) (μ : AlgebraicClosure ℚ) hμ).1

theorem finrank_KPencil (μ : A) (hμ : (μ : AlgebraicClosure ℚ) ≠ 0) :
    Module.finrank (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q)) = 2 * q :=
  (ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun (q := q) (μ : AlgebraicClosure ℚ) hμ).2

end PencilLine
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"

section InstanceMu

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

private theorem _root_.ModularCurve.PlaceSpecialization.mem_adjoin_gPencilGen (μ : A)
    (x : PlaceSpecialization.KPencil (q := q) μ) :
    x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {PlaceSpecialization.gPencilGen (q := q) μ} :=
  GaussPencil.mem_adjoin_simple_gen _ x

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.mem_adjoin_gPencilGen" "ModularCurve.PlaceSpecialization.mem_adjoin_gPencilGen"

theorem frickeInvolutionBar_gPencil (μ : A) :
    frickeInvolutionBar (1 * q) (PlaceSpecialization.gPencil (q := q) μ)
      = jqFun (q := q) + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ)
          * jFun (q := q) := by
  rw [PlaceSpecialization.gPencil, map_add, map_mul, frickeInvolutionBar_jFun', AlgEquiv.commutes,
    frickeInvolutionBar_jqFun']

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.gPencil_mem_integers₁ (μ : A) : PlaceSpecialization.gPencil (q := q) μ ∈ R.R₁.integers :=
  add_mem R.jFun_mem_integers₁.1
    (mul_mem ((R.R₁.algebraMap_mem_iff (μ : AlgebraicClosure ℚ)).mpr μ.2) R.jqFun_mem_integers₁.1)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "gPencil_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.frickeInvolutionBar_gPencil_mem_integers₁ (μ : A) :
    frickeInvolutionBar (1 * q) (PlaceSpecialization.gPencil (q := q) μ) ∈ R.R₁.integers := by
  rw [frickeInvolutionBar_gPencil]
  exact add_mem R.jqFun_mem_integers₁.1
    (mul_mem ((R.R₁.algebraMap_mem_iff (μ : AlgebraicClosure ℚ)).mpr μ.2) R.jFun_mem_integers₁.1)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "frickeInvolutionBar_gPencil_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.gPencil_mem_integers₂ (μ : A) : PlaceSpecialization.gPencil (q := q) μ ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (R.frickeInvolutionBar_gPencil_mem_integers₁ μ)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "gPencil_mem_integers₂"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.jTilde (k₀ : Type*) [Field k₀] :
    ↥(modularFunctionFieldFullC k₀ 1) :=
  ⟨jqModC k₀, jqModC_mem_full k₀ 1⟩

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.jTilde" "ModularCurve.PlaceSpecialization.jTilde"
private theorem _root_.ModularCurve.PlaceSpecialization.transcendental_jTilde (k₀ : Type*) [Field k₀] :
    Transcendental k₀ (PlaceSpecialization.jTilde k₀) :=
  fun h => ModularCurve.transcendental_jqModC k₀ (h.algHom (IntermediateField.val _))

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.transcendental_jTilde" "ModularCurve.PlaceSpecialization.transcendental_jTilde"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_eq_jTilde (h : jFun (q := q) ∈ R.R₁.integers) :
    R.R₁.residue ⟨jFun (q := q), h⟩ = PlaceSpecialization.jTilde (ResidueField A) := by
  obtain ⟨h', e⟩ := R.exists_jFun_mem_integers₁
  exact Subtype.ext e

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_jFun_eq_jTilde"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jqFun_eq_jTilde_pow (h : jqFun (q := q) ∈ R.R₁.integers) :
    R.R₁.residue ⟨jqFun (q := q), h⟩ = PlaceSpecialization.jTilde (ResidueField A) ^ q := by
  obtain ⟨h', e⟩ := R.exists_jqFun_mem_integers₁
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact e.trans (qExpand_one_mul_jqModC R)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_jqFun_eq_jTilde_pow"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_algebraMap_eq (μ : A)
    (h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ = algebraMap (ResidueField A) _ (IsLocalRing.residue A μ) :=
  R.R₁.residue_algebraMap μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_algebraMap_eq"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_gPencil_eq (μ : A) (h : PlaceSpecialization.gPencil (q := q) μ ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩
      = PlaceSpecialization.jTilde (ResidueField A)
        + algebraMap (ResidueField A) _ (IsLocalRing.residue A μ) * PlaceSpecialization.jTilde (ResidueField A) ^ q := by
  have hj := R.jFun_mem_integers₁.1
  have hjq := R.jqFun_mem_integers₁.1
  have hμ := (R.R₁.algebraMap_mem_iff (μ : AlgebraicClosure ℚ)).mpr μ.2
  have e : (⟨_, h⟩ : R.R₁.integers)
      = ⟨jFun (q := q), hj⟩ + ⟨_, hμ⟩ * ⟨jqFun (q := q), hjq⟩ := rfl
  rw [e, map_add, map_mul, R.residue_jFun_eq_jTilde, R.residue_jqFun_eq_jTilde_pow, R.residue_algebraMap_eq]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_gPencil_eq"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_frickeInvolutionBar_gPencil_eq (μ : A)
    (h : frickeInvolutionBar (1 * q) (PlaceSpecialization.gPencil (q := q) μ) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩
      = PlaceSpecialization.jTilde (ResidueField A) ^ q
        + algebraMap (ResidueField A) _ (IsLocalRing.residue A μ) * PlaceSpecialization.jTilde (ResidueField A) := by
  have hj := R.jFun_mem_integers₁.1
  have hjq := R.jqFun_mem_integers₁.1
  have hμ := (R.R₁.algebraMap_mem_iff (μ : AlgebraicClosure ℚ)).mpr μ.2
  have h' : jqFun (q := q) + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ)
      * jFun (q := q) ∈ R.R₁.integers := by rw [← frickeInvolutionBar_gPencil]; exact h
  have e0 : (⟨_, h⟩ : R.R₁.integers) = ⟨_, h'⟩ := Subtype.ext (frickeInvolutionBar_gPencil μ)
  have e : (⟨_, h'⟩ : R.R₁.integers)
      = ⟨jqFun (q := q), hjq⟩ + ⟨_, hμ⟩ * ⟨jFun (q := q), hj⟩ := rfl
  rw [e0, e, map_add, map_mul, R.residue_jFun_eq_jTilde, R.residue_jqFun_eq_jTilde_pow, R.residue_algebraMap_eq]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_frickeInvolutionBar_gPencil_eq"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.transcendental_residue_gPencil (μ : A) (h : PlaceSpecialization.gPencil (q := q) μ ∈ R.R₁.integers) :
    Transcendental (ResidueField A) (R.R₁.residue ⟨_, h⟩) := by
  rw [R.residue_gPencil_eq μ h]
  exact GaussPencil.transcendental_add_C_mul_pow (PlaceSpecialization.transcendental_jTilde _) _
    (Fact.out : q.Prime).one_lt.ne'

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "transcendental_residue_gPencil"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.transcendental_residue_frickeInvolutionBar_gPencil (μ : A)
    (h : frickeInvolutionBar (1 * q) (PlaceSpecialization.gPencil (q := q) μ) ∈ R.R₁.integers) :
    Transcendental (ResidueField A) (R.R₁.residue ⟨_, h⟩) := by
  rw [R.residue_frickeInvolutionBar_gPencil_eq μ h]
  exact GaussPencil.transcendental_pow_add_C_mul (PlaceSpecialization.transcendental_jTilde _) _
    (Fact.out : q.Prime).ne_zero (Fact.out : q.Prime).one_lt.ne'

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "transcendental_residue_frickeInvolutionBar_gPencil"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.valuation_aeval_gPencil_eq_one (μ : A) (Q : Polynomial A) (hQ : ∃ i, Q.coeff i ∉ maximalIdeal A) :
    R.R₁.integers.valuation
      (Polynomial.aeval (PlaceSpecialization.gPencil (q := q) μ) (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 :=
  GaussPencil.valuation_aeval_map_eq_one_of_transcendental A R.R₁.integers
    (fun a => (R.R₁.algebraMap_mem_iff a).mpr a.2) R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap
    (R.gPencil_mem_integers₁ μ) (R.transcendental_residue_gPencil μ _) Q hQ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "valuation_aeval_gPencil_eq_one"
include R in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.transcendental_gPencil (μ : A) : Transcendental (AlgebraicClosure ℚ) (PlaceSpecialization.gPencil (q := q) μ) := by
  rintro ⟨p, hp0, hp⟩
  obtain ⟨c, Q, hc, hQ, rfl⟩ := GaussPencil.exists_C_mul_primitive A hp0
  have h1 := R.valuation_aeval_gPencil_eq_one μ Q hQ
  rw [map_mul, Polynomial.aeval_C, mul_eq_zero] at hp
  rcases hp with h | h
  · exact hc ((_root_.map_eq_zero _).mp h)
  · rw [h, map_zero] at h1
    exact zero_ne_one h1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "transcendental_gPencil"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.valuation_aeval_frickeInvolutionBar_gPencil_eq_one (μ : A) (Q : Polynomial A)
    (hQ : ∃ i, Q.coeff i ∉ maximalIdeal A) :
    R.R₁.integers.valuation
      (Polynomial.aeval (frickeInvolutionBar (1 * q) (PlaceSpecialization.gPencil (q := q) μ))
        (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 :=
  GaussPencil.valuation_aeval_map_eq_one_of_transcendental A R.R₁.integers
    (fun a => (R.R₁.algebraMap_mem_iff a).mpr a.2) R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap
    (R.frickeInvolutionBar_gPencil_mem_integers₁ μ) (R.transcendental_residue_frickeInvolutionBar_gPencil μ _) Q hQ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "valuation_aeval_frickeInvolutionBar_gPencil_eq_one"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integers₁_iff_frickeInvolutionBar_mem_pencil (μ : A) (x : PlaceSpecialization.KPencil (q := q) μ) :
    (x : modularFunctionFieldBar (1 * q)) ∈ R.R₁.integers
      ↔ frickeInvolutionBar (1 * q) (x : modularFunctionFieldBar (1 * q)) ∈ R.R₁.integers := by
  have hφ : ∀ Q : Polynomial A, (∃ i, Q.coeff i ∉ maximalIdeal A) →
      R.R₁.integers.valuation (Polynomial.aeval
        ((IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ)) (PlaceSpecialization.gPencilGen (q := q) μ))
        (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 :=
    fun Q hQ => R.valuation_aeval_gPencil_eq_one μ Q hQ
  have hψ : ∀ Q : Polynomial A, (∃ i, Q.coeff i ∉ maximalIdeal A) →
      R.R₁.integers.valuation (Polynomial.aeval
        (((frickeInvolutionBar (1 * q)).toAlgHom.comp
            (IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ))) (PlaceSpecialization.gPencilGen (q := q) μ))
        (Q.map (algebraMap A (AlgebraicClosure ℚ)))) = 1 :=
    fun Q hQ => R.valuation_aeval_frickeInvolutionBar_gPencil_eq_one μ Q hQ
  exact GaussPencil.algHom_mem_iff_of_primitive_isUnit A R.R₁.integers (PlaceSpecialization.gPencilGen (q := q) μ)
    (IntermediateField.val _) ((frickeInvolutionBar (1 * q)).toAlgHom.comp (IntermediateField.val _)) hφ hψ
    (PlaceSpecialization.mem_adjoin_gPencilGen μ x)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "mem_integers₁_iff_frickeInvolutionBar_mem_pencil"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_integers₂_of_mem_integers₁_pencil (μ : A) (x : PlaceSpecialization.KPencil (q := q) μ)
    (hx : algebraMap _ (modularFunctionFieldBar (1 * q)) x ∈ R.R₁.integers) :
    algebraMap _ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers := by
  rw [PlaceSpecialization.algebraMap_KPencil_apply] at hx ⊢
  rw [R.mem_integers₂_iff]
  exact (R.mem_integers₁_iff_frickeInvolutionBar_mem_pencil μ x).mp hx

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_mem_integers₂_of_mem_integers₁_pencil"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_integers₁_of_mem_integers₂_pencil (μ : A) (x : PlaceSpecialization.KPencil (q := q) μ)
    (hx : algebraMap _ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers) :
    algebraMap _ (modularFunctionFieldBar (1 * q)) x ∈ R.R₁.integers := by
  rw [PlaceSpecialization.algebraMap_KPencil_apply] at hx ⊢
  rw [R.mem_integers₂_iff] at hx
  exact (R.mem_integers₁_iff_frickeInvolutionBar_mem_pencil μ x).mpr hx

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_mem_integers₁_of_mem_integers₂_pencil"

scoped instance hasGaussTransport_pencil (μ : A) : R.HasGaussTransport (PlaceSpecialization.KPencil (q := q) μ) where
  mem₂_of_mem₁ x hx := R.algebraMap_mem_integers₂_of_mem_integers₁_pencil μ x hx
  mem₁_of_mem₂ x hx := R.algebraMap_mem_integers₁_of_mem_integers₂_pencil μ x hx

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.gPencilGen_mem_gaussBase (μ : A) :
    PlaceSpecialization.gPencilGen (q := q) μ ∈ R.gaussBase (PlaceSpecialization.KPencil (q := q) μ) := by
  rw [mem_gaussBase_iff, PlaceSpecialization.algebraMap_gPencilGen]
  exact R.gPencil_mem_integers₁ μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "gPencilGen_mem_gaussBase"
end InstanceMu
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"

section PencilPlumbing

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

attribute [local instance] algGaussBase isScalarTower_gaussBase isLocalHom_resBase₁ isLocalHom_resBase₂
  isScalarTower_resOne isScalarTower_resTwo isLocalHom_constToGaussBase algResidueConst

include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isUnit_of_red_ne_zero (μ : A) (hμ : red μ ≠ 0) : IsUnit μ := by
  by_contra h
  apply hμ
  rw [← R.redBar_residue μ, (IsLocalRing.residue_eq_zero_iff μ).mpr ((IsLocalRing.mem_maximalIdeal μ).mpr (mem_nonunits_iff.mpr h)),
    map_zero]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "isUnit_of_red_ne_zero"
theorem coe_ne_zero_of_red_ne_zero (μ : A) (hμ : red μ ≠ 0) : (μ : AlgebraicClosure ℚ) ≠ 0 := by
  intro h
  apply hμ
  rw [show μ = 0 from Subtype.ext h, map_zero]

include R in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_coe_mul_eq_one (μ : A) (hμ : red μ ≠ 0) : ∃ ν : A, (ν : AlgebraicClosure ℚ) * μ = 1 := by
  obtain ⟨u, hu⟩ := R.isUnit_of_red_ne_zero μ hμ
  refine ⟨((u⁻¹ : Aˣ) : A), ?_⟩
  have h1 : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := Units.inv_mul u
  rw [← hu]
  exact_mod_cast congrArg (fun a : A => (a : AlgebraicClosure ℚ)) h1

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_coe_mul_eq_one"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_order_pencil (μ : A) (hμ : red μ ≠ 0) (f : modularFunctionFieldBar (1 * q)) :
    jqFun (q := q) ∈ R.gaussOrder (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) f := by
  obtain ⟨ν, hν⟩ := R.exists_coe_mul_eq_one μ hμ
  let νV : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ) :=
    ⟨algebraMap (AlgebraicClosure ℚ) (PlaceSpecialization.KPencil (q := q) μ) ν, (R.algebraMap_mem_gaussBase_iff _).mpr ν.2⟩
  let gV : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ) :=
    ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩
  have hνF : algebraMap (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) (modularFunctionFieldBar (1 * q)) νV
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (ν : AlgebraicClosure ℚ) := by
    rw [algebraMap_gaussBase_apply]
    exact (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (PlaceSpecialization.KPencil (q := q) μ)
      (modularFunctionFieldBar (1 * q)) (ν : AlgebraicClosure ℚ)).symm
  have hgF : algebraMap (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) (modularFunctionFieldBar (1 * q)) gV
      = PlaceSpecialization.gPencil (q := q) μ := by
    rw [algebraMap_gaussBase_apply]; rfl
  have e : jqFun (q := q)
      = algebraMap (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) (modularFunctionFieldBar (1 * q)) νV
        * (algebraMap (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) (modularFunctionFieldBar (1 * q)) gV
            - jFun (q := q)) := by
    rw [hνF, hgF, PlaceSpecialization.gPencil, add_sub_cancel_left, ← mul_assoc, ← map_mul, hν, map_one, one_mul (jqFun (q := q))]
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ _) (R.gen_mem_gaussOrder _ _))

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_order_pencil"
include R in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.jqFun_mem_adjoin_pencil (μ : A) (hμ : red μ ≠ 0) :
    jqFun (q := q) ∈ IntermediateField.adjoin (PlaceSpecialization.KPencil (q := q) μ) {jFun (q := q)} := by
  obtain ⟨ν, hν⟩ := R.exists_coe_mul_eq_one μ hμ
  have e : jqFun (q := q)
      = algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
          (algebraMap (AlgebraicClosure ℚ) (PlaceSpecialization.KPencil (q := q) μ) ν)
        * (algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
            (PlaceSpecialization.gPencilGen (q := q) μ) - jFun (q := q)) := by
    rw [← IsScalarTower.algebraMap_apply, PlaceSpecialization.algebraMap_gPencilGen, PlaceSpecialization.gPencil,
      add_sub_cancel_left, ← mul_assoc, ← map_mul, hν, map_one, one_mul (jqFun (q := q))]
  rw [e]
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (sub_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _))

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "jqFun_mem_adjoin_pencil"

include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.adjoin_pencil_jFun_eq_top (μ : A) (hμ : red μ ≠ 0) :
    IntermediateField.adjoin (PlaceSpecialization.KPencil (q := q) μ) {jFun (q := q)}
      = (⊤ : IntermediateField (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))) := by
  rw [eq_top_iff]
  intro x _
  have h353 := ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) (1 * q)
  have hx : x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩,
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩} :
        Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)))) := by
    rw [h353]
    exact IntermediateField.mem_top
  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩,
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩} :
        Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q))))
      ≤ (IntermediateField.adjoin (PlaceSpecialization.KPencil (q := q) μ) {jFun (q := q)}).restrictScalars
          (AlgebraicClosure ℚ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y hy
    rcases hy with rfl | hy
    · rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
      exact IntermediateField.mem_adjoin_simple_self _ (jFun (q := q))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
      exact R.jqFun_mem_adjoin_pencil μ hμ
  exact hle hx

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "adjoin_pencil_jFun_eq_top"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.span_order_pencil_eq_top (μ : A) (hμ : red μ ≠ 0) (f : modularFunctionFieldBar (1 * q)) :
    Submodule.span (PlaceSpecialization.KPencil (q := q) μ)
        (R.gaussOrder (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) f : Set (modularFunctionFieldBar (1 * q))) = ⊤ := by
  have hμ0 : (μ : AlgebraicClosure ℚ) ≠ 0 := fun h => hμ (by rw [show μ = 0 from Subtype.ext h, map_zero])
  haveI := finiteDimensional_KPencil (q := q) μ hμ0
  have hint : IsIntegral (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) :=
    IsIntegral.of_finite (R := ↥(PlaceSpecialization.KPencil (q := q) μ)) (jFun (q := q))
  have hA : Algebra.adjoin (PlaceSpecialization.KPencil (q := q) μ) {jFun (q := q)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, R.adjoin_pencil_jFun_eq_top μ hμ,
      IntermediateField.top_toSubalgebra]
  rw [eq_top_iff, ← Algebra.top_toSubmodule, ← hA, Algebra.adjoin_eq_span]
  apply Submodule.span_mono
  exact (Submonoid.closure_le (S := (R.gaussOrder (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) f).toSubsemiring.toSubmonoid)).mpr
    (Set.singleton_subset_iff.mpr (R.gen_mem_gaussOrder (jFun (q := q)) f))

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "span_order_pencil_eq_top"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rho₁_pencil_eq (μ : A) {f : modularFunctionFieldBar (1 * q)} (h₁ : f ∈ R.R₁.integers) :
    ∃ s : R.gaussOrder (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) f,
      ((ResOne.val R (R.rho₁ (PlaceSpecialization.KPencil (q := q) μ) R.jFun_mem_integers₁.1 h₁ s) :
        modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
  refine ⟨⟨jFun (q := q), R.gen_mem_gaussOrder _ _⟩, ?_⟩
  rw [rho₁_apply]
  obtain ⟨h, e⟩ := R.jFun_mem_integers₁.2
  have : R.gaussOrderToIntegers₁ (PlaceSpecialization.KPencil (q := q) μ) R.jFun_mem_integers₁.1 h₁ ⟨jFun (q := q), R.gen_mem_gaussOrder _ _⟩
      = ⟨jFun (q := q), h⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₁ _ _ _)
  rw [this, e]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_rho₁_pencil_eq"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_rho₂_pencil_eq (μ : A) (hμ : red μ ≠ 0) {f : modularFunctionFieldBar (1 * q)} (h₂ : f ∈ R.R₂.integers) :
    ∃ s : R.gaussOrder (PlaceSpecialization.KPencil (q := q) μ) (jFun (q := q)) f,
      ((ResTwo.val R (R.rho₂ (PlaceSpecialization.KPencil (q := q) μ) R.jFun_mem_integers₂ h₂ s) :
        modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
  refine ⟨⟨jqFun (q := q), R.jqFun_mem_order_pencil μ hμ f⟩, ?_⟩
  rw [rho₂_apply]
  have : R.gaussOrderToIntegers₂ (PlaceSpecialization.KPencil (q := q) μ) R.jFun_mem_integers₂ h₂ ⟨jqFun (q := q), R.jqFun_mem_order_pencil μ hμ f⟩
      = ⟨jqFun (q := q), R.jqFun_mem_integers₂⟩ := Subtype.ext (R.coe_gaussOrderToIntegers₂ _ _ _)
  rw [this]
  exact R.residue₂_jqFun

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_rho₂_pencil_eq"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ePencil (μ : A) :
    RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] ↥(PlaceSpecialization.KPencil (q := q) μ) :=
  RatFunc.algEquivOfTranscendental (PlaceSpecialization.gPencil (q := q) μ) (R.transcendental_gPencil μ)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ePencil"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ePencil_X (μ : A) :
    R.ePencil μ RatFunc.X = PlaceSpecialization.gPencilGen (q := q) μ := by
  apply Subtype.ext
  rw [ePencil, RatFunc.algEquivOfTranscendental_X]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ePencil_X"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_ePencil_X (μ : A) :
    algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
      (R.ePencil μ RatFunc.X) = PlaceSpecialization.gPencil (q := q) μ := by
  rw [R.ePencil_X]; rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_ePencil_X"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ePencil_X_mem_gaussBase (μ : A) :
    R.ePencil μ RatFunc.X ∈ R.gaussBase (PlaceSpecialization.KPencil (q := q) μ) := by
  rw [R.ePencil_X]; exact R.gPencilGen_mem_gaussBase μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ePencil_X_mem_gaussBase"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_resBase₁_ePencil_X (μ : A) :
    ((ResOne.val R (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ)
        ⟨R.ePencil μ RatFunc.X, R.ePencil_X_mem_gaussBase μ⟩) :
        modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A)
        + algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A μ) * jqModC (ResidueField A) ^ q := by
  have h1 : R.toIntegers₁ (PlaceSpecialization.KPencil (q := q) μ)
      ⟨R.ePencil μ RatFunc.X, R.ePencil_X_mem_gaussBase μ⟩
      = ⟨PlaceSpecialization.gPencil (q := q) μ, R.gPencil_mem_integers₁ μ⟩ :=
    Subtype.ext (by rw [coe_toIntegers₁]; exact R.algebraMap_ePencil_X μ)
  show ((R.R₁.residue (R.toIntegers₁ (PlaceSpecialization.KPencil (q := q) μ) _) :
    modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = _
  rw [h1, R.residue_gPencil_eq μ]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "coe_resBase₁_ePencil_X"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.transcendental_residue_ePencil_X (μ : A) :
    Transcendental (ResidueField A)
      (IsLocalRing.residue (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))
        ⟨R.ePencil μ RatFunc.X, R.ePencil_X_mem_gaussBase μ⟩) := by
  have hres_alg : ∀ x : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ),
      algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne (IsLocalRing.residue _ x)
        = algebraMap (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) R.ResOne x := fun x =>
    (IsScalarTower.algebraMap_apply (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne x).symm
  let G : ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) →+* LaurentSeries (ResidueField A) :=
    (show R.ResOne →+* LaurentSeries (ResidueField A) from
      (IntermediateField.val (modularFunctionFieldFullC (ResidueField A) 1)).toRingHom).comp
      (algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne)
  have hGconst : ∀ a : ResidueField A,
      G (algebraMap (ResidueField A) (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) a)
        = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) a := by
    intro a
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
    rw [R.algebraMap_residueConst a₀]
    show ((ResOne.val R (algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne
        (IsLocalRing.residue _ _)) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = _
    rw [hres_alg]
    show ((ResOne.val R (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ) _) : modularFunctionFieldFullC (ResidueField A) 1) :
        LaurentSeries (ResidueField A)) = _
    rw [R.resBase₁_algebraMap a₀]
    rfl
  have hGx : G (IsLocalRing.residue (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) ⟨R.ePencil μ RatFunc.X, R.ePencil_X_mem_gaussBase μ⟩)
      = jqModC (ResidueField A)
        + algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A μ) * jqModC (ResidueField A) ^ q := by
    show ((ResOne.val R (algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne
        (IsLocalRing.residue _ _)) : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = _
    rw [hres_alg]
    exact R.coe_resBase₁_ePencil_X μ
  rintro ⟨p, hp0, hp⟩
  apply GaussPencil.transcendental_add_C_mul_pow (ModularCurve.transcendental_jqModC (ResidueField A))
    (IsLocalRing.residue A μ) (Fact.out : q.Prime).one_lt.ne'
  refine ⟨p, hp0, ?_⟩
  have h := congrArg G hp
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hGx] at h
  rw [Polynomial.aeval_def, ← h]
  congr 1
  exact RingHom.ext fun a => (hGconst a).symm

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "transcendental_residue_ePencil_X"

theorem natDegree_rOne {c : k} (hc : c ≠ 0) : (C c * X ^ q + X : k[X]).natDegree = q := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have h1 : (C c * X ^ q : k[X]).natDegree = q := natDegree_C_mul_X_pow q c hc
  rw [natDegree_add_eq_left_of_natDegree_lt, h1]
  rw [h1, natDegree_X]; exact hq

theorem natDegree_rTwo (c : k) : (X ^ q + C c * X : k[X]).natDegree = q := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  exact lt_of_le_of_lt (natDegree_C_mul_le c X |>.trans natDegree_X_le) hq

theorem ratFuncEquivCharLOneC_algebraMap (p : k[X]) :
    ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) p) = aeval (ratFuncEquivCharLOneC k RatFunc.X) p :=
  by rw [aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_ePencil_X (μ : A) :
    R.residue₁ ⟨algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
        (R.ePencil μ RatFunc.X), (R.mem_gaussBase_iff _).mp (R.ePencil_X_mem_gaussBase μ)⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) (C (red μ) * X ^ q + X)) := by
  have hsub : (⟨algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
        (R.ePencil μ RatFunc.X), (R.mem_gaussBase_iff _).mp (R.ePencil_X_mem_gaussBase μ)⟩ : R.R₁.integers)
      = ⟨PlaceSpecialization.gPencil (q := q) μ, R.gPencil_mem_integers₁ μ⟩ :=
    Subtype.ext (R.algebraMap_ePencil_X μ)
  rw [hsub, residue₁_apply, R.residue_gPencil_eq μ, map_add, map_mul, map_pow, R.ι_algebraMap, R.redBar_residue,
    R.ι_eq_ratFuncEquivCharLOneC_X (PlaceSpecialization.jTilde (ResidueField A)) rfl,
    ratFuncEquivCharLOneC_algebraMap]
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]
  ring

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁_ePencil_X"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_ePencil_X (μ : A) :
    R.residue₂ ⟨algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
        (R.ePencil μ RatFunc.X), R.algebraMap_mem_integers₂_of_mem_gaussBase _ (R.ePencil_X_mem_gaussBase μ)⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) (X ^ q + C (red μ) * X)) := by
  have hsub : (⟨algebraMap (PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q))
        (R.ePencil μ RatFunc.X), R.algebraMap_mem_integers₂_of_mem_gaussBase _ (R.ePencil_X_mem_gaussBase μ)⟩ : R.R₂.integers)
      = ⟨PlaceSpecialization.gPencil (q := q) μ, R.gPencil_mem_integers₂ μ⟩ :=
    Subtype.ext (R.algebraMap_ePencil_X μ)
  rw [hsub, residue₂_apply, R.residue₂_eq, R.residue_frickeInvolutionBar_gPencil_eq μ, map_add, map_mul, map_pow,
    R.ι_algebraMap, R.redBar_residue, R.ι_eq_ratFuncEquivCharLOneC_X (PlaceSpecialization.jTilde (ResidueField A)) rfl,
    ratFuncEquivCharLOneC_algebraMap]
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₂_ePencil_X"
end PencilPlumbing
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"

section PencilResidueDegrees

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

attribute [local instance] algGaussBase isScalarTower_gaussBase isLocalHom_resBase₁ isLocalHom_resBase₂
  isScalarTower_resOne isScalarTower_resTwo

include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_ne_zero_of_red_ne_zero (μ : A) (hμ : red μ ≠ 0) : IsLocalRing.residue A μ ≠ 0 :=
  fun h => hμ (by rw [← R.redBar_residue μ, h, map_zero])

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_ne_zero_of_red_ne_zero"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.resGen₁ (q : ℕ) (μ : A) :
    ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  PlaceSpecialization.jTilde (ResidueField A)
    + algebraMap (ResidueField A) _ (IsLocalRing.residue A μ) * PlaceSpecialization.jTilde (ResidueField A) ^ q

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resGen₁" "ModularCurve.PlaceSpecialization.resGen₁"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.resGen₂ (q : ℕ) (μ : A) :
    ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  PlaceSpecialization.jTilde (ResidueField A) ^ q
    + algebraMap (ResidueField A) _ (IsLocalRing.residue A μ) * PlaceSpecialization.jTilde (ResidueField A)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resGen₂" "ModularCurve.PlaceSpecialization.resGen₂"
private theorem _root_.ModularCurve.PlaceSpecialization.resGen₁_eq_aeval (μ : A) :
    PlaceSpecialization.resGen₁ q μ
      = aeval (PlaceSpecialization.jTilde (ResidueField A)) (X + C (IsLocalRing.residue A μ) * X ^ q) := by
  rw [PlaceSpecialization.resGen₁, map_add, map_mul, aeval_C, map_pow, aeval_X]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resGen₁_eq_aeval" "ModularCurve.PlaceSpecialization.resGen₁_eq_aeval"
private theorem _root_.ModularCurve.PlaceSpecialization.resGen₂_eq_aeval (μ : A) :
    PlaceSpecialization.resGen₂ q μ
      = aeval (PlaceSpecialization.jTilde (ResidueField A)) (X ^ q + C (IsLocalRing.residue A μ) * X) := by
  rw [PlaceSpecialization.resGen₂, map_add, map_mul, map_pow, aeval_X, aeval_C]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resGen₂_eq_aeval" "ModularCurve.PlaceSpecialization.resGen₂_eq_aeval"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.resField₁ (q : ℕ) (μ : A) :
    IntermediateField (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₁ q μ} : Set ↥(modularFunctionFieldFullC (ResidueField A) 1))

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resField₁" "ModularCurve.PlaceSpecialization.resField₁"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.resField₂ (q : ℕ) (μ : A) :
    IntermediateField (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₂ q μ} : Set ↥(modularFunctionFieldFullC (ResidueField A) 1))

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.resField₂" "ModularCurve.PlaceSpecialization.resField₂"
include R in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_resField₁ (μ : A) (hμ : red μ ≠ 0) :
    Module.finrank ↥(PlaceSpecialization.resField₁ q μ) ↥(modularFunctionFieldFullC (ResidueField A) 1) = q := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hd := GaussPencil.Mu.natDegree_X_add_C_mul_X_pow (R.residue_ne_zero_of_red_ne_zero μ hμ) hq
  show Module.finrank ↥(IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₁ q μ} :
    Set ↥(modularFunctionFieldFullC (ResidueField A) 1))) ↥(modularFunctionFieldFullC (ResidueField A) 1) = q
  rw [PlaceSpecialization.resGen₁_eq_aeval]
  exact (ModularCurve.finrank_adjoin_aeval_jqModC (ResidueField A) _ (by rw [hd]; exact lt_trans zero_lt_one hq)).trans hd

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "finrank_resField₁"

theorem finrank_resField₂ (μ : A) :
    Module.finrank ↥(PlaceSpecialization.resField₂ q μ) ↥(modularFunctionFieldFullC (ResidueField A) 1) = q := by
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hd := GaussPencil.Mu.natDegree_X_pow_add_C_mul_X (IsLocalRing.residue A μ) hq
  show Module.finrank ↥(IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₂ q μ} :
    Set ↥(modularFunctionFieldFullC (ResidueField A) 1))) ↥(modularFunctionFieldFullC (ResidueField A) 1) = q
  rw [PlaceSpecialization.resGen₂_eq_aeval]
  exact (ModularCurve.finrank_adjoin_aeval_jqModC (ResidueField A) _ (by rw [hd]; exact lt_trans zero_lt_one hq)).trans hd

private noncomputable def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.kappaToFull₁ (μ : A) :
    ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) →+* ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  (show ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) →+* R.ResOne from
    IsLocalRing.ResidueField.lift (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ)))

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "kappaToFull₁"
theorem kappaToFull₁_residue (μ : A) (v : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) :
    R.kappaToFull₁ μ (IsLocalRing.residue _ v) = ResOne.val R (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ) v) :=
  IsLocalRing.ResidueField.lift_residue_apply (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ)) v

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_resOne_eq_kappaToFull₁ (μ : A) (c : ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) :
    algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne c = ResOne.mk R (R.kappaToFull₁ μ c) := by
  rw [RingHom.algebraMap_toAlgebra]; rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_resOne_eq_kappaToFull₁"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.resBase₁_gPencilGen (μ : A) :
    ResOne.val R (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ)
        ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩)
      = PlaceSpecialization.resGen₁ q μ := by
  have h1 : R.toIntegers₁ (PlaceSpecialization.KPencil (q := q) μ)
      ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩
      = ⟨PlaceSpecialization.gPencil (q := q) μ, R.gPencil_mem_integers₁ μ⟩ :=
    Subtype.ext (by rw [coe_toIntegers₁]; rfl)
  show R.R₁.residue (R.toIntegers₁ (PlaceSpecialization.KPencil (q := q) μ) _) = _
  rw [h1, R.residue_gPencil_eq μ]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "resBase₁_gPencilGen"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.val_resBase₁_mem_adjoin_resGen₁ (μ : A) (v : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) :
    ResOne.val R (R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ) v)
      ∈ IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₁ q μ} :
          Set ↥(modularFunctionFieldFullC (ResidueField A) 1)) := by
  have hOA : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ∈ R.R₁.integers
      ↔ c ∈ A := R.R₁.algebraMap_mem_iff
  have ht : (IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ)) (PlaceSpecialization.gPencilGen (q := q) μ)
      ∈ R.R₁.integers := R.gPencil_mem_integers₁ μ
  have hgen : R.R₁.residue ⟨(IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ))
      (PlaceSpecialization.gPencilGen (q := q) μ), ht⟩ = PlaceSpecialization.resGen₁ q μ :=
    R.residue_gPencil_eq μ _
  have htr : Transcendental (ResidueField A) (R.R₁.residue ⟨(IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ))
      (PlaceSpecialization.gPencilGen (q := q) μ), ht⟩) := R.transcendental_residue_gPencil μ _
  have hvx : (IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ)) (v : PlaceSpecialization.KPencil (q := q) μ)
      ∈ R.R₁.integers := (R.mem_gaussBase_iff _).mp v.2
  have key := GaussPencil.res_algHom_mem_adjoin_of_transcendental A R.R₁.integers hOA R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap
    (PlaceSpecialization.gPencilGen (q := q) μ) (IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ)) ht htr
    (PlaceSpecialization.mem_adjoin_gPencilGen μ (v : PlaceSpecialization.KPencil (q := q) μ)) hvx
  rw [hgen] at key
  have hv : R.resBase₁ (PlaceSpecialization.KPencil (q := q) μ) v
      = R.R₁.residue ⟨(IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ)) (v : PlaceSpecialization.KPencil (q := q) μ), hvx⟩ := by
    show R.R₁.residue (R.toIntegers₁ (PlaceSpecialization.KPencil (q := q) μ) v) = _
    congr 1
  rw [hv]
  exact key

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "val_resBase₁_mem_adjoin_resGen₁"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_fieldRange_kappaToFull₁ (μ : A) (c : ResidueField A) :
    algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c ∈ (R.kappaToFull₁ (q := q) μ).fieldRange := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨IsLocalRing.residue _ ⟨algebraMap (AlgebraicClosure ℚ) (PlaceSpecialization.KPencil (q := q) μ) a,
    (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩, ?_⟩
  rw [kappaToFull₁_residue, R.resBase₁_algebraMap a]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_mem_fieldRange_kappaToFull₁"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.fieldRange_kappaToFull₁_eq (μ : A) :
    (R.kappaToFull₁ (q := q) μ).fieldRange.toIntermediateField (R.algebraMap_mem_fieldRange_kappaToFull₁ μ)
      = PlaceSpecialization.resField₁ q μ := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective c
    show R.kappaToFull₁ μ (IsLocalRing.residue _ v) ∈ _
    rw [kappaToFull₁_residue]
    exact R.val_resBase₁_mem_adjoin_resGen₁ μ v
  · show IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₁ q μ} :
      Set ↥(modularFunctionFieldFullC (ResidueField A) 1)) ≤ _
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    refine ⟨IsLocalRing.residue _ ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩, ?_⟩
    rw [kappaToFull₁_residue]
    exact R.resBase₁_gPencilGen μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "fieldRange_kappaToFull₁_eq"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_resOne_pencil (μ : A) (hμ : red μ ≠ 0) :
    Module.finrank (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResOne = q := by
  have hE : (R.kappaToFull₁ (q := q) μ).fieldRange.toSubring = (PlaceSpecialization.resField₁ q μ).toSubring := by
    have := congrArg IntermediateField.toSubfield (R.fieldRange_kappaToFull₁_eq μ)
    rw [Subfield.toIntermediateField_toSubfield] at this
    exact congrArg Subfield.toSubring this
  have h := Algebra.finrank_eq_of_equiv_equiv
    (R₀ := ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) (S₀ := R.ResOne)
    (R₁ := ↥(PlaceSpecialization.resField₁ q μ)) (S₁ := ↥(modularFunctionFieldFullC (ResidueField A) 1))
    ((R.kappaToFull₁ (q := q) μ).rangeRestrictFieldEquiv.trans (RingEquiv.subringCongr hE))
    (RingEquiv.refl _)
    (RingHom.ext fun c => (R.algebraMap_resOne_eq_kappaToFull₁ μ c).symm)
  rw [h]
  exact R.finrank_resField₁ μ hμ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "finrank_resOne_pencil"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.fricVal (μ : A) :
    ↥(PlaceSpecialization.KPencil (q := q) μ) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (1 * q)) :=
  (frickeInvolutionBar (1 * q)).toAlgHom.comp (IntermediateField.val (PlaceSpecialization.KPencil (q := q) μ))

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.fricVal" "ModularCurve.PlaceSpecialization.fricVal"
private theorem _root_.ModularCurve.PlaceSpecialization.fricVal_apply (μ : A) (x : PlaceSpecialization.KPencil (q := q) μ) :
    PlaceSpecialization.fricVal (q := q) μ x = frickeInvolutionBar (1 * q) (x : modularFunctionFieldBar (1 * q)) := rfl

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.fricVal_apply" "ModularCurve.PlaceSpecialization.fricVal_apply"
private noncomputable def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.kappaToFull₂ (μ : A) :
    ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) →+* ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
  (show ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) →+* R.ResTwo from
    IsLocalRing.ResidueField.lift (R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ)))

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "kappaToFull₂"
theorem kappaToFull₂_residue (μ : A) (v : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) :
    R.kappaToFull₂ μ (IsLocalRing.residue _ v) = ResTwo.val R (R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ) v) :=
  IsLocalRing.ResidueField.lift_residue_apply (R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ)) v

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_resTwo_eq_kappaToFull₂ (μ : A) (c : ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) :
    algebraMap (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResTwo c = ResTwo.mk R (R.kappaToFull₂ μ c) := by
  rw [RingHom.algebraMap_toAlgebra]; rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_resTwo_eq_kappaToFull₂"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.resBase₂_gPencilGen (μ : A) :
    ResTwo.val R (R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ)
        ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩)
      = PlaceSpecialization.resGen₂ q μ := by
  have h1 : R.toIntegers₂ (PlaceSpecialization.KPencil (q := q) μ)
      ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩
      = ⟨PlaceSpecialization.gPencil (q := q) μ, R.gPencil_mem_integers₂ μ⟩ :=
    Subtype.ext (by rw [coe_toIntegers₂]; rfl)
  show R.R₂.residue (R.toIntegers₂ (PlaceSpecialization.KPencil (q := q) μ) _) = _
  rw [h1, R.residue₂_eq, R.residue_frickeInvolutionBar_gPencil_eq μ]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "resBase₂_gPencilGen"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.val_resBase₂_mem_adjoin_resGen₂ (μ : A) (v : R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) :
    ResTwo.val R (R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ) v)
      ∈ IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₂ q μ} :
          Set ↥(modularFunctionFieldFullC (ResidueField A) 1)) := by
  have hOA : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ∈ R.R₁.integers
      ↔ c ∈ A := R.R₁.algebraMap_mem_iff
  let ψ := PlaceSpecialization.fricVal (q := q) μ
  have ht : ψ (PlaceSpecialization.gPencilGen (q := q) μ) ∈ R.R₁.integers := R.frickeInvolutionBar_gPencil_mem_integers₁ μ
  have hgen : R.R₁.residue ⟨ψ (PlaceSpecialization.gPencilGen (q := q) μ), ht⟩ = PlaceSpecialization.resGen₂ q μ :=
    R.residue_frickeInvolutionBar_gPencil_eq μ _
  have htr : Transcendental (ResidueField A) (R.R₁.residue ⟨ψ (PlaceSpecialization.gPencilGen (q := q) μ), ht⟩) :=
    R.transcendental_residue_frickeInvolutionBar_gPencil μ _
  have hv₂ : algebraMap _ (modularFunctionFieldBar (1 * q)) (v : PlaceSpecialization.KPencil (q := q) μ) ∈ R.R₂.integers :=
    R.algebraMap_mem_integers₂_of_mem_gaussBase _ v.2
  have hvx : ψ (v : PlaceSpecialization.KPencil (q := q) μ) ∈ R.R₁.integers := (R.mem_integers₂_iff _).mp hv₂
  have key := GaussPencil.res_algHom_mem_adjoin_of_transcendental A R.R₁.integers hOA R.R₁.residue
    (fun z hz => R.R₁.isUnit_of_residue_ne_zero hz) (IsLocalRing.residue A)
    (fun a ha h0 => ha ((IsLocalRing.residue_eq_zero_iff a).mp h0)) R.R₁.residue_algebraMap
    (PlaceSpecialization.gPencilGen (q := q) μ) ψ ht htr
    (PlaceSpecialization.mem_adjoin_gPencilGen μ (v : PlaceSpecialization.KPencil (q := q) μ)) hvx
  rw [hgen] at key
  have hto : R.toIntegers₂ (PlaceSpecialization.KPencil (q := q) μ) v
      = ⟨algebraMap _ (modularFunctionFieldBar (1 * q)) (v : PlaceSpecialization.KPencil (q := q) μ), hv₂⟩ :=
    Subtype.ext (R.coe_toIntegers₂ _)
  have hv : R.resBase₂ (PlaceSpecialization.KPencil (q := q) μ) v
      = R.R₁.residue ⟨ψ (v : PlaceSpecialization.KPencil (q := q) μ), hvx⟩ :=
    (congrArg R.R₂.residue hto).trans (R.residue₂_eq _ _)
  rw [hv]
  exact key

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "val_resBase₂_mem_adjoin_resGen₂"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algebraMap_mem_fieldRange_kappaToFull₂ (μ : A) (c : ResidueField A) :
    algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c ∈ (R.kappaToFull₂ (q := q) μ).fieldRange := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨IsLocalRing.residue _ ⟨algebraMap (AlgebraicClosure ℚ) (PlaceSpecialization.KPencil (q := q) μ) a,
    (R.algebraMap_mem_gaussBase_iff a).mpr a.2⟩, ?_⟩
  rw [kappaToFull₂_residue, R.resBase₂_algebraMap a]
  rfl

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "algebraMap_mem_fieldRange_kappaToFull₂"
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.fieldRange_kappaToFull₂_eq (μ : A) :
    (R.kappaToFull₂ (q := q) μ).fieldRange.toIntermediateField (R.algebraMap_mem_fieldRange_kappaToFull₂ μ)
      = PlaceSpecialization.resField₂ q μ := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective c
    show R.kappaToFull₂ μ (IsLocalRing.residue _ v) ∈ _
    rw [kappaToFull₂_residue]
    exact R.val_resBase₂_mem_adjoin_resGen₂ μ v
  · show IntermediateField.adjoin (ResidueField A) ({PlaceSpecialization.resGen₂ q μ} :
      Set ↥(modularFunctionFieldFullC (ResidueField A) 1)) ≤ _
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    refine ⟨IsLocalRing.residue _ ⟨PlaceSpecialization.gPencilGen (q := q) μ, R.gPencilGen_mem_gaussBase μ⟩, ?_⟩
    rw [kappaToFull₂_residue]
    exact R.resBase₂_gPencilGen μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "fieldRange_kappaToFull₂_eq"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_resTwo_pencil (μ : A) :
    Module.finrank (ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) R.ResTwo = q := by
  have hE : (R.kappaToFull₂ (q := q) μ).fieldRange.toSubring = (PlaceSpecialization.resField₂ q μ).toSubring := by
    have := congrArg IntermediateField.toSubfield (R.fieldRange_kappaToFull₂_eq μ)
    rw [Subfield.toIntermediateField_toSubfield] at this
    exact congrArg Subfield.toSubring this
  have h := Algebra.finrank_eq_of_equiv_equiv
    (R₀ := ResidueField (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ))) (S₀ := R.ResTwo)
    (R₁ := ↥(PlaceSpecialization.resField₂ q μ)) (S₁ := ↥(modularFunctionFieldFullC (ResidueField A) 1))
    ((R.kappaToFull₂ (q := q) μ).rangeRestrictFieldEquiv.trans (RingEquiv.subringCongr hE))
    (RingEquiv.refl _)
    (RingHom.ext fun c => (R.algebraMap_resTwo_eq_kappaToFull₂ μ c).symm)
  rw [h]
  exact finrank_resField₂ μ

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "finrank_resTwo_pencil"
end PencilResidueDegrees
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"

section PencilAssembly

open Polynomial AlgebraicCurve.RationalFunctionField

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

attribute [local instance] algGaussBase isScalarTower_gaussBase isLocalHom_resBase₁ isLocalHom_resBase₂
  isScalarTower_resOne isScalarTower_resTwo isLocalHom_constToGaussBase algResidueConst

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isIntegral_gaussBase_pencil_of_mem (μ : A) (hμ : red μ ≠ 0) (f : modularFunctionFieldBar (1 * q))
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    IsIntegral (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) f := by
  refine ValuationSubring.isIntegral_of_forall_mem (K := ↥(PlaceSpecialization.KPencil (q := q) μ))
    (R.gaussBase (PlaceSpecialization.KPencil (q := q) μ)) f fun B hB => ?_
  have hO : ∀ x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jFun (q := q) + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ)
          * jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))),
      x ∈ B ↔ x ∈ R.R₁.integers := by
    intro x hx
    have h := hB ⟨x, hx⟩
    rw [PlaceSpecialization.algebraMap_KPencil_apply, mem_gaussBase_iff, PlaceSpecialization.algebraMap_KPencil_apply] at h
    exact h
  rcases R.integers_eq_or_eq_of_forall_mem_iff_pencil μ hμ B hO with h | h
  · rw [h]; exact h₁
  · rw [h]; exact h₂

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "isIntegral_gaussBase_pencil_of_mem"
open Classical in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencilMu [DecidableEq k]
    (μ : A) (hμ : red μ ≠ 0)
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (PlaceSpecialization.gPencil (q := q) μ
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = (∑ a ∈ (C (red μ) * X ^ q + X - C c₀ : k[X]).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
        + ∑ b ∈ (X ^ q + C (red μ) * X - C c₀ : k[X]).roots.toFinset, (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩) := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hμ0 : (μ : AlgebraicClosure ℚ) ≠ 0 := fun h => hμ (by rw [show μ = 0 from Subtype.ext h, map_zero])
  haveI := finiteDimensional_KPencil (q := q) μ hμ0
  haveI : CharZero ↥(PlaceSpecialization.KPencil (q := q) μ) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(PlaceSpecialization.KPencil (q := q) μ)).injective
  haveI : PerfectField ↥(PlaceSpecialization.KPencil (q := q) μ) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable ↥(PlaceSpecialization.KPencil (q := q) μ) (modularFunctionFieldBar (1 * q)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hd₁ : (C (red μ) * X ^ q + X : k[X]).natDegree = q := GaussPencil.Mu.natDegree_C_mul_X_pow_add_X hμ hq1
  have hd₂ : (X ^ q + C (red μ) * X : k[X]).natDegree = q := GaussPencil.Mu.natDegree_X_pow_add_C_mul_X (red μ) hq1
  have hxF := R.algebraMap_ePencil_X μ
  have key := R.sum_filter_value_eq_sum_roots_add (K₁ := ↥(PlaceSpecialization.KPencil (q := q) μ)) (jFun (q := q)) f
    R.jFun_mem_integers₁.1 h₁ R.jFun_mem_integers₂ h₂
    (R.isIntegral_gaussBase_pencil_of_mem μ hμ _ R.jFun_mem_integers₁.1 R.jFun_mem_integers₂)
    (R.isIntegral_gaussBase_pencil_of_mem μ hμ f h₁ h₂)
    (R.gen_mem_gaussOrder _ _) (R.jqFun_mem_order_pencil μ hμ f) (R.span_order_pencil_eq_top μ hμ f)
    (by rw [R.finrank_resOne_pencil μ hμ, R.finrank_resTwo_pencil μ, finrank_KPencil μ hμ0]; ring)
    (R.exists_rho₁_pencil_eq μ h₁) (R.exists_rho₂_pencil_eq μ hμ h₂)
    (R.ePencil μ) (R.ePencil_X_mem_gaussBase μ) (R.transcendental_residue_ePencil_X μ)
    (C (red μ) * X ^ q + X) (X ^ q + C (red μ) * X) (by rw [hd₁]; exact hqpos) (by rw [hd₂]; exact hqpos)
    (R.residue₁_ePencil_X μ) (R.residue₂_ePencil_X μ)
    (by rw [R.finrank_resOne_pencil μ hμ, hd₁]) (by rw [R.finrank_resTwo_pencil μ, hd₂])
    hu₁ hu₂ D hD c₀
  rw [hxF] at key
  exact key

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "sum_filter_value_eq_sum_roots_add_pencilMu"
end PencilAssembly
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization"

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.GaussPencil P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve"

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.ModularCurve.PlaceSpecialization in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (μ : A) (hμ : red μ ≠ 0)
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (jFun (q := q)
              + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = ((Polynomial.C (red μ) * Polynomial.X ^ q + Polynomial.X - Polynomial.C c₀).roots.toFinset.sum
            fun a => (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
        + ((Polynomial.X ^ q + Polynomial.C (red μ) * Polynomial.X - Polynomial.C c₀).roots.toFinset.sum
            fun b => (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩)) :=
  R.sum_filter_value_eq_sum_roots_add_pencilMu μ hμ f h₁ h₂ hu₁ hu₂ D hD c₀

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil (solution)
