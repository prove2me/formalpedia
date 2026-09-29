-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9357a075-a90b-5fdb-bf79-a7124813c8ee

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_GaussPencilAdapter
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_norm_mem_and_residue_norm_eq_core
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
section

set_option autoImplicit false

p2m_open "Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty"

namespace GaussPencil
namespace B14

theorem mapDomain_apply_eq_sum_filter {α β M : Type*} [AddCommMonoid M] [DecidableEq β]
    (f : α → β) (D : α →₀ M) (b : β) :
    Finsupp.mapDomain f D b = ((D.support.filter fun a => f a = b).sum fun a => D a) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b <;> simp [Finsupp.single_apply, h]

section SpValue
variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {k : Type*} [Field k] (red : A →+* k)

noncomputable def spValue [DecidableEq (RatFunc k)] (w : Place L (RatFunc L)) : Place k (RatFunc k) :=
  open Classical in
  if h : ∃ a : A, w = placeOfPoint L (a : L) then placeOfPoint k (red h.choose) else placeInfty k

variable [DecidableEq (RatFunc L)] [DecidableEq (RatFunc k)]

theorem placeOfPoint_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] (a : K) :
    placeOfPoint K a ≠ placeInfty K := by
  intro h
  have hX : (RatFunc.X : RatFunc K) ∈ (placeOfPoint K a).toValuationSubring := by
    rw [placeOfPoint_eq_ofHeightOneSpectrum]
    have := algebraMap_mem_ofHeightOneSpectrum K
      (heightOneSpectrumOfIrreducible K (Polynomial.irreducible_X_sub_C a)) Polynomial.X
    rwa [RatFunc.algebraMap_X] at this
  rw [h, placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hX
  norm_num at hX

theorem spValue_placeOfPoint_coe (a : A) :
    spValue A red (placeOfPoint L (a : L)) = placeOfPoint k (red a) := by
  classical
  have h : ∃ a' : A, placeOfPoint L (a : L) = placeOfPoint L (a' : L) := ⟨a, rfl⟩
  rw [spValue, dif_pos h]
  have e : (h.choose : L) = a := (placeOfPoint_injective L h.choose_spec).symm
  rw [show h.choose = a from Subtype.ext e]

theorem spValue_eq_placeOfPoint_iff (w : Place L (RatFunc L)) (c : k) :
    spValue A red w = placeOfPoint k c ↔ ∃ a : A, red a = c ∧ w = placeOfPoint L (a : L) := by
  classical
  constructor
  · intro h
    by_cases hw : ∃ a : A, w = placeOfPoint L (a : L)
    · obtain ⟨a, rfl⟩ := hw
      rw [spValue_placeOfPoint_coe] at h
      exact ⟨a, placeOfPoint_injective k h, rfl⟩
    · rw [spValue, dif_neg hw] at h
      exact absurd h.symm (placeOfPoint_ne_placeInfty k c)
  · rintro ⟨a, rfl, rfl⟩
    exact spValue_placeOfPoint_coe A red a

theorem spValue_placeOfPoint_of_not_mem (a : L) (ha : a ∉ A) :
    spValue A red (placeOfPoint L a) = placeInfty k := by
  classical
  rw [spValue, dif_neg]
  rintro ⟨a', ha'⟩
  exact ha ((placeOfPoint_injective L ha') ▸ a'.2)

theorem spValue_placeInfty : spValue A red (placeInfty L) = placeInfty k := by
  classical
  rw [spValue, dif_neg]
  rintro ⟨a', ha'⟩
  exact placeOfPoint_ne_placeInfty L (a' : L) ha'.symm

theorem mapDomain_spValue_eq_ord
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (P Q : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A)
    (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A)
    (D : Divisor L (RatFunc L))
    (hD : ∀ w, D w = w.ord (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
                              / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))) :
    ∀ v' : Place k (RatFunc k),
      Finsupp.mapDomain (spValue A red) D v'
        = v'.ord (algebraMap (Polynomial k) (RatFunc k) (P.map red)
                  / algebraMap (Polynomial k) (RatFunc k) (Q.map red)) :=
  mapDomain_eq_ord_div_map_of_primitive red hred (spValue A red)
    (spValue_placeOfPoint_coe A red) (spValue_placeOfPoint_of_not_mem A red) (spValue_placeInfty A red)
    P Q hP hQ D hD

omit A red in

theorem eq_placeOfPoint_iff_ord_pos (v : Place L (RatFunc L)) (a : L) :
    v = placeOfPoint L a ↔ 0 < v.ord (RatFunc.X - algebraMap L (RatFunc L) a) := by
  classical
  have hXa : (RatFunc.X - algebraMap L (RatFunc L) a)
      = algebraMap (Polynomial L) (RatFunc L) (Polynomial.X - Polynomial.C a) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hXa, ord_X_sub_C L a v, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  rcases eq_placeOfPoint_or_eq_placeInfty L v with ⟨b, rfl⟩ | rfl
  · have hne : placeInfty L ≠ placeOfPoint L b := (placeOfPoint_ne_placeInfty L b).symm
    rw [if_neg hne]
    by_cases hb : placeOfPoint L a = placeOfPoint L b
    · rw [if_pos hb]; simp [hb]
    · rw [if_neg hb]; simp [Ne.symm hb]
  · have hne : placeOfPoint L a ≠ placeInfty L := placeOfPoint_ne_placeInfty L a
    rw [if_neg hne, if_pos rfl]
    simp [hne.symm]

end SpValue
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

section PullUp
variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)]
  {F : Type*} [Field F] [Algebra L F] (ι : RatFunc L →ₐ[L] F) (hι : ι.toRingHom.IsIntegral)

theorem restrictAlong_eq_placeOfPoint_iff (W : Place L F) (a : L) :
    W.restrictAlong ι hι = placeOfPoint L a ↔ 0 < W.ord (ι RatFunc.X - algebraMap L F a) := by
  have key : W.ord (ι RatFunc.X - algebraMap L F a)
      = (Place.ramificationIndexAlong ι W : ℤ) * (W.restrictAlong ι hι).ord (RatFunc.X - algebraMap L (RatFunc L) a) := by
    rw [← ι.commutes a, ← map_sub, Place.ord_restrictAlong ι hι]
  have hepos : 0 < (Place.ramificationIndexAlong ι W : ℤ) := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI := isIntegral_along ι hι
    exact_mod_cast Place.ramificationIndex_pos (F := RatFunc L) W
  rw [key, eq_placeOfPoint_iff_ord_pos]
  constructor
  · intro h; exact mul_pos hepos h
  · intro h; exact pos_of_mul_pos_right h hepos.le

end PullUp
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

section B
variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)]
  {K₁ F : Type*} [Field K₁] [Field F] [Algebra L K₁] [Algebra L F] [Algebra K₁ F] [IsScalarTower L K₁ F]
  [FiniteDimensional K₁ F] [Algebra.IsSeparable K₁ F] [CharZero K₁]
  (e₁ : RatFunc L ≃ₐ[L] K₁)

include e₁ in

theorem isRational_of_line {E : Type*} [Field E] [Algebra L E] [Algebra K₁ E] [IsScalarTower L K₁ E]
    [FiniteDimensional K₁ E] (W : Place L E) : W.IsRational := by
  letI : Algebra (RatFunc L) K₁ := e₁.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower L (RatFunc L) K₁ := IsScalarTower.of_algebraMap_eq fun a => (e₁.commutes a).symm
  letI : Algebra (RatFunc L) E := ((algebraMap K₁ E).comp e₁.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc L) K₁ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L (RatFunc L) E := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap L E a = algebraMap K₁ E (e₁ (algebraMap L (RatFunc L) a))
    rw [e₁.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc L) K₁ :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc L) K₁) fun y => ⟨e₁.symm y, e₁.apply_symm_apply y⟩
  haveI : FiniteDimensional (RatFunc L) E := Module.Finite.trans K₁ E
  exact Place.isRational_of_isAlgClosed W

include e₁ in

theorem sum_fiberOver_ord_eq_ord_norm (f : F) (hf : f ≠ 0) (v : Place L K₁) :
    ∑ W ∈ v.fiberOver F, W.ord f = v.ord (Algebra.norm K₁ f) := by
  rw [Place.ord_norm_eq_sum_fiberOver v hf]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Place.inertiaDeg_eq_one_of_isRational W (isRational_of_line e₁ W) (isRational_of_line e₁ _),
    Nat.cast_one, one_mul]

include e₁ in

theorem mapDomain_restrict_eq (D : Divisor L F) (f : F) (hf : f ≠ 0) (hD : ∀ W, D W = W.ord f)
    (v : Place L K₁) :
    Finsupp.mapDomain (fun W : Place L F => W.restrict K₁) D v = v.ord (Algebra.norm K₁ f) := by
  classical
  rw [mapDomain_apply_eq_sum_filter, ← sum_fiberOver_ord_eq_ord_norm e₁ f hf v]
  have hset : (D.support.filter fun W : Place L F => W.restrict K₁ = v)
      = (v.fiberOver F).filter fun W => W ∈ D.support := by
    ext W
    simp only [Finset.mem_filter, Place.mem_fiberOver]
    tauto
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases h : W ∈ D.support
  · rw [if_pos h, hD]
  · rw [if_neg h]
    have h0 : D W = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [← hD W, h0]

noncomputable def lineEmb : RatFunc L →ₐ[L] F := (IsScalarTower.toAlgHom L K₁ F).comp e₁.toAlgHom

theorem lineEmb_apply (y : RatFunc L) : lineEmb e₁ y = algebraMap K₁ F (e₁ y) := rfl

theorem lineEmb_isIntegral : (lineEmb (F := F) e₁).toRingHom.IsIntegral := by
  haveI : Algebra.IsIntegral K₁ F := Algebra.IsIntegral.of_finite K₁ F
  intro y
  have h1 : (e₁.toAlgHom.toRingHom : RatFunc L →+* K₁).IsIntegral := RingHom.isIntegral_of_surjective _ e₁.surjective
  have h2 : (algebraMap K₁ F).IsIntegral := fun z => Algebra.IsIntegral.isIntegral z
  exact RingHom.IsIntegral.trans _ _ h1 h2 y

theorem congrEquiv_symm_restrict (W : Place L F) :
    (Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b)).symm (W.restrict K₁)
      = W.restrictAlong (lineEmb e₁) (lineEmb_isIntegral e₁) := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [Place.congrEquiv_symm_apply, Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap,
    Place.mem_restrict_iff]
  show algebraMap K₁ F (e₁.toRingEquiv.symm.symm y) ∈ W.toValuationSubring ↔ _
  rw [RingEquiv.symm_symm]
  exact Iff.rfl

theorem restrict_eq_congr_placeOfPoint_iff (W : Place L F) (a : L) :
    W.restrict K₁ = Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b) (placeOfPoint L a)
      ↔ 0 < W.ord (algebraMap K₁ F (e₁ RatFunc.X) - algebraMap L F a) := by
  rw [← Equiv.symm_apply_eq, congrEquiv_symm_restrict]
  exact restrictAlong_eq_placeOfPoint_iff (lineEmb e₁) (lineEmb_isIntegral e₁) W a

open Classical in

theorem mapDomain_spValue_congr_restrict_placeOfPoint (A : ValuationSubring L) {k : Type*} [Field k]
    [DecidableEq (RatFunc k)] (red : A →+* k) (D : Divisor L F) (c₀ : k) :
    Finsupp.mapDomain (fun (W : Place L F) =>
        spValue A red ((Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b)).symm (W.restrict K₁))) D
        (placeOfPoint k c₀)
      = ((D.support.filter fun (W : Place L F) =>
            ∃ a : A, red a = c₀ ∧ 0 < W.ord (algebraMap K₁ F (e₁ RatFunc.X) - algebraMap L F (a : L))).sum
          fun W => D W) := by
  classical
  rw [mapDomain_apply_eq_sum_filter]
  refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) fun _ _ => rfl
  rw [spValue_eq_placeOfPoint_iff]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [Equiv.symm_apply_eq]
  exact restrict_eq_congr_placeOfPoint_iff e₁ W a

end B
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

section B3
variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)]
  {K₁ : Type*} [Field K₁] [Algebra L K₁] (e₁ : RatFunc L ≃ₐ[L] K₁)
  (A : ValuationSubring L) {k : Type*} [Field k] [DecidableEq (RatFunc k)] (red : A →+* k)

theorem mapDomain_spValue_congr_symm_eq_ord
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (c : A) (hc : c ∉ IsLocalRing.maximalIdeal A)
    (P Q : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A)
    (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A)
    (D₁ : Divisor L K₁)
    (hD₁ : ∀ v, D₁ v = v.ord (e₁ (RatFunc.C (c : L)
        * (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
            / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))))) :
    ∀ v' : Place k (RatFunc k),
      Finsupp.mapDomain (fun v => spValue A red
          ((Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b)).symm v)) D₁ v'
        = v'.ord (RatFunc.C (red c)
            * (algebraMap (Polynomial k) (RatFunc k) (P.map red)
                / algebraMap (Polynomial k) (RatFunc k) (Q.map red))) := by
  classical
  intro v'
  set g := Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b) with hg

  set P' : Polynomial A := Polynomial.C c * P with hP'
  have hP'prim : ∃ i, P'.coeff i ∉ IsLocalRing.maximalIdeal A := by
    obtain ⟨i, hi⟩ := hP
    refine ⟨i, ?_⟩
    rw [hP', Polynomial.coeff_C_mul]
    intro hmem
    rcases (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_or_mem hmem with h | h
    · exact hc h
    · exact hi h
  have hupL : RatFunc.C (c : L) * (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
        / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))
      = algebraMap (Polynomial L) (RatFunc L) (P'.map (algebraMap A L))
        / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)) := by
    rw [hP', Polynomial.map_mul, Polynomial.map_C, map_mul, RatFunc.algebraMap_C, mul_div_assoc]
    rfl
  have hupk : RatFunc.C (red c) * (algebraMap (Polynomial k) (RatFunc k) (P.map red)
        / algebraMap (Polynomial k) (RatFunc k) (Q.map red))
      = algebraMap (Polynomial k) (RatFunc k) (P'.map red)
        / algebraMap (Polynomial k) (RatFunc k) (Q.map red) := by
    rw [hP', Polynomial.map_mul, Polynomial.map_C, map_mul, RatFunc.algebraMap_C, mul_div_assoc]

  have hcomp : (fun v => spValue A red (g.symm v)) = spValue A red ∘ g.symm := rfl
  rw [hcomp, Finsupp.mapDomain_comp]
  have hD' : ∀ w, Finsupp.mapDomain g.symm D₁ w
      = w.ord (algebraMap (Polynomial L) (RatFunc L) (P'.map (algebraMap A L))
          / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L))) := by
    intro w
    rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, hD₁, ← hupL, hg, Place.congrEquiv_apply]
    exact Place.ord_congrRingEquiv e₁.toRingEquiv (fun b => e₁.commutes b) w _
  rw [hupk]
  exact mapDomain_spValue_eq_ord A red hred P' Q hP'prim hQ _ hD' v'

end B3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end GaussPencil.B14
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
section

set_option autoImplicit false

namespace GaussPencil

theorem algebraMap_norm_eq_norm_of_basis {κ κ' E E' : Type*} [Field κ] [Field κ'] [CommRing E] [CommRing E']
    [Algebra κ E] [Algebra κ' E'] (θ : κ →+* κ') (Ψ : E →+* E')
    (hcomm : ∀ c, Ψ (algebraMap κ E c) = algebraMap κ' E' (θ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι κ E) (b' : Module.Basis ι κ' E')
    (hb : ∀ i, Ψ (b i) = b' i) (z : E) :
    θ (Algebra.norm κ z) = Algebra.norm κ' (Ψ z) := by
  classical

  have key : ∀ e : E, Ψ e = ∑ j, θ (b.repr e j) • b' j := by
    intro e
    conv_lhs => rw [← b.sum_repr e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hcomm, hb, ← Algebra.smul_def]
  have hrepr : ∀ (e : E) (i : ι), b'.repr (Ψ e) i = θ (b.repr e i) := by
    intro e i
    rw [key e, b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb j, ← map_mul, hrepr]

theorem algebraMap_norm_eq_norm_of_span {κ κ' E E' : Type*} [Field κ] [Field κ'] [CommRing E] [CommRing E']
    [Algebra κ E] [Algebra κ' E'] (θ : κ →+* κ') (Ψ : E →+* E')
    (hcomm : ∀ c, Ψ (algebraMap κ E c) = algebraMap κ' E' (θ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι κ E)
    (hspan : ⊤ ≤ Submodule.span κ' (Set.range (Ψ ∘ b)))
    (hcard : Fintype.card ι = Module.finrank κ' E') (z : E) :
    θ (Algebra.norm κ z) = Algebra.norm κ' (Ψ z) :=
  algebraMap_norm_eq_norm_of_basis θ Ψ hcomm b (basisOfTopLeSpanOfCardEqFinrank (Ψ ∘ b) hspan hcard)
    (fun i => by rw [coe_basisOfTopLeSpanOfCardEqFinrank]; rfl) z

end GaussPencil
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
section

set_option autoImplicit false

open Polynomial

namespace GaussPencil
namespace A4Res

theorem ratFunc_algHom_ext {k L : Type*} [Field k] [Field L] [Algebra k L]
    (φ ψ : RatFunc k →ₐ[k] L) (h : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have hpoly : ∀ p : k[X], φ (algebraMap k[X] (RatFunc k) p) = ψ (algebraMap k[X] (RatFunc k) p) := by
    intro p
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algHom_apply, ← aeval_algHom_apply, h]
  ext f
  induction f using RatFunc.induction_on with
  | f p q hq => rw [map_div₀, map_div₀, hpoly, hpoly]

section Setup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (e : RatFunc k ≃ₐ[k] F)

theorem e_algebraMap (p : k[X]) : e (algebraMap k[X] (RatFunc k) p) = aeval (e RatFunc.X) p := by
  rw [aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]

theorem mem_adjoin_e_X (K₀ : Type*) [Field K₀] [Algebra k K₀] [Algebra K₀ F] [IsScalarTower k K₀ F]
    (y : F) : y ∈ IntermediateField.adjoin K₀ {e RatFunc.X} := by
  obtain ⟨f, rfl⟩ := e.surjective y
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [map_div₀, e_algebraMap, e_algebraMap]
    have hmem : ∀ s : k[X], aeval (e RatFunc.X) s ∈ IntermediateField.adjoin K₀ {e RatFunc.X} := by
      intro s
      rw [← aeval_map_algebraMap K₀]
      exact IntermediateField.algebra_adjoin_le_adjoin K₀ _ (Polynomial.aeval_mem_adjoin_singleton K₀ _)
    exact div_mem (hmem p) (hmem q)

theorem adjoin_e_X_eq_top (K₀ : Type*) [Field K₀] [Algebra k K₀] [Algebra K₀ F] [IsScalarTower k K₀ F] :
    IntermediateField.adjoin K₀ {e RatFunc.X} = ⊤ :=
  eq_top_iff.mpr fun y _ => mem_adjoin_e_X e K₀ y

theorem transcendental_algebraMap (r : k[X]) (hr : 0 < r.natDegree) :
    Transcendental k (algebraMap k[X] (RatFunc k) r) := by
  refine RatFunc.transcendental_of_ne_C (algebraMap k[X] (RatFunc k) r) ?_
  rintro ⟨c, hc⟩
  have h := congrArg RatFunc.num hc
  rw [RatFunc.num_algebraMap, RatFunc.num_C] at h
  rw [h, natDegree_C] at hr
  exact lt_irrefl 0 hr

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  (r : k[X]) (hr : 0 < r.natDegree)
  (hT : algebraMap (RatFunc k) F RatFunc.X = e (algebraMap k[X] (RatFunc k) r))

omit [IsScalarTower k (RatFunc k) F] in
include hT in
theorem algebraMap_X_eq_aeval : algebraMap (RatFunc k) F RatFunc.X = aeval (e RatFunc.X) r := by
  rw [hT, e_algebraMap]

include hr hT in

theorem finrank_eq_natDegree : Module.finrank (RatFunc k) F = r.natDegree := by
  have htr := transcendental_algebraMap r hr
  set i := RatFunc.algEquivOfTranscendental (algebraMap k[X] (RatFunc k) r) htr with hi

  have hc : ((IntermediateField.val (IntermediateField.adjoin k {algebraMap k[X] (RatFunc k) r})).comp i.toAlgHom)
      = (e.symm : F →ₐ[k] RatFunc k).comp (IsScalarTower.toAlgHom k (RatFunc k) F) := by
    refine ratFunc_algHom_ext _ _ ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_algHom,
      IsScalarTower.coe_toAlgHom', hT, AlgEquiv.symm_apply_apply]
    rw [hi, RatFunc.algEquivOfTranscendental_X]
  have hfin := Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.symm.toRingEquiv (by
    ext f
    have := AlgHom.congr_fun hc f
    simpa using this)
  rw [hfin, RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    natDegree_one, max_eq_left (Nat.zero_le _)]

noncomputable def defPoly (k : Type*) [Field k] (r : k[X]) : (RatFunc k)[X] :=
  r.map (algebraMap k (RatFunc k)) - C RatFunc.X

omit [Algebra k F] in
theorem natDegree_defPoly : (defPoly k r).natDegree = r.natDegree := by
  rw [defPoly, natDegree_sub_C, natDegree_map]

include hr in
omit [Algebra k F] in
theorem leadingCoeff_defPoly : (defPoly k r).leadingCoeff = algebraMap k (RatFunc k) r.leadingCoeff := by
  rw [defPoly, leadingCoeff, natDegree_sub_C, natDegree_map, coeff_sub, coeff_map, coeff_C,
    if_neg hr.ne', sub_zero, coeff_natDegree]

include hr in
omit [Algebra k F] in
theorem defPoly_ne_zero : defPoly k r ≠ 0 := fun h => by
  have := natDegree_defPoly (k := k) r
  rw [h, natDegree_zero] at this
  omega

include hT in
theorem aeval_defPoly : aeval (e RatFunc.X) (defPoly k r) = 0 := by
  rw [defPoly, map_sub, aeval_map_algebraMap, aeval_C, algebraMap_X_eq_aeval e r hT, sub_self]

include hr hT in

theorem minpoly_eq [FiniteDimensional (RatFunc k) F] :
    minpoly (RatFunc k) (e RatFunc.X) = C (algebraMap k (RatFunc k) r.leadingCoeff)⁻¹ * defPoly k r := by
  have hlc : algebraMap k (RatFunc k) r.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k (RatFunc k)).injective).mpr
      (leadingCoeff_ne_zero.mpr fun h => by rw [h, natDegree_zero] at hr; exact lt_irrefl 0 hr)
  have hint : IsIntegral (RatFunc k) (e RatFunc.X) := IsIntegral.of_finite _ _
  have hQmonic : (C (algebraMap k (RatFunc k) r.leadingCoeff)⁻¹ * defPoly k r).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_defPoly r hr, inv_mul_cancel₀ hlc]
  have hQ : aeval (e RatFunc.X) (C (algebraMap k (RatFunc k) r.leadingCoeff)⁻¹ * defPoly k r) = 0 := by
    rw [map_mul, aeval_defPoly e r hT, mul_zero]
  have hdeg : (minpoly (RatFunc k) (e RatFunc.X)).natDegree = r.natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, adjoin_e_X_eq_top e (RatFunc k),
      IntermediateField.finrank_top', finrank_eq_natDegree e r hr hT]
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hQmonic
    (minpoly.dvd _ _ hQ) ?_
  rw [hdeg, natDegree_C_mul (inv_ne_zero hlc), natDegree_defPoly]

include hr hT in

theorem norm_X_sub_algebraMap [FiniteDimensional (RatFunc k) F] (a : k) :
    Algebra.norm (RatFunc k) (e RatFunc.X - algebraMap k F a)
      = (-1) ^ r.natDegree * ((algebraMap k (RatFunc k) r.leadingCoeff)⁻¹
          * (algebraMap k (RatFunc k) (r.eval a) - RatFunc.X)) := by
  have hlc : algebraMap k (RatFunc k) r.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k (RatFunc k)).injective).mpr
      (leadingCoeff_ne_zero.mpr fun h => by rw [h, natDegree_zero] at hr; exact lt_irrefl 0 hr)
  have haF : algebraMap k F a = algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a) :=
    IsScalarTower.algebraMap_apply k (RatFunc k) F a
  rw [haF]
  have hzint : IsIntegral (RatFunc k) (e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a)) :=
    IsIntegral.of_finite _ _

  have htop : IntermediateField.adjoin (RatFunc k)
      {e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a)} = ⊤ := by
    rw [eq_top_iff, ← adjoin_e_X_eq_top e (RatFunc k), IntermediateField.adjoin_simple_le_iff]
    have hmem := add_mem (IntermediateField.mem_adjoin_simple_self (RatFunc k)
        (e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a)))
      (algebraMap_mem (IntermediateField.adjoin (RatFunc k)
        {e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a)}) (algebraMap k (RatFunc k) a))
    rwa [sub_add_cancel] at hmem

  let pb : PowerBasis (RatFunc k) F :=
    (IntermediateField.adjoin.powerBasis hzint).map
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  have hgen : pb.gen = e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a) := by
    simp only [pb, PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hdim : pb.dim = (minpoly (RatFunc k)
      (e RatFunc.X - algebraMap (RatFunc k) F (algebraMap k (RatFunc k) a))).natDegree := by simp [pb]
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hgen, hdim, minpoly.sub_algebraMap, natDegree_comp, natDegree_X_add_C, mul_one,
    coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add] at hnorm
  rw [hnorm, minpoly_eq e r hr hT, natDegree_C_mul (inv_ne_zero hlc), natDegree_defPoly, eval_mul, eval_C,
    defPoly, eval_sub, eval_C, eval_map, eval₂_at_apply]

include hr hT in

private theorem _root_.GaussPencil.A4Res.norm_algebraMap [FiniteDimensional (RatFunc k) F] (d : k) :
    Algebra.norm (RatFunc k) (algebraMap k F d) = algebraMap k (RatFunc k) d ^ r.natDegree := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) F, Algebra.norm_algebraMap, finrank_eq_natDegree e r hr hT]

p2m_export "GaussPencil.A4Res" "norm_algebraMap"
end Setup
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

section Ord

p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty"

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (e : RatFunc k ≃ₐ[k] F)
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  (r : k[X]) (hr : 0 < r.natDegree)
  (hT : algebraMap (RatFunc k) F RatFunc.X = e (algebraMap k[X] (RatFunc k) r))

noncomputable def normPoly (p : k[X]) : k[X] :=
  C (p.leadingCoeff ^ r.natDegree)
    * (p.roots.map fun a => C (-((-1 : k) ^ r.natDegree * (r.leadingCoeff)⁻¹)) * (X - C (r.eval a))).prod

include hr in
omit [Algebra k F] in
theorem normPoly_unit_ne_zero : (-((-1 : k) ^ r.natDegree * (r.leadingCoeff)⁻¹)) ≠ 0 := by
  have hlc : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun h => by
    rw [h, natDegree_zero] at hr; exact lt_irrefl 0 hr
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (inv_ne_zero hlc))

include hr in
omit [Algebra k F] in
theorem roots_normPoly (p : k[X]) (hp : p ≠ 0) : (normPoly r p).roots = p.roots.map r.eval := by
  classical
  have hu := normPoly_unit_ne_zero r hr
  rw [normPoly, roots_C_mul _ (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp)), roots_multiset_prod,
    Multiset.bind_map]
  · simp_rw [roots_C_mul _ hu, roots_X_sub_C]
    exact Multiset.bind_singleton _ _
  · rw [Multiset.mem_map]
    rintro ⟨a, _, ha⟩
    exact (mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_sub_C_ne_zero _)) ha

include hr in
omit [Algebra k F] in
theorem normPoly_ne_zero (p : k[X]) (hp : p ≠ 0) : normPoly r p ≠ 0 := by
  classical
  have hu := normPoly_unit_ne_zero r hr
  rw [normPoly]
  refine mul_ne_zero (by rw [Ne, C_eq_zero]; exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp)) ?_
  rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨a, _, ha⟩
  exact (mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_sub_C_ne_zero _)) ha

include hr hT in
theorem norm_e_algebraMap [IsAlgClosed k] [FiniteDimensional (RatFunc k) F] (p : k[X]) :
    Algebra.norm (RatFunc k) (e (algebraMap k[X] (RatFunc k) p))
      = algebraMap k[X] (RatFunc k) (normPoly r p) := by
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p))
  conv_lhs => rw [← hsplit]
  rw [e_algebraMap, map_mul, aeval_C, map_multiset_prod, Multiset.map_map, map_mul,
    norm_algebraMap e r hr hT, map_multiset_prod, Multiset.map_map]
  rw [normPoly, map_mul, RatFunc.algebraMap_C, map_pow, map_multiset_prod, Multiset.map_map]
  congr 1
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C, norm_X_sub_algebraMap e r hr hT a,
    map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_neg, map_pow, map_one, map_inv₀,
    ← RatFunc.algebraMap_eq_C]
  ring

include hr hT in

theorem ord_norm_e_algebraMap [IsAlgClosed k] [DecidableEq k] [FiniteDimensional (RatFunc k) F]
    (p : k[X]) (hp : p ≠ 0) (c : k) :
    (placeOfPoint k c).ord (Algebra.norm (RatFunc k) (e (algebraMap k[X] (RatFunc k) p)))
      = ((p.roots.map r.eval).count c : ℕ) := by
  classical
  rw [norm_e_algebraMap e r hr hT, ord_placeOfPoint_algebraMap c (normPoly_ne_zero r hr p hp),
    ← count_roots, roots_normPoly r hr p hp]

omit [Algebra k F] in

theorem sum_count_eq_count_map [DecidableEq k] (m : Multiset k) (c : k) (hrc : r - C c ≠ 0) :
    ∑ a ∈ (r - C c).roots.toFinset, (m.count a : ℤ) = ((m.map r.eval).count c : ℕ) := by
  have hmem : ∀ a : k, a ∈ (r - C c).roots.toFinset ↔ r.eval a = c := by
    intro a
    rw [Multiset.mem_toFinset, mem_roots hrc, IsRoot, eval_sub, eval_C, sub_eq_zero]
  induction m using Multiset.induction_on with
  | empty => simp
  | cons b m ih =>
    simp only [Multiset.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_add_distrib, ih, Multiset.map_cons]
    rw [Finset.sum_ite_eq' ((r - C c).roots.toFinset) b (fun _ => (1 : ℤ))]
    simp only [hmem]
    by_cases hb : r.eval b = c
    · rw [if_pos hb, if_pos hb.symm]
    · rw [if_neg hb, if_neg (Ne.symm hb)]

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] in

theorem sum_ord_e_algebraMap [DecidableEq k] (p : k[X]) (hp : p ≠ 0) (c : k) (hrc : r - C c ≠ 0) :
    ∑ a ∈ (r - C c).roots.toFinset,
        (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord
          (e (algebraMap k[X] (RatFunc k) p))
      = ((p.roots.map r.eval).count c : ℕ) := by
  classical
  have hterm : ∀ a : k, (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord
      (e (algebraMap k[X] (RatFunc k) p)) = (p.roots.count a : ℤ) := by
    intro a
    rw [Place.congrEquiv_apply, count_roots, ← ord_placeOfPoint_algebraMap a hp]
    exact Place.ord_congrRingEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a) _
  simp_rw [hterm]
  exact sum_count_eq_count_map r p.roots c hrc

include hr hT in

theorem ord_placeOfPoint_norm_eq_sum_ord' [IsAlgClosed k] [DecidableEq k] [FiniteDimensional (RatFunc k) F]
    (y : F) (hy : y ≠ 0) (c : k) :
    (placeOfPoint k c).ord (Algebra.norm (RatFunc k) y)
      = ∑ a ∈ (r - C c).roots.toFinset,
          (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord y := by
  classical
  have hrc : r - C c ≠ 0 := fun h => by
    have := congrArg natDegree h
    rw [natDegree_sub_C, natDegree_zero] at this
    omega

  obtain ⟨f, rfl⟩ := e.surjective y
  have hf : f ≠ 0 := fun h => hy (by rw [h, map_zero])
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  set N := e (algebraMap k[X] (RatFunc k) f.num) with hN
  set D := e (algebraMap k[X] (RatFunc k) f.denom) with hD
  have hN0 : N ≠ 0 := by rw [hN, map_ne_zero_iff _ e.injective]; exact RatFunc.algebraMap_ne_zero hnum
  have hD0 : D ≠ 0 := by rw [hD, map_ne_zero_iff _ e.injective]; exact RatFunc.algebraMap_ne_zero hden
  have hy' : e f = N / D := by rw [hN, hD, ← map_div₀, RatFunc.num_div_denom]
  have hnormD : Algebra.norm (RatFunc k) D ≠ 0 := Algebra.norm_ne_zero_iff.mpr hD0
  have hnormN : Algebra.norm (RatFunc k) N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hN0
  have hnorm : Algebra.norm (RatFunc k) (N / D) = Algebra.norm (RatFunc k) N / Algebra.norm (RatFunc k) D := by
    rw [eq_div_iff hnormD, ← map_mul, div_mul_cancel₀ _ hD0]
  rw [hy', hnorm, div_eq_mul_inv, (placeOfPoint k c).ord_mul hnormN (inv_ne_zero hnormD), Place.ord_inv,
    ord_norm_e_algebraMap e r hr hT _ hnum, ord_norm_e_algebraMap e r hr hT _ hden]
  have hrhs : ∀ a : k, (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord (N / D)
      = (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord N
        - (Place.congrEquiv e.toRingEquiv (fun b => e.commutes b) (placeOfPoint k a)).ord D := by
    intro a
    rw [div_eq_mul_inv, Place.ord_mul _ hN0 (inv_ne_zero hD0), Place.ord_inv, sub_eq_add_neg]
  simp_rw [hrhs]
  rw [Finset.sum_sub_distrib, sum_ord_e_algebraMap e r _ hnum c hrc, sum_ord_e_algebraMap e r _ hden c hrc]
  ring

end Ord
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

theorem ord_placeOfPoint_norm_eq_sum_ord
    (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k]
    {F : Type*} [Field F] [Algebra k F] (e : RatFunc k ≃ₐ[k] F)
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (r : k[X]) (hr : 0 < r.natDegree)
    (hT : algebraMap (RatFunc k) F RatFunc.X = e (algebraMap k[X] (RatFunc k) r))
    (y : F) (hy : y ≠ 0) (c : k) :
    (AlgebraicCurve.RationalFunctionField.placeOfPoint k c).ord (Algebra.norm (RatFunc k) y)
      = ∑ a ∈ (r - C c).roots.toFinset,
          (AlgebraicCurve.Place.congrEquiv e.toRingEquiv (fun b => e.commutes b)
            (AlgebraicCurve.RationalFunctionField.placeOfPoint k a)).ord y :=
  ord_placeOfPoint_norm_eq_sum_ord' e r hr hT y hy c

theorem finrank_eq_natDegree_of_algebraMap_X_eq
    (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (e : RatFunc k ≃ₐ[k] F)
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    (r : k[X]) (hr : 0 < r.natDegree)
    (hT : algebraMap (RatFunc k) F RatFunc.X = e (algebraMap k[X] (RatFunc k) r)) :
    Module.finrank (RatFunc k) F = r.natDegree :=
  finrank_eq_natDegree e r hr hT

end GaussPencil.A4Res
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

section
p2m_open "Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.ModularCurve"

set_option autoImplicit false

namespace GaussPencil
namespace B6

theorem ratFunc_ringHom_ext {K E : Type*} [Field K] [Field E] (φ ψ : RatFunc K →+* E)
    (hC : ∀ a : K, φ (RatFunc.C a) = ψ (RatFunc.C a)) (hX : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have hp : ∀ p : K[X], φ (algebraMap K[X] (RatFunc K) p) = ψ (algebraMap K[X] (RatFunc K) p) := by
    intro p
    have h : φ.comp (algebraMap K[X] (RatFunc K)) = ψ.comp (algebraMap K[X] (RatFunc K)) :=
      Polynomial.ringHom_ext (fun a => by simpa [RatFunc.algebraMap_C] using hC a)
        (by simpa [RatFunc.algebraMap_X] using hX)
    exact RingHom.congr_fun h p
  refine RingHom.ext fun f => ?_
  induction f using RatFunc.induction_on with
  | f p q hq => rw [map_div₀, map_div₀, hp, hp]

theorem top_le_of_forall_pow_mem {κ' E : Type*} [Field κ'] [Field E] [Algebra κ' E]
    (x : E) (hx : IntermediateField.adjoin κ' {x} = ⊤) (hint : IsIntegral κ' x)
    (M : Submodule κ' E) (hM : ∀ n : ℕ, x ^ n ∈ M) : ⊤ ≤ M := by
  intro y _
  have hy : y ∈ (IntermediateField.adjoin κ' {x}).toSubalgebra := by
    rw [hx]; exact Algebra.mem_top
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  change Polynomial.aeval x p ∈ M
  rw [Polynomial.aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hM i)

theorem coe_ratFuncEquivCharLOneC_X (k : Type*) [Field k] :
    ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k := by
  change (((RatFunc.algEquivOfTranscendental (jqModC k) (ModularCurve.transcendental_jqModC k)) RatFunc.X :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k) = jqModC k
  exact RatFunc.algEquivOfTranscendental_X _ _

theorem ord_map_norm_eq_sum_ord (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k]
    {κ κᵢ : Type*} [Field κ] [Field κᵢ] [Algebra κ κᵢ] [FiniteDimensional κ κᵢ]
    (θ₀ : κ →+* RatFunc k) (θ : RatFunc k →ₐ[k] ↥(modularFunctionFieldC k 1))
    (r : k[X]) (hr : 0 < r.natDegree)
    (hθ : θ RatFunc.X = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r))
    (Ψ : κᵢ →+* ↥(modularFunctionFieldC k 1))
    (hcomm : ∀ c, Ψ (algebraMap κ κᵢ c) = θ (θ₀ c))
    (hgen : (ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) ∈ Set.range Ψ)
    (hdeg : Module.finrank κ κᵢ = r.natDegree)
    (z : κᵢ) (hz : z ≠ 0) (c₀ : k) :
    (placeOfPoint k c₀).ord (θ₀ (Algebra.norm κ z))
      = ∑ a ∈ (r - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (Ψ z) := by
  classical
  letI : Algebra (RatFunc k) ↥(modularFunctionFieldC k 1) := θ.toRingHom.toAlgebra
  haveI : IsScalarTower k (RatFunc k) ↥(modularFunctionFieldC k 1) :=
    IsScalarTower.of_algebraMap_eq fun a => (θ.commutes a).symm
  have hT : algebraMap (RatFunc k) ↥(modularFunctionFieldC k 1) RatFunc.X
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r) := hθ
  have hfin : Module.finrank (RatFunc k) ↥(modularFunctionFieldC k 1) = r.natDegree :=
    GaussPencil.A4Res.finrank_eq_natDegree_of_algebraMap_X_eq k (ratFuncEquivCharLOneC k) r hr hT
  haveI : FiniteDimensional (RatFunc k) ↥(modularFunctionFieldC k 1) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact hr)
  have hnorm : θ₀ (Algebra.norm κ z) = Algebra.norm (RatFunc k) (Ψ z) := by
    refine GaussPencil.algebraMap_norm_eq_norm_of_span θ₀ Ψ (fun c => hcomm c) (Module.finBasis κ κᵢ) ?_ ?_ z
    · have hsub : ∀ w : κᵢ,
          Ψ w ∈ Submodule.span (RatFunc k) (Set.range (⇑Ψ ∘ ⇑(Module.finBasis κ κᵢ))) := by
        intro w
        rw [← (Module.finBasis κ κᵢ).sum_repr w, map_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [Algebra.smul_def, map_mul, hcomm,
          show θ (θ₀ ((Module.finBasis κ κᵢ).repr w i))
            = algebraMap (RatFunc k) ↥(modularFunctionFieldC k 1) (θ₀ ((Module.finBasis κ κᵢ).repr w i)) from rfl,
          ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine top_le_of_forall_pow_mem (ratFuncEquivCharLOneC k RatFunc.X)
        (GaussPencil.A4Res.adjoin_e_X_eq_top (ratFuncEquivCharLOneC k) (RatFunc k))
        (IsIntegral.of_finite (RatFunc k) _) _ fun n => ?_
      obtain ⟨s, hs⟩ := hgen
      rw [← hs, ← map_pow]
      exact hsub _
    · rw [Fintype.card_fin, hdeg, hfin]
  rw [hnorm, GaussPencil.A4Res.ord_placeOfPoint_norm_eq_sum_ord k (ratFuncEquivCharLOneC k) r hr hT (Ψ z)
    ((_root_.map_ne_zero Ψ).mpr hz) c₀]
  exact Finset.sum_congr rfl fun a _ => rfl

end GaussPencil.B6
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
section
p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.ModularCurve"

set_option autoImplicit false

namespace GaussPencil
namespace B6

noncomputable def thetaOf (k : Type*) [Field k] (r : k[X]) (hr : 0 < r.natDegree) :
    RatFunc k →ₐ[k] ↥(modularFunctionFieldC k 1) :=
  (ratFuncEquivCharLOneC k).toAlgHom.comp
    ((IntermediateField.val _).comp
      (RatFunc.algEquivOfTranscendental _ (GaussPencil.A4Res.transcendental_algebraMap r hr)).toAlgHom)

theorem thetaOf_X (k : Type*) [Field k] (r : k[X]) (hr : 0 < r.natDegree) :
    thetaOf k r hr RatFunc.X = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r) := by
  change ratFuncEquivCharLOneC k
      (((RatFunc.algEquivOfTranscendental _ (GaussPencil.A4Res.transcendental_algebraMap r hr)) RatFunc.X :
        ↥(IntermediateField.adjoin k {algebraMap k[X] (RatFunc k) r})) : RatFunc k) = _
  rw [RatFunc.algEquivOfTranscendental_X]

end GaussPencil.B6
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar ModularPolynomialData coeffMap coeffMap_single algebraMap_laurentSeries_eq_single jqModC modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC coeffMap_jqModC modularFunctionFieldFullC PlaceSpecialization.LevelOneProlongationPair.ResOne PlaceSpecialization.LevelOneProlongationPair.ResTwo PlaceSpecialization.LevelOneProlongationPair.ResOne.val PlaceSpecialization.LevelOneProlongationPair.ResTwo.val"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.ResOne LevelOneProlongationPair.ResTwo LevelOneProlongationPair.ResOne.val LevelOneProlongationPair.ResTwo.val isAlgClosed"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₂ R₂ redBar ι_coe ι R₁ redBar_residue gaussBase mem_gaussBase_iff algebraMap_mem_gaussBase_iff HasGaussTransport algGaussBase isScalarTower_gaussBase toIntegers₁ coe_toIntegers₁ gaussOrder self_mem_gaussOrder ResOne ResTwo ResOne.val ResTwo.val resBase₁ isLocalHom_resBase₁ isScalarTower_resOne resBase₁_algebraMap gaussOrderToIntegers₁ coe_gaussOrderToIntegers₁ rho₁ rho₁_apply constToGaussBase algebraMap_residueConst psiOne psiTwo psiOne_apply psiTwo_apply algebraMap_mem_integers₂_of_mem_gaussBase toIntegers₂ coe_toIntegers₂ resBase₂ isLocalHom_resBase₂ isScalarTower_resTwo resBase₂_algebraMap gaussOrderToIntegers₂ coe_gaussOrderToIntegers₂ rho₂ rho₂_apply norm_mem_and_residue_norm_eq_core"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

section RFacts2

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext R.redBar_residue

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "redBar_comp_residue"
include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.red_eq_zero_of_mem (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  rw [← R.redBar_residue, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "red_eq_zero_of_mem"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
section PhaseB

p2m_open "Polynomial AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty"

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

attribute [local instance] algGaussBase isScalarTower_gaussBase isLocalHom_resBase₁ isLocalHom_resBase₂
  isScalarTower_resOne isScalarTower_resTwo

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.psi_algebraMap_eq_theta
    (e₁ : RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] K₁) (hxV : e₁ RatFunc.X ∈ R.gaussBase K₁)
    (htr : Transcendental (ResidueField A) (IsLocalRing.residue (R.gaussBase K₁) ⟨e₁ RatFunc.X, hxV⟩))
    {T : Type*} [Field T] [Algebra (R.gaussBase K₁) T] [Algebra (ResidueField (R.gaussBase K₁)) T]
    [IsScalarTower (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) T]
    (Ψ : T →+* ↥(modularFunctionFieldC k 1))
    (hΨconst : ∀ a : A, Ψ (algebraMap (R.gaussBase K₁) T (R.constToGaussBase K₁ a))
      = algebraMap k (modularFunctionFieldC k 1) (red a))
    (θ : RatFunc k →ₐ[k] ↥(modularFunctionFieldC k 1)) (r : k[X])
    (hθ : θ RatFunc.X = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r))
    (hΨX : Ψ (algebraMap (R.gaussBase K₁) T ⟨e₁ RatFunc.X, hxV⟩)
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r))
    (c : ResidueField (R.gaussBase K₁)) :
    Ψ (algebraMap (ResidueField (R.gaussBase K₁)) T c)
      = θ (GaussPencil.Theta A (R.gaussBase K₁) (fun c => R.algebraMap_mem_gaussBase_iff c) e₁ hxV
          (fun a => R.algebraMap_residueConst a) htr R.redBar c) := by
  set te := GaussPencil.thetaEquiv A (R.gaussBase K₁) (fun c => R.algebraMap_mem_gaussBase_iff c) e₁ hxV
    (fun a => R.algebraMap_residueConst a) htr with hte
  set Θ := GaussPencil.Theta A (R.gaussBase K₁) (fun c => R.algebraMap_mem_gaussBase_iff c) e₁ hxV
    (fun a => R.algebraMap_residueConst a) htr R.redBar with hΘ
  have hres_alg : ∀ x : R.gaussBase K₁, algebraMap (ResidueField (R.gaussBase K₁)) T (IsLocalRing.residue _ x)
      = algebraMap (R.gaussBase K₁) T x :=
    fun x => (IsScalarTower.algebraMap_apply (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) T x).symm
  let φ₁ : RatFunc (ResidueField A) →+* ↥(modularFunctionFieldC k 1) :=
    (Ψ.comp (algebraMap (ResidueField (R.gaussBase K₁)) T)).comp te.toAlgHom.toRingHom
  let φ₂ : RatFunc (ResidueField A) →+* ↥(modularFunctionFieldC k 1) :=
    (θ.toRingHom.comp Θ).comp te.toAlgHom.toRingHom
  have H : φ₁ = φ₂ := by
    apply GaussPencil.B6.ratFunc_ringHom_ext
    · intro a
      obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
      have hteC : te (RatFunc.C (IsLocalRing.residue A a₀))
          = algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁)) (IsLocalRing.residue A a₀) := by
        rw [← RatFunc.algebraMap_eq_C]; exact te.commutes _
      show Ψ (algebraMap _ T (te (RatFunc.C (IsLocalRing.residue A a₀))))
        = θ (Θ (te (RatFunc.C (IsLocalRing.residue A a₀))))
      rw [hteC]
      have lhs : Ψ (algebraMap _ T (algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁)) (IsLocalRing.residue A a₀)))
          = algebraMap k (modularFunctionFieldC k 1) (red a₀) := by
        rw [R.algebraMap_residueConst a₀, hres_alg]
        exact hΨconst a₀
      have rhs : θ (Θ (algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁)) (IsLocalRing.residue A a₀)))
          = algebraMap k (modularFunctionFieldC k 1) (red a₀) := by
        rw [hΘ, GaussPencil.Theta_algebraMap, R.redBar_residue, ← RatFunc.algebraMap_eq_C]
        exact θ.commutes (red a₀)
      rw [lhs, rhs]
    · show Ψ (algebraMap _ T (te RatFunc.X)) = θ (Θ (te RatFunc.X))
      rw [hte, GaussPencil.thetaEquiv_X, hres_alg, hΨX, hΘ, GaussPencil.Theta_residue_X, hθ]
  obtain ⟨g, rfl⟩ := te.surjective c
  exact RingHom.congr_fun H g

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "psi_algebraMap_eq_theta"
open Classical in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_impl
    [FiniteDimensional K₁ (modularFunctionFieldBar (1 * q))] [Algebra.IsSeparable K₁ (modularFunctionFieldBar (1 * q))]
    [CharZero K₁] [DecidableEq k]
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (e₁ : RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] K₁) (hxV : e₁ RatFunc.X ∈ R.gaussBase K₁)
    (htr : Transcendental (ResidueField A) (IsLocalRing.residue (R.gaussBase K₁) ⟨e₁ RatFunc.X, hxV⟩))
    (r₁ r₂ : k[X]) (hr₁ : 0 < r₁.natDegree) (hr₂ : 0 < r₂.natDegree)
    (hres₁ : R.residue₁ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X), (R.mem_gaussBase_iff _).mp hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₁))
    (hres₂ : R.residue₂ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X),
        R.algebraMap_mem_integers₂_of_mem_gaussBase _ hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₂))
    (hdim₁ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne = r₁.natDegree)
    (hdim₂ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo = r₂.natDegree)
    (hu₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = (∑ a ∈ (r₁ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, hf₁⟩))
        + ∑ b ∈ (r₂ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, hf₂⟩) := by
  classical
  haveI : IsAlgClosed k := P.isAlgClosed
  have hVA : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) K₁ c ∈ R.gaussBase K₁ ↔ c ∈ A :=
    fun c => R.algebraMap_mem_gaussBase_iff c
  have hψ : ∀ a : A, algebraMap (ResidueField A) (ResidueField (R.gaussBase K₁)) (IsLocalRing.residue A a)
      = IsLocalRing.residue (R.gaussBase K₁) ⟨algebraMap (AlgebraicClosure ℚ) K₁ a, (hVA a).mpr a.2⟩ :=
    fun a => R.algebraMap_residueConst a
  haveI hfinOne : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResOne :=
    Module.finite_of_finrank_pos (by rw [hdim₁]; exact hr₁)
  haveI hfinTwo : FiniteDimensional (ResidueField (R.gaussBase K₁)) R.ResTwo :=
    Module.finite_of_finrank_pos (by rw [hdim₂]; exact hr₂)

  obtain ⟨hN, hres⟩ := R.norm_mem_and_residue_norm_eq_core y f hy₁ hf₁ hy₂ hf₂ hyint hfint hjS hjqS hspan
    (by rw [hdim₁]; exact hr₁) (by rw [hdim₂]; exact hr₂) hdeg hgen₁ hgen₂
  set fS : R.gaussOrder K₁ y f := ⟨f, R.self_mem_gaussOrder y f⟩ with hfS
  set NS := Algebra.norm (R.gaussBase K₁) fS with hNS

  have hf0 : f ≠ 0 := by
    intro h
    apply hu₁
    have : (⟨f, hf₁⟩ : R.R₁.integers) = 0 := Subtype.ext h
    rw [this, map_zero]
  have hρ₁ : ResOne.val R (R.rho₁ K₁ hy₁ hf₁ fS) = R.R₁.residue ⟨f, hf₁⟩ := by
    rw [rho₁_apply, show R.gaussOrderToIntegers₁ K₁ hy₁ hf₁ fS = ⟨f, hf₁⟩ from Subtype.ext (R.coe_gaussOrderToIntegers₁ hy₁ hf₁ fS)]
  have hρ₂ : ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ fS) = R.R₂.residue ⟨f, hf₂⟩ := by
    rw [rho₂_apply, show R.gaussOrderToIntegers₂ K₁ hy₂ hf₂ fS = ⟨f, hf₂⟩ from Subtype.ext (R.coe_gaussOrderToIntegers₂ hy₂ hf₂ fS)]
  have hρ₁0 : R.rho₁ K₁ hy₁ hf₁ fS ≠ 0 := fun h => hu₁ (by rw [← hρ₁, h]; rfl)
  have hρ₂0 : R.rho₂ K₁ hy₂ hf₂ fS ≠ 0 := fun h => hu₂ (by rw [← hρ₂, h]; rfl)
  have hn₁ : Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₁ K₁ hy₁ hf₁ fS) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hρ₁0
  have hn₂ : Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₂ K₁ hy₂ hf₂ fS) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hρ₂0
  have hNS0 : IsLocalRing.residue (R.gaussBase K₁) NS ≠ 0 := by
    rw [hres]; exact mul_ne_zero hn₁ hn₂

  obtain ⟨c, hc, Pp, Qp, hP, hQ, hpres⟩ :=
    GaussPencil.exists_eq_e₁_C_mul_div A (R.gaussBase K₁) hVA e₁ hxV hψ htr NS hNS0
  have hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0 := fun a ha => R.red_eq_zero_of_mem a ha

  rw [← GaussPencil.B14.mapDomain_spValue_congr_restrict_placeOfPoint e₁ A red D c₀]
  rw [show (fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) =>
        GaussPencil.B14.spValue A red
          ((Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b)).symm (W.restrict K₁)))
      = (fun v : Place (AlgebraicClosure ℚ) K₁ => GaussPencil.B14.spValue A red
          ((Place.congrEquiv e₁.toRingEquiv (fun b => e₁.commutes b)).symm v))
        ∘ (fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) => W.restrict K₁) from rfl,
    Finsupp.mapDomain_comp]
  have hD₁ : ∀ v, Finsupp.mapDomain
        (fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) => W.restrict K₁) D v
      = v.ord (e₁ (RatFunc.C (c : AlgebraicClosure ℚ)
          * (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
                (Pp.map (algebraMap A (AlgebraicClosure ℚ)))
              / algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
                (Qp.map (algebraMap A (AlgebraicClosure ℚ)))))) := by
    intro v
    rw [GaussPencil.B14.mapDomain_restrict_eq e₁ D f hf0 hD v, hN]
    rw [show algebraMap (R.gaussBase K₁) K₁ NS = (NS : K₁) from rfl, hpres, RatFunc.algebraMap_eq_C]
  rw [GaussPencil.B14.mapDomain_spValue_congr_symm_eq_ord e₁ A red hred c hc Pp Qp hP hQ _ hD₁ (placeOfPoint k c₀)]

  obtain ⟨hv, hΘ⟩ := GaussPencil.Theta_residue_e₁_C_mul_div A (R.gaussBase K₁) hVA e₁ hxV hψ htr R.redBar
    c Pp Qp hP hQ
  rw [R.redBar_residue, R.redBar_comp_residue] at hΘ
  have hNS' : (⟨_, hv⟩ : R.gaussBase K₁) = NS := Subtype.ext hpres.symm
  rw [hNS'] at hΘ
  rw [← hΘ, hres, map_mul]
  set Θ := GaussPencil.Theta A (R.gaussBase K₁) hVA e₁ hxV hψ htr R.redBar with hΘdef
  have hΘ₁ : Θ (Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₁ K₁ hy₁ hf₁ fS)) ≠ 0 := (_root_.map_ne_zero Θ).mpr hn₁
  have hΘ₂ : Θ (Algebra.norm (ResidueField (R.gaussBase K₁)) (R.rho₂ K₁ hy₂ hf₂ fS)) ≠ 0 := (_root_.map_ne_zero Θ).mpr hn₂
  rw [(placeOfPoint k c₀).ord_mul hΘ₁ hΘ₂]

  set θ₁ := GaussPencil.B6.thetaOf k r₁ hr₁ with hθ₁def
  set θ₂ := GaussPencil.B6.thetaOf k r₂ hr₂ with hθ₂def
  have hθ₁ : θ₁ RatFunc.X = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₁) := GaussPencil.B6.thetaOf_X k r₁ hr₁
  have hθ₂ : θ₂ RatFunc.X = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₂) := GaussPencil.B6.thetaOf_X k r₂ hr₂

  have hx₁ : R.toIntegers₁ K₁ ⟨e₁ RatFunc.X, hxV⟩
      = ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X), (R.mem_gaussBase_iff _).mp hxV⟩ :=
    Subtype.ext (R.coe_toIntegers₁ _)
  have hx₂ : R.toIntegers₂ K₁ ⟨e₁ RatFunc.X, hxV⟩
      = ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X), R.algebraMap_mem_integers₂_of_mem_gaussBase _ hxV⟩ :=
    Subtype.ext (R.coe_toIntegers₂ _)
  have hcomm₁ : ∀ c, R.psiOne (algebraMap (ResidueField (R.gaussBase K₁)) R.ResOne c) = θ₁ (Θ c) := by
    refine R.psi_algebraMap_eq_theta e₁ hxV htr R.psiOne (fun a => ?_) θ₁ r₁ hθ₁ ?_
    · have hca : R.constToGaussBase K₁ a = ⟨algebraMap (AlgebraicClosure ℚ) K₁ a,
          (R.algebraMap_mem_gaussBase_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := rfl
      show R.psiOne (R.resBase₁ K₁ (R.constToGaussBase K₁ a)) = _
      rw [hca, R.resBase₁_algebraMap a]
      show R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a)) = _
      rw [R.ι_algebraMap, R.redBar_residue]
    · show R.ι (R.R₁.residue (R.toIntegers₁ K₁ ⟨e₁ RatFunc.X, hxV⟩)) = _
      rw [hx₁]
      exact hres₁
  have hcomm₂ : ∀ c, R.psiTwo (algebraMap (ResidueField (R.gaussBase K₁)) R.ResTwo c) = θ₂ (Θ c) := by
    refine R.psi_algebraMap_eq_theta e₁ hxV htr R.psiTwo (fun a => ?_) θ₂ r₂ hθ₂ ?_
    · have hca : R.constToGaussBase K₁ a = ⟨algebraMap (AlgebraicClosure ℚ) K₁ a,
          (R.algebraMap_mem_gaussBase_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := rfl
      show R.psiTwo (R.resBase₂ K₁ (R.constToGaussBase K₁ a)) = _
      rw [hca, R.resBase₂_algebraMap a]
      show R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a)) = _
      rw [R.ι_algebraMap, R.redBar_residue]
    · show R.ι (R.R₂.residue (R.toIntegers₂ K₁ ⟨e₁ RatFunc.X, hxV⟩)) = _
      rw [hx₂]
      exact hres₂
  have hgenΨ₁ : (ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) ∈ Set.range R.psiOne := by
    obtain ⟨s, hs⟩ := hgen₁
    exact ⟨R.rho₁ K₁ hy₁ hf₁ s, R.ι_eq_ratFuncEquivCharLOneC_X _ hs⟩
  have hgenΨ₂ : (ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) ∈ Set.range R.psiTwo := by
    obtain ⟨s, hs⟩ := hgen₂
    exact ⟨R.rho₂ K₁ hy₂ hf₂ s, R.ι_eq_ratFuncEquivCharLOneC_X _ hs⟩
  have h₁ := GaussPencil.B6.ord_map_norm_eq_sum_ord k Θ θ₁ r₁ hr₁ hθ₁ R.psiOne hcomm₁ hgenΨ₁ hdim₁
    (R.rho₁ K₁ hy₁ hf₁ fS) hρ₁0 c₀
  have h₂ := GaussPencil.B6.ord_map_norm_eq_sum_ord k Θ θ₂ r₂ hr₂ hθ₂ R.psiTwo hcomm₂ hgenΨ₂ hdim₂
    (R.rho₂ K₁ hy₂ hf₂ fS) hρ₂0 c₀
  have hΨf₁ : R.psiOne (R.rho₁ K₁ hy₁ hf₁ fS) = R.residue₁ ⟨f, hf₁⟩ := by
    rw [psiOne_apply, hρ₁]; rfl
  have hΨf₂ : R.psiTwo (R.rho₂ K₁ hy₂ hf₂ fS) = R.residue₂ ⟨f, hf₂⟩ := by
    rw [psiTwo_apply, hρ₂]; rfl
  rw [h₁, h₂, hΨf₁, hΨf₂]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "sum_filter_value_eq_sum_roots_add_impl"
end PhaseB
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.GaussPencil"

open Polynomial in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
    [Algebra K₁ (modularFunctionFieldBar (1 * q))]
    [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]
    (R : P.LevelOneProlongationPair) [R.HasGaussTransport K₁]
    [FiniteDimensional K₁ (modularFunctionFieldBar (1 * q))] [Algebra.IsSeparable K₁ (modularFunctionFieldBar (1 * q))]
    [CharZero K₁] [DecidableEq k]
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : PlaceSpecialization.jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : PlaceSpecialization.jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (e₁ : RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] K₁) (hxV : e₁ RatFunc.X ∈ R.gaussBase K₁)
    (htr : Transcendental (ResidueField A) (IsLocalRing.residue (R.gaussBase K₁) ⟨e₁ RatFunc.X, hxV⟩))
    (r₁ r₂ : k[X]) (hr₁ : 0 < r₁.natDegree) (hr₂ : 0 < r₂.natDegree)
    (hres₁ : R.residue₁ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X), (R.mem_gaussBase_iff _).mp hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₁))
    (hres₂ : R.residue₂ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X),
        R.algebraMap_mem_integers₂_of_mem_gaussBase _ hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₂))
    (hdim₁ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne = r₁.natDegree)
    (hdim₂ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo = r₂.natDegree)
    (hu₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = (∑ a ∈ (r₁ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, hf₁⟩))
        + ∑ b ∈ (r₂ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, hf₂⟩) :=
  R.sum_filter_value_eq_sum_roots_add_impl y f hy₁ hf₁ hy₂ hf₂ hyint hfint hjS hjqS hspan hdeg hgen₁ hgen₂ e₁ hxV htr r₁ r₂ hr₁ hr₂ hres₁ hres₂ hdim₁ hdim₂ hu₁ hu₂ D hD c₀

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add (solution)
