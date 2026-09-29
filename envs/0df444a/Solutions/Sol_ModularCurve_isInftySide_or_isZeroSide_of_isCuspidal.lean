-- Prove2me | solution 1 for ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dec8eef7-7724-5a6b-ac10-b8fb296a9b01

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_natDegree_kroneckerRemainder_le
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb existsUnique_kroneckerRemainder natDegree_kroneckerRemainder_le deg_eq_one_modularFunctionFieldBar exists_isFrickeAutFull_of_neZero eq_cuspInftyBar_or_eq_cuspZeroBar"
p2m_open "ModularCurve"

theorem order_coeffEmb_eq (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) :
    (coeffEmb L x).order = x.order := by
  by_cases hx : x = 0
  · subst hx; simp
  have h1 : (coeffEmb L x).coeff x.order ≠ 0 := by
    rw [coeffEmb_coeff]
    exact (map_ne_zero (algebraMap ℚ L)).mpr ((HahnSeries.coeff_order_eq_zero.not.mpr) hx)
  have hne : coeffEmb L x ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have h2 := (HahnSeries.coeff_order_eq_zero.not.mpr) hne
  rw [coeffEmb_coeff, HahnSeries.coeff_eq_zero_of_lt_order h, map_zero] at h2
  exact h2 rfl

theorem coeff_qExpand_jq_of_lt (N : ℕ) [NeZero N] {m : ℤ} (hm : m < -(N : ℤ)) :
    (qExpand ℚ N jq).coeff m = 0 := by
  by_cases hd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hd
    rw [qExpand_coeff_mul]
    apply coeff_jq_of_lt
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    by_contra! hk
    nlinarith
  · exact qExpand_coeff_of_not_dvd (R := ℚ) (N := N) (f := jq) hd

theorem coeff_qExpand_jq_neg (N : ℕ) [NeZero N] : (qExpand ℚ N jq).coeff (-(N : ℤ)) = 1 := by
  rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jq_neg_one]

theorem order_qExpand_jq (N : ℕ) [NeZero N] : (qExpand ℚ N jq).order = -(N : ℤ) := by
  have h1 : (qExpand ℚ N jq).coeff (-(N : ℤ)) ≠ 0 := by rw [coeff_qExpand_jq_neg]; exact one_ne_zero
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have hne : qExpand ℚ N jq ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) hne (coeff_qExpand_jq_of_lt N h)

theorem order_qExpand_jq_sub_pow (N : ℕ) [NeZero N] (h : qExpand ℚ N jq - jq ^ N ≠ 0) :
    -(N : ℤ) < (qExpand ℚ N jq - jq ^ N).order := by
  by_contra! hle
  apply (HahnSeries.coeff_order_eq_zero.not.mpr) h
  set m := (qExpand ℚ N jq - jq ^ N).order with hm
  rw [HahnSeries.coeff_sub]
  rcases hle.lt_or_eq with hlt | heq
  · rw [coeff_qExpand_jq_of_lt N hlt, coeff_jq_pow_of_lt hlt, sub_zero]
  · rw [heq, coeff_qExpand_jq_neg, coeff_jq_pow_self, sub_self]

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb existsUnique_kroneckerRemainder natDegree_kroneckerRemainder_le deg_eq_one_modularFunctionFieldBar exists_isFrickeAutFull_of_neZero eq_cuspInftyBar_or_eq_cuspZeroBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsCuspidal IsInftySide IsCuspidal' IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

section qorders

theorem qSeriesBar_jFun :
    qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jFun (q := q))
      = coeffEmb (AlgebraicClosure ℚ) jq := rfl

theorem qSeriesBar_jqFun :
    qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jqFun (q := q))
      = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := rfl

theorem order_qSeriesBar_jFun :
    (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jFun (q := q))).order = -1 := by
  rw [qSeriesBar_jFun]; exact order_coeffEmb_jq _

theorem order_qSeriesBar_jqFun :
    (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jqFun (q := q))).order
      = -((1 * q : ℕ) : ℤ) := by
  rw [qSeriesBar_jqFun, order_coeffEmb_eq, order_qExpand_jq]

theorem jFun_ne_zero : (jFun (q := q)) ≠ 0 := by
  intro h
  have := order_qSeriesBar_jFun (q := q)
  rw [h, qSeriesBar_zero, HahnSeries.order_zero] at this
  exact absurd this (by norm_num)

theorem jqFun_ne_zero : (jqFun (q := q)) ≠ 0 := by
  intro h
  have := order_qSeriesBar_jqFun (q := q)
  rw [h, qSeriesBar_zero, HahnSeries.order_zero] at this
  have hq : (0 : ℤ) < ((1 * q : ℕ) : ℤ) := by
    have := (Fact.out : q.Prime).pos; exact_mod_cast (by omega : 0 < 1 * q)
  omega

theorem order_qSeriesBar_tInfty :
    (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tInfty (q := q))).order = 0 := by
  have hj := qSeriesBar_ne_zero (L := AlgebraicClosure ℚ) (jFun_ne_zero (q := q))
  have hjq := qSeriesBar_ne_zero (L := AlgebraicClosure ℚ) (jqFun_ne_zero (q := q))
  rw [tInfty, qSeriesBar_div, qSeriesBar_pow, order_div_of_ne_zero_bar hjq (pow_ne_zero _ hj),
    order_pow_of_ne_zero_bar hj, order_qSeriesBar_jFun, order_qSeriesBar_jqFun]
  push_cast; ring

theorem order_qSeriesBar_tZero :
    (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tZero (q := q))).order
      = ((1 * q : ℕ) : ℤ) ^ 2 - 1 := by
  have hj := qSeriesBar_ne_zero (L := AlgebraicClosure ℚ) (jFun_ne_zero (q := q))
  have hjq := qSeriesBar_ne_zero (L := AlgebraicClosure ℚ) (jqFun_ne_zero (q := q))
  rw [tZero, qSeriesBar_div, qSeriesBar_pow, order_div_of_ne_zero_bar hj (pow_ne_zero _ hjq),
    order_pow_of_ne_zero_bar hjq, order_qSeriesBar_jFun, order_qSeriesBar_jqFun]
  push_cast; ring

theorem order_qSeriesBar_tInfty_sub_one (h : tInfty (q := q) - 1 ≠ 0) :
    0 < (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tInfty (q := q) - 1)).order := by
  set n : ℕ := 1 * q with hn
  set L := AlgebraicClosure ℚ
  have hj : coeffEmb L jq ≠ 0 := qSeriesBar_ne_zero (L := L) (jFun_ne_zero (q := q))
  have hjn : (coeffEmb L jq) ^ n ≠ 0 := pow_ne_zero _ hj

  have e : qSeriesBar L (modularFunctionFieldBar (1 * q)) (tInfty (q := q) - 1)
      = coeffEmb L (qExpand ℚ n jq - jq ^ n) / (coeffEmb L jq) ^ n := by
    rw [qSeriesBar_sub, qSeriesBar_one, tInfty, qSeriesBar_div, qSeriesBar_pow, qSeriesBar_jFun,
      qSeriesBar_jqFun, map_sub, map_pow, sub_div, div_self hjn]
  have hD : coeffEmb L (qExpand ℚ n jq - jq ^ n) ≠ 0 := by
    intro h0
    apply h
    have : qSeriesBar L (modularFunctionFieldBar (1 * q)) (tInfty (q := q) - 1) = 0 := by
      rw [e, h0, zero_div]
    exact qSeriesBar_eq_zero_iff.mp this
  have hD' : qExpand ℚ n jq - jq ^ n ≠ 0 := fun h0 => hD (by rw [h0, map_zero])
  rw [e, order_div_of_ne_zero_bar hD hjn, order_pow_of_ne_zero_bar hj, order_coeffEmb_eq, order_coeffEmb_jq]
  have := order_qExpand_jq_sub_pow n hD'
  push_cast at this ⊢
  linarith

end qorders

theorem residue_cuspInftyBar_eq_zero_of_order_ne_zero
    {g : modularFunctionFieldBar (1 * q)} (hg : g ∈ (cuspInftyBar (1 * q)).toValuationSubring)
    (hord : (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) g).order ≠ 0) :
    IsLocalRing.residue (cuspInftyBar (1 * q)).toValuationSubring ⟨g, hg⟩ = 0 := by
  by_cases hg0 : g = 0
  · subst hg0
    exact map_zero _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hord ((isUnit_qIntegersBar_iff (L := AlgebraicClosure ℚ)
    (x := (⟨g, hg⟩ : qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) hg0).mp hu)

theorem isCuspidal_cuspInftyBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsCuspidal (cuspInftyBar (1 * q)) := by
  intro a
  by_contra h
  push_neg at h
  have hj : (jFun (q := q)) ∉ (cuspInftyBar (1 * q)).toValuationSubring :=
    notMem_qIntegersBar_of_order_eq_neg_one (order_qSeriesBar_jFun (q := q))
  apply hj
  set c := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) with hc
  have hcm : c ∈ (cuspInftyBar (1 * q)).toValuationSubring := (cuspInftyBar (1 * q)).algebraMap_mem' _
  have hdm : jFun (q := q) - c ∈ (cuspInftyBar (1 * q)).toValuationSubring := by
    by_cases h0 : jFun (q := q) - c = 0
    · rw [h0]; exact zero_mem _
    · exact (cuspInftyBar (1 * q)).mem_of_ord_nonneg h0 h.le
  have := add_mem hdm hcm
  rwa [sub_add_cancel] at this

theorem isInftySide_cuspInftyBar'_hasValue :
    (cuspInftyBar (1 * q)).HasValue (tInfty (q := q)) ((1 : A) : AlgebraicClosure ℚ) := by
  have hmem : tInfty (q := q) ∈ (cuspInftyBar (1 * q)).toValuationSubring := by
    show 0 ≤ (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tInfty (q := q))).order
    rw [order_qSeriesBar_tInfty]
  refine ⟨hmem, ?_⟩
  rw [OneMemClass.coe_one, map_one]
  by_cases h1 : tInfty (q := q) - 1 = 0
  · have : (⟨tInfty (q := q), hmem⟩ : (cuspInftyBar (1 * q)).toValuationSubring) = 1 :=
      Subtype.ext (sub_eq_zero.mp h1)
    rw [this, map_one]
  have hsmem : tInfty (q := q) - 1 ∈ (cuspInftyBar (1 * q)).toValuationSubring := by
    show 0 ≤ (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tInfty (q := q) - 1)).order
    exact (order_qSeriesBar_tInfty_sub_one h1).le
  have hres0 := residue_cuspInftyBar_eq_zero_of_order_ne_zero hsmem (order_qSeriesBar_tInfty_sub_one h1).ne'
  have e : (⟨tInfty (q := q), hmem⟩ : (cuspInftyBar (1 * q)).toValuationSubring)
      = ⟨tInfty (q := q) - 1, hsmem⟩ + 1 := Subtype.ext (by simp)
  rw [e, map_add, map_one, hres0, zero_add]

theorem isInftySide_cuspInftyBar' (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsInftySide (cuspInftyBar (1 * q)) :=
  ⟨isCuspidal_cuspInftyBar P, 1, map_one red, isInftySide_cuspInftyBar'_hasValue⟩

theorem eq_zero_of_hasValue_tZero_cuspInftyBar {τ : A}
    (hval : (cuspInftyBar (1 * q)).HasValue (tZero (q := q)) (τ : AlgebraicClosure ℚ)) : τ = 0 := by
  have hpos : 0 < (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (tZero (q := q))).order := by
    rw [order_qSeriesBar_tZero]
    have hq : (2 : ℤ) ≤ ((1 * q : ℕ) : ℤ) := by
      have := (Fact.out : q.Prime).two_le; exact_mod_cast (by omega : 2 ≤ 1 * q)
    nlinarith
  have hres0 := residue_cuspInftyBar_eq_zero_of_order_ne_zero hval.mem hpos.ne'
  have hval' := hval.residue_eq
  rw [hres0, eq_comm, map_eq_zero] at hval'
  exact_mod_cast hval'

theorem not_isZeroSide_cuspInftyBar' (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    ¬ P.IsZeroSide (cuspInftyBar (1 * q)) := by
  rintro ⟨-, τ, hτ, hval⟩
  rw [eq_zero_of_hasValue_tZero_cuspInftyBar hval, map_zero] at hτ
  exact zero_ne_one hτ

theorem isFrickeAutFull_one_mul :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (ModularCurve.exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jFun : frickeInvolutionBar (1 * q) (jFun (q := q)) = jqFun (q := q) := by
  have e1 : jFun (q := q) = ⟨coeffEmb (AlgebraicClosure ℚ)
      ((⟨jq, jq_mem_full (1 * q)⟩ : modularFunctionFieldFull (1 * q)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨jq, jq_mem_full (1 * q)⟩ : modularFunctionFieldFull (1 * q)).2⟩ := rfl
  rw [frickeInvolutionBar_def, e1, geomAut_coeffEmb]
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull (1 * q) ⟨jq, jq_mem_full (1 * q)⟩ :
      modularFunctionFieldFull (1 * q)) : LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  have e2 : (⟨jq, jq_mem_full (1 * q)⟩ : modularFunctionFieldFull (1 * q))
      = ⟨qExpand ℚ 1 jq, jqd_mem_full (1 * q) (one_dvd _)⟩ := Subtype.ext (qExpand_one_apply jq).symm
  rw [e2, isFrickeAutFull_one_mul (q := q) 1 (1 * q) (one_mul _) inferInstance inferInstance]

theorem frickeInvolutionBar_jqFun : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) := by
  have e1 : jqFun (q := q) = ⟨coeffEmb (AlgebraicClosure ℚ)
      ((⟨qExpand ℚ (1 * q) jq, jqd_mem_full (1 * q) (dvd_refl (1 * q))⟩ : modularFunctionFieldFull (1 * q)) :
        LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (1 * q) (dvd_refl (1 * q))⟩ : modularFunctionFieldFull (1 * q)).2⟩ := rfl
  rw [frickeInvolutionBar_def, e1, geomAut_coeffEmb]
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull (1 * q)
      ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (1 * q) (dvd_refl (1 * q))⟩ : modularFunctionFieldFull (1 * q)) :
        LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) jq
  have e2 : (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (1 * q) (dvd_refl (1 * q))⟩ : modularFunctionFieldFull (1 * q))
      = ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (1 * q) (dvd_refl _)⟩ := rfl
  rw [e2, isFrickeAutFull_one_mul (q := q) (1 * q) 1 (mul_one _) inferInstance inferInstance]
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = _
  rw [qExpand_one_apply]

theorem frickeInvolutionBar_tInfty : frickeInvolutionBar (1 * q) (tInfty (q := q)) = tZero (q := q) := by
  rw [tInfty, tZero, map_div₀, map_pow, frickeInvolutionBar_jFun, frickeInvolutionBar_jqFun]

theorem frickeInvolutionBar_tZero : frickeInvolutionBar (1 * q) (tZero (q := q)) = tInfty (q := q) := by
  rw [tInfty, tZero, map_div₀, map_pow, frickeInvolutionBar_jFun, frickeInvolutionBar_jqFun]

end ModularCurve.PlaceSpecialization

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.HasValue Place Place.ord_smul Place.deg_eq_one_iff_surjective_algebraMap_residueField Place.HasValue.add Place.HasValue.neg Place.HasValue.sub Place.HasValue.pow Place.hasValue_intCast Place.hasValue_zero' Place.HasValue.eval₂_int Place.HasValue.eval₂_bivariate Place.hasValue_zero_of_ord_pos Place.ord_pos_of_hasValue_zero'"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField deg ord ord_coe_unit smulRingEquiv coe_smulRingEquiv_apply smul_toValuationSubring ord_smul smulResidueAlgEquiv algebraMap_mem' toValuationSubring ord_nonneg_of_mem mem_of_ord_nonneg deg_eq_one_iff_surjective_algebraMap_residueField HasValue.add HasValue.neg HasValue.sub HasValue.pow hasValue_intCast hasValue_zero' HasValue.eval₂_int HasValue.eval₂_bivariate hasValue_zero_of_ord_pos ord_pos_of_hasValue_zero'"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mem residue_eq mul ne_zero inv unique add neg sub pow eval₂_int eval₂_bivariate" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem _root_.AlgebraicCurve.Place.HasValue.map_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F} {g : F} {a : K}
    (σ : F ≃ₐ[K] F) (h : v.HasValue g a) : (σ • v).HasValue (σ g) a := by
  obtain ⟨hm, hr⟩ := h
  have hmem : σ g ∈ (σ • v).toValuationSubring := by
    rw [smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul σ g v.toValuationSubring hm
  refine ⟨hmem, ?_⟩
  have hx : (⟨σ g, hmem⟩ : (σ • v).toValuationSubring) = smulRingEquiv σ v.toValuationSubring ⟨g, hm⟩ :=
    Subtype.ext (coe_smulRingEquiv_apply σ v.toValuationSubring ⟨g, hm⟩).symm
  rw [hx]
  have hc := (smulResidueAlgEquiv (σ := σ) (v := v)).commutes a
  rw [← hr] at hc
  rw [← hc]
  show _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.map_algEquiv"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem _root_.AlgebraicCurve.Place.HasValue.of_map_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F} {g : F} {a : K}
    (σ : F ≃ₐ[K] F) (h : (σ • v).HasValue (σ g) a) : v.HasValue g a := by
  have := h.map_algEquiv σ⁻¹
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.of_map_algEquiv"
end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb existsUnique_kroneckerRemainder natDegree_kroneckerRemainder_le deg_eq_one_modularFunctionFieldBar exists_isFrickeAutFull_of_neZero eq_cuspInftyBar_or_eq_cuspZeroBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsCuspidal IsInftySide IsCuspidal' IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem isCuspidal'_cuspZeroBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    IsCuspidal' P (cuspZeroBar (1 * q)) := by
  intro a
  have e : jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
      = frickeInvolutionBar (1 * q) (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) := by
    rw [map_sub, frickeInvolutionBar_jFun, AlgEquiv.commutes]
  rw [cuspZeroBar_def, e, Place.ord_smul]
  exact isCuspidal_cuspInftyBar P a

theorem isZeroSide_cuspZeroBar' (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsZeroSide (cuspZeroBar (1 * q)) := by
  refine ⟨isCuspidal'_cuspZeroBar P, 1, map_one red, ?_⟩
  rw [cuspZeroBar_def, ← frickeInvolutionBar_tInfty]
  exact (isInftySide_cuspInftyBar'_hasValue (q := q) (A := A)).map_algEquiv _

theorem not_isInftySide_cuspZeroBar' (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    ¬ P.IsInftySide (cuspZeroBar (1 * q)) := by
  rintro ⟨-, τ, hτ, hval⟩
  rw [cuspZeroBar_def, ← frickeInvolutionBar_tZero] at hval
  rw [eq_zero_of_hasValue_tZero_cuspInftyBar (hval.of_map_algEquiv _), map_zero] at hτ
  exact zero_ne_one hτ

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb existsUnique_kroneckerRemainder natDegree_kroneckerRemainder_le deg_eq_one_modularFunctionFieldBar exists_isFrickeAutFull_of_neZero eq_cuspInftyBar_or_eq_cuspZeroBar"
p2m_open "ModularCurve"

theorem eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_neg_level (N : ℕ) [Fact N.Prime]
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hW : W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) < 0) :
    W = cuspInftyBar N ∨ W = cuspZeroBar N := by
  refine ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar N W ?_
  intro hmem
  exact (not_le.mpr hW) (W.ord_nonneg_of_mem hmem)

theorem eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg {q : ℕ} [Fact q.Prime]
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : W.ord (PlaceSpecialization.jFun (q := q)) < 0) :
    W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  have key : ∀ (N : ℕ) (hN : Fact N.Prime), N = q →
      ∀ (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) < 0 →
        W = cuspInftyBar N ∨ W = cuspZeroBar N := by
    intro N hN _ W hW
    exact eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_neg_level N W hW
  have h1q : Fact (1 * q).Prime := ⟨by rw [Nat.one_mul]; exact Fact.out⟩
  exact key (1 * q) h1q (Nat.one_mul q) W hW

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsCuspidal IsInftySide IsCuspidal' IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime]

theorem ord_cuspInftyBar_jqFun_neg : (cuspInftyBar (1 * q)).ord (jqFun (q := q)) < 0 := by
  have hnm : jqFun (q := q) ∉ (cuspInftyBar (1 * q)).toValuationSubring := by
    show ¬ (0 ≤ (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jqFun (q := q))).order)
    rw [order_qSeriesBar_jqFun]
    have : (0 : ℤ) < ((1 * q : ℕ) : ℤ) := by
      have := (Fact.out : q.Prime).pos; exact_mod_cast (by omega : 0 < 1 * q)
    omega
  by_contra! h
  exact hnm ((cuspInftyBar (1 * q)).mem_of_ord_nonneg jqFun_ne_zero h)

theorem ord_cuspInftyBar_jFun_neg : (cuspInftyBar (1 * q)).ord (jFun (q := q)) < 0 := by
  have hnm : jFun (q := q) ∉ (cuspInftyBar (1 * q)).toValuationSubring :=
    notMem_qIntegersBar_of_order_eq_neg_one (order_qSeriesBar_jFun (q := q))
  by_contra! h
  exact hnm ((cuspInftyBar (1 * q)).mem_of_ord_nonneg jFun_ne_zero h)

theorem ord_cuspZeroBar_jFun_neg : (cuspZeroBar (1 * q)).ord (jFun (q := q)) < 0 := by
  rw [cuspZeroBar_def, ← frickeInvolutionBar_jqFun, Place.ord_smul]
  exact ord_cuspInftyBar_jqFun_neg

theorem ord_cuspZeroBar_jqFun_neg : (cuspZeroBar (1 * q)).ord (jqFun (q := q)) < 0 := by
  rw [cuspZeroBar_def, ← frickeInvolutionBar_jFun, Place.ord_smul]
  exact ord_cuspInftyBar_jFun_neg

theorem cuspInftyBar_ne_cuspZeroBar : cuspInftyBar (1 * q) ≠ cuspZeroBar (1 * q) := by
  intro h
  have h1 : (cuspInftyBar (1 * q)).HasValue (tInfty (q := q))
      ((1 : (⊤ : ValuationSubring (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ) :=
    isInftySide_cuspInftyBar'_hasValue (A := ⊤)
  rw [h, cuspZeroBar_def, ← frickeInvolutionBar_tZero] at h1
  have := eq_zero_of_hasValue_tZero_cuspInftyBar (A := ⊤) (h1.of_map_algEquiv _)
  exact one_ne_zero this

theorem frickeInvolutionBar_smul_cuspZeroBar :
    frickeInvolutionBar (1 * q) • cuspZeroBar (1 * q) = cuspInftyBar (1 * q) := by
  have hpole : (frickeInvolutionBar (1 * q) • cuspZeroBar (1 * q)).ord (jFun (q := q)) < 0 := by
    rw [← frickeInvolutionBar_jqFun, Place.ord_smul]
    exact ord_cuspZeroBar_jqFun_neg
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg _ hpole with h | h
  · exact h
  · exfalso

    rw [cuspZeroBar_def] at h
    have h' : frickeInvolutionBar (1 * q) • cuspInftyBar (1 * q) = cuspInftyBar (1 * q) :=
      MulAction.injective (frickeInvolutionBar (1 * q)) h
    exact cuspInftyBar_ne_cuspZeroBar (q := q) (by rw [cuspZeroBar_def, h'])

theorem eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jqFun_neg
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : W.ord (jqFun (q := q)) < 0) :
    W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by

  have hpole : (frickeInvolutionBar (1 * q) • W).ord (jFun (q := q)) < 0 := by
    rw [← frickeInvolutionBar_jqFun, Place.ord_smul]; exact hW
  rcases eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg _ hpole with h | h
  ·
    right
    rw [← frickeInvolutionBar_smul_cuspZeroBar] at h
    exact MulAction.injective (frickeInvolutionBar (1 * q)) h
  ·
    left
    rw [cuspZeroBar_def] at h
    exact MulAction.injective (frickeInvolutionBar (1 * q)) h

theorem jFun_mem_and_jqFun_mem_of_ne_cusps
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h1 : W ≠ cuspInftyBar (1 * q)) (h2 : W ≠ cuspZeroBar (1 * q)) :
    jFun (q := q) ∈ W.toValuationSubring ∧ jqFun (q := q) ∈ W.toValuationSubring := by
  constructor
  · refine W.mem_of_ord_nonneg jFun_ne_zero (not_lt.mp fun h => ?_)
    rcases eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg W h with e | e
    exacts [h1 e, h2 e]
  · refine W.mem_of_ord_nonneg jqFun_ne_zero (not_lt.mp fun h => ?_)
    rcases eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jqFun_neg W h with e | e
    exacts [h1 e, h2 e]

end PlaceSpecialization

end ModularCurve

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb existsUnique_kroneckerRemainder natDegree_kroneckerRemainder_le deg_eq_one_modularFunctionFieldBar exists_isFrickeAutFull_of_neZero eq_cuspInftyBar_or_eq_cuspZeroBar"
p2m_open "ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsCuspidal IsInftySide IsCuspidal' IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"

section hasValue
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

private theorem _root_.AlgebraicCurve.Place.HasValue.add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.add" "AlgebraicCurve.Place.HasValue.add"
private theorem _root_.AlgebraicCurve.Place.HasValue.neg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.neg" "AlgebraicCurve.Place.HasValue.neg"
private theorem _root_.AlgebraicCurve.Place.HasValue.sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h.add h'.neg

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.sub" "AlgebraicCurve.Place.HasValue.sub"
private theorem _root_.AlgebraicCurve.Place.HasValue.pow {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.pow" "AlgebraicCurve.Place.HasValue.pow"
private theorem _root_.AlgebraicCurve.Place.hasValue_intCast (n : ℤ) : v.HasValue (n : F) (n : K) := by
  simpa using v.hasValue_algebraMap (n : K)

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.hasValue_intCast" "AlgebraicCurve.Place.hasValue_intCast"
private theorem _root_.AlgebraicCurve.Place.hasValue_zero' : v.HasValue (0 : F) (0 : K) := by
  simpa using v.hasValue_algebraMap (0 : K)

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.hasValue_zero'" "AlgebraicCurve.Place.hasValue_zero'"

private theorem _root_.AlgebraicCurve.Place.HasValue.eval₂_int {g : F} {a : K} (h : v.HasValue g a) (c : Polynomial ℤ) :
    v.HasValue (c.eval₂ (Int.castRingHom F) g) (c.eval₂ (Int.castRingHom K) a) := by
  induction c using Polynomial.induction_on' with
  | add p r hp hr => rw [eval₂_add, eval₂_add]; exact hp.add hr
  | monomial n z =>
    rw [eval₂_monomial, eval₂_monomial]
    simpa using (Place.hasValue_intCast (v := v) z).mul (h.pow n)

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.eval₂_int" "AlgebraicCurve.Place.HasValue.eval₂_int"

private theorem _root_.AlgebraicCurve.Place.HasValue.eval₂_bivariate {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a')
    (Φ : Polynomial (Polynomial ℤ)) :
    v.HasValue (Φ.eval₂ (eval₂RingHom (Int.castRingHom F) g) g') (Φ.eval₂ (eval₂RingHom (Int.castRingHom K) a) a') := by
  induction Φ using Polynomial.induction_on' with
  | add p r hp hr => rw [eval₂_add, eval₂_add]; exact hp.add hr
  | monomial n c =>
    rw [eval₂_monomial, eval₂_monomial]
    exact (h.eval₂_int c).mul (h'.pow n)

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.HasValue.eval₂_bivariate" "AlgebraicCurve.Place.HasValue.eval₂_bivariate"

private theorem _root_.AlgebraicCurve.Place.hasValue_zero_of_ord_pos {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  by_contra hne
  have hu : IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := (residue_ne_zero_iff_isUnit _).mp hne
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  simp only at this
  omega

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.hasValue_zero_of_ord_pos" "AlgebraicCurve.Place.hasValue_zero_of_ord_pos"

private theorem _root_.AlgebraicCurve.Place.ord_pos_of_hasValue_zero' {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have h0 := v.ord_nonneg_of_mem h.mem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have := (residue_ne_zero_iff_isUnit _).mpr hu
    exact this (by rw [h.residue_eq, map_zero])

p2m_alias "P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.AlgebraicCurve.Place.ord_pos_of_hasValue_zero'" "AlgebraicCurve.Place.ord_pos_of_hasValue_zero'"
end hasValue

theorem modeq_jFun_jqFun :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (modularFunctionFieldBar (1 * q))) (jFun (q := q))) (jqFun (q := q)) = 0 := by
  haveI : NeZero (1 * q) := ⟨by rw [Nat.one_mul]; exact (Fact.out : q.Prime).ne_zero⟩

  apply Subtype.val_injective
  set ι : ↥(modularFunctionFieldBar (1 * q)) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap (↥(modularFunctionFieldBar (1 * q))) (LaurentSeries (AlgebraicClosure ℚ))) with hι
  have hιapp : ∀ z : ↥(modularFunctionFieldBar (1 * q)), ι z = (z : LaurentSeries (AlgebraicClosure ℚ)) := fun z => rfl
  show ((data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (modularFunctionFieldBar (1 * q))) (jFun (q := q))) (jqFun (q := q)) :
      ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((0 : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries _)
  rw [← hιapp, ← hιapp, map_zero, Polynomial.hom_eval₂]

  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0

  have hhom : ι.comp (eval₂RingHom (Int.castRingHom (modularFunctionFieldBar (1 * q))) (jFun (q := q)))
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, evalAtJ_X, hιapp]; rfl
  have harg : ι (jqFun (q := q)) = coeffEmb (AlgebraicClosure ℚ) (jqN q) := by
    rw [hιapp]
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = coeffEmb (AlgebraicClosure ℚ) (jqN q)
    rw [jqN, qExpand_congr (one_mul q)]
  rw [hhom, harg]
  exact h0

theorem valuation_eval₂_le_pow {K : Type*} [Field K] (B : ValuationSubring K) {x : K} (hx : 1 ≤ B.valuation x)
    (c : Polynomial ℤ) {d : ℕ} (hc : c.natDegree ≤ d) :
    B.valuation (c.eval₂ (Int.castRingHom K) x) ≤ B.valuation x ^ d := by
  rw [eval₂_eq_sum_range' (Int.castRingHom K) (show c.natDegree < d + 1 by omega) x]
  apply Valuation.map_sum_le
  intro i hi
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow]
  have hz : B.valuation ((Int.castRingHom K) (c.coeff i)) ≤ 1 := by
    have h := B.valuation_le_one ((c.coeff i : ℤ) : B)
    rw [show (((c.coeff i : ℤ) : B) : K) = (Int.castRingHom K) (c.coeff i) from by push_cast; rfl] at h
    exact h
  calc B.valuation ((Int.castRingHom K) (c.coeff i)) * B.valuation x ^ i ≤ 1 * B.valuation x ^ i :=
        mul_le_mul_left hz _
    _ = B.valuation x ^ i := one_mul _
    _ ≤ B.valuation x ^ d := pow_le_pow_right₀ hx (by omega)

theorem isInftySide_or_isZeroSide_of_isCuspidal' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    P.IsInftySide W ∨ P.IsZeroSide W := by
  classical
  by_cases hinf : W = cuspInftyBar (1 * q)
  · left; subst hinf; exact isInftySide_cuspInftyBar' P
  by_cases hzero : W = cuspZeroBar (1 * q)
  · right; subst hzero; exact isZeroSide_cuspZeroBar' P
  obtain ⟨hjmem, hjqmem⟩ := jFun_mem_and_jqFun_mem_of_ne_cusps W hinf hzero

  haveI : NeZero (1 * q) := ⟨by rw [Nat.one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField W).mp
      (deg_eq_one_modularFunctionFieldBar (1 * q) W)
  obtain ⟨x₀, hx₀, -⟩ := W.exists_hasValue_of_surjective hsurj hjmem
  obtain ⟨y, hy, -⟩ := W.exists_hasValue_of_surjective hsurj hjqmem
  set v := A.valuation with hv

  have hx₀A : ∀ a : A, (a : AlgebraicClosure ℚ) ≠ x₀ := by
    intro a ha
    have hval : W.HasValue (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) 0 := by
      have := hx₀.sub (W.hasValue_algebraMap (a : AlgebraicClosure ℚ))
      rwa [← ha, sub_self] at this
    have hne : jFun (q := q) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have hj : jFun (q := q) = algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := sub_eq_zero.mp h0
      have h1 := ord_cuspInftyBar_jFun_neg (q := q)
      rw [hj] at h1
      exact absurd ((cuspInftyBar (1 * q)).ord_nonneg_of_mem ((cuspInftyBar (1 * q)).algebraMap_mem' _)) (not_le.mpr h1)
    have hpos := Place.ord_pos_of_hasValue_zero' hval hne
    exact absurd (hW a) (not_le.mpr hpos)
  have hvx : 1 < v x₀ := by
    rw [← not_le, hv, A.valuation_le_one_iff]
    intro hmem
    exact hx₀A ⟨x₀, hmem⟩ rfl
  have hx₀ne : x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvx; exact not_lt_zero' hvx

  obtain ⟨R, hR, -⟩ := existsUnique_kroneckerRemainder q data hKr
  obtain ⟨hRdeg, hRX, hRqq⟩ := natDegree_kroneckerRemainder_le q data R hR
  set H : Polynomial (AlgebraicClosure ℚ) := R.map (eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) x₀) with hH
  have hΦval : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) x₀) y = 0 := by
    have h1 := (hx₀.eval₂_bivariate hy data.Φ)
    rw [modeq_jFun_jqFun] at h1
    exact (h1.unique Place.hasValue_zero').symm ▸ rfl
  have hroot : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C ((q : ℕ) : AlgebraicClosure ℚ) * H).IsRoot y := by
    rw [Polynomial.IsRoot.def]
    rw [hR] at hΦval
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow, hH, eval_map]
    simp only [eval₂_add, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X, eval₂_pow, coe_eval₂RingHom, eval₂_X, eval₂_C,
      eq_intCast, Int.cast_natCast, eval₂_natCast, map_natCast] at hΦval
    exact hΦval

  have hHdeg : H.natDegree ≤ q := (natDegree_map_le).trans hRdeg
  have hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q := by
    intro b _
    rw [hH, coeff_map, coe_eval₂RingHom]
    exact valuation_eval₂_le_pow A hvx.le _ (hRX b)
  have hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1) := by
    rw [hH, coeff_map, coe_eval₂RingHom]
    apply valuation_eval₂_le_pow A hvx.le

    have h1 := hRX q
    rcases h1.lt_or_eq with hlt | heq
    · omega
    · have : (R.coeff q).leadingCoeff = 0 := by rw [leadingCoeff, heq, hRqq]
      rw [leadingCoeff_eq_zero] at this
      rw [this, natDegree_zero]; omega
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hc : v ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := by
    have h := A.valuation_le_one ((q : ℕ) : A)
    rw [show (((q : ℕ) : A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) from by push_cast; rfl] at h
    exact h

  rcases Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape v hq1 x₀ _ hvx hc H hHdeg hHb hHq y hroot
    with hI | ⟨hvy, hZ⟩
  ·
    left
    refine ⟨hW, ?_⟩
    have hmemτ : y / x₀ ^ q ∈ A := by
      rw [← A.valuation_le_one_iff]
      have : y / x₀ ^ q = (y / x₀ ^ q - 1) + 1 := by ring
      rw [this]
      refine (v.map_add _ _).trans (max_le hI.le ?_)
      rw [map_one]
    refine ⟨⟨y / x₀ ^ q, hmemτ⟩, ?_, ?_⟩
    ·
      have hm : (⟨y / x₀ ^ q, hmemτ⟩ : A) - 1 ∈ maximalIdeal A := by
        rw [A.valuation_lt_one_iff]; push_cast; exact hI
      have := ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red hm
      rwa [map_sub, map_one, sub_eq_zero] at this
    ·
      show W.HasValue (tInfty (q := q)) (y / x₀ ^ q)
      have := hy.mul ((hx₀.pow (1 * q)).inv (pow_ne_zero _ hx₀ne))
      have e : x₀ ^ (1 * q) = x₀ ^ q := by rw [Nat.one_mul]
      rw [e] at this
      simpa [tInfty, div_eq_mul_inv] using this
  ·
    right
    have hyA : ∀ a : A, (a : AlgebraicClosure ℚ) ≠ y := by
      intro a ha
      have : v y ≤ 1 := by rw [← ha]; exact A.valuation_le_one a
      exact absurd hvy (not_lt.mpr this)
    have hyne : y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvy; exact not_lt_zero' hvy
    refine ⟨?_, ?_⟩
    ·
      intro a
      by_contra hpos
      push Not at hpos
      have hne : jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0; rw [h0] at hpos; simp at hpos
      have h0val := Place.hasValue_zero_of_ord_pos hne hpos
      have hval := hy.sub (W.hasValue_algebraMap (a : AlgebraicClosure ℚ))
      have := hval.unique h0val
      exact hyA a (sub_eq_zero.mp this).symm
    · have hmemτ : x₀ / y ^ q ∈ A := by
        rw [← A.valuation_le_one_iff]
        have : x₀ / y ^ q = (x₀ / y ^ q - 1) + 1 := by ring
        rw [this]
        refine (v.map_add _ _).trans (max_le hZ.le ?_)
        rw [map_one]
      refine ⟨⟨x₀ / y ^ q, hmemτ⟩, ?_, ?_⟩
      · have hm : (⟨x₀ / y ^ q, hmemτ⟩ : A) - 1 ∈ maximalIdeal A := by
          rw [A.valuation_lt_one_iff]; push_cast; exact hZ
        have := ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red hm
        rwa [map_sub, map_one, sub_eq_zero] at this
      · show W.HasValue (tZero (q := q)) (x₀ / y ^ q)
        have := hx₀.mul ((hy.pow (1 * q)).inv (pow_ne_zero _ hyne))
        have e : y ^ (1 * q) = y ^ q := by rw [Nat.one_mul]
        rw [e] at this
        simpa [tZero, div_eq_mul_inv] using this

end PlaceSpecialization
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    P.IsInftySide W ∨ P.IsZeroSide W :=
  ModularCurve.PlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal' P W hW

end S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
end P2MW
export P2MW.S_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal (solution)
