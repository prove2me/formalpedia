-- Prove2me | solution 1 for ModularCurve.isZeroSide_cuspZeroBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/19439a46-c1ef-5e4e-8933-7a04614aa53b

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isZeroSide_cuspZeroBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isZeroSide_cuspZeroBar.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isZeroSide_cuspZeroBar.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb exists_isFrickeAutFull_of_neZero"
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
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb exists_isFrickeAutFull_of_neZero"
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
p2m_export "AlgebraicCurve" "Place Place.ord_smul"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue ext ResidueField smulRingEquiv coe_smulRingEquiv_apply smul_toValuationSubring ord_smul smulResidueAlgEquiv algebraMap_mem' toValuationSubring mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mem residue_eq" end HasValue
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
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq coeff_jq_pow_self coeff_jq_pow_of_lt coeff_jq_neg_one coeff_jq_of_lt ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar cuspZeroBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull order_coeffEmb_jq cuspInftyBar order_pow_of_ne_zero_bar order_div_of_ne_zero_bar qSeriesBar qSeriesBar_zero qSeriesBar_one qSeriesBar_sub qSeriesBar_div qSeriesBar_pow qSeriesBar_eq_zero_iff qSeriesBar_ne_zero qIntegersBar isUnit_qIntegersBar_iff notMem_qIntegersBar_of_order_eq_neg_one jq_mem_full geomAut_coeffEmb exists_isFrickeAutFull_of_neZero"
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

theorem solution {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsZeroSide (cuspZeroBar (1 * q)) :=
  ModularCurve.PlaceSpecialization.isZeroSide_cuspZeroBar' P

end S_ModularCurve_isZeroSide_cuspZeroBar
end P2MW
export P2MW.S_ModularCurve_isZeroSide_cuspZeroBar (solution)
