-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b2f34728-3edd-5cd2-aa59-9b856daff61c

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section
open AlgebraicCurve

set_option autoImplicit false

namespace GaussPencil
namespace B6

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have h := Valuation.map_add (v.adicValuation) f g
  change min (-(WithZero.log (v.adicValuation f))) (-(WithZero.log (v.adicValuation g)))
    ≤ -(WithZero.log (v.adicValuation (f + g)))
  rcases le_max_iff.mp h with h' | h'
  · have h2 := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hf)).mpr h'
    exact (min_le_left _ _).trans (neg_le_neg h2)
  · have h2 := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hg)).mpr h'
    exact (min_le_right _ _).trans (neg_le_neg h2)

theorem ord_add_pos {f g : F} (hf : 0 < v.ord f) (hg : 0 < v.ord g) (hfg : f + g ≠ 0) : 0 < v.ord (f + g) := by
  have hf0 : f ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hf; exact lt_irrefl 0 hf
  have hg0 : g ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hg; exact lt_irrefl 0 hg
  exact lt_of_lt_of_le (lt_min hf hg) (min_ord_le_ord_add v hf0 hg0 hfg)

theorem ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  change -(WithZero.log (v.adicValuation (-f))) = -(WithZero.log (v.adicValuation f))
  rw [Valuation.map_neg]

theorem ord_algebraMap_eq_zero {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' _⟩, Subtype.ext (by
      show algebraMap K F c * algebraMap K F c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one])⟩
  obtain ⟨u, hu⟩ := hu
  have h := v.ord_coe_unit u
  rwa [hu] at h

theorem algebraMap_eq_of_ord_sub_pos (g : F) {a a' : K} (h : 0 < v.ord (g - algebraMap K F a))
    (h' : 0 < v.ord (g - algebraMap K F a')) : a = a' := by
  by_contra hne
  have hd : algebraMap K F (a' - a) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hne))
  have heq : (g - algebraMap K F a) + (-(g - algebraMap K F a')) = algebraMap K F (a' - a) := by
    rw [map_sub]; ring
  have hpos := ord_add_pos v h (by rw [ord_neg']; exact h') (by rw [heq]; exact hd)
  rw [heq, ord_algebraMap_eq_zero v (sub_ne_zero.mpr (Ne.symm hne))] at hpos
  exact lt_irrefl 0 hpos

theorem ord_const_mul_pos {c : K} (hc : c ≠ 0) {f : F} (hf : 0 < v.ord f) : 0 < v.ord (algebraMap K F c * f) := by
  have hf0 : f ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hf; exact lt_irrefl 0 hf
  rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hf0, ord_algebraMap_eq_zero v hc, zero_add]
  exact hf

end GaussPencil.B6

end

section
open AlgebraicCurve

namespace GaussPencil
namespace Mu

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have : g = -f := (neg_eq_of_add_eq_zero_right h0).symm
    rw [this, GaussPencil.B6.ord_neg'] at h
    exact lt_irrefl _ h
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : min (v.ord (f + g)) (v.ord (-g)) ≤ v.ord (f + g + -g) :=
      GaussPencil.B6.min_ord_le_ord_add v hfg (neg_ne_zero.mpr hg) (by rw [add_neg_cancel_right]; exact hf)
    rw [add_neg_cancel_right, GaussPencil.B6.ord_neg'] at h1
    rcases min_le_iff.mp h1 with h2 | h2
    · exact lt_irrefl _ (lt_of_lt_of_le hlt h2)
    · exact lt_irrefl _ (lt_of_lt_of_le h h2)
  · have h1 := GaussPencil.B6.min_ord_le_ord_add v hf hg hfg
    rwa [min_eq_left h.le] at h1

theorem ord_add_eq_of_gt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord g < v.ord f) :
    v.ord (f + g) = v.ord g := by
  rw [add_comm]; exact ord_add_eq_of_lt v hg hf h

theorem ord_add_nonneg {f g : F} (hf : 0 ≤ v.ord f) (hg : 0 ≤ v.ord g) : 0 ≤ v.ord (f + g) := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · rw [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · rw [hfg, Place.ord_zero]
  exact (le_min hf hg).trans (GaussPencil.B6.min_ord_le_ord_add v hf0 hg0 hfg)

theorem ne_zero_of_ord_ne_zero {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact h (Place.ord_zero v)

end GaussPencil.Mu

end

section

open Polynomial

namespace GaussPencil
namespace Mu

theorem exists_algebraMap_eq_of_unit_trinomial
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {κ : Type*} [Field κ] [Algebra L κ]
    (Z : κ) (u b c : A) (hu : IsUnit u) (n : ℕ) (hn : 2 ≤ n)
    (h : algebraMap L κ (u : L) * Z ^ n + algebraMap L κ (b : L) * Z + algebraMap L κ (c : L) = 0) :
    ∃ z : A, algebraMap L κ (z : L) = Z := by
  have hu0 : (u : L) ≠ 0 := by
    intro h0
    have : u = 0 := Subtype.ext h0
    rw [this] at hu
    exact not_isUnit_zero hu

  let p : L[X] := C (u : L) * X ^ n + C (b : L) * X + C (c : L)
  have hp : aeval Z p = 0 := by
    simp only [p, map_add, map_mul, aeval_C, map_pow, aeval_X]
    exact h
  have hn0 : n ≠ 0 := by omega
  have hpn : p.coeff n = (u : L) := by
    rw [coeff_add, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, coeff_C_mul, coeff_X,
      if_neg (by omega : ¬ (1 : ℕ) = n), mul_zero, add_zero, coeff_C, if_neg hn0, add_zero]
  have hp0 : p ≠ 0 := fun h0 => hu0 (by rw [← hpn, h0, coeff_zero])
  have halg : IsAlgebraic L Z := ⟨p, hp0, hp⟩
  have hint : IsIntegral L Z := halg.isIntegral

  have hdeg : (minpoly L Z).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨z₀, hz₀⟩ : Z ∈ (algebraMap L κ).range := minpoly.mem_range_of_degree_eq_one L Z hdeg

  have hrel : (u : L) * z₀ ^ n + (b : L) * z₀ + (c : L) = 0 := by
    apply (algebraMap L κ).injective
    rw [map_add, map_add, map_mul, map_mul, map_pow, hz₀, map_zero]
    exact h

  obtain ⟨v, hv⟩ := hu
  let ν : A := ((v⁻¹ : Aˣ) : A)
  have hνu : (ν : L) * (u : L) = 1 := by
    have h1 : ((v⁻¹ : Aˣ) : A) * (v : A) = 1 := Units.inv_mul v
    rw [← hv]
    exact_mod_cast congrArg (fun a : A => (a : L)) h1
  let P₀ : A[X] := X ^ n + (C (ν * b) * X + C (ν * c))
  have hP₀m : P₀.Monic := by
    apply (monic_X_pow n).add_of_left
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    rw [degree_X_pow]
    refine max_lt (lt_of_le_of_lt (degree_C_mul_X_le _) ?_) (lt_of_le_of_lt degree_C_le ?_)
    · exact_mod_cast hn
    · exact_mod_cast (lt_of_lt_of_le (by norm_num) hn : (0 : ℕ) < n)
  have hP₀ : eval₂ (algebraMap A L) z₀ P₀ = 0 := by
    simp only [P₀, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, map_mul]
    have : (algebraMap A L ν) = (ν : L) := rfl
    have hb : (algebraMap A L b) = (b : L) := rfl
    have hc : (algebraMap A L c) = (c : L) := rfl
    rw [this, hb, hc]
    have := congrArg (fun t => (ν : L) * t) hrel
    simp only [mul_add, mul_zero] at this
    rw [← mul_assoc, hνu, one_mul] at this
    linear_combination this
  have hzint : IsIntegral A z₀ := ⟨P₀, hP₀m, hP₀⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  refine ⟨z, ?_⟩
  rw [← hz₀, ← hz]
  rfl

end GaussPencil.Mu

end

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_one_apply jq ModularPolynomialData jqd_mem_full coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar isFrickeAutFull_frickeInvolutionFull cuspInftyBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero frickeInvolutionBar_frickeInvolutionBar ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg isInftySide_or_isZeroSide_of_isCuspidal PlaceSpecialization.gPencil PlaceSpecialization.exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun tInfty tZero IsCuspidal gPencil exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "redBar_residue"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

section Basics

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

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

theorem frickeInvolutionBar_jqFun' :
    frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
  frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)
    |>.trans (Subtype.ext (congrArg (fun x => coeffEmb (AlgebraicClosure ℚ) x) (qExpand_one_apply jq)))

include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.red_eq_zero_of_mem (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  rw [← R.redBar_residue, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "red_eq_zero_of_mem"
include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isUnit_of_red_ne_zero (μ : A) (hμ : red μ ≠ 0) : IsUnit μ := by
  by_contra h
  apply hμ
  rw [← R.redBar_residue μ, (IsLocalRing.residue_eq_zero_iff μ).mpr ((IsLocalRing.mem_maximalIdeal μ).mpr (mem_nonunits_iff.mpr h)),
    map_zero]

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "isUnit_of_red_ne_zero"

private noncomputable def _root_.ModularCurve.PlaceSpecialization.gPencil (μ : A) : ↥(modularFunctionFieldBar (1 * q)) :=
  jFun (q := q) + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos.ModularCurve.PlaceSpecialization.gPencil" "ModularCurve.PlaceSpecialization.gPencil"
end Basics

section Poles

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem ord_cuspInftyBar_jFun : (cuspInftyBar (1 * q)).ord (jFun (q := q)) = -1 :=
  ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * q)

theorem ord_cuspInftyBar_jqFun : (cuspInftyBar (1 * q)).ord (jqFun (q := q)) = -(q : ℤ) := by
  have h := ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (1 * q) (1 * q) (dvd_refl _)
  refine h.trans ?_
  push_cast
  ring

theorem ord_cuspZeroBar_eq (f : modularFunctionFieldBar (1 * q)) :
    (cuspZeroBar (1 * q)).ord f = (cuspInftyBar (1 * q)).ord (frickeInvolutionBar (1 * q) f) := by
  conv_lhs => rw [← ModularCurve.frickeInvolutionBar_frickeInvolutionBar (1 * q) f]
  exact Place.ord_smul (frickeInvolutionBar (1 * q)) (cuspInftyBar (1 * q)) (frickeInvolutionBar (1 * q) f)

theorem ord_cuspZeroBar_jFun : (cuspZeroBar (1 * q)).ord (jFun (q := q)) = -(q : ℤ) := by
  rw [ord_cuspZeroBar_eq, frickeInvolutionBar_jFun']; exact ord_cuspInftyBar_jqFun

theorem ord_cuspZeroBar_jqFun : (cuspZeroBar (1 * q)).ord (jqFun (q := q)) = -1 := by
  rw [ord_cuspZeroBar_eq, frickeInvolutionBar_jqFun']; exact ord_cuspInftyBar_jFun

theorem jFun_ne_zero : jFun (q := q) ≠ 0 :=
  GaussPencil.Mu.ne_zero_of_ord_ne_zero (cuspInftyBar (1 * q)) (by rw [ord_cuspInftyBar_jFun]; norm_num)

theorem jqFun_ne_zero : jqFun (q := q) ≠ 0 :=
  GaussPencil.Mu.ne_zero_of_ord_ne_zero (cuspZeroBar (1 * q)) (by rw [ord_cuspZeroBar_jqFun]; norm_num)

theorem cuspInftyBar_ne_cuspZeroBar : cuspInftyBar (1 * q) ≠ cuspZeroBar (1 * q) := by
  intro h
  have e := ord_cuspInftyBar_jFun (q := q)
  rw [h, ord_cuspZeroBar_jFun] at e
  have : (q : ℤ) = 1 := by omega
  exact (Fact.out : q.Prime).one_lt.ne' (by exact_mod_cast this)

theorem frickeInvolutionBar_mul_self : frickeInvolutionBar (1 * q) * frickeInvolutionBar (1 * q) = 1 :=
  AlgEquiv.ext fun y => ModularCurve.frickeInvolutionBar_frickeInvolutionBar (1 * q) y

theorem frickeInvolutionBar_smul_smul (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) • frickeInvolutionBar (1 * q) • W = W := by
  rw [smul_smul, frickeInvolutionBar_mul_self, one_smul]

theorem frickeInvolutionBar_smul_cuspInftyBar :
    frickeInvolutionBar (1 * q) • cuspInftyBar (1 * q) = cuspZeroBar (1 * q) := rfl

theorem frickeInvolutionBar_smul_cuspZeroBar :
    frickeInvolutionBar (1 * q) • cuspZeroBar (1 * q) = cuspInftyBar (1 * q) := by
  rw [← frickeInvolutionBar_smul_cuspInftyBar, frickeInvolutionBar_smul_smul]

theorem ord_eq_ord_smul_frickeInvolutionBar (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (f : modularFunctionFieldBar (1 * q)) :
    W.ord f = (frickeInvolutionBar (1 * q) • W).ord (frickeInvolutionBar (1 * q) f) :=
  (Place.ord_smul (frickeInvolutionBar (1 * q)) W f).symm

theorem ord_jFun_nonneg_of_ne (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h₁ : W ≠ cuspInftyBar (1 * q)) (h₂ : W ≠ cuspZeroBar (1 * q)) : 0 ≤ W.ord (jFun (q := q)) := by
  by_contra h
  rcases ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg W (not_le.mp h) with e | e
  exacts [h₁ e, h₂ e]

theorem ord_jqFun_nonneg_of_ne (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h₁ : W ≠ cuspInftyBar (1 * q)) (h₂ : W ≠ cuspZeroBar (1 * q)) : 0 ≤ W.ord (jqFun (q := q)) := by
  rw [ord_eq_ord_smul_frickeInvolutionBar, frickeInvolutionBar_jqFun']
  apply ord_jFun_nonneg_of_ne
  · intro h; apply h₂
    rw [← frickeInvolutionBar_smul_smul W, h, frickeInvolutionBar_smul_cuspInftyBar]
  · intro h; apply h₁
    rw [← frickeInvolutionBar_smul_smul W, h, frickeInvolutionBar_smul_cuspZeroBar]

theorem algebraMap_mul_jqFun_ne_zero (μ : A) (hμ : (μ : AlgebraicClosure ℚ) ≠ 0) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q) ≠ 0 :=
  mul_ne_zero ((_root_.map_ne_zero _).mpr hμ) jqFun_ne_zero

theorem ord_algebraMap_mul_jqFun (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (μ : A) (hμ : (μ : AlgebraicClosure ℚ) ≠ 0) :
    W.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q))
      = W.ord (jqFun (q := q)) := by
  have hc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hμ
  rw [W.ord_mul hc jqFun_ne_zero, GaussPencil.B6.ord_algebraMap_eq_zero W hμ, zero_add]

theorem ord_cuspInftyBar_gPencil (μ : A) (hμ : (μ : AlgebraicClosure ℚ) ≠ 0) :
    (cuspInftyBar (1 * q)).ord (PlaceSpecialization.gPencil (q := q) μ) = -(q : ℤ) := by
  have hq : (1 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [PlaceSpecialization.gPencil, GaussPencil.Mu.ord_add_eq_of_gt _ jFun_ne_zero (algebraMap_mul_jqFun_ne_zero μ hμ),
    ord_algebraMap_mul_jqFun _ μ hμ, ord_cuspInftyBar_jqFun]
  rw [ord_algebraMap_mul_jqFun _ μ hμ, ord_cuspInftyBar_jqFun, ord_cuspInftyBar_jFun]
  omega

theorem ord_cuspZeroBar_gPencil (μ : A) :
    (cuspZeroBar (1 * q)).ord (PlaceSpecialization.gPencil (q := q) μ) = -(q : ℤ) := by
  have hq : (1 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  by_cases hμ : (μ : AlgebraicClosure ℚ) = 0
  · rw [PlaceSpecialization.gPencil, hμ, map_zero, zero_mul, add_zero]; exact ord_cuspZeroBar_jFun
  rw [PlaceSpecialization.gPencil, GaussPencil.Mu.ord_add_eq_of_lt _ jFun_ne_zero (algebraMap_mul_jqFun_ne_zero μ hμ),
    ord_cuspZeroBar_jFun]
  rw [ord_algebraMap_mul_jqFun _ μ hμ, ord_cuspZeroBar_jqFun, ord_cuspZeroBar_jFun]
  omega

theorem ord_gPencil_nonneg_of_ne (μ : A) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h₁ : W ≠ cuspInftyBar (1 * q)) (h₂ : W ≠ cuspZeroBar (1 * q)) :
    0 ≤ W.ord (PlaceSpecialization.gPencil (q := q) μ) := by
  rw [PlaceSpecialization.gPencil]
  refine GaussPencil.Mu.ord_add_nonneg W (ord_jFun_nonneg_of_ne W h₁ h₂) ?_
  by_cases hμ : (μ : AlgebraicClosure ℚ) = 0
  · rw [hμ, map_zero, zero_mul, Place.ord_zero]
  rw [ord_algebraMap_mul_jqFun _ μ hμ]; exact ord_jqFun_nonneg_of_ne W h₁ h₂

end Poles

section PencilCusp

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

theorem ord_sub_algebraMap_of_ord_neg (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    {f : modularFunctionFieldBar (1 * q)} (hf : W.ord f < 0) (a : AlgebraicClosure ℚ) :
    W.ord (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) a) = W.ord f := by
  by_cases ha : a = 0
  · rw [ha, map_zero, sub_zero]
  have hf0 : f ≠ 0 := GaussPencil.Mu.ne_zero_of_ord_ne_zero W hf.ne
  rw [sub_eq_add_neg, GaussPencil.Mu.ord_add_eq_of_lt W hf0 (neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr ha))]
  rw [GaussPencil.B6.ord_neg', GaussPencil.B6.ord_algebraMap_eq_zero W ha]; exact hf

include R in
private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isUnit_of_red_eq_one (τ : A) (hτ : red τ = 1) : IsUnit τ := by
  by_contra h
  have := R.red_eq_zero_of_mem τ ((IsLocalRing.mem_maximalIdeal τ).mpr (mem_nonunits_iff.mpr h))
  rw [hτ] at this
  exact one_ne_zero this

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "isUnit_of_red_eq_one"
include R in

private theorem _root_.ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos
    (μ : A) (hμ : red μ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : A)
    (ha : 0 < W.ord (PlaceSpecialization.gPencil (q := q) μ
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))) :
    ∃ x : A, 0 < W.ord (jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) := by
  classical
  by_contra hno
  push_neg at hno
  have hcusp : P.IsCuspidal W := hno
  have hμ0 : (μ : AlgebraicClosure ℚ) ≠ 0 := fun h => hμ (by rw [show μ = 0 from Subtype.ext h, map_zero])
  have hμu : IsUnit μ := R.isUnit_of_red_ne_zero μ hμ
  have hq2 : 2 ≤ 1 * q := by rw [one_mul]; exact (Fact.out : q.Prime).two_le
  have hqneg : -(q : ℤ) < 0 := neg_lt_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)

  have hW₁ : W ≠ cuspInftyBar (1 * q) := by
    rintro rfl
    rw [ord_sub_algebraMap_of_ord_neg _ (by rw [ord_cuspInftyBar_gPencil μ hμ0]; exact hqneg),
      ord_cuspInftyBar_gPencil μ hμ0] at ha
    exact lt_irrefl _ (ha.trans hqneg)
  have hW₂ : W ≠ cuspZeroBar (1 * q) := by
    rintro rfl
    rw [ord_sub_algebraMap_of_ord_neg _ (by rw [ord_cuspZeroBar_gPencil μ]; exact hqneg),
      ord_cuspZeroBar_gPencil μ] at ha
    exact lt_irrefl _ (ha.trans hqneg)

  have hj : jFun (q := q) ∈ W.toValuationSubring :=
    Place.mem_of_ord_nonneg W jFun_ne_zero (ord_jFun_nonneg_of_ne W hW₁ hW₂)
  have hjq : jqFun (q := q) ∈ W.toValuationSubring :=
    Place.mem_of_ord_nonneg W jqFun_ne_zero (ord_jqFun_nonneg_of_ne W hW₁ hW₂)
  have hcst : ∀ c : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ∈ W.toValuationSubring := W.algebraMap_mem'
  have hg : PlaceSpecialization.gPencil (q := q) μ ∈ W.toValuationSubring := add_mem hj (mul_mem (hcst _) hjq)

  have hres_cst : ∀ c : AlgebraicClosure ℚ,
      IsLocalRing.residue W.toValuationSubring ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c, hcst c⟩
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField c := fun c => (W.hasValue_algebraMap c).residue_eq
  have hga0 : PlaceSpecialization.gPencil (q := q) μ
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ≠ 0 :=
    GaussPencil.Mu.ne_zero_of_ord_ne_zero W ha.ne'
  have hga : IsLocalRing.residue W.toValuationSubring ⟨_, sub_mem hg (hcst (a : AlgebraicClosure ℚ))⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (W.mem_maximalIdeal_iff_ord_pos hga0 _).mpr ha
  have hXY : IsLocalRing.residue W.toValuationSubring ⟨jFun (q := q), hj⟩
      + algebraMap (AlgebraicClosure ℚ) W.ResidueField (μ : AlgebraicClosure ℚ)
        * IsLocalRing.residue W.toValuationSubring ⟨jqFun (q := q), hjq⟩
      = algebraMap (AlgebraicClosure ℚ) W.ResidueField (a : AlgebraicClosure ℚ) := by
    have e : (⟨_, sub_mem hg (hcst (a : AlgebraicClosure ℚ))⟩ : W.toValuationSubring)
        = (⟨jFun (q := q), hj⟩ + ⟨_, hcst (μ : AlgebraicClosure ℚ)⟩ * ⟨jqFun (q := q), hjq⟩) - ⟨_, hcst (a : AlgebraicClosure ℚ)⟩ := rfl
    rw [e, map_sub, map_add, map_mul, hres_cst, hres_cst, sub_eq_zero] at hga
    exact hga

  have key : ∀ x : A, algebraMap (AlgebraicClosure ℚ) W.ResidueField (x : AlgebraicClosure ℚ)
      = IsLocalRing.residue W.toValuationSubring ⟨jFun (q := q), hj⟩ → False := by
    intro x hx
    apply absurd (hno x)
    push_neg
    have hsub0 : jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      have e := ord_cuspInftyBar_jFun (q := q)
      rw [h0] at e
      by_cases hx0 : (x : AlgebraicClosure ℚ) = 0
      · rw [hx0, map_zero, Place.ord_zero] at e; norm_num at e
      · rw [GaussPencil.B6.ord_algebraMap_eq_zero _ hx0] at e; norm_num at e
    refine (W.mem_maximalIdeal_iff_ord_pos hsub0 (sub_mem hj (hcst _))).mp ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    have e : (⟨_, sub_mem hj (hcst (x : AlgebraicClosure ℚ))⟩ : W.toValuationSubring)
        = ⟨jFun (q := q), hj⟩ - ⟨_, hcst (x : AlgebraicClosure ℚ)⟩ := rfl
    rw [e, map_sub, hres_cst, ← hx, sub_self]

  rcases ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal P W hcusp with ⟨-, τ, hτ, ht, hτres⟩ | ⟨-, τ, hτ, ht, hτres⟩
  ·
    have hτu : IsUnit τ := R.isUnit_of_red_eq_one τ hτ
    have hrel : (⟨tInfty (q := q), ht⟩ : W.toValuationSubring) * ⟨jFun (q := q), hj⟩ ^ (1 * q) = ⟨jqFun (q := q), hjq⟩ := by
      apply Subtype.ext
      show tInfty (q := q) * jFun (q := q) ^ (1 * q) = jqFun (q := q)
      exact div_mul_cancel₀ _ (pow_ne_zero _ jFun_ne_zero)
    have hY : IsLocalRing.residue W.toValuationSubring ⟨jqFun (q := q), hjq⟩
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField (τ : AlgebraicClosure ℚ)
          * IsLocalRing.residue W.toValuationSubring ⟨jFun (q := q), hj⟩ ^ (1 * q) := by
      rw [← hrel, map_mul, map_pow, hτres]
    obtain ⟨x, hx⟩ := GaussPencil.Mu.exists_algebraMap_eq_of_unit_trinomial A
      (IsLocalRing.residue W.toValuationSubring ⟨jFun (q := q), hj⟩) (μ * τ) 1 (-a) (hμu.mul hτu) (1 * q) hq2 (by
        have h := hXY
        rw [hY] at h
        have e1 : ((μ * τ : A) : AlgebraicClosure ℚ) = (μ : AlgebraicClosure ℚ) * (τ : AlgebraicClosure ℚ) := rfl
        have e2 : ((1 : A) : AlgebraicClosure ℚ) = 1 := rfl
        have e3 : ((-a : A) : AlgebraicClosure ℚ) = -(a : AlgebraicClosure ℚ) := rfl
        rw [e1, e2, e3, map_mul, map_one, map_neg]
        linear_combination h)
    exact key x hx
  ·
    have hτu : IsUnit τ := R.isUnit_of_red_eq_one τ hτ
    have hrel : (⟨tZero (q := q), ht⟩ : W.toValuationSubring) * ⟨jqFun (q := q), hjq⟩ ^ (1 * q) = ⟨jFun (q := q), hj⟩ := by
      apply Subtype.ext
      show tZero (q := q) * jqFun (q := q) ^ (1 * q) = jFun (q := q)
      exact div_mul_cancel₀ _ (pow_ne_zero _ jqFun_ne_zero)
    have hX : IsLocalRing.residue W.toValuationSubring ⟨jFun (q := q), hj⟩
        = algebraMap (AlgebraicClosure ℚ) W.ResidueField (τ : AlgebraicClosure ℚ)
          * IsLocalRing.residue W.toValuationSubring ⟨jqFun (q := q), hjq⟩ ^ (1 * q) := by
      rw [← hrel, map_mul, map_pow, hτres]
    obtain ⟨y, hy⟩ := GaussPencil.Mu.exists_algebraMap_eq_of_unit_trinomial A
      (IsLocalRing.residue W.toValuationSubring ⟨jqFun (q := q), hjq⟩) τ μ (-a) hτu (1 * q) hq2 (by
        have h := hXY
        rw [hX] at h
        have e3 : ((-a : A) : AlgebraicClosure ℚ) = -(a : AlgebraicClosure ℚ) := rfl
        rw [e3, map_neg]
        linear_combination h)
    refine key (τ * y ^ (1 * q)) ?_
    have e : ((τ * y ^ (1 * q) : A) : AlgebraicClosure ℚ) = (τ : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ) ^ (1 * q) := by
      push_cast; ring
    rw [hX, ← hy, e, map_mul, map_pow]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos.ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos" "ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos"
end PencilCusp

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (μ : A) (hμ : red μ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : A)
    (ha : 0 < W.ord (jFun (q := q)
      + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))) :
    ∃ x : A, 0 < W.ord (jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) :=
  ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_ord_gPencil_sub_pos R μ hμ W a ha

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos (solution)
