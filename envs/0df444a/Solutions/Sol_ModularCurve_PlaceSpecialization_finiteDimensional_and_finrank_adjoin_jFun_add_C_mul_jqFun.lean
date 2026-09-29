-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ff5ae8b2-32a6-5084-8027-91d23921e2b7

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

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

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar qExpand qExpand_one_apply jq jqd_mem_full coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization frickeInvolutionBar cuspZeroBar isFrickeAutFull_frickeInvolutionFull cuspInftyBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero frickeInvolutionBar_frickeInvolutionBar ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg exists_transcendental_finiteDimensional_modularFunctionFieldBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

section PencilLine

variable {q : ℕ} [Fact q.Prime]

theorem frickeInvolutionBar_jFun'' :
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

theorem frickeInvolutionBar_jqFun'' :
    frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) :=
  frickeInvolutionBar_coeffEmb_qExpand (1 * q)
      (isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)
    |>.trans (Subtype.ext (congrArg (fun x => coeffEmb (AlgebraicClosure ℚ) x) (qExpand_one_apply jq)))

noncomputable abbrev gLine (c : AlgebraicClosure ℚ) : ↥(modularFunctionFieldBar (1 * q)) :=
  jFun (q := q) + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * jqFun (q := q)

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
  rw [ord_cuspZeroBar_eq, frickeInvolutionBar_jFun'']; exact ord_cuspInftyBar_jqFun

theorem ord_cuspZeroBar_jqFun : (cuspZeroBar (1 * q)).ord (jqFun (q := q)) = -1 := by
  rw [ord_cuspZeroBar_eq, frickeInvolutionBar_jqFun'']; exact ord_cuspInftyBar_jFun

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
  rw [ord_eq_ord_smul_frickeInvolutionBar, frickeInvolutionBar_jqFun'']
  apply ord_jFun_nonneg_of_ne
  · intro h; apply h₂
    rw [← frickeInvolutionBar_smul_smul W, h, frickeInvolutionBar_smul_cuspInftyBar]
  · intro h; apply h₁
    rw [← frickeInvolutionBar_smul_smul W, h, frickeInvolutionBar_smul_cuspZeroBar]

variable (c : AlgebraicClosure ℚ) (hc0 : c ≠ 0)

include hc0 in
theorem algebraMap_mul_jqFun_ne_zero :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * jqFun (q := q) ≠ 0 :=
  mul_ne_zero ((_root_.map_ne_zero _).mpr hc0) jqFun_ne_zero

include hc0 in
theorem ord_algebraMap_mul_jqFun (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    W.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * jqFun (q := q))
      = W.ord (jqFun (q := q)) := by
  have hc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ≠ 0 :=
    (_root_.map_ne_zero _).mpr hc0
  rw [W.ord_mul hc jqFun_ne_zero, GaussPencil.B6.ord_algebraMap_eq_zero W hc0, zero_add]

include hc0 in
theorem ord_cuspInftyBar_gLine : (cuspInftyBar (1 * q)).ord (gLine (q := q) c) = -(q : ℤ) := by
  have hq : (1 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [gLine, GaussPencil.Mu.ord_add_eq_of_gt _ jFun_ne_zero (algebraMap_mul_jqFun_ne_zero c hc0),
    ord_algebraMap_mul_jqFun c hc0, ord_cuspInftyBar_jqFun]
  rw [ord_algebraMap_mul_jqFun c hc0, ord_cuspInftyBar_jqFun, ord_cuspInftyBar_jFun]
  omega

include hc0 in
theorem ord_cuspZeroBar_gLine : (cuspZeroBar (1 * q)).ord (gLine (q := q) c) = -(q : ℤ) := by
  have hq : (1 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [gLine, GaussPencil.Mu.ord_add_eq_of_lt _ jFun_ne_zero (algebraMap_mul_jqFun_ne_zero c hc0),
    ord_cuspZeroBar_jFun]
  rw [ord_algebraMap_mul_jqFun c hc0, ord_cuspZeroBar_jqFun, ord_cuspZeroBar_jFun]
  omega

include hc0 in
theorem ord_gLine_nonneg_of_ne (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h₁ : W ≠ cuspInftyBar (1 * q)) (h₂ : W ≠ cuspZeroBar (1 * q)) :
    0 ≤ W.ord (gLine (q := q) c) := by
  rw [gLine]
  refine GaussPencil.Mu.ord_add_nonneg W (ord_jFun_nonneg_of_ne W h₁ h₂) ?_
  rw [ord_algebraMap_mul_jqFun c hc0]; exact ord_jqFun_nonneg_of_ne W h₁ h₂

include hc0 in
theorem transcendental_gLine : Transcendental (AlgebraicClosure ℚ) (gLine (q := q) c) :=
  Place.transcendental_of_ord_ne_zero (cuspZeroBar (1 * q))
    (by rw [ord_cuspZeroBar_gLine c hc0]; exact neg_ne_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).ne_zero))

include hc0 in
theorem finiteDimensional_adjoin_gLine :
    FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({gLine (q := q) c} : Set ↥(modularFunctionFieldBar (1 * q))))
      (modularFunctionFieldBar (1 * q)) := by
  obtain ⟨x, -, hfin⟩ := ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar (1 * q)
  haveI := hfin
  exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x (transcendental_gLine c hc0)

end PencilLine

end ModularCurve.PlaceSpecialization

section
open AlgebraicCurve

namespace GaussPencil

theorem ord_pow_nat {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0)
    (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero =>
    have h := v.ord_mul (one_ne_zero (α := F)) (one_ne_zero (α := F))
    rw [one_mul] at h
    rw [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem isRational_of_line {L : Type*} [Field L] [IsAlgClosed L] {K₁ : Type*} [Field K₁] [Algebra L K₁]
    (e₁ : RatFunc L ≃ₐ[L] K₁) {E : Type*} [Field E] [Algebra L E] [Algebra K₁ E] [IsScalarTower L K₁ E]
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

end GaussPencil

end

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar qExpand qExpand_one_apply jq jqd_mem_full coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization frickeInvolutionBar cuspZeroBar isFrickeAutFull_frickeInvolutionFull cuspInftyBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero frickeInvolutionBar_frickeInvolutionBar ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg exists_transcendental_finiteDimensional_modularFunctionFieldBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

section PencilNorm

open Polynomial

variable {q : ℕ} [Fact q.Prime]

theorem transcendental_gLine' (c : AlgebraicClosure ℚ) : Transcendental (AlgebraicClosure ℚ) (gLine (q := q) c) := by
  by_cases hc0 : c = 0
  · refine Place.transcendental_of_ord_ne_zero (cuspInftyBar (1 * q)) ?_
    rw [gLine, hc0, map_zero, zero_mul, add_zero, ord_cuspInftyBar_jFun]
    norm_num
  · exact transcendental_gLine c hc0

variable (c : AlgebraicClosure ℚ)

noncomputable abbrev KLine : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) ({gLine (q := q) c} : Set ↥(modularFunctionFieldBar (1 * q)))

scoped instance finiteDimensional_KLine :
    FiniteDimensional ↥(KLine (q := q) c) ↥(modularFunctionFieldBar (1 * q)) := by
  obtain ⟨x, -, hfin⟩ := ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar (1 * q)
  haveI := hfin
  exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x (transcendental_gLine' c)

noncomputable def genLine : ↥(KLine (q := q) c) :=
  IntermediateField.AdjoinSimple.gen (AlgebraicClosure ℚ) (gLine (q := q) c)

theorem coe_genLine :
    ((genLine (q := q) c : ↥(KLine (q := q) c)) : ↥(modularFunctionFieldBar (1 * q))) = gLine (q := q) c := rfl

theorem algebraMap_genLine :
    algebraMap ↥(KLine (q := q) c) ↥(modularFunctionFieldBar (1 * q)) (genLine (q := q) c) = gLine (q := q) c := rfl

theorem gLine_ne_zero (hc0 : c ≠ 0) : gLine (q := q) c ≠ 0 :=
  GaussPencil.Mu.ne_zero_of_ord_ne_zero (cuspZeroBar (1 * q))
    (by rw [ord_cuspZeroBar_gLine c hc0]; exact neg_ne_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).ne_zero))

theorem genLine_ne_zero (hc0 : c ≠ 0) : genLine (q := q) c ≠ 0 := by
  intro h
  apply gLine_ne_zero (q := q) c hc0
  have h' := congrArg Subtype.val h
  exact h'

theorem ord_cuspInftyBar_gLine_neg (hc0 : c ≠ 0) : (cuspInftyBar (1 * q)).ord (gLine (q := q) c) < 0 := by
  rw [ord_cuspInftyBar_gLine c hc0]
  exact neg_lt_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)

theorem ord_cuspZeroBar_gLine_neg (hc0 : c ≠ 0) : (cuspZeroBar (1 * q)).ord (gLine (q := q) c) < 0 := by
  rw [ord_cuspZeroBar_gLine c hc0]
  exact neg_lt_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)

noncomputable def eLine (hc0 : c ≠ 0) :
    RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] ↥(KLine (q := q) c) :=
  RatFunc.algEquivOfTranscendental (gLine (q := q) c) (transcendental_gLine c hc0)

theorem eLine_symm_genLine (hc0 : c ≠ 0) : (eLine (q := q) c hc0).symm (genLine (q := q) c) = RatFunc.X :=
  RatFunc.algEquivOfTranscendental_symm_gen _ _

theorem eLine_symm_commutes (hc0 : c ≠ 0) (a : AlgebraicClosure ℚ) :
    ((eLine (q := q) c hc0).symm : ↥(KLine (q := q) c) ≃+* RatFunc (AlgebraicClosure ℚ))
        (algebraMap (AlgebraicClosure ℚ) ↥(KLine (q := q) c) a)
      = algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) a :=
  (eLine (q := q) c hc0).symm.commutes a

noncomputable def toRatPlace (hc0 : c ≠ 0) (v : Place (AlgebraicClosure ℚ) ↥(KLine (q := q) c)) :
    Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
  Place.congrRingEquiv ((eLine (q := q) c hc0).symm : ↥(KLine (q := q) c) ≃+* RatFunc (AlgebraicClosure ℚ))
    (eLine_symm_commutes (q := q) c hc0) v

theorem toRatPlace_injective (hc0 : c ≠ 0) : Function.Injective (toRatPlace (q := q) c hc0) :=
  (Place.congrEquiv ((eLine (q := q) c hc0).symm : ↥(KLine (q := q) c) ≃+* RatFunc (AlgebraicClosure ℚ))
    (eLine_symm_commutes (q := q) c hc0)).injective

theorem ord_toRatPlace_X (hc0 : c ≠ 0) (v : Place (AlgebraicClosure ℚ) ↥(KLine (q := q) c)) :
    (toRatPlace (q := q) c hc0 v).ord (RatFunc.X : RatFunc (AlgebraicClosure ℚ)) = v.ord (genLine (q := q) c) := by
  rw [toRatPlace, ← eLine_symm_genLine (q := q) c hc0]
  exact Place.ord_congrRingEquiv _ (eLine_symm_commutes (q := q) c hc0) v (genLine (q := q) c)

theorem ord_restrict_genLine_neg {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : W.ord (gLine (q := q) c) < 0) : (W.restrict ↥(KLine (q := q) c)).ord (genLine (q := q) c) < 0 := by
  have h := Place.ord_restrict (F := ↥(KLine (q := q) c)) W (genLine (q := q) c)
  rw [algebraMap_genLine] at h
  have he : 0 < (Place.ramificationIndex (F := ↥(KLine (q := q) c)) W : ℤ) := by
    exact_mod_cast Place.ramificationIndex_pos (F := ↥(KLine (q := q) c)) W
  rw [h] at hW
  by_contra hx
  push_neg at hx
  exact absurd hW (not_lt.mpr (mul_nonneg he.le hx))

theorem toRatPlace_restrict_eq_placeInfty [DecidableEq (RatFunc (AlgebraicClosure ℚ))] (hc0 : c ≠ 0)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : W.ord (gLine (q := q) c) < 0) :
    toRatPlace (q := q) c hc0 (W.restrict ↥(KLine (q := q) c)) = RationalFunctionField.placeInfty (AlgebraicClosure ℚ) :=
  RationalFunctionField.eq_placeInfty_of_ord_X_neg _ (by rw [ord_toRatPlace_X]; exact ord_restrict_genLine_neg (q := q) c hW)

noncomputable def vInf : Place (AlgebraicClosure ℚ) ↥(KLine (q := q) c) :=
  (cuspInftyBar (1 * q)).restrict ↥(KLine (q := q) c)

theorem restrict_eq_vInf_of_ord_neg (hc0 : c ≠ 0)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : W.ord (gLine (q := q) c) < 0) :
    W.restrict ↥(KLine (q := q) c) = vInf (q := q) c := by
  classical
  apply toRatPlace_injective (q := q) c hc0
  rw [toRatPlace_restrict_eq_placeInfty (q := q) c hc0 hW, vInf,
    toRatPlace_restrict_eq_placeInfty (q := q) c hc0 (ord_cuspInftyBar_gLine_neg (q := q) c hc0)]

theorem ord_vInf_genLine (hc0 : c ≠ 0) : (vInf (q := q) c).ord (genLine (q := q) c) = -1 := by
  classical
  rw [← ord_toRatPlace_X (q := q) c hc0, vInf, toRatPlace_restrict_eq_placeInfty (q := q) c hc0 (ord_cuspInftyBar_gLine_neg (q := q) c hc0),
    RationalFunctionField.ord_placeInfty RatFunc.X_ne_zero, RatFunc.intDegree_X]

theorem ord_neg_of_restrict_eq_vInf (hc0 : c ≠ 0)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (h : W.restrict ↥(KLine (q := q) c) = vInf (q := q) c) :
    W.ord (gLine (q := q) c) < 0 := by
  have h1 := Place.ord_restrict (F := ↥(KLine (q := q) c)) W (genLine (q := q) c)
  rw [algebraMap_genLine, h, ord_vInf_genLine (q := q) c hc0] at h1
  have he : 0 < (Place.ramificationIndex (F := ↥(KLine (q := q) c)) W : ℤ) := by
    exact_mod_cast Place.ramificationIndex_pos (F := ↥(KLine (q := q) c)) W
  rw [h1]
  linarith

theorem fiberOver_vInf [DecidableEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))] (hc0 : c ≠ 0) :
    (vInf (q := q) c).fiberOver ↥(modularFunctionFieldBar (1 * q)) = {cuspInftyBar (1 * q), cuspZeroBar (1 * q)} := by
  classical
  ext W
  rw [Place.mem_fiberOver, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact absurd (ord_neg_of_restrict_eq_vInf (q := q) c hc0 h) (not_lt.mpr (ord_gLine_nonneg_of_ne c hc0 W hne.1 hne.2))
  · rintro (rfl | rfl)
    · exact restrict_eq_vInf_of_ord_neg (q := q) c hc0 (ord_cuspInftyBar_gLine_neg (q := q) c hc0)
    · exact restrict_eq_vInf_of_ord_neg (q := q) c hc0 (ord_cuspZeroBar_gLine_neg (q := q) c hc0)

theorem inertiaDeg_eq_one (hc0 : c ≠ 0) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    W.inertiaDeg ↥(KLine (q := q) c) = 1 :=
  Place.inertiaDeg_eq_one_of_isRational W (GaussPencil.isRational_of_line (eLine (q := q) c hc0) W)
    (GaussPencil.isRational_of_line (E := ↥(KLine (q := q) c)) (eLine (q := q) c hc0)
      (W.restrict ↥(KLine (q := q) c)))

theorem finrank_KLine (hc0 : c ≠ 0) :
    Module.finrank ↥(KLine (q := q) c) ↥(modularFunctionFieldBar (1 * q)) = 2 * q := by
  classical
  have hnorm := Place.ord_norm_eq_sum_fiberOver (vInf (q := q) c) (gLine_ne_zero (q := q) c hc0)
  have hL : (vInf (q := q) c).ord (Algebra.norm ↥(KLine (q := q) c) (gLine (q := q) c))
      = -(Module.finrank ↥(KLine (q := q) c) ↥(modularFunctionFieldBar (1 * q)) : ℤ) := by
    rw [← algebraMap_genLine c, Algebra.norm_algebraMap, GaussPencil.ord_pow_nat _ (genLine_ne_zero (q := q) c hc0),
      ord_vInf_genLine (q := q) c hc0, mul_neg, mul_one]
  have hR : ∑ w ∈ (vInf (q := q) c).fiberOver ↥(modularFunctionFieldBar (1 * q)),
      (w.inertiaDeg ↥(KLine (q := q) c) : ℤ) * w.ord (gLine (q := q) c) = -(2 * q : ℤ) := by
    rw [fiberOver_vInf (q := q) c hc0, Finset.sum_pair cuspInftyBar_ne_cuspZeroBar, inertiaDeg_eq_one (q := q) c hc0,
      inertiaDeg_eq_one (q := q) c hc0, ord_cuspInftyBar_gLine c hc0, ord_cuspZeroBar_gLine c hc0]
    push_cast
    ring
  rw [hL, hR] at hnorm
  have : (Module.finrank ↥(KLine (q := q) c) ↥(modularFunctionFieldBar (1 * q)) : ℤ) = 2 * q := by linarith
  exact_mod_cast this

end PencilNorm

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.ModularCurve"

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (hc : c ≠ 0) :
    FiniteDimensional
        ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({PlaceSpecialization.jFun (q := q)
              + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
        ↥(modularFunctionFieldBar (1 * q))
      ∧ Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({PlaceSpecialization.jFun (q := q)
                + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                  * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
          ↥(modularFunctionFieldBar (1 * q)) = 2 * q :=
  ⟨finiteDimensional_KLine c, finrank_KLine c hc⟩

end S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun (solution)
