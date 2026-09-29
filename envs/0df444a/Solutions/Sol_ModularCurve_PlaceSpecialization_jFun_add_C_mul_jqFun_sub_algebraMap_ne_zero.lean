-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/deb2a148-8729-5cc0-8329-f07076d63d8b

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

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

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar qExpand qExpand_one_apply jq jqd_mem_full coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization frickeInvolutionBar cuspZeroBar isFrickeAutFull_frickeInvolutionFull cuspInftyBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero frickeInvolutionBar_frickeInvolutionBar ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg"
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

theorem ord_sub_algebraMap_of_ord_neg (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    {f : modularFunctionFieldBar (1 * q)} (hf : W.ord f < 0) (a : AlgebraicClosure ℚ) :
    W.ord (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) a) = W.ord f := by
  by_cases ha : a = 0
  · rw [ha, map_zero, sub_zero]
  have hf0 : f ≠ 0 := GaussPencil.Mu.ne_zero_of_ord_ne_zero W hf.ne
  rw [sub_eq_add_neg, GaussPencil.Mu.ord_add_eq_of_lt W hf0 (neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr ha))]
  rw [GaussPencil.B6.ord_neg', GaussPencil.B6.ord_algebraMap_eq_zero W ha]; exact hf

theorem gLine_sub_algebraMap_ne_zero (c a : AlgebraicClosure ℚ) :
    gLine (q := q) c - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) a ≠ 0 := by
  have hqneg : -(q : ℤ) < 0 := neg_lt_zero.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)
  by_cases hc : c = 0
  · refine GaussPencil.Mu.ne_zero_of_ord_ne_zero (cuspInftyBar (1 * q)) ?_
    have hj : (cuspInftyBar (1 * q)).ord (gLine (q := q) c) = -1 := by
      rw [gLine, hc, map_zero, zero_mul, add_zero]; exact ord_cuspInftyBar_jFun
    rw [ord_sub_algebraMap_of_ord_neg _ (by rw [hj]; norm_num), hj]
    norm_num
  · refine GaussPencil.Mu.ne_zero_of_ord_ne_zero (cuspZeroBar (1 * q)) ?_
    rw [ord_sub_algebraMap_of_ord_neg _ (by rw [ord_cuspZeroBar_gLine c hc]; exact hqneg), ord_cuspZeroBar_gLine c hc]
    exact hqneg.ne

end PencilLine

end ModularCurve.PlaceSpecialization

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] (c a : AlgebraicClosure ℚ) :
    PlaceSpecialization.jFun (q := q)
        + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c * PlaceSpecialization.jqFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a ≠ 0 :=
  gLine_sub_algebraMap_ne_zero c a

end S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero (solution)
