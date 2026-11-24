-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.integral_qMat_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:55.147803+00:00
-- url     : https://prove2.me/submissions/d38fde2b-4ae9-424c-93c2-be42f844b7e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_ae_affine_ne
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_integral_moebius
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_qMat_eq
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_fsDens_eq
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_one_add_ne
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_div_fractions_bilinear_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv
namespace GlobalTheory.FibLine.UnitaryInv
theorem _root_.solution (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    ∫ x : ℂ, qMat (U * H * star U) x ^ k * (fsDens x : ℂ) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have e := fun i j => congrFun (congrFun h1 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, RCLike.star_def,
    if_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false] at e00 e01 e10 e11
  set p := U 0 0 with hp
  set q := U 0 1 with hq
  set r := U 1 0 with hr
  set t := U 1 1 with ht
  set a := starRingEnd ℂ p with ha
  set c := starRingEnd ℂ q with hc
  set b := starRingEnd ℂ r with hb
  set d := starRingEnd ℂ t with hd
  have hDD : (a * d - b * c) * (p * t - r * q) = 1 := by
    linear_combination (r * b + t * d) * e00 + e11 - (r * a + t * c) * e01 - 0 * e10
  have hD : a * d - b * c ≠ 0 := left_ne_zero_of_mul_eq_one hDD
  rw [integral_moebius a b c d hD (fun x => qMat H x ^ k * (fsDens x : ℂ))]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  apply integral_congr_ae
  filter_upwards [ae_affine_ne a b hab] with x hx
  set y := starRingEnd ℂ x with hy
  have hcj : starRingEnd ℂ (a + b * x) = p + r * y := by simp [ha, hb, hy]
  have hcj2 : starRingEnd ℂ (c + d * x) = q + t * y := by simp [hc, hd, hy]
  have hcj3 : starRingEnd ℂ (a * d - b * c) = p * t - r * q := by simp [ha, hb, hc, hd]
  have hx' : p + r * y ≠ 0 := by rw [← hcj]; simpa only [ne_eq, map_eq_zero] using hx
  have hN : 1 + x * y ≠ 0 := one_add_ne x
  have hsum : (a + b * x) * (p + r * y) + (c + d * x) * (q + t * y) = 1 + x * y := by
    linear_combination e00 + x * e01 + y * e10 + x * y * e11
  have hm : 1 + (c + d * x) / (a + b * x) * ((q + t * y) / (p + r * y))
      = (1 + x * y) / ((a + b * x) * (p + r * y)) := by
    rw [← hsum, add_div ((a + b * x) * (p + r * y)), div_self (mul_ne_zero hx hx'), div_mul_div_comm]
  have hq' : qMat H ((c + d * x) / (a + b * x)) = qMat (U * H * star U) x := by
    rw [qMat_eq, qMat_eq, map_div₀, hcj, hcj2, hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, RCLike.star_def]
    rw [← hy, ← hp, ← hq, ← hr, ← ht, ← ha, ← hb, ← hc, ← hd]
    rw [div_fractions_bilinear_formula _ _ _ _ _ _ _ _ _ hx hx' hN]
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf : ((Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2) : ℝ) : ℂ) *
      (fsDens ((c + d * x) / (a + b * x)) : ℂ) = fsDens x := by
    rw [fsDens_eq, fsDens_eq, ← Complex.mul_conj, map_div₀, map_div₀, map_pow, hcj, hcj2, hcj3, hm, ← hy,
      div_mul_div_comm, hDD]
    generalize a + b * x = A at *
    generalize p + r * y = B at *
    generalize 1 + x * y = N at *
    field_simp
  simp only [Complex.real_smul]
  rw [hq', ← hf]
  ring
end GlobalTheory.FibLine.UnitaryInv
