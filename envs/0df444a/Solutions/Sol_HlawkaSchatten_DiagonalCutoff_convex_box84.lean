-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.convex_box84
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T08:08:42.689518+00:00
-- url     : https://prove2.me/submissions/6d9fb221-2975-4704-86de-0b3fffa005f3

import Theorems.Thm_HlawkaCodex84SOSPolynomial_polynomial_row0
import Theorems.Thm_HlawkaCodex84SOSPolynomial_polynomial_row1
import Theorems.Thm_HlawkaCodex84SOSPolynomial_polynomial_row2
import Theorems.Thm_HlawkaCodex84SOSCache_gram_rows0
import Theorems.Thm_HlawkaCodex84SOSCache_gram_rows1
import Theorems.Thm_HlawkaCodex84SOSCache_gram_rows2
import Theorems.Thm_HlawkaCodex84SOSCache_small_certificates
/- Modular cutoff84 dependency, preserving the original exact argument. -/
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib

set_option autoImplicit false
/- Local module: Solutions.Hlawka85_NormCalculus -/
/-
Adapted from Ezzeri Esa's Apache-2.0 Hlawka development, including the
accepted cutoff-87 formalization by Claude Opus 5.5. New coefficient and
box estimates are developed separately for cutoff 85.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex85Curvature
open HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]


theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']


theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i


theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]


theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp


theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))


theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

end Basic

section Norm
variable {ι : Type*} [Fintype ι]

theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p


theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl


theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in

private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]


theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)


theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]


theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))


theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)


theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in

private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm


theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm


theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh


theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring


theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]


theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end Norm

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)


theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)


theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]


theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]


theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)


theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]


theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]


theorem lpNorm_pred_le_three_mul {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ M) :
    lpNorm p v ^ (p - 1) ≤ 3 * M ^ (p - 1) := by
  have hp0 := zero_lt_one.trans hp
  have hN := lpNorm_le_card_root_mul hp0 hM v hv
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hN
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg p v) hN (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by norm_num)] at hpower
  have he : 1 / p * (p - 1) = 1 - 1 / p := by field_simp
  rw [he] at hpower
  have hthree : (3 : ℝ) ^ (1 - 1 / p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show 1 - 1 / p ≤ 1 by have := one_div_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using h
  exact hpower.trans (mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hM _))


end HlawkaCodex85Curvature


/- Local module: Solutions.Sol_Hlawka85_CurvatureMargins -/

set_option autoImplicit false

namespace HlawkaCodex85Margins

/-- Exponential decay beats the linear coefficient on the full tail p ≥ 85. -/
theorem total_margin {p : ℝ} (hp : 85 ≤ p) :
    20 * p * (73 / 80 : ℝ) ^ (p - 2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (20 * 85 : ℝ) < (80 / 73 : ℝ) ^ (83 : ℕ) := by norm_num
  have hlog : (7 / 80 : ℝ) ≤ Real.log (80 / 73) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 80 / 73 by norm_num)
    norm_num at h
    exact h
  have hgrowth : p / 85 ≤ (80 / 73 : ℝ) ^ (p - 85) := by
    have h := Real.add_one_le_exp (Real.log (80 / 73) * (p - 85))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p - 85 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hr : 0 < (80 / 73 : ℝ) ^ (p - 85) := by positivity
  have hprod := mul_lt_mul_of_pos_right hbase hr
  have he : (80 / 73 : ℝ) ^ (83 : ℕ) * (80 / 73 : ℝ) ^ (p - 85) =
      (80 / 73 : ℝ) ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  rw [he] at hprod
  have hlarge : 20 * p < (80 / 73 : ℝ) ^ (p - 2) := by linarith
  have hinv : (73 / 80 : ℝ) ^ (p - 2) = ((80 / 73 : ℝ) ^ (p - 2))⁻¹ := by
    rw [show (73 / 80 : ℝ) = (80 / 73 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
  rw [hinv, ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge

/-- The small-coordinate pair curvature is dominated by column curvature. -/
theorem column_margin {p : ℝ} (hp : 85 ≤ p) :
    3 * (9 / 25 : ℝ) ^ (p - 2) < 9 / 50000 := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 9 / 25)
    (by norm_num : (9 / 25 : ℝ) ≤ 1) (show (83 : ℝ) ≤ p - 2 by linarith)
  have hbase : 3 * (9 / 25 : ℝ) ^ (83 : ℕ) < 9 / 50000 := by norm_num
  rw [← Real.rpow_natCast] at hbase
  linarith

end HlawkaCodex85Margins

theorem HlawkaCodex85Margins.solution : ∀ p : ℝ, 85 ≤ p →
    (20 * p * (73 / 80 : ℝ) ^ (p - 2) < 1) ∧
      (3 * (9 / 25 : ℝ) ^ (p - 2) < 9 / 50000) := by
  intro p hp
  exact ⟨HlawkaCodex85Margins.total_margin hp, HlawkaCodex85Margins.column_margin hp⟩


/- Local module: Solutions.Hlawka85_CoefficientComparison -/

set_option autoImplicit false

namespace HlawkaCodex85Coefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (4177 / 10000 : ℝ) ^ (p - 2) /
    (3 * (15823 / 10000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (8059 / 10000 : ℝ) ^ (p - 2) /
    (3 * (11941 / 10000 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (1941 / 5000 : ℝ) ^ (p - 2) /
    (8059 / 5000 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (427221 / 128944) *
      (30712443 / 33662443 : ℝ) ^ (p - 2) := by
  have hM : (15823 / 10000 : ℝ) ^ (p - 1) =
      (15823 / 10000 : ℝ) ^ (p - 2) * (15823 / 10000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8059 / 5000 : ℝ) ^ (p - 1) =
      (8059 / 5000 : ℝ) ^ (p - 2) * (8059 / 5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (30712443 / 33662443 : ℝ) ^ (p - 2) =
      ((1941 / 5000 : ℝ) ^ (p - 2) * (15823 / 10000 : ℝ) ^ (p - 2)) /
        ((8059 / 5000 : ℝ) ^ (p - 2) * (4177 / 10000 : ℝ) ^ (p - 2)) := by
    rw [show (30712443 / 33662443 : ℝ) =
      ((1941 / 5000) * (15823 / 10000)) / ((8059 / 5000) * (4177 / 10000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (322407 / 128944) *
      (23177481 / 64947481 : ℝ) ^ (p - 2) := by
  have hM : (11941 / 10000 : ℝ) ^ (p - 1) =
      (11941 / 10000 : ℝ) ^ (p - 2) * (11941 / 10000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8059 / 5000 : ℝ) ^ (p - 1) =
      (8059 / 5000 : ℝ) ^ (p - 2) * (8059 / 5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (23177481 / 64947481 : ℝ) ^ (p - 2) =
      ((1941 / 5000 : ℝ) ^ (p - 2) * (11941 / 10000 : ℝ) ^ (p - 2)) /
        ((8059 / 5000 : ℝ) ^ (p - 2) * (8059 / 10000 : ℝ) ^ (p - 2)) := by
    rw [show (23177481 / 64947481 : ℝ) =
      ((1941 / 5000) * (11941 / 10000)) / ((8059 / 5000) * (8059 / 10000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerColumn, hM, hL, hbase]
  field_simp
  ring

theorem lowerTotal_pos {p : ℝ} (hp : 1 < p) : 0 < lowerTotal p := by
  unfold lowerTotal
  positivity

theorem lowerColumn_pos {p : ℝ} (hp : 1 < p) : 0 < lowerColumn p := by
  unfold lowerColumn
  positivity

theorem total_comparison {p : ℝ} (hp : 85 ≤ p) :
    6 * p * upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 30712443 / 33662443)
    (by norm_num : (30712443 / 33662443 : ℝ) ≤ 73 / 80) (show 0 ≤ p - 2 by linarith)
  have hratio : upperPair p ≤ lowerTotal p * (10 / 3) * (73 / 80 : ℝ) ^ (p - 2) := by
    rw [total_ratio]
    calc
      _ ≤ lowerTotal p * (10 / 3) * (30712443 / 33662443 : ℝ) ^ (p - 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (427221 / 128944 : ℝ) ≤ 10 / 3) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hup := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 6 * p by linarith)
  have hmargin := mul_lt_mul_of_pos_left (HlawkaCodex85Margins.total_margin hp) hl
  nlinarith

theorem column_comparison {p : ℝ} (hp : 85 ≤ p) :
    5000 * upperPair p < (9 / 10 : ℝ) * lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 23177481 / 64947481)
    (by norm_num : (23177481 / 64947481 : ℝ) ≤ 9 / 25) (show 0 ≤ p - 2 by linarith)
  have hratio : upperPair p ≤ lowerColumn p * 3 * (9 / 25 : ℝ) ^ (p - 2) := by
    rw [column_ratio]
    calc
      _ ≤ lowerColumn p * 3 * (23177481 / 64947481 : ℝ) ^ (p - 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (322407 / 128944 : ℝ) ≤ 3) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hmargin := mul_lt_mul_of_pos_left (HlawkaCodex85Margins.column_margin hp) hl
  nlinarith

end HlawkaCodex85Coefficients


/- Local module: Solutions.Hlawka85_BoxHessianBounds -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex85Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Coefficients

def codexEntryBox : Set Triple := {X | ∀ j i, |X j i - cyclicCenter j i| ≤ 1941 / 10000}

theorem codexEntryBox_off_lower {X : Triple} (hX : X ∈ codexEntryBox)
    (j i : Fin 3) (hij : i ≠ j) : (8059 / 10000 : ℝ) ≤ X j i := by
  have h := abs_le.mp (hX j i)
  simp only [cyclicCenter, if_neg hij] at h
  linarith

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]


theorem codexEntryBox_column_bounds {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) :
    8059 / 10000 ≤ |X j i| ∧ |X j i| ≤ 11941 / 10000 := by
  have h := abs_le.mp (hX j i)
  by_cases hij : i = j
  · simp only [cyclicCenter, if_pos hij] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [cyclicCenter, if_neg hij] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith


theorem codexEntryBox_total_bounds {X : Triple} (hX : X ∈ codexEntryBox) (i : Fin 3) :
    4177 / 10000 ≤ totalTriple X i ∧ totalTriple X i ≤ 15823 / 10000 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  rw [totalTriple_eq]
  simp only [Pi.add_apply]
  fin_cases i <;> norm_num [cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    constructor <;> linarith!


theorem codexEntryBox_pair_large {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    8059 / 5000 ≤ |pairTriple X j j| := by
  have h0 := abs_le.mp (hX 0 j)
  have h1 := abs_le.mp (hX 1 j)
  have h2 := abs_le.mp (hX 2 j)
  have hl : 8059 / 5000 ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
      linarith!
  exact hl.trans (le_abs_self _)


theorem codexEntryBox_pair_small {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 1941 / 5000 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, cyclicCenter, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!


theorem codexEntryBox_column_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (codexEntryBox_column_bounds hX j 0).1
  norm_num [he] at h


theorem codexEntryBox_total_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (codexEntryBox_total_bounds hX 0).1
  norm_num [he] at h


theorem codexEntryBox_pair_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    pairTriple X j ≠ 0 := by
  intro he
  have h := codexEntryBox_pair_large hX j
  norm_num [he] at h


noncomputable def lowerCoefficient (p m M : ℝ) : ℝ :=
  (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1))

theorem normHessian_lower_generic {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hlo : ∀ i, m ≤ |v i|) (hhi : ∀ i, |v i| ≤ M) :
    lowerCoefficient p m M * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by
    intro hv
    have hh := hlo 0
    simp only [hv, Pi.zero_apply, abs_zero] at hh
    linarith
  have hN := lpNorm_pos hp0 hv
  have hden := lpNorm_pred_le_three_mul (p := p) (by linarith) hM.le v hhi
  have hweight : (m : ℝ) ^ (p - 2) *
      euclideanSq (h - radialCoefficient p v h • v) ≤
        powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le (hlo i) (by linarith))
      (sq_nonneg _)
  have hcoefficient : lowerCoefficient p m M ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * (m : ℝ) ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    change (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1)) ≤ _
    calc
      _ ≤ ((p - 1) * (m : ℝ) ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoefficient (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        ((m : ℝ) ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)



theorem normHessian_upper_canceled {p : ℝ} (hp : 2 < p)
    (v h : Fin 3 → ℝ) (k : Fin 3) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hk : m ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ M) :
    normHessian p v h ≤
      ((p - 1) * M ^ (p - 2) / m ^ (p - 1)) *
        (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hkv : v k ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hk
    linarith
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : m ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm (by linarith) v k)
  have hden : m ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow hm.le hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi'
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
      (sq_nonneg _)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / m ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hm _) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / m ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.rpow_nonneg hM _)
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
    _ = _ := by ring

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (8059 / 5000) (1941 / 5000) (by norm_num) (by norm_num)
    (codexEntryBox_pair_large hX j) (codexEntryBox_pair_small hX j)
  have hc : (p - 1) * (1941 / 5000 : ℝ) ^ (p - 2) / (8059 / 5000 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (1941 / 5000 : ℝ) ^ (p - 2) /
        (8059 / 5000 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (1941 / 5000 : ℝ) ^ (p - 2) /
          (8059 / 5000 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

end HlawkaCodex85Curvature


/- Local module: Solutions.Sol_Hlawka85_RangeGeometry -/

set_option autoImplicit false

namespace HlawkaCodex85Geometry

/-! Recover coefficient spread from two coordinates of a cyclic-box image.
The total-coordinate terms disappear from the antisymmetric combination.
This preserves geometry that the earlier uniform inverse estimate discarded.
-/

theorem extreme_pair_separation
    (m t0 t1 x00 x10 x20 x01 x11 x21 a0 a1 a2 : ℝ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1)
    (hrow0 : t0 = x00 + x10 + x20)
    (hrow1 : t1 = x01 + x11 + x21)
    (h00 : x00 ≤ -m) (h11 : x11 ≤ -m)
    (h10 : m ≤ x10) (h01 : m ≤ x01)
    (ha1 : a1 ≤ a2) (ha0 : a2 ≤ a0) :
    m * (t0 + t1) * (a0 - a1) ≤
      t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) := by
  have hgap : 0 ≤ a0 - a1 := by linarith
  by_cases hc : 0 ≤ t0 * x21 - t1 * x20
  · have hbase : m * (t0 + t1) ≤ t0 * x01 - t1 * x00 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h01),
        mul_nonneg ht1 (show 0 ≤ -x00 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc (sub_nonneg.mpr ha1)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t0 * x01 - t1 * x00) * (a0 - a1) +
          (t0 * x21 - t1 * x20) * (a2 - a1) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith
  · have hc' : 0 ≤ -(t0 * x21 - t1 * x20) := by linarith
    have hbase : m * (t0 + t1) ≤ t1 * x10 - t0 * x11 := by
      nlinarith [mul_nonneg ht1 (sub_nonneg.mpr h10),
        mul_nonneg ht0 (show 0 ≤ -x11 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc' (sub_nonneg.mpr ha0)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t1 * x10 - t0 * x11) * (a0 - a1) -
          (t0 * x21 - t1 * x20) * (a0 - a2) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith

theorem total_pair_shape (s t : ℝ)
    (hslo : 4177 / 10000 ≤ s) (hshi : s ≤ 15823 / 10000)
    (htlo : 4177 / 10000 ≤ t) (hthi : t ≤ 15823 / 10000) :
    s ^ 2 + t ^ 2 ≤ (1031 / 1000 : ℝ) * (8059 / 10000) ^ 2 * (s + t) ^ 2 := by
  have ha : 0 ≤ (15823 / 10000 : ℝ) * s - (4177 / 10000) * t := by
    nlinarith
  have hb : 0 ≤ (15823 / 10000 : ℝ) * t - (4177 / 10000) * s := by
    nlinarith
  have hprod := mul_nonneg ha hb
  nlinarith [sq_nonneg (s + t)]

theorem spread_from_residual_pair (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 4177 / 10000 ≤ t0) (ht0hi : t0 ≤ 15823 / 10000)
    (ht1lo : 4177 / 10000 ≤ t1) (ht1hi : t1 ≤ 15823 / 10000)
    (hgap : 0 ≤ gap)
    (hseparate : (8059 / 10000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (1031 / 1000 : ℝ) * (r0 ^ 2 + r1 ^ 2) := by
  have hleft : 0 ≤ (8059 / 10000 : ℝ) * (t0 + t1) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hseparate
  have hcauchy : (t0 * r1 - t1 * r0) ^ 2 ≤
      (t0 ^ 2 + t1 ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (t0 * r0 + t1 * r1)]
  have hshape := total_pair_shape t0 t1 ht0lo ht0hi ht1lo ht1hi
  have hbound := mul_le_mul_of_nonneg_right hshape
    (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hscale : 0 < (8059 / 10000 : ℝ) ^ 2 * (t0 + t1) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem spread_with_error (t0 t1 d0 d1 u0 u1 gap : ℝ)
    (ht0lo : 4177 / 10000 ≤ t0) (ht0hi : t0 ≤ 15823 / 10000)
    (ht1lo : 4177 / 10000 ≤ t1) (ht1hi : t1 ≤ 15823 / 10000)
    (hgap : 0 ≤ gap)
    (hseparate : (8059 / 10000 : ℝ) * (t0 + t1) * gap ≤
      t0 * (d1 - u1) - t1 * (d0 - u0)) :
    gap ^ 2 ≤ (104131 / 100000 : ℝ) * (d0 ^ 2 + d1 ^ 2) +
      (104131 / 1000 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by
  have h := spread_from_residual_pair t0 t1 (d0 - u0) (d1 - u1) gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
  have h0 : (d0 - u0) ^ 2 ≤ (101 / 100 : ℝ) * d0 ^ 2 + 101 * u0 ^ 2 := by
    nlinarith [sq_nonneg (d0 / 10 + 10 * u0)]
  have h1 : (d1 - u1) ^ 2 ≤ (101 / 100 : ℝ) * d1 ^ 2 + 101 * u1 ^ 2 := by
    nlinarith [sq_nonneg (d1 / 10 + 10 * u1)]
  nlinarith

theorem ordered_pair_difference_sum (a b c : ℝ) (h1 : b ≤ c) (h2 : c ≤ a) :
    (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≤ 2 * (a - b) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

end HlawkaCodex85Geometry

theorem HlawkaCodex85Geometry.solution (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 4177 / 10000 ≤ t0) (ht0hi : t0 ≤ 15823 / 10000)
    (ht1lo : 4177 / 10000 ≤ t1) (ht1hi : t1 ≤ 15823 / 10000)
    (hgap : 0 ≤ gap)
    (hseparate : (8059 / 10000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (1031 / 1000 : ℝ) * (r0 ^ 2 + r1 ^ 2) :=
  HlawkaCodex85Geometry.spread_from_residual_pair t0 t1 r0 r1 gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate


/- Local module: Solutions.Sol_Hlawka85_PairResidualGeometry -/

set_option autoImplicit false

namespace HlawkaCodex85Pairs

theorem weighted_component_bound (a b c d M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |(b * c - a * d) / (a + b)| ≤ M := by
  have hab : 0 < a + b := by positivity
  rw [abs_div, abs_of_pos hab, div_le_iff₀ hab]
  calc
    |b * c - a * d| ≤ |b * c| + |a * d| := abs_sub _ _
    _ = b * |c| + a * |d| := by rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_pos ha]
    _ ≤ b * M + a * M := by gcongr
    _ = M * (a + b) := by ring

theorem four_term_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem error_component_sq (u v w z eta : ℝ) (heta : |eta| ≤ 1) :
    (u + v - eta * (w + z)) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2 + w ^ 2 + z ^ 2) := by
  have he : eta ^ 2 ≤ 1 := by
    have hs := abs_le.mp heta
    nlinarith [sq_abs eta]
  have hw := mul_le_mul_of_nonneg_right he (sq_nonneg w)
  have hz := mul_le_mul_of_nonneg_right he (sq_nonneg z)
  have h := four_term_sq u v (-eta * w) (-eta * z)
  nlinarith

theorem two_error_components_sq (u0 u1 u2 v0 v1 v2 eta0 eta1 : ℝ)
    (h0 : |eta0| ≤ 1) (h1 : |eta1| ≤ 1) :
    (u0 + v0 - eta0 * (u2 + v2)) ^ 2 +
      (u1 + v1 - eta1 * (u2 + v2)) ^ 2 ≤
      8 * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + v0 ^ 2 + v1 ^ 2 + v2 ^ 2) := by
  have he0 := error_component_sq u0 v0 u2 v2 eta0 h0
  have he1 := error_component_sq u1 v1 u2 v2 eta1 h1
  nlinarith [sq_nonneg u0, sq_nonneg u1, sq_nonneg v0, sq_nonneg v1]

theorem young_pair_sq (r e : ℝ) :
    (r + e) ^ 2 ≤ (101 / 100 : ℝ) * r ^ 2 + 101 * e ^ 2 := by
  nlinarith [sq_nonneg (r / 10 - 10 * e)]

/-- The rational constants close the proposed weighted Hessian estimate.
Its premises still have to be supplied for the actual norm Hessians. -/
theorem weighted_pair_bound (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (104131 / 100000 : ℝ) * D + (312393 / 1000 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (11941 / 10000 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (6 * D + 4000 * U) := by
  have hbound : (101 / 100 : ℝ) * 2 * (11941 / 10000 : ℝ) ^ 2 * R + 101 * E ≤
      6 * D + 4000 * U := by
    nlinarith
  exact hpair.trans (mul_le_mul_of_nonneg_left hbound hdp)

end HlawkaCodex85Pairs

theorem HlawkaCodex85Pairs.solution (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (104131 / 100000 : ℝ) * D + (312393 / 1000 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (11941 / 10000 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (6 * D + 4000 * U) :=
  HlawkaCodex85Pairs.weighted_pair_bound P dp D U A R E hdp hD hU
    hspread hdiff herror hpair


/- Local module: Solutions.Hlawka85_TripleGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex85Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Geometry

def pairLeft : Fin 3 → Fin 3 := ![1, 0, 0]
def pairRight : Fin 3 → Fin 3 := ![2, 2, 1]
def pairDifference (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ a (pairLeft j) - a (pairRight j)

theorem pairTriple_eq_indices (X : Triple) (j : Fin 3) :
    pairTriple X j = X (pairLeft j) + X (pairRight j) := by
  fin_cases j <;> rfl

theorem sum_three_distinct (v : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ i, v i) = v j + v k + v l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [Fin.sum_univ_three] <;> ring

theorem exists_ordered_indices (a : Fin 3 → ℝ) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ a k ≤ a l ∧ a l ≤ a j := by
  by_cases h01 : a 0 ≤ a 1
  · by_cases h12 : a 1 ≤ a 2
    · exact ⟨2, 0, 1, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : a 0 ≤ a 2
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h02, le_of_not_ge h12⟩
      · exact ⟨1, 2, 0, by decide, by decide, by decide, le_of_not_ge h02, h01⟩
  · by_cases h02 : a 0 ≤ a 2
    · exact ⟨2, 1, 0, by decide, by decide, by decide, le_of_not_ge h01, h02⟩
    · by_cases h12 : a 1 ≤ a 2
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h12, le_of_not_ge h02⟩
      · exact ⟨0, 2, 1, by decide, by decide, by decide, le_of_not_ge h12, le_of_not_ge h01⟩

theorem pair_difference_ordered (a : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 * (a j - a k) ^ 2 := by
  have hs : (∑ i, pairDifference a i ^ 2) =
      (a j - a k) ^ 2 + (a j - a l) ^ 2 + (a k - a l) ^ 2 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [pairDifference, pairLeft, pairRight, Fin.sum_univ_three] <;> ring
  rw [hs]
  exact ordered_pair_difference_sum _ _ _ hlo hhi

theorem two_coordinates_sq_le (v : Fin 3 → ℝ) (j k : Fin 3) (hjk : j ≠ k) :
    v j ^ 2 + v k ^ 2 ≤ euclideanSq v := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := {j, k}) (t := Finset.univ) (f := fun i ↦ v i ^ 2)
    (Finset.subset_univ _) (fun i _ _ ↦ sq_nonneg _)
  simpa [euclideanSq, Finset.sum_pair hjk] using h

theorem ordered_spread_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (a j - a k) ^ 2 ≤ (104131 / 100000 : ℝ) * euclideanSq D +
      (312393 / 1000 : ℝ) * frobeniusSq U := by
  have hjj : X j j ≤ -(8059 / 10000 : ℝ) := by
    have h := abs_le.mp (hX j j)
    simp [cyclicCenter] at h
    linarith
  have hkk : X k k ≤ -(8059 / 10000 : ℝ) := by
    have h := abs_le.mp (hX k k)
    simp [cyclicCenter] at h
    linarith
  have hkj : (8059 / 10000 : ℝ) ≤ X k j := by
    have h := abs_le.mp (hX k j)
    simp only [cyclicCenter, if_neg hjk] at h
    linarith
  have hjk' : (8059 / 10000 : ℝ) ≤ X j k := by
    have h := abs_le.mp (hX j k)
    simp only [cyclicCenter, if_neg hjk.symm] at h
    linarith
  have htj := codexEntryBox_total_bounds hX j
  have htk := codexEntryBox_total_bounds hX k
  have hsep := extreme_pair_separation (8059 / 10000) (totalTriple X j) (totalTriple X k)
    (X j j) (X k j) (X l j) (X j k) (X k k) (X l k) (a j) (a k) (a l)
    (by linarith) (by linarith)
    (sum_three_distinct (fun i ↦ X i j) j k l hjk hjl hkl)
    (sum_three_distinct (fun i ↦ X i k) j k l hjk hjl hkl)
    hjj hkk hkj hjk' hlo hhi
  have happly (i : Fin 3) : applyTriple X a i = X j i * a j + X k i * a k + X l i * a l := by
    rw [applyTriple, sum_three_distinct _ j k l hjk hjl hkl]
    ring
  have hc : totalTriple X j * (D k - totalTriple U k) -
      totalTriple X k * (D j - totalTriple U j) =
      totalTriple X j * (X j k * a j + X k k * a k + X l k * a l) -
      totalTriple X k * (X j j * a j + X k j * a k + X l j * a l) := by
    rw [hD]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, happly]
    ring
  have hs := spread_with_error (totalTriple X j) (totalTriple X k) (D j) (D k)
    (totalTriple U j) (totalTriple U k) (a j - a k) htj.1 htj.2 htk.1 htk.2
    (by linarith) (by rw [hc]; exact hsep)
  have hd := two_coordinates_sq_le D j k hjk
  have hu := two_coordinates_sq_le (totalTriple U) j k hjk
  have hut := euclideanSq_total_le U
  nlinarith

theorem coefficient_differences_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 *
      ((104131 / 100000 : ℝ) * euclideanSq D + (312393 / 1000 : ℝ) * frobeniusSq U) := by
  obtain ⟨j,k,l,hjk,hjl,hkl,hlo,hhi⟩ := exists_ordered_indices a
  have hs := ordered_spread_bound hX a b U D hD j k l hjk hjl hkl hlo hhi
  have hd := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end HlawkaCodex85Curvature


/- Local module: cached exact SOS certificate facade -/
set_option autoImplicit false
namespace HlawkaCodex84SOSCache
/-- Assemble the independently checked rows into the exact Gram identity. -/
theorem gram_factorization :
    gram = gramLower * Matrix.diagonal gramPivots * gramLower.transpose := by
  ext i j
  by_cases h0 : i.val < 10
  · let k : Fin 10 := ⟨i.val, h0⟩
    have hi : (⟨k.val + 0, by omega⟩ : Fin 30) = i := by
      apply Fin.ext
      simp [k]
    simpa only [hi] using gram_rows0 k j
  · by_cases h1 : i.val < 20
    · let k : Fin 10 := ⟨i.val - 10, by omega⟩
      have hi : (⟨k.val + 10, by dsimp [k]; omega⟩ : Fin 30) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa only [hi] using gram_rows1 k j
    · let k : Fin 10 := ⟨i.val - 20, by omega⟩
      have hi : (⟨k.val + 20, by dsimp [k]; omega⟩ : Fin 30) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa only [hi] using gram_rows2 k j
end HlawkaCodex84SOSCache

namespace HlawkaCodex84SOSData
abbrev gram := HlawkaCodex84SOSCache.gram
abbrev gramLower := HlawkaCodex84SOSCache.gramLower
abbrev gramPivots := HlawkaCodex84SOSCache.gramPivots
abbrev multiplier0 := HlawkaCodex84SOSCache.multiplier0
abbrev multiplier0Lower := HlawkaCodex84SOSCache.multiplier0Lower
abbrev multiplier0Pivots := HlawkaCodex84SOSCache.multiplier0Pivots
abbrev multiplier1 := HlawkaCodex84SOSCache.multiplier1
abbrev multiplier1Lower := HlawkaCodex84SOSCache.multiplier1Lower
abbrev multiplier1Pivots := HlawkaCodex84SOSCache.multiplier1Pivots
abbrev multiplier2 := HlawkaCodex84SOSCache.multiplier2
abbrev multiplier2Lower := HlawkaCodex84SOSCache.multiplier2Lower
abbrev multiplier2Pivots := HlawkaCodex84SOSCache.multiplier2Pivots
abbrev multiplier3 := HlawkaCodex84SOSCache.multiplier3
abbrev multiplier3Lower := HlawkaCodex84SOSCache.multiplier3Lower
abbrev multiplier3Pivots := HlawkaCodex84SOSCache.multiplier3Pivots
abbrev multiplier4 := HlawkaCodex84SOSCache.multiplier4
abbrev multiplier4Lower := HlawkaCodex84SOSCache.multiplier4Lower
abbrev multiplier4Pivots := HlawkaCodex84SOSCache.multiplier4Pivots
abbrev multiplier5 := HlawkaCodex84SOSCache.multiplier5
abbrev multiplier5Lower := HlawkaCodex84SOSCache.multiplier5Lower
abbrev multiplier5Pivots := HlawkaCodex84SOSCache.multiplier5Pivots
abbrev multiplier6 := HlawkaCodex84SOSCache.multiplier6
abbrev multiplier6Lower := HlawkaCodex84SOSCache.multiplier6Lower
abbrev multiplier6Pivots := HlawkaCodex84SOSCache.multiplier6Pivots
abbrev multiplier7 := HlawkaCodex84SOSCache.multiplier7
abbrev multiplier7Lower := HlawkaCodex84SOSCache.multiplier7Lower
abbrev multiplier7Pivots := HlawkaCodex84SOSCache.multiplier7Pivots
abbrev multiplier8 := HlawkaCodex84SOSCache.multiplier8
abbrev multiplier8Lower := HlawkaCodex84SOSCache.multiplier8Lower
abbrev multiplier8Pivots := HlawkaCodex84SOSCache.multiplier8Pivots
theorem gram_factorization : gram = gramLower * Matrix.diagonal gramPivots * gramLower.transpose := HlawkaCodex84SOSCache.gram_factorization
theorem gram_pivots_nonneg : ∀ i, 0 ≤ gramPivots i := HlawkaCodex84SOSCache.small_certificates.1
theorem multiplier0_factorization : multiplier0 = multiplier0Lower * Matrix.diagonal multiplier0Pivots * multiplier0Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.1
theorem multiplier0_pivots_nonneg : ∀ i, 0 ≤ multiplier0Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.1
theorem multiplier1_factorization : multiplier1 = multiplier1Lower * Matrix.diagonal multiplier1Pivots * multiplier1Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.1
theorem multiplier1_pivots_nonneg : ∀ i, 0 ≤ multiplier1Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.1
theorem multiplier2_factorization : multiplier2 = multiplier2Lower * Matrix.diagonal multiplier2Pivots * multiplier2Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.1
theorem multiplier2_pivots_nonneg : ∀ i, 0 ≤ multiplier2Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.1
theorem multiplier3_factorization : multiplier3 = multiplier3Lower * Matrix.diagonal multiplier3Pivots * multiplier3Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.1
theorem multiplier3_pivots_nonneg : ∀ i, 0 ≤ multiplier3Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.1
theorem multiplier4_factorization : multiplier4 = multiplier4Lower * Matrix.diagonal multiplier4Pivots * multiplier4Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.1
theorem multiplier4_pivots_nonneg : ∀ i, 0 ≤ multiplier4Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier5_factorization : multiplier5 = multiplier5Lower * Matrix.diagonal multiplier5Pivots * multiplier5Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier5_pivots_nonneg : ∀ i, 0 ≤ multiplier5Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier6_factorization : multiplier6 = multiplier6Lower * Matrix.diagonal multiplier6Pivots * multiplier6Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier6_pivots_nonneg : ∀ i, 0 ≤ multiplier6Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier7_factorization : multiplier7 = multiplier7Lower * Matrix.diagonal multiplier7Pivots * multiplier7Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier7_pivots_nonneg : ∀ i, 0 ≤ multiplier7Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier8_factorization : multiplier8 = multiplier8Lower * Matrix.diagonal multiplier8Pivots * multiplier8Lower.transpose := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem multiplier8_pivots_nonneg : ∀ i, 0 ≤ multiplier8Pivots i := HlawkaCodex84SOSCache.small_certificates.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
end HlawkaCodex84SOSData

/- Local module: Solutions.Hlawka84_RationalPSD -/

set_option autoImplicit false

namespace HlawkaCodex84Geometry

theorem rational_ldl_real_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (D : n → ℚ)
    (hfactor : A = L * Matrix.diagonal D * L.transpose)
    (hD : ∀ i, 0 ≤ D i) : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  have hf := congrArg (fun M : Matrix n n ℚ => M.map (fun q : ℚ => (q : ℝ))) hfactor
  simp only [Matrix.map_mul_ratCast, Matrix.transpose_map] at hf
  have hdmap : (Matrix.diagonal D).map (fun q : ℚ => (q : ℝ)) =
      Matrix.diagonal (fun i => (D i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [hdmap] at hf
  have hDR : ∀ i, 0 ≤ (D i : ℝ) := by
    intro i
    exact_mod_cast hD i
  have hdiag : (Matrix.diagonal (fun i => (D i : ℝ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hDR
  rw [hf]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hdiag.mul_mul_conjTranspose_same (L.map (fun q : ℚ => (q : ℝ)))

end HlawkaCodex84Geometry


/- Local module: Solutions.Hlawka84_QuadraticSOSPositive -/

set_option autoImplicit false

namespace HlawkaCodex84SOS
open HlawkaCodex84SOSData HlawkaCodex84Geometry
open scoped BigOperators

def realGram : Matrix (Fin 30) (Fin 30) ℝ := gram.map (fun q : ℚ => (q : ℝ))

theorem realGram_posSemidef : realGram.PosSemidef :=
  rational_ldl_real_posSemidef gram gramLower gramPivots gram_factorization gram_pivots_nonneg

def realMultiplier (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℝ :=
  (![multiplier0, multiplier1, multiplier2, multiplier3, multiplier4,
    multiplier5, multiplier6, multiplier7, multiplier8] k).map (fun q : ℚ => (q : ℝ))

theorem realMultiplier_posSemidef (k : Fin 9) : (realMultiplier k).PosSemidef := by
  fin_cases k
  · exact rational_ldl_real_posSemidef multiplier0 multiplier0Lower multiplier0Pivots
      multiplier0_factorization multiplier0_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier1 multiplier1Lower multiplier1Pivots
      multiplier1_factorization multiplier1_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier2 multiplier2Lower multiplier2Pivots
      multiplier2_factorization multiplier2_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier3 multiplier3Lower multiplier3Pivots
      multiplier3_factorization multiplier3_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier4 multiplier4Lower multiplier4Pivots
      multiplier4_factorization multiplier4_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier5 multiplier5Lower multiplier5Pivots
      multiplier5_factorization multiplier5_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier6 multiplier6Lower multiplier6Pivots
      multiplier6_factorization multiplier6_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier7 multiplier7Lower multiplier7Pivots
      multiplier7_factorization multiplier7_pivots_nonneg
  · exact rational_ldl_real_posSemidef multiplier8 multiplier8Lower multiplier8Pivots
      multiplier8_factorization multiplier8_pivots_nonneg

def blockWeights (e : Fin 9 → ℝ) : Fin 10 → ℝ :=
  ![1,e 0,e 1,e 2,e 3,e 4,e 5,e 6,e 7,e 8]
def tensorLift (e : Fin 9 → ℝ) : Matrix (Fin 30) (Fin 3) ℝ :=
  fun j i => if j.val%3 = i.val then blockWeights e ⟨j.val/3, by omega⟩ else 0

noncomputable def certificateMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (tensorLift e).transpose * realGram * tensorLift e +
    ∑ k : Fin 9, ((1953/10000 : ℝ)^2 - (e k)^2) • realMultiplier k

/-- The reconstructed SOS expression is nonnegative on the continuous box.
Identification with the original radial comparison is a separate obligation. -/
theorem certificateMatrix_posSemidef (e : Fin 9 → ℝ)
    (he : ∀ k, |e k| ≤ (1953/10000 : ℝ)) : (certificateMatrix e).PosSemidef := by
  have hbase : ((tensorLift e).transpose * realGram * tensorLift e).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      realGram_posSemidef.conjTranspose_mul_mul_same (tensorLift e)
  have hweight (k : Fin 9) : 0 ≤ (1953/10000 : ℝ)^2 - (e k)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (e k)) (by norm_num : (0 : ℝ) ≤ 1953/10000)).mpr (he k)
    rw [sq_abs] at h
    linarith
  have hsum (s : Finset (Fin 9)) :
      (∑ k ∈ s, ((1953/10000 : ℝ)^2 - (e k)^2) • realMultiplier k).PosSemidef := by
    classical
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty]; exact Matrix.PosSemidef.zero
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact ((realMultiplier_posSemidef k).smul (hweight k)).add ih
  exact hbase.add (hsum Finset.univ)

end HlawkaCodex84SOS


/- Local module: Solutions.Hlawka84_QuadraticSOSCoefficients -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace HlawkaCodex84SOSCoefficients
open HlawkaCodex84SOSData
open scoped BigOperators

def rho : ℚ := 1953/10000
def coefficient : ℚ := 14/5
def center : Matrix (Fin 3) (Fin 3) ℚ := !![-1,1,1; 1,-1,1; 1,1,-1]
def basis (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => if k.val = 3*i.val+j.val then 1 else 0
def pairLeft : Fin 3 → Fin 3 := ![1,0,0]
def pairRight : Fin 3 → Fin 3 := ![2,2,1]
def pairVector (p : Fin 3) : Fin 3 → ℚ :=
  fun i => (if i = pairLeft p then 1 else 0) - (if i = pairRight p then 1 else 0)
def graph (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  ∑ p : Fin 3, if (k.val/3 = (pairLeft p).val ∨ k.val/3 = (pairRight p).val) ∧
      k.val%3 ≠ p.val then
    ((1+rho)/2) • Matrix.vecMulVec (pairVector p) (pairVector p) else 0

def constant : Matrix (Fin 3) (Fin 3) ℚ :=
  coefficient • (center * center.transpose) - ∑ k : Fin 9, graph k
def linear (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  coefficient • (basis k * center.transpose + center * (basis k).transpose) -
    (2 * center ⟨k.val/3, by omega⟩ ⟨k.val%3, by omega⟩) • graph k
def diagonal (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  coefficient • (basis k * (basis k).transpose) - graph k
def cross (i j : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  coefficient • (basis i * (basis j).transpose + basis j * (basis i).transpose)

def multiplier (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![multiplier0,multiplier1,multiplier2,multiplier3,multiplier4,
    multiplier5,multiplier6,multiplier7,multiplier8] k
def nextBlock (k : Fin 9) : Fin 10 := ⟨k.val+1, by omega⟩
def blockIndex (a : Fin 10) (i : Fin 3) : Fin 30 := ⟨3*a.val+i.val, by omega⟩
def block (a b : Fin 10) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => gram (blockIndex a i) (blockIndex b j)





end HlawkaCodex84SOSCoefficients


/- Local module: Solutions.Hlawka84_QuadraticSOSBridge -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace HlawkaCodex84SOS
open scoped BigOperators

def boxMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1+e 0,1+e 1,1+e 2; 1+e 3,-1+e 4,1+e 5; 1+e 6,1+e 7,-1+e 8]

def realGraph (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℝ :=
  (HlawkaCodex84SOSCoefficients.graph k).map (fun q : ℚ => (q : ℝ))

noncomputable def comparisonMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (14/5 : ℝ) • (boxMatrix e * (boxMatrix e).transpose) -
    ∑ k : Fin 9, (boxMatrix e ⟨k.val/3, by omega⟩ ⟨k.val%3, by omega⟩)^2 • realGraph k

theorem certificateMatrix_eq_comparison (e : Fin 9 → ℝ) :
    certificateMatrix e = comparisonMatrix e := by
  change HlawkaCodex84SOSPolynomialData.certificateMatrix e =
    HlawkaCodex84SOSPolynomialData.comparisonMatrix e
  ext i j
  fin_cases i
  · exact HlawkaCodex84SOSPolynomial.polynomial_row0 e j
  · exact HlawkaCodex84SOSPolynomial.polynomial_row1 e j
  · exact HlawkaCodex84SOSPolynomial.polynomial_row2 e j

theorem comparisonMatrix_posSemidef (e : Fin 9 → ℝ)
    (he : ∀ k, |e k| ≤ (1953/10000 : ℝ)) : (comparisonMatrix e).PosSemidef := by
  rw [← certificateMatrix_eq_comparison]
  exact certificateMatrix_posSemidef e he

end HlawkaCodex84SOS


/- Local module: Solutions.Hlawka84_WeightedCancellation -/

set_option autoImplicit false

namespace HlawkaCodex84Geometry

theorem weighted_difference_square (u v a b : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ((v*a-u*b)/(u+v))^2 ≤ (v/(u+v))*a^2 + (u/(u+v))*b^2 := by
  have hsum : 0 < u+v := by positivity
  have hs : 0 ≤ u*v*(a+b)^2 := by positivity
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hsum)).mpr
  · change (v*a-u*b)^2 ≤ _
    have he : ((v/(u+v))*a^2 + (u/(u+v))*b^2)*(u+v)^2 =
        (u+v)*(v*a^2+u*b^2) := by field_simp
    rw [he]
    nlinarith

theorem bounded_weight (lo hi u v : ℝ) (hlo : 0 < lo)
    (hu0 : lo ≤ u) (hu1 : u ≤ hi) (hv0 : lo ≤ v) :
    u/(u+v) ≤ hi/(lo+hi) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo (hu0.trans hu1)
  have hsum : 0 < u+v := by linarith
  have hsum' : 0 < lo+hi := by positivity
  apply (div_le_div_iff₀ hsum hsum').mpr
  have h0 := mul_le_mul_of_nonneg_right hu1 hlo.le
  have h1 := mul_le_mul_of_nonneg_left hv0 hhi.le
  nlinarith

/-- A denominator-free comparison retaining all four input squares. -/
theorem two_coordinate_cancellation_bound (lo hi u v a b c d : ℝ)
    (hlo : 0 < lo) (hu0 : lo ≤ u) (hu1 : u ≤ hi)
    (hv0 : lo ≤ v) (hv1 : v ≤ hi) :
    ((v*a-u*b)/(u+v))^2 + ((v*c-u*d)/(u+v))^2 ≤
      (hi/(lo+hi))*(a^2+b^2+c^2+d^2) := by
  have hu : 0 < u := lt_of_lt_of_le hlo hu0
  have hv : 0 < v := lt_of_lt_of_le hlo hv0
  have h0 := weighted_difference_square u v a b hu hv
  have h1 := weighted_difference_square u v c d hu hv
  have hw0 := bounded_weight lo hi u v hlo hu0 hu1 hv0
  have hw1 : v/(u+v) ≤ hi/(lo+hi) := by
    simpa only [add_comm] using bounded_weight lo hi v u hlo hv0 hv1 hu0
  have h2 := mul_le_mul_of_nonneg_right hw1 (sq_nonneg a)
  have h3 := mul_le_mul_of_nonneg_right hw0 (sq_nonneg b)
  have h4 := mul_le_mul_of_nonneg_right hw1 (sq_nonneg c)
  have h5 := mul_le_mul_of_nonneg_right hw0 (sq_nonneg d)
  nlinarith

end HlawkaCodex84Geometry


/- Local module: Solutions.Hlawka84_RadialOperator -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace HlawkaCodex84Geometry
open HlawkaCodex84SOS
open scoped BigOperators

def pairL : Fin 3 → Fin 3 := ![1,0,0]
def pairR : Fin 3 → Fin 3 := ![2,2,1]
def entryBox84 (X : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ j i, |X j i - (if j=i then -1 else 1)| ≤ (1953/10000 : ℝ)
def perturbation (X : Matrix (Fin 3) (Fin 3) ℝ) : Fin 9 → ℝ :=
  ![X 0 0+1,X 0 1-1,X 0 2-1,X 1 0-1,X 1 1+1,X 1 2-1,
    X 2 0-1,X 2 1-1,X 2 2+1]
noncomputable def coarsePairEnergy (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : ℝ :=
  (11953/20000 : ℝ) * ∑ j : Fin 3, ∑ i : Fin 3,
    if i=j then 0 else (X (pairL j) i^2 + X (pairR j) i^2)*(a (pairL j)-a (pairR j))^2
def transposeEnergy (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, (∑ j : Fin 3, X j i * a j)^2

theorem perturbation_mem_box (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X) :
    ∀ k, |perturbation X k| ≤ (1953/10000 : ℝ) := by
  intro k
  fin_cases k
  · simpa [perturbation] using hX 0 0
  · simpa [perturbation] using hX 0 1
  · simpa [perturbation] using hX 0 2
  · simpa [perturbation] using hX 1 0
  · simpa [perturbation] using hX 1 1
  · simpa [perturbation] using hX 1 2
  · simpa [perturbation] using hX 2 0
  · simpa [perturbation] using hX 2 1
  · simpa [perturbation] using hX 2 2

theorem coarsePairEnergy_le (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) : coarsePairEnergy X a ≤ (14/5 : ℝ)*transposeEnergy X a := by
  have h := comparisonMatrix_posSemidef (perturbation X) (perturbation_mem_box X hX)
  have hq := h.dotProduct_mulVec_nonneg a
  apply sub_nonneg.mp
  convert! hq using 2
  norm_num [coarsePairEnergy, transposeEnergy, pairL, pairR,
    comparisonMatrix, boxMatrix, perturbation, realGraph,
    HlawkaCodex84SOSCoefficients.graph, HlawkaCodex84SOSCoefficients.pairVector,
    HlawkaCodex84SOSCoefficients.pairLeft, HlawkaCodex84SOSCoefficients.pairRight,
    HlawkaCodex84SOSCoefficients.rho, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose, Matrix.map, Matrix.vecMulVec, Fin.succ, Fin.mk.injEq,
    Fin.sum_univ_succ]
  try simp
  ring!

noncomputable def radialComponent (X : Matrix (Fin 3) (Fin 3) ℝ)
    (a : Fin 3 → ℝ) (j i : Fin 3) : ℝ :=
  (a (pairL j)-a (pairR j))*
    ((X (pairR j) j*X (pairL j) i-X (pairL j) j*X (pairR j) i) /
      (X (pairL j) j+X (pairR j) j))
noncomputable def radialEnergy (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, if i=j then 0 else (radialComponent X a j i)^2

theorem off_bounds (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (j i : Fin 3) (hji : j ≠ i) :
    (8047/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11953/10000 : ℝ) := by
  have h := abs_le.mp (hX j i)
  rw [if_neg hji] at h
  constructor <;> linarith

theorem radial_pair_le_coarse (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i : Fin 3, if i=j then 0 else (radialComponent X a j i)^2) ≤
      (11953/20000 : ℝ) * ∑ i : Fin 3, if i=j then 0 else
        (X (pairL j) i^2+X (pairR j) i^2)*(a (pairL j)-a (pairR j))^2 := by
  have hlj : pairL j ≠ j := by fin_cases j <;> decide
  have hrj : pairR j ≠ j := by fin_cases j <;> decide
  have hu := off_bounds X hX (pairL j) j hlj
  have hv := off_bounds X hX (pairR j) j hrj
  have hw := two_coordinate_cancellation_bound (8047/10000) (11953/10000)
    (X (pairL j) j) (X (pairR j) j)
    (X (pairL j) (pairL j)) (X (pairR j) (pairL j))
    (X (pairL j) (pairR j)) (X (pairR j) (pairR j))
    (by norm_num) hu.1 hu.2 hv.1 hv.2
  have hm := mul_le_mul_of_nonneg_right hw (sq_nonneg (a (pairL j)-a (pairR j)))
  fin_cases j <;>
    norm_num [radialComponent, pairL, pairR, Fin.sum_univ_succ, mul_pow, Fin.succ] at hm ⊢ <;>
    convert! hm using 1 <;> ring!

/-- Uniform canceled radial bound on the continuous radius-.1953 box. -/
theorem radialEnergy_le (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) : radialEnergy X a ≤ (14/5 : ℝ)*transposeEnergy X a := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => radial_pair_le_coarse X hX a j)
  have hcoarse : radialEnergy X a ≤ coarsePairEnergy X a := by
    simpa only [radialEnergy, coarsePairEnergy, Finset.mul_sum] using h
  exact hcoarse.trans (coarsePairEnergy_le X hX a)

theorem radialComponent_shift (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ)
    (b : ℝ) (j i : Fin 3) :
    radialComponent X (fun k => a k-b) j i = radialComponent X a j i := by
  unfold radialComponent
  simp only
  congr 1
  ring

theorem radialEnergy_shift (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (b : ℝ) :
    radialEnergy X (fun k => a k-b) = radialEnergy X a := by
  simp only [radialEnergy, radialComponent_shift]

theorem transposeEnergy_shift (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (b : ℝ) :
    transposeEnergy X (fun k => a k-b) =
      ∑ i : Fin 3, ((∑ j : Fin 3, X j i*a j)-b*(∑ j : Fin 3, X j i))^2 := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Fin.sum_univ_three]
  ring

theorem radialEnergy_le_relative (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) (b : ℝ) : radialEnergy X a ≤ (14/5 : ℝ) *
      ∑ i : Fin 3, ((∑ j : Fin 3, X j i*a j)-b*(∑ j : Fin 3, X j i))^2 := by
  have h := radialEnergy_le X hX (fun k => a k-b)
  rwa [radialEnergy_shift, transposeEnergy_shift] at h

end HlawkaCodex84Geometry


/- Local module: Solutions.Hlawka84_BoxBounds -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex84Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature

def codexEntryBox : Set Triple := {X | ∀ j i, |X j i - cyclicCenter j i| ≤ 1953 / 10000}

theorem codexEntryBox_off_lower {X : Triple} (hX : X ∈ codexEntryBox)
    (j i : Fin 3) (hij : i ≠ j) : (8047 / 10000 : ℝ) ≤ X j i := by
  have h := abs_le.mp (hX j i)
  simp only [cyclicCenter, if_neg hij] at h
  linarith

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]


theorem codexEntryBox_column_bounds {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) :
    8047 / 10000 ≤ |X j i| ∧ |X j i| ≤ 11953 / 10000 := by
  have h := abs_le.mp (hX j i)
  by_cases hij : i = j
  · simp only [cyclicCenter, if_pos hij] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [cyclicCenter, if_neg hij] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith


theorem codexEntryBox_total_bounds {X : Triple} (hX : X ∈ codexEntryBox) (i : Fin 3) :
    4141 / 10000 ≤ totalTriple X i ∧ totalTriple X i ≤ 15859 / 10000 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  rw [totalTriple_eq]
  simp only [Pi.add_apply]
  fin_cases i <;> norm_num [cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    constructor <;> linarith!


theorem codexEntryBox_pair_large {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    8047 / 5000 ≤ |pairTriple X j j| := by
  have h0 := abs_le.mp (hX 0 j)
  have h1 := abs_le.mp (hX 1 j)
  have h2 := abs_le.mp (hX 2 j)
  have hl : 8047 / 5000 ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
      linarith!
  exact hl.trans (le_abs_self _)


theorem codexEntryBox_pair_small {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 1953 / 5000 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, cyclicCenter, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!


theorem codexEntryBox_column_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (codexEntryBox_column_bounds hX j 0).1
  norm_num [he] at h


theorem codexEntryBox_total_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (codexEntryBox_total_bounds hX 0).1
  norm_num [he] at h


theorem codexEntryBox_pair_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    pairTriple X j ≠ 0 := by
  intro he
  have h := codexEntryBox_pair_large hX j
  norm_num [he] at h


end HlawkaCodex84Curvature


/- Local module: Solutions.Hlawka84_ResidualCombination -/

set_option autoImplicit false

namespace HlawkaCodex84Geometry
open scoped BigOperators

def residualSq (U : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ j, ∑ i, U j i ^ 2

theorem total_residual_sq_le (U : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i : Fin 3, (∑ j : Fin 3, U j i)^2) ≤ 3 * residualSq U := by
  have h (i : Fin 3) : (∑ j : Fin 3, U j i)^2 ≤ 3 * ∑ j : Fin 3, U j i^2 := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (U 0 i-U 1 i), sq_nonneg (U 0 i-U 2 i),
      sq_nonneg (U 1 i-U 2 i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [← Finset.mul_sum, Finset.sum_comm] at hs
  exact hs

theorem radialEnergy_le_deficit (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) (D : Fin 3 → ℝ)
    (hD : ∀ i, D i = (∑ j, X j i*a j)+(∑ j, U j i)-b*(∑ j, X j i)) :
    radialEnergy X a ≤ (707/250 : ℝ)*(∑ i, D i^2)+(4242/5 : ℝ)*residualSq U := by
  have hr := radialEnergy_le_relative X hX a b
  have hi (i : Fin 3) : ((∑ j, X j i*a j)-b*(∑ j, X j i))^2 ≤
      (101/100 : ℝ)*D i^2+101*(∑ j, U j i)^2 := by
    have he : (∑ j, X j i*a j)-b*(∑ j, X j i) = D i-(∑ j, U j i) := by
      linarith [hD i]
    rw [he]
    simpa only [neg_sq, sub_eq_add_neg] using
      HlawkaCodex85Pairs.young_pair_sq (D i) (-(∑ j, U j i))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht := total_residual_sq_le U
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 14/5)
  linarith

/-- Combines the uniform radial estimate with the two Young inequalities.
The explicit premises are the canceled-pair and residual-error estimates. -/
theorem canceled_energy_le_deficit (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : entryBox84 X)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) (D : Fin 3 → ℝ)
    (hD : ∀ i, D i = (∑ j, X j i*a j)+(∑ j, U j i)-b*(∑ j, X j i))
    (C E : ℝ) (hC : C ≤ (101/100 : ℝ)*radialEnergy X a+101*E)
    (hE : E ≤ 16*residualSq U) :
    C ≤ (143/50 : ℝ)*(∑ i, D i^2)+2500*residualSq U := by
  have hr := radialEnergy_le_deficit X hX a b U D hD
  have hm := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 101/100)
  have hd : 0 ≤ ∑ i, D i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hf : 0 ≤ residualSq U := Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _))
  linarith

end HlawkaCodex84Geometry


/- Local module: Solutions.Hlawka84_PairErrors -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex84Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature HlawkaCodex85Pairs

noncomputable def pairRadial (X : Triple) (a : Fin 3 → ℝ) (j i : Fin 3) : ℝ :=
  pairDifference a j *
    ((X (pairRight j) j * X (pairLeft j) i - X (pairLeft j) j * X (pairRight j) i) /
      (X (pairLeft j) j + X (pairRight j) j))

noncomputable def pairError (X U : Triple) (j i : Fin 3) : ℝ :=
  pairTriple U j i - (pairTriple X j i / pairTriple X j j) * pairTriple U j j

noncomputable def canceledPairSq (X Z : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j,
    (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2

noncomputable def radialPairSq (X : Triple) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairRadial X a j i ^ 2

noncomputable def errorPairSq (X U : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairError X U j i ^ 2

theorem pair_indices_off (j : Fin 3) : j ≠ pairLeft j ∧ j ≠ pairRight j := by
  fin_cases j <;> decide

theorem canceled_pair_decomposition {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (j i : Fin 3) :
    pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i =
      pairRadial X a j i + pairError X U j i := by
  have ho := pair_indices_off j
  have hl := codexEntryBox_off_lower hX (pairLeft j) j ho.1
  have hr := codexEntryBox_off_lower hX (pairRight j) j ho.2
  have hden : X (pairLeft j) j + X (pairRight j) j ≠ 0 := by linarith
  simp only [pairRadial, pairError, pairDifference, pairTriple_eq_indices, Pi.add_apply, hZ]
  field_simp
  ring

theorem error_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (U : Triple) (j : Fin 3) :
    errorPairSq X U j ≤ 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j))) := by
  have hlarge := codexEntryBox_pair_large hX j
  have heta (i : Fin 3) (hij : i ≠ j) : |pairTriple X j i / pairTriple X j j| ≤ 1 := by
    rw [abs_div, div_le_iff₀ (by linarith : 0 < |pairTriple X j j|)]
    linarith [codexEntryBox_pair_small hX j i hij]
  have hi (i : Fin 3) (hij : i ≠ j) : pairError X U j i ^ 2 ≤
      4 * (U (pairLeft j) i ^ 2 + U (pairRight j) i ^ 2 +
        U (pairLeft j) j ^ 2 + U (pairRight j) j ^ 2) := by
    simpa only [pairError, pairTriple_eq_indices, Pi.add_apply] using
      error_component_sq (U (pairLeft j) i) (U (pairRight j) i)
        (U (pairLeft j) j) (U (pairRight j) j) _ (heta i hij)
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i hi' ↦ hi i (Finset.mem_erase.mp hi').1)
  have hsL : (∑ i ∈ Finset.univ.erase j, U (pairLeft j) i ^ 2) + U (pairLeft j) j ^ 2 =
      euclideanSq (U (pairLeft j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hsR : (∑ i ∈ Finset.univ.erase j, U (pairRight j) i ^ 2) + U (pairRight j) j ^ 2 =
      euclideanSq (U (pairRight j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  change errorPairSq X U j ≤ _ at hh
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hh
  have hsL0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairLeft j) i))
  have hsR0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairRight j) i))
  linarith

theorem error_pairs_sq_bound {X : Triple} (hX : X ∈ codexEntryBox) (U : Triple) :
    (∑ j, errorPairSq X U j) ≤ 16 * frobeniusSq U := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ error_pair_sq_bound hX U j)
  have hs : (∑ j, 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j)))) =
      16 * frobeniusSq U := by
    simp only [pairLeft, pairRight, frobeniusSq, Fin.sum_univ_three]
    simp
    ring
  rwa [hs] at hh

theorem canceled_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i) (j : Fin 3) :
    canceledPairSq X Z j ≤ (101 / 100 : ℝ) * radialPairSq X a j + 101 * errorPairSq X U j := by
  unfold canceledPairSq radialPairSq errorPairSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [canceled_pair_decomposition hX Z U a hZ j i]
  exact young_pair_sq _ _


theorem radial_pairs_eq_energy (X : Triple) (a : Fin 3 → ℝ) :
    (∑ j, radialPairSq X a j) = HlawkaCodex84Geometry.radialEnergy X a := by
  unfold radialPairSq HlawkaCodex84Geometry.radialEnergy
  apply Finset.sum_congr rfl
  intro j _
  fin_cases j <;>
    simp [Fin.sum_univ_three, pairRadial, pairDifference,
      pairLeft, pairRight, HlawkaCodex84Geometry.radialComponent,
      HlawkaCodex84Geometry.pairL, HlawkaCodex84Geometry.pairR] <;> ring

theorem entryBox_to_matrix {X : Triple} (hX : X ∈ codexEntryBox) :
    HlawkaCodex84Geometry.entryBox84 X := by
  intro j i
  simpa only [cyclicCenter, eq_comm] using hX j i

theorem canceled_pairs_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, canceledPairSq X Z j) ≤ (143/50 : ℝ)*euclideanSq D+2500*frobeniusSq U := by
  have hc := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => canceled_pair_sq_bound hX Z U a hZ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    radial_pairs_eq_energy] at hc
  have he := error_pairs_sq_bound hX U
  have hd (i : Fin 3) : D i = (∑ j, X j i*a j)+(∑ j, U j i)-b*(∑ j, X j i) := by
    simp only [hD, applyTriple, totalTriple, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_comm]
  exact HlawkaCodex84Geometry.canceled_energy_le_deficit X (entryBox_to_matrix hX)
    a b U D hd (∑ j, canceledPairSq X Z j) (∑ j, errorPairSq X U j) hc he

end HlawkaCodex84Curvature


/- Local module: Solutions.Hlawka84_TotalCurvatureMargin -/

set_option autoImplicit false

namespace HlawkaCodex84Margins

/-- The exact scalar margin needed for a radial coefficient 143/50 and K≤p/2. -/
theorem total_margin {p : ℝ} (hp : 84 ≤ p) :
    (4710123 / 990400 : ℝ) * p * (30972627 / 33322627 : ℝ) ^ (p-2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (4710123 / 990400 * 84 : ℝ) <
      (33322627 / 30972627 : ℝ) ^ (82 : ℕ) := by norm_num
  have hlog : (1/84 : ℝ) ≤ Real.log (33322627 / 30972627) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 33322627 / 30972627 by norm_num)
    norm_num at h
    linarith
  have hgrowth : p/84 ≤ (33322627 / 30972627 : ℝ) ^ (p-84) := by
    have h := Real.add_one_le_exp (Real.log (33322627 / 30972627) * (p-84))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p-84 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hprod := mul_lt_mul_of_pos_right hbase
    (show 0 < (33322627 / 30972627 : ℝ) ^ (p-84) by positivity)
  have he : (33322627 / 30972627 : ℝ) ^ (82 : ℕ) *
      (33322627 / 30972627 : ℝ) ^ (p-84) = (33322627 / 30972627 : ℝ) ^ (p-2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he] at hprod
  have hlarge : (4710123 / 990400 : ℝ)*p < (33322627 / 30972627 : ℝ) ^ (p-2) := by
    nlinarith
  rw [show (30972627 / 33322627 : ℝ) = (33322627 / 30972627 : ℝ)⁻¹ by norm_num,
    Real.inv_rpow (by norm_num), ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge

end HlawkaCodex84Margins


/- Local module: Solutions.Hlawka84_CoefficientComparison -/

set_option autoImplicit false

namespace HlawkaCodex84Coefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (4141 / 10000 : ℝ) ^ (p - 2) /
    (3 * (15859 / 10000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (8047 / 10000 : ℝ) ^ (p - 2) /
    (3 * (11953 / 10000 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (1953 / 5000 : ℝ) ^ (p - 2) /
    (8047 / 5000 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (428193 / 128752) *
      (30972627 / 33322627 : ℝ) ^ (p - 2) := by
  have hM : (15859 / 10000 : ℝ) ^ (p - 1) =
      (15859 / 10000 : ℝ) ^ (p - 2) * (15859 / 10000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8047 / 5000 : ℝ) ^ (p - 1) =
      (8047 / 5000 : ℝ) ^ (p - 2) * (8047 / 5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (30972627 / 33322627 : ℝ) ^ (p - 2) =
      ((1953 / 5000 : ℝ) ^ (p - 2) * (15859 / 10000 : ℝ) ^ (p - 2)) /
        ((8047 / 5000 : ℝ) ^ (p - 2) * (4141 / 10000 : ℝ) ^ (p - 2)) := by
    rw [show (30972627 / 33322627 : ℝ) =
      ((1953 / 5000) * (15859 / 10000)) / ((8047 / 5000) * (4141 / 10000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (322731 / 128752) *
      (23344209 / 64754209 : ℝ) ^ (p - 2) := by
  have hM : (11953 / 10000 : ℝ) ^ (p - 1) =
      (11953 / 10000 : ℝ) ^ (p - 2) * (11953 / 10000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8047 / 5000 : ℝ) ^ (p - 1) =
      (8047 / 5000 : ℝ) ^ (p - 2) * (8047 / 5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (23344209 / 64754209 : ℝ) ^ (p - 2) =
      ((1953 / 5000 : ℝ) ^ (p - 2) * (11953 / 10000 : ℝ) ^ (p - 2)) /
        ((8047 / 5000 : ℝ) ^ (p - 2) * (8047 / 10000 : ℝ) ^ (p - 2)) := by
    rw [show (23344209 / 64754209 : ℝ) =
      ((1953 / 5000) * (11953 / 10000)) / ((8047 / 5000) * (8047 / 10000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerColumn, hM, hL, hbase]
  field_simp
  ring

theorem lowerTotal_pos {p : ℝ} (hp : 1 < p) : 0 < lowerTotal p := by
  unfold lowerTotal
  positivity

theorem lowerColumn_pos {p : ℝ} (hp : 1 < p) : 0 < lowerColumn p := by
  unfold lowerColumn
  positivity

theorem total_comparison {p : ℝ} (hp : 84 ≤ p) :
    (143/100 : ℝ)*p*upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  have hm := mul_lt_mul_of_pos_left (HlawkaCodex84Margins.total_margin hp) hl
  rw [total_ratio]
  calc
    _ = lowerTotal p*((4710123/990400 : ℝ)*p*(30972627/33322627 : ℝ)^(p-2)) := by ring
    _ < lowerTotal p := by simpa only [mul_one] using hm

theorem column_margin {p : ℝ} (hp : 84 ≤ p) :
    3*(37/100 : ℝ)^(p-2) < 9/25000 := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 37/100)
    (by norm_num : (37/100 : ℝ) ≤ 1) (show (82 : ℝ) ≤ p-2 by linarith)
  have hb : 3*(37/100 : ℝ)^(82 : ℕ) < 9/25000 := by norm_num
  rw [← Real.rpow_natCast] at hb
  linarith

theorem column_comparison {p : ℝ} (hp : 84 ≤ p) :
    2500*upperPair p < (9/10 : ℝ)*lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 23344209/64754209)
    (by norm_num : (23344209/64754209 : ℝ) ≤ 37/100) (show 0 ≤ p-2 by linarith)
  have hratio : upperPair p ≤ lowerColumn p*3*(37/100 : ℝ)^(p-2) := by
    rw [column_ratio]
    calc
      _ ≤ lowerColumn p*3*(23344209/64754209 : ℝ)^(p-2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (322731/128752 : ℝ) ≤ 3) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hm := mul_lt_mul_of_pos_left (column_margin hp) hl
  nlinarith

end HlawkaCodex84Coefficients


/- Local module: Solutions.Hlawka84_PairHessian -/

set_option autoImplicit false
namespace HlawkaCodex84Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex84Coefficients
open HlawkaCodex85Curvature (normHessian_upper_canceled)

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (8047 / 5000) (1953 / 5000) (by norm_num) (by norm_num)
    (codexEntryBox_pair_large hX j) (codexEntryBox_pair_small hX j)
  have hc : (p - 1) * (1953 / 5000 : ℝ) ^ (p - 2) / (8047 / 5000 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (1953 / 5000 : ℝ) ^ (p - 2) /
        (8047 / 5000 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (1953 / 5000 : ℝ) ^ (p - 2) /
          (8047 / 5000 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

theorem pair_hessian_sum_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      upperPair p * ((143/50) * euclideanSq D + 2500 * frobeniusSq U) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ pair_hessian_canceled_bound hp hX Z j)
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    ∑ j, upperPair p * canceledPairSq X Z j at hh
  rw [← Finset.mul_sum] at hh
  have hpred : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ upperPair p := by unfold upperPair; positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (canceled_pairs_sq_bound hX Z U a b D hZ hD) hcoef)

end HlawkaCodex84Curvature


/- Local module: Solutions.Hlawka84_DeficitHessian -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex84Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex84Coefficients
open HlawkaCodex85Curvature (normHessian_lower_generic lowerCoefficient normHessian_nonneg euclideanSq_nonneg frobeniusSq_nonneg)

theorem deficitHessian_nonneg {p K : ℝ} (hp : 84 ≤ p)
    (hKlo : (20 / 43 : ℝ) * p ≤ K) (hKhi : K ≤ p/2)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) :
    0 ≤ deficitHessian p K X Z := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hZ : ∀ j i, Z j i = a j * X j i + U j i := by
    intro j i
    dsimp [U]
    ring
  have htotal : totalTriple Z = applyTriple X a + totalTriple U := by
    funext i
    change (∑ j, Z j i) = (∑ j, a j * X j i) + (∑ j, U j i)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hZ j i
  have hD : D = applyTriple X a + totalTriple U - b • totalTriple X := by
    dsimp only [D]
    rw [htotal]
  have hcol (j : Fin 3) : lowerColumn p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    simpa only [lowerColumn, lowerCoefficient, U, a] using
      normHessian_lower_generic hp2 (X j) (Z j) (8047 / 10000) (11953 / 10000)
        (by norm_num) (by norm_num)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).1)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).2)
  have hcols : lowerColumn p * frobeniusSq U ≤ ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerTotal p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower_generic hp2 _ _ (4141 / 10000) (15859 / 10000)
      (by norm_num) (by norm_num)
    · intro i
      have hi := codexEntryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := codexEntryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hweight : (9 / 10 : ℝ) * p ≤ 2 * K - 1 := by linarith
  have hpos1 := mul_le_mul_of_nonneg_left hcols (show 0 ≤ (9 / 10 : ℝ) * p by positivity)
  have hpos2 := mul_le_mul_of_nonneg_right hweight hcols0
  have hpairs := pair_hessian_sum_bound hp2 hX Z U a b D hZ hD
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p/2 by positivity)
  have hneg2 := mul_le_mul_of_nonneg_right hKhi hpair0
  have hD0 := euclideanSq_nonneg D
  have hU0 := frobeniusSq_nonneg U
  have hmarginD := mul_le_mul_of_nonneg_right (total_comparison hp).le hD0
  have hdpos : 0 ≤ upperPair p := by
    have hpred : 0 ≤ p - 1 := by linarith
    unfold upperPair
    positivity
  have hmarginUp := mul_le_mul_of_nonneg_left (column_comparison hp).le hp0
  have hmarginUcoef : 1250 * p * upperPair p ≤ (9 / 10 : ℝ) * p * lowerColumn p := by
    nlinarith [mul_nonneg hp0 hdpos]
  have hmarginU := mul_le_mul_of_nonneg_right hmarginUcoef hU0
  unfold deficitHessian
  nlinarith

end HlawkaCodex84Curvature


/- Local module: Solutions.Hlawka84_BoxConvexity -/
/- Adapted from the Apache-2.0 Hlawka development by Ezzeri Esa and the
accepted cutoff-87 source produced by Claude Opus 5.5. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex84Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature (hasDerivAt_lpNorm_line hasDerivAt_normSlope_line continuous_lpNorm)

theorem convex_codexEntryBox : Convex ℝ codexEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have heq : (a • X + b • Y) j i - cyclicCenter j i =
      a * (X j i - cyclicCenter j i) + b * (Y j i - cyclicCenter j i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * cyclicCenter j i) hab]
  rw [heq]
  calc
    _ ≤ |a * (X j i - cyclicCenter j i)| + |b * (Y j i - cyclicCenter j i)| := abs_add_le _ _
    _ = a * |X j i - cyclicCenter j i| + b * |Y j i - cyclicCenter j i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (1953 / 10000) + b * (1953 / 10000) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX j i) ha)
        (mul_le_mul_of_nonneg_left (hY j i) hb)
    _ = 1953 / 10000 := by nlinarith



theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring


theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]


theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring


theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ codexEntryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (codexEntryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact codexEntryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact codexEntryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ codexEntryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (codexEntryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact codexEntryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact codexEntryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))


theorem convexOn_tripleDeficit {p K : ℝ} (hp : 84 ≤ p) (hK : (20 / 43 : ℝ) * p ≤ K) (hKp : K ≤ p/2) :
    ConvexOn ℝ codexEntryBox (tripleDeficit p K) := by
  refine ⟨convex_codexEntryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ codexEntryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_codexEntryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact deficitHessian_nonneg hp hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end HlawkaCodex84Curvature

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p K : ℝ, 84 ≤ p → (20/43 : ℝ)*p ≤ K → K ≤ p/2 →
    ConvexOn ℝ {X : Triple | ∀ j i, |X j i - cyclicCenter j i| ≤ (1953/10000 : ℝ)}
      (tripleDeficit p K) := by
  intro p K hp hK hKp
  exact HlawkaCodex84Curvature.convexOn_tripleDeficit hp hK hKp

#print axioms solution

/- Exact reviewed public geometry type. -/
example : ∀ p K : ℝ, 84 ≤ p → (20/43 : ℝ)*p ≤ K → K ≤ p/2 →
    ConvexOn ℝ {X : Triple | ∀ j i, |X j i - cyclicCenter j i| ≤ (1953/10000 : ℝ)}
      (tripleDeficit p K) := solution
