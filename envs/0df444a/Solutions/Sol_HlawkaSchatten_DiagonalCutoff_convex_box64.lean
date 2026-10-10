-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.convex_box64
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T06:51:04.61799+00:00
-- url     : https://prove2.me/submissions/bfb4e1e7-2e8f-4156-b1fc-5deeaf54ece5

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib
set_option autoImplicit false

/- Solutions/Hlawka85_NormCalculus.lean -/
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


/- Solutions/Sol_Hlawka85_CurvatureMargins.lean -/
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


/- Solutions/Hlawka85_CoefficientComparison.lean -/
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


/- Solutions/Hlawka85_BoxHessianBounds.lean -/
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

/- Solutions/Hlawka64_AsymmetricBoxBounds.lean -/
set_option autoImplicit false
namespace HlawkaCodex64Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev entryMin : ℝ := 23847/32000
noncomputable abbrev entryMax : ℝ := 273/250
noncomputable abbrev radius : ℝ := 1733/8000
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -entryMax ≤ X j i ∧ X j i ≤ -entryMin
  else entryMin ≤ X j i ∧ X j i ≤ entryMax}
theorem asymmetricBox_of_radius_upper (X : Triple)
    (hr : ∀ j i, |X j i - cyclicCenter j i| ≤ radius)
    (hu : ∀ j i, |X j i| ≤ entryMax) : X ∈ asymmetricBox := by
  intro j i
  have h := abs_le.mp (hr j i)
  have h' := abs_le.mp (hu j i)
  by_cases he : j = i
  · simp only [he, cyclicCenter, ite_true] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
  · simp only [cyclicCenter, if_neg (Ne.symm he), if_neg he] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
theorem asymmetricBox_of_norm_data (X : Triple) (N : Fin 3 → ℝ)
    (hS : ∑ j, N j = 3) (hN : ∀ j, N j ≤ entryMax)
    (hcoord : ∀ j i, |X j i| ≤ N j)
    (hT : ∀ i, ∑ j, X j i ≤ entryMax)
    (hpair : ∀ i, 3-N i-(453/6400 : ℝ) ≤ (∑ j, X j i)-X i i) :
    X ∈ asymmetricBox := by
  have h0 := hN 0
  have h1 := hN 1
  have h2 := hN 2
  simp only [Fin.sum_univ_three] at hS
  intro j i
  have hc := abs_le.mp (hcoord j i)
  have hn := hN j
  have ht := hT i
  have hp := hpair i
  by_cases he : j = i
  · subst j
    simp only [ite_true]
    constructor
    · linarith!
    · norm_num [entryMin, entryMax] at *
      linarith!
  · simp only [if_neg he]
    refine ⟨?_, by linarith!⟩
    have hc0 := abs_le.mp (hcoord 0 i)
    have hc1 := abs_le.mp (hcoord 1 i)
    have hc2 := abs_le.mp (hcoord 2 i)
    fin_cases j <;> fin_cases i <;> first
    | exact (he rfl).elim
    | norm_num [Fin.sum_univ_three, Fin.ext_iff, entryMin, entryMax] at *; linarith!

theorem column_total_bounds (X : Triple) (hX : X ∈ asymmetricBox) (i : Fin 3) :
    2*entryMin-entryMax ≤ ∑ j, X j i ∧ ∑ j, X j i ≤ 2*entryMax-entryMin := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] at * <;> constructor <;> linarith!
theorem dominant_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k : Fin 3) (hak : a ≠ k) (hbk : b ≠ k) :
    2*entryMin ≤ X a k + X b k ∧ X a k + X b k ≤ 2*entryMax := by
  have ha := hX a k
  have hb := hX b k
  simp only [if_neg hak, if_neg hbk] at ha hb
  constructor <;> linarith!
theorem canceled_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k i : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (hik : i ≠ k) :
    |X a i + X b i| ≤ entryMax-entryMin := by
  have hi : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  have ha := hX a i
  have hb := hX b i
  rcases hi with rfl | rfl
  · simp only [ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
  · simp only [ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
theorem rectangular_power_base :
    ((entryMax-entryMin)*(2*entryMax-entryMin)) /
      ((2*entryMin)*(2*entryMin-entryMax)) < (9/10 : ℝ) := by norm_num
end HlawkaCodex64Geometry
/- Solutions/Hlawka64_RectangularMargin.lean -/
set_option autoImplicit false
namespace HlawkaCodex64Margins

theorem log_reciprocal_base : (1 / 10 : ℝ) ≤ Real.log (67566500 / 56768553) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 67566500 / 56768553 by norm_num)
  have heq : (1 : ℝ) - (67566500 / 56768553)⁻¹ = 10797947 / 67566500 := by norm_num
  have hlow : (1 / 10 : ℝ) ≤ 10797947 / 67566500 := by norm_num
  linarith

theorem ratio_growth {p : ℝ} (hp : 64 ≤ p) :
    p / 64 ≤ (67566500 / 56768553 : ℝ) ^ (p - 64) := by
  have hlog := log_reciprocal_base
  have hmul := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p - 64 by linarith)
  have hexp := Real.add_one_le_exp (Real.log (67566500 / 56768553) * (p - 64))
  have hrpow : (67566500 / 56768553 : ℝ) ^ (p - 64) =
      Real.exp (Real.log (67566500 / 56768553) * (p - 64)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have hlin : p / 64 ≤ 1 + (p - 64) / 10 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rw [hrpow]
  linarith

theorem endpoint_power :
    (7 : ℝ) * 64 * (414369 / 127184) * (56768553 / 67566500) ^ (62 : ℕ) < 1 := by
  norm_num

theorem total_margin {p : ℝ} (hp : 64 ≤ p) :
    (7 : ℝ) * p * (414369 / 127184) * (56768553 / 67566500) ^ (p - 2) < 1 := by
  have hgrow := ratio_growth hp
  have hsplit : (56768553 / 67566500 : ℝ) ^ (p - 2) =
      (56768553 / 67566500) ^ (62 : ℝ) * (56768553 / 67566500) ^ (p - 64) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hnat : (56768553 / 67566500 : ℝ) ^ (62 : ℝ) =
      (56768553 / 67566500) ^ (62 : ℕ) := Real.rpow_natCast _ _
  have hinv : (56768553 / 67566500 : ℝ) ^ (p - 64) =
      ((67566500 / 56768553) ^ (p - 64))⁻¹ := by
    rw [← Real.inv_rpow (by norm_num), inv_div]
  have hsmall : (p / 64) * (56768553 / 67566500 : ℝ) ^ (p - 64) ≤ 1 := by
    rw [hinv]
    exact (div_le_one (by positivity)).mpr hgrow
  have hmain : (7 : ℝ) * p * (414369 / 127184) * (56768553 / 67566500) ^ (p - 2) =
      ((7 : ℝ) * 64 * (414369 / 127184) * (56768553 / 67566500) ^ (62 : ℕ)) *
        ((p / 64) * (56768553 / 67566500) ^ (p - 64)) := by
    rw [hsplit, hnat]
    ring
  rw [hmain]
  have hend := endpoint_power
  have hpos : 0 < (7 : ℝ) * 64 * (414369 / 127184) * (56768553 / 67566500) ^ (62 : ℕ) := by
    positivity
  have hposr : 0 ≤ (p / 64) * (56768553 / 67566500 : ℝ) ^ (p - 64) := by positivity
  nlinarith [hsmall, hend]

end HlawkaCodex64Margins
/- Solutions/Hlawka64_CoefficientComparison.lean -/
set_option autoImplicit false

namespace HlawkaCodex64Coefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (51/128 : ℝ) ^ (p - 2) /
    (3 * (46041/32000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (23847/32000 : ℝ) ^ (p - 2) /
    (3 * (273/250 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (11097/32000 : ℝ) ^ (p - 2) /
    (23847/16000 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (414369/127184) *
      (56768553/67566500 : ℝ) ^ (p - 2) := by
  have hM : (46041/32000 : ℝ) ^ (p - 1) =
      (46041/32000 : ℝ) ^ (p - 2) * (46041/32000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (23847/16000 : ℝ) ^ (p - 1) =
      (23847/16000 : ℝ) ^ (p - 2) * (23847/16000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (56768553/67566500 : ℝ) ^ (p - 2) =
      ((11097/32000 : ℝ) ^ (p - 2) * (46041/32000 : ℝ) ^ (p - 2)) /
        ((23847/16000 : ℝ) ^ (p - 2) * (51/128 : ℝ) ^ (p - 2)) := by
    rw [show (56768553/67566500 : ℝ) =
      ((11097/32000) * (46041/32000)) / ((23847/16000) * (51/128)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (19656/7949) *
      (21542976/63186601 : ℝ) ^ (p - 2) := by
  have hM : (273/250 : ℝ) ^ (p - 1) =
      (273/250 : ℝ) ^ (p - 2) * (273/250) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (23847/16000 : ℝ) ^ (p - 1) =
      (23847/16000 : ℝ) ^ (p - 2) * (23847/16000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (21542976/63186601 : ℝ) ^ (p - 2) =
      ((11097/32000 : ℝ) ^ (p - 2) * (273/250 : ℝ) ^ (p - 2)) /
        ((23847/16000 : ℝ) ^ (p - 2) * (23847/32000 : ℝ) ^ (p - 2)) := by
    rw [show (21542976/63186601 : ℝ) =
      ((11097/32000) * (273/250)) / ((23847/16000) * (23847/32000)) by norm_num,
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


theorem total_comparison {p : ℝ} (hp : 64 ≤ p) :
    7 * p * upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  rw [total_ratio]
  have hmargin := mul_lt_mul_of_pos_left (HlawkaCodex64Margins.total_margin hp) hl
  calc
    7 * p * (lowerTotal p * (414369 / 127184) * (56768553 / 67566500 : ℝ) ^ (p - 2))
        = lowerTotal p * (7 * p * (414369 / 127184) * (56768553 / 67566500 : ℝ) ^ (p - 2)) := by ring
    _ < lowerTotal p * 1 := hmargin
    _ = lowerTotal p := by ring

theorem column_comparison {p : ℝ} (hp : 64 ≤ p) :
    5000 * upperPair p < (9 / 10 : ℝ) * lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 21542976 / 63186601)
    (by norm_num : (21542976 / 63186601 : ℝ) ≤ 2 / 5) (show 0 ≤ p - 2 by linarith)
  have hratio : upperPair p ≤ lowerColumn p * (5 / 2) * (2 / 5 : ℝ) ^ (p - 2) := by
    rw [column_ratio]
    calc
      _ ≤ lowerColumn p * (5 / 2) * (21542976 / 63186601 : ℝ) ^ (p - 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (19656 / 7949 : ℝ) ≤ 5 / 2) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hsmall : (12500 : ℝ) * (2 / 5) ^ (62 : ℕ) < 9 / 10 := by
    have h4 : (5 / 2 : ℝ) ^ 4 = 625 / 16 := by norm_num
    have h8 : (5 / 2 : ℝ) ^ 8 = (625 / 16) ^ 2 := by
      rw [show (5 / 2 : ℝ) ^ 8 = ((5 / 2 : ℝ) ^ 4) ^ 2 by ring, h4]
    have h16 : (5 / 2 : ℝ) ^ 16 = ((625 / 16) ^ 2) ^ 2 := by
      rw [show (5 / 2 : ℝ) ^ 16 = ((5 / 2 : ℝ) ^ 8) ^ 2 by ring, h8]
    have h32 : (5 / 2 : ℝ) ^ 32 = (((625 / 16) ^ 2) ^ 2) ^ 2 := by
      rw [show (5 / 2 : ℝ) ^ 32 = ((5 / 2 : ℝ) ^ 16) ^ 2 by ring, h16]
    have h64 : (5 / 2 : ℝ) ^ 64 = ((((625 / 16) ^ 2) ^ 2) ^ 2) ^ 2 := by
      rw [show (5 / 2 : ℝ) ^ 64 = ((5 / 2 : ℝ) ^ 32) ^ 2 by ring, h32]
    have h62 : (5 / 2 : ℝ) ^ 62 = (5 / 2 : ℝ) ^ 64 * (2 / 5) ^ 2 := by
      have hpow : (5 / 2 : ℝ) ^ 64 = (5 / 2 : ℝ) ^ 62 * (5 / 2) ^ 2 := by ring
      rw [hpow]
      field_simp
    have hbig : (12500 : ℝ) * (10 / 9) * ((5 / 2) ^ 2) < (5 / 2) ^ 64 := by
      rw [h64]
      norm_num
    have hbig62 : (12500 : ℝ) * (10 / 9) < (5 / 2) ^ 62 := by
      rw [h62]
      have hpos : (0 : ℝ) < (2 / 5) ^ 2 := by positivity
      have hmul := mul_lt_mul_of_pos_right hbig hpos
      have hcancel : ((5 / 2 : ℝ) ^ 2) * ((2 / 5) ^ 2) = 1 := by norm_num
      nlinarith [hmul, hcancel]
    rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, inv_pow]
    refine (mul_inv_lt_iff₀ (by positivity)).mpr ?_
    linarith [hbig62]
  have hpow68 : (2 / 5 : ℝ) ^ (p - 2) ≤ (2 / 5) ^ (62 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 2 / 5) (by norm_num : (2 / 5 : ℝ) ≤ 1)
      (show (62 : ℝ) ≤ p - 2 by linarith)
    simpa [Real.rpow_natCast] using h
  have hcoeff : (5000 : ℝ) * (5 / 2) * (2 / 5) ^ (p - 2) < 9 / 10 := by
    have hnonneg : 0 ≤ (2 / 5 : ℝ) ^ (p - 2) := by positivity
    nlinarith [hpow68, hsmall]
  have hup := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 5000)
  calc
    _ ≤ lowerColumn p * ((5000 : ℝ) * (5 / 2) * (2 / 5) ^ (p - 2)) := by
      rw [show 5000 * (lowerColumn p * (5 / 2) * (2 / 5 : ℝ) ^ (p - 2)) =
        lowerColumn p * (5000 * (5 / 2) * (2 / 5 : ℝ) ^ (p - 2)) by ring] at hup
      exact hup
    _ < (9 / 10) * lowerColumn p := by
      have hpos : 0 < lowerColumn p := hl
      have := mul_lt_mul_of_pos_left hcoeff hpos
      linarith

end HlawkaCodex64Coefficients
/- Solutions/Hlawka64_BoxHessianBounds.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace HlawkaCodex64Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex64Coefficients
open HlawkaCodex85Curvature (normHessian_lower_generic normHessian_upper_canceled)
abbrev codexEntryBox : Set Triple := HlawkaCodex64Geometry.asymmetricBox
theorem codexEntryBox_off_lower {X : Triple} (hX : X ∈ codexEntryBox)
    (j i : Fin 3) (hij : i ≠ j) : (23847/32000 : ℝ) ≤ X j i := by
  have h := hX j i
  simp only [if_neg (Ne.symm hij)] at h
  exact h.1
theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]
theorem codexEntryBox_column_bounds {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) :
    23847/32000 ≤ |X j i| ∧ |X j i| ≤ 273/250 := by
  have h := hX j i
  by_cases he : j = i
  · simp only [if_pos he] at h
    norm_num [HlawkaCodex64Geometry.entryMin,HlawkaCodex64Geometry.entryMax] at h
    rw [abs_of_neg (by norm_num [HlawkaCodex64Geometry.entryMin] at h; linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [if_neg he] at h
    norm_num [HlawkaCodex64Geometry.entryMin,HlawkaCodex64Geometry.entryMax] at h
    rw [abs_of_pos (by norm_num [HlawkaCodex64Geometry.entryMin] at h; linarith : 0 < X j i)]
    exact h
theorem codexEntryBox_total_bounds {X : Triple} (hX : X ∈ codexEntryBox) (i : Fin 3) :
    51/128 ≤ totalTriple X i ∧ totalTriple X i ≤ 46041/32000 := by
  have h := HlawkaCodex64Geometry.column_total_bounds X hX i
  change 2*HlawkaCodex64Geometry.entryMin-HlawkaCodex64Geometry.entryMax ≤ totalTriple X i ∧
    totalTriple X i ≤ 2*HlawkaCodex64Geometry.entryMax-HlawkaCodex64Geometry.entryMin at h
  norm_num [HlawkaCodex64Geometry.entryMin,HlawkaCodex64Geometry.entryMax] at h
  exact h
theorem codexEntryBox_pair_large {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    23847/16000 ≤ |pairTriple X j j| := by
  have h0 := hX 0 j
  have h1 := hX 1 j
  have h2 := hX 2 j
  have hl : (23847/16000 : ℝ) ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, Fin.ext_iff] at h0 h1 h2 ⊢ <;> linarith!
  exact hl.trans (le_abs_self _)
theorem codexEntryBox_pair_small {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 11097/32000 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!
theorem codexEntryBox_column_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (codexEntryBox_column_bounds hX j 0).1
  norm_num [he] at h
theorem codexEntryBox_total_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (codexEntryBox_total_bounds hX 0).1
  norm_num [he] at h
theorem codexEntryBox_pair_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : pairTriple X j ≠ 0 := by
  intro he
  have h := codexEntryBox_pair_large hX j
  norm_num [he] at h

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (23847/16000) (11097/32000) (by norm_num) (by norm_num)
    (codexEntryBox_pair_large hX j) (codexEntryBox_pair_small hX j)
  have hc : (p - 1) * (11097/32000 : ℝ) ^ (p - 2) / (23847/16000 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (11097/32000 : ℝ) ^ (p - 2) /
        (23847/16000 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (11097/32000 : ℝ) ^ (p - 2) /
          (23847/16000 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

end HlawkaCodex64Curvature
/- Solutions/Hlawka64_RangeGeometry.lean -/
set_option autoImplicit false

namespace HlawkaCodex64Geometry

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
    (hslo : 51/128 ≤ s) (hshi : s ≤ 46041/32000)
    (htlo : 51/128 ≤ t) (hthi : t ≤ 46041/32000) :
    s ^ 2 + t ^ 2 ≤ (5/4 : ℝ) * (23847/32000) ^ 2 * (s + t) ^ 2 := by
  have ha : 0 ≤ (46041/32000 : ℝ) * s - (51/128) * t := by
    nlinarith
  have hb : 0 ≤ (46041/32000 : ℝ) * t - (51/128) * s := by
    nlinarith
  have hprod := mul_nonneg ha hb
  nlinarith [sq_nonneg (s + t)]

theorem spread_from_residual_pair (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 51/128 ≤ t0) (ht0hi : t0 ≤ 46041/32000)
    (ht1lo : 51/128 ≤ t1) (ht1hi : t1 ≤ 46041/32000)
    (hgap : 0 ≤ gap)
    (hseparate : (23847/32000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (5/4 : ℝ) * (r0 ^ 2 + r1 ^ 2) := by
  have hleft : 0 ≤ (23847/32000 : ℝ) * (t0 + t1) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hseparate
  have hcauchy : (t0 * r1 - t1 * r0) ^ 2 ≤
      (t0 ^ 2 + t1 ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (t0 * r0 + t1 * r1)]
  have hshape := total_pair_shape t0 t1 ht0lo ht0hi ht1lo ht1hi
  have hbound := mul_le_mul_of_nonneg_right hshape
    (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hscale : 0 < (23847/32000 : ℝ) ^ 2 * (t0 + t1) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem spread_with_error (t0 t1 d0 d1 u0 u1 gap : ℝ)
    (ht0lo : 51/128 ≤ t0) (ht0hi : t0 ≤ 46041/32000)
    (ht1lo : 51/128 ≤ t1) (ht1hi : t1 ≤ 46041/32000)
    (hgap : 0 ≤ gap)
    (hseparate : (23847/32000 : ℝ) * (t0 + t1) * gap ≤
      t0 * (d1 - u1) - t1 * (d0 - u0)) :
    gap ^ 2 ≤ (101/80 : ℝ) * (d0 ^ 2 + d1 ^ 2) +
      (505/4 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by
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

end HlawkaCodex64Geometry

theorem HlawkaCodex64Geometry.solution (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 51/128 ≤ t0) (ht0hi : t0 ≤ 46041/32000)
    (ht1lo : 51/128 ≤ t1) (ht1hi : t1 ≤ 46041/32000)
    (hgap : 0 ≤ gap)
    (hseparate : (23847/32000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (5/4 : ℝ) * (r0 ^ 2 + r1 ^ 2) :=
  HlawkaCodex64Geometry.spread_from_residual_pair t0 t1 r0 r1 gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
/- Solutions/Hlawka64_PairResidualGeometry.lean -/
set_option autoImplicit false

namespace HlawkaCodex64Pairs

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
    (hspread : A ≤ (101/80 : ℝ) * D + (1515/4 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (273/250 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (7 * D + 4000 * U) := by
  have hbound : (101 / 100 : ℝ) * 2 * (273/250 : ℝ) ^ 2 * R + 101 * E ≤
      7 * D + 4000 * U := by
    nlinarith
  exact hpair.trans (mul_le_mul_of_nonneg_left hbound hdp)

end HlawkaCodex64Pairs

theorem HlawkaCodex64Pairs.solution (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (101/80 : ℝ) * D + (1515/4 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (273/250 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (7 * D + 4000 * U) :=
  HlawkaCodex64Pairs.weighted_pair_bound P dp D U A R E hdp hD hU
    hspread hdiff herror hpair
/- Solutions/Hlawka64_TripleGeometry.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex64Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex64Geometry
open HlawkaCodex85Curvature (euclideanSq_total_le)

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
    (a j - a k) ^ 2 ≤ (101/80 : ℝ) * euclideanSq D +
      (1515/4 : ℝ) * frobeniusSq U := by
  have hjj : X j j ≤ -(23847/32000 : ℝ) := by
    have h := hX j j
    simp only [ite_true] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hkk : X k k ≤ -(23847/32000 : ℝ) := by
    have h := hX k k
    simp only [ite_true] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hkj : (23847/32000 : ℝ) ≤ X k j := by
    have h := hX k j
    simp only [if_neg (Ne.symm hjk)] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hjk' : (23847/32000 : ℝ) ≤ X j k := by
    have h := hX j k
    simp only [if_neg hjk] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have htj := codexEntryBox_total_bounds hX j
  have htk := codexEntryBox_total_bounds hX k
  have hsep := extreme_pair_separation (23847/32000) (totalTriple X j) (totalTriple X k)
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
      ((101/80 : ℝ) * euclideanSq D + (1515/4 : ℝ) * frobeniusSq U) := by
  obtain ⟨j,k,l,hjk,hjl,hkl,hlo,hhi⟩ := exists_ordered_indices a
  have hs := ordered_spread_bound hX a b U D hD j k l hjk hjl hkl hlo hhi
  have hd := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end HlawkaCodex64Curvature
/- Solutions/Hlawka64_PairHessianGeometry.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex64Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature
open HlawkaCodex64Coefficients HlawkaCodex64Pairs

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

theorem radial_pair_component_sq {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (j i : Fin 3) :
    pairRadial X a j i ^ 2 ≤ (273/250 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have ho := pair_indices_off j
  have hl := codexEntryBox_off_lower hX (pairLeft j) j ho.1
  have hr := codexEntryBox_off_lower hX (pairRight j) j ho.2
  have hc := weighted_component_bound (X (pairLeft j) j) (X (pairRight j) j)
    (X (pairLeft j) i) (X (pairRight j) i) (273/250)
    (by linarith) (by linarith)
    (codexEntryBox_column_bounds hX (pairLeft j) i).2
    (codexEntryBox_column_bounds hX (pairRight j) i).2
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 273/250)).mpr hc
  rw [sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (pairDifference a j))
  simpa only [pairRadial, mul_pow, mul_comm] using hm

theorem radial_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (j : Fin 3) :
    radialPairSq X a j ≤ 2 * (273/250 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i _ ↦ radial_pair_component_sq hX a j i)
  simpa [radialPairSq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
    mul_assoc] using hh

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

theorem canceled_pairs_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, canceledPairSq X Z j) ≤ 7 * euclideanSq D + 4000 * frobeniusSq U := by
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ radial_pair_sq_bound hX a j)
  rw [← Finset.mul_sum] at hr
  have he := error_pairs_sq_bound hX U
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ canceled_pair_sq_bound hX Z U a hZ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hc
  have hr' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 101 / 100)
  have hd := coefficient_differences_bound hX a b U D hD
  have hp : (∑ j, canceledPairSq X Z j) ≤ (1 : ℝ) *
      ((101 / 100 : ℝ) * 2 * (273/250 : ℝ) ^ 2 * (∑ j, pairDifference a j ^ 2) +
        101 * (∑ j, errorPairSq X U j)) := by linarith
  simpa only [one_mul] using weighted_pair_bound (∑ j, canceledPairSq X Z j) 1
    (euclideanSq D) (frobeniusSq U)
    ((101/80 : ℝ) * euclideanSq D + (1515/4 : ℝ) * frobeniusSq U)
    (∑ j, pairDifference a j ^ 2) (∑ j, errorPairSq X U j)
    (by norm_num) (euclideanSq_nonneg D) (frobeniusSq_nonneg U) le_rfl hd he hp

theorem pair_hessian_sum_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      upperPair p * (7 * euclideanSq D + 4000 * frobeniusSq U) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ pair_hessian_canceled_bound hp hX Z j)
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    ∑ j, upperPair p * canceledPairSq X Z j at hh
  rw [← Finset.mul_sum] at hh
  have hpred : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ upperPair p := by unfold upperPair; positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (canceled_pairs_sq_bound hX Z U a b D hZ hD) hcoef)

end HlawkaCodex64Curvature
/- Solutions/Hlawka64_DeficitHessian.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex64Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature
open HlawkaCodex64Coefficients

theorem deficitHessian_nonneg {p K : ℝ} (hp : 64 ≤ p)
    (hKlo : (23 / 50 : ℝ) * p ≤ K) (hKhi : K ≤ p)
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
      normHessian_lower_generic hp2 (X j) (Z j) (23847/32000) (273/250)
        (by norm_num) (by norm_num)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).1)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).2)
  have hcols : lowerColumn p * frobeniusSq U ≤ ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerTotal p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower_generic hp2 _ _ (51/128) (46041/32000)
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
  have hneg1 := mul_le_mul_of_nonneg_left hpairs hp0
  have hneg2 := mul_le_mul_of_nonneg_right hKhi hpair0
  have hD0 := euclideanSq_nonneg D
  have hU0 := frobeniusSq_nonneg U
  have hmarginD := mul_le_mul_of_nonneg_right (total_comparison hp).le hD0
  have hdpos : 0 ≤ upperPair p := by
    have hpred : 0 ≤ p - 1 := by linarith
    unfold upperPair
    positivity
  have hmarginUp := mul_le_mul_of_nonneg_left (column_comparison hp).le hp0
  have hmarginUcoef : 4000 * p * upperPair p ≤ (9 / 10 : ℝ) * p * lowerColumn p := by
    nlinarith [mul_nonneg hp0 hdpos]
  have hmarginU := mul_le_mul_of_nonneg_right hmarginUcoef hU0
  unfold deficitHessian
  nlinarith

end HlawkaCodex64Curvature
/- Solutions/Hlawka64_BoxConvexity.lean -/
/- Adapted from the Apache-2.0 Hlawka development by Ezzeri Esa and the
accepted cutoff-87 source produced by Claude Opus 5.5. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex64Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex85Curvature

theorem convex_codexEntryBox : Convex ℝ codexEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  have hw (l u : ℝ) (hx : l ≤ X j i ∧ X j i ≤ u) (hy : l ≤ Y j i ∧ Y j i ≤ u) :
      l ≤ (a • X+b • Y) j i ∧ (a • X+b • Y) j i ≤ u := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    rw [← add_mul, hab, one_mul] at hlo hhi
    exact ⟨hlo,hhi⟩
  by_cases he : j = i
  · simp only [if_pos he] at hx hy ⊢
    exact hw _ _ hx hy
  · simp only [if_neg he] at hx hy ⊢
    exact hw _ _ hx hy

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


theorem convexOn_tripleDeficit {p K : ℝ} (hp : 64 ≤ p) (hK : (23 / 50 : ℝ) * p ≤ K) (hKp : K ≤ p) :
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


end HlawkaCodex64Curvature

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p K : ℝ, 64 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(23847 / 32000 : ℝ)
      else (23847 / 32000 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)}
      (tripleDeficit p K) := by
  intro p K hp hK hKp
  simpa [HlawkaCodex64Curvature.codexEntryBox, HlawkaCodex64Geometry.asymmetricBox,
      HlawkaCodex64Geometry.entryMin, HlawkaCodex64Geometry.entryMax] using
    HlawkaCodex64Curvature.convexOn_tripleDeficit hp hK hKp
