-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.convex_box32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:18.43075+00:00
-- url     : https://prove2.me/submissions/9194204b-0072-43c0-8df1-f8fce4b9c5ef

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Algebra.Order.Star.Real
set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl32Norm
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



section Generic
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
end Generic

end Hl32Norm

set_option autoImplicit false
namespace Hl32Geometry
open HlawkaSchatten.DiagonalConstruction

/-- Diagonal magnitudes lie in `[625/1000, 1065/1000]`, off-diagonals in `[849/1000, 1121/1000]`. -/
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -(1065 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625 / 1000 : ℝ)
  else (849 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121 / 1000 : ℝ)}

theorem column_total_bounds (X : Triple) (hX : X ∈ asymmetricBox) (i : Fin 3) :
    (633 / 1000 : ℝ) ≤ ∑ j, X j i ∧ ∑ j, X j i ≤ 1617 / 1000 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] at * <;> constructor <;> linarith!

end Hl32Geometry

set_option autoImplicit false

namespace Hl32Coefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (633/1000 : ℝ) ^ (p - 2) /
    (3 * (1617/1000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (5/8 : ℝ) ^ (p - 2) /
    (3 * (1121/1000 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (62/125 : ℝ) ^ (p - 2) /
    (849/500 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (14553/4528) *
      (133672/179139 : ℝ) ^ (p - 2) := by
  have hM : (1617/1000 : ℝ) ^ (p - 1) =
      (1617/1000 : ℝ) ^ (p - 2) * (1617/1000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (849/500 : ℝ) ^ (p - 1) =
      (849/500 : ℝ) ^ (p - 2) * (849/500) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (133672/179139 : ℝ) ^ (p - 2) =
      ((62/125 : ℝ) ^ (p - 2) * (1617/1000 : ℝ) ^ (p - 2)) /
        ((849/500 : ℝ) ^ (p - 2) * (633/1000 : ℝ) ^ (p - 2)) := by
    rw [show (133672/179139 : ℝ) =
      ((62/125) * (1617/1000)) / ((849/500) * (633/1000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (10089/4528) *
      (278008/530625 : ℝ) ^ (p - 2) := by
  have hM : (1121/1000 : ℝ) ^ (p - 1) =
      (1121/1000 : ℝ) ^ (p - 2) * (1121/1000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (849/500 : ℝ) ^ (p - 1) =
      (849/500 : ℝ) ^ (p - 2) * (849/500) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (278008/530625 : ℝ) ^ (p - 2) =
      ((62/125 : ℝ) ^ (p - 2) * (1121/1000 : ℝ) ^ (p - 2)) /
        ((849/500 : ℝ) ^ (p - 2) * (5/8 : ℝ) ^ (p - 2)) := by
    rw [show (278008/530625 : ℝ) =
      ((62/125) * (1121/1000)) / ((849/500) * (5/8)) by norm_num,
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

/-- For `p ≥ 32`, a base `r ≤ q < 1` gives `r ^ (p - 2) ≤ q ^ 30`. -/
theorem rpow_le_pow30 {r q p : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hp : 32 ≤ p) : r ^ (p - 2) ≤ q ^ (30 : ℕ) := by
  have h1 := Real.rpow_le_rpow hr hrq (show 0 ≤ p - 2 by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (show (30 : ℝ) ≤ p - 2 by linarith)
  have h3 : q ^ (30 : ℝ) = q ^ (30 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [← h3]
  exact h1.trans h2

theorem total_comparison {p : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) :
    9 * (p / 2) * upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  have hpow := rpow_le_pow30 (r := (133672/179139 : ℝ)) (q := 3 / 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp
  have hratio : upperPair p ≤ lowerTotal p * ((33 / 10) * (3 / 4 : ℝ) ^ (30 : ℕ)) := by
    rw [total_ratio, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hl.le
    exact mul_le_mul (by norm_num) hpow (by positivity) (by norm_num)
  have hsmall : (9 : ℝ) * 25 * ((33 / 10) * (3 / 4 : ℝ) ^ (30 : ℕ)) < 1 := by norm_num
  have hc : 0 ≤ (33 / 10) * (3 / 4 : ℝ) ^ (30 : ℕ) := by positivity
  have hup := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 7 * (p / 2) by linarith)
  have hlin : 9 * (p / 2) * (lowerTotal p * ((33 / 10) * (3 / 4 : ℝ) ^ (30 : ℕ))) ≤
      lowerTotal p * ((9 : ℝ) * 25 * ((33 / 10) * (3 / 4 : ℝ) ^ (30 : ℕ))) := by
    have := mul_le_mul_of_nonneg_left (show p / 2 ≤ 25 by linarith) (mul_nonneg hl.le hc)
    nlinarith
  have hfin := mul_lt_mul_of_pos_left hsmall hl
  linarith

theorem column_comparison {p : ℝ} (hp : 32 ≤ p) :
    2100 * upperPair p < (432 / 500 : ℝ) * lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := rpow_le_pow30 (r := (278008/530625 : ℝ)) (q := 3 / 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp
  have hratio : upperPair p ≤ lowerColumn p * (3 * (3 / 5 : ℝ) ^ (30 : ℕ)) := by
    rw [column_ratio, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hl.le
    exact mul_le_mul (by norm_num) hpow (by positivity) (by norm_num)
  have hsmall : (2100 : ℝ) * (3 * (3 / 5 : ℝ) ^ (30 : ℕ)) < 432 / 500 := by norm_num
  have hup := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2100 by norm_num)
  have hfin := mul_lt_mul_of_pos_left hsmall hl
  nlinarith

end Hl32Coefficients
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Hl32Curvature
open HlawkaSchatten.DiagonalConstruction
open Hl32Coefficients
open Hl32Norm (normHessian_lower_generic normHessian_upper_canceled)
abbrev entryBox : Set Triple := Hl32Geometry.asymmetricBox
theorem entryBox_off_lower {X : Triple} (hX : X ∈ entryBox)
    (j i : Fin 3) (hij : i ≠ j) : (849 / 1000 : ℝ) ≤ X j i := by
  have h := hX j i
  simp only [if_neg (Ne.symm hij)] at h
  exact h.1
theorem entryBox_diag_upper {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    X j j ≤ -(625 / 1000 : ℝ) := by
  have h := hX j j
  simp only [ite_true] at h
  exact h.2
theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]
theorem entryBox_column_bounds {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) :
    5/8 ≤ |X j i| ∧ |X j i| ≤ 1121/1000 := by
  have h := hX j i
  by_cases he : j = i
  · simp only [if_pos he] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [if_neg he] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith
theorem entryBox_total_bounds {X : Triple} (hX : X ∈ entryBox) (i : Fin 3) :
    633/1000 ≤ totalTriple X i ∧ totalTriple X i ≤ 1617/1000 :=
  Hl32Geometry.column_total_bounds X hX i
theorem entryBox_pair_large {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    849/500 ≤ |pairTriple X j j| := by
  have h0 := hX 0 j
  have h1 := hX 1 j
  have h2 := hX 2 j
  have hl : (849/500 : ℝ) ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, Fin.ext_iff] at h0 h1 h2 ⊢ <;> linarith!
  exact hl.trans (le_abs_self _)
theorem entryBox_pair_small {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 62/125 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!
theorem entryBox_column_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (entryBox_column_bounds hX j 0).1
  norm_num [he] at h
theorem entryBox_total_ne_zero {X : Triple} (hX : X ∈ entryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (entryBox_total_bounds hX 0).1
  norm_num [he] at h
theorem entryBox_pair_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : pairTriple X j ≠ 0 := by
  intro he
  have h := entryBox_pair_large hX j
  norm_num [he] at h

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (849/500) (62/125) (by norm_num) (by norm_num)
    (entryBox_pair_large hX j) (entryBox_pair_small hX j)
  have hc : (p - 1) * (62/125 : ℝ) ^ (p - 2) / (849/500 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (62/125 : ℝ) ^ (p - 2) /
        (849/500 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (62/125 : ℝ) ^ (p - 2) /
          (849/500 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

end Hl32Curvature
set_option autoImplicit false

namespace Hl32Geometry

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
    (hslo : 633/1000 ≤ s) (hshi : s ≤ 1617/1000)
    (htlo : 633/1000 ≤ t) (hthi : t ≤ 1617/1000) :
    s ^ 2 + t ^ 2 ≤ (8/5 : ℝ) * (5/8) ^ 2 * (s + t) ^ 2 := by
  have ha : 0 ≤ (1617/1000 : ℝ) * s - (633/1000) * t := by
    nlinarith
  have hb : 0 ≤ (1617/1000 : ℝ) * t - (633/1000) * s := by
    nlinarith
  have hprod := mul_nonneg ha hb
  nlinarith [sq_nonneg (s + t)]

theorem spread_from_residual_pair (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 633/1000 ≤ t0) (ht0hi : t0 ≤ 1617/1000)
    (ht1lo : 633/1000 ≤ t1) (ht1hi : t1 ≤ 1617/1000)
    (hgap : 0 ≤ gap)
    (hseparate : (5/8 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (8/5 : ℝ) * (r0 ^ 2 + r1 ^ 2) := by
  have hleft : 0 ≤ (5/8 : ℝ) * (t0 + t1) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hseparate
  have hcauchy : (t0 * r1 - t1 * r0) ^ 2 ≤
      (t0 ^ 2 + t1 ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (t0 * r0 + t1 * r1)]
  have hshape := total_pair_shape t0 t1 ht0lo ht0hi ht1lo ht1hi
  have hbound := mul_le_mul_of_nonneg_right hshape
    (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hscale : 0 < (5/8 : ℝ) ^ 2 * (t0 + t1) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem spread_with_error (t0 t1 d0 d1 u0 u1 gap : ℝ)
    (ht0lo : 633/1000 ≤ t0) (ht0hi : t0 ≤ 1617/1000)
    (ht1lo : 633/1000 ≤ t1) (ht1hi : t1 ≤ 1617/1000)
    (hgap : 0 ≤ gap)
    (hseparate : (5/8 : ℝ) * (t0 + t1) * gap ≤
      t0 * (d1 - u1) - t1 * (d0 - u0)) :
    gap ^ 2 ≤ (202/125 : ℝ) * (d0 ^ 2 + d1 ^ 2) +
      (808/5 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by
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

end Hl32Geometry

theorem Hl32Geometry.solution (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 633/1000 ≤ t0) (ht0hi : t0 ≤ 1617/1000)
    (ht1lo : 633/1000 ≤ t1) (ht1hi : t1 ≤ 1617/1000)
    (hgap : 0 ≤ gap)
    (hseparate : (5/8 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (8/5 : ℝ) * (r0 ^ 2 + r1 ^ 2) :=
  Hl32Geometry.spread_from_residual_pair t0 t1 r0 r1 gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
set_option autoImplicit false

namespace Hl32Pairs

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
    (hspread : A ≤ (202/125 : ℝ) * D + (2424/5 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (1121/1000 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (9 * D + 4200 * U) := by
  have hbound : (101 / 100 : ℝ) * 2 * (1121/1000 : ℝ) ^ 2 * R + 101 * E ≤
      9 * D + 4200 * U := by
    nlinarith
  exact hpair.trans (mul_le_mul_of_nonneg_left hbound hdp)

end Hl32Pairs

theorem Hl32Pairs.solution (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (202/125 : ℝ) * D + (2424/5 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (1121/1000 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (9 * D + 4200 * U) :=
  Hl32Pairs.weighted_pair_bound P dp D U A R E hdp hD hU
    hspread hdiff herror hpair
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl32Curvature
open HlawkaSchatten.DiagonalConstruction
open Hl32Geometry
open Hl32Norm (euclideanSq_total_le)

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

theorem ordered_spread_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (a j - a k) ^ 2 ≤ (202/125 : ℝ) * euclideanSq D +
      (2424/5 : ℝ) * frobeniusSq U := by
  have hjj : X j j ≤ -(5/8 : ℝ) := by
    have h := entryBox_diag_upper hX j
    linarith
  have hkk : X k k ≤ -(5/8 : ℝ) := by
    have h := entryBox_diag_upper hX k
    linarith
  have hkj : (5/8 : ℝ) ≤ X k j := by
    have h := entryBox_off_lower hX k j hjk
    linarith
  have hjk' : (5/8 : ℝ) ≤ X j k := by
    have h := entryBox_off_lower hX j k (Ne.symm hjk)
    linarith
  have htj := entryBox_total_bounds hX j
  have htk := entryBox_total_bounds hX k
  have hsep := extreme_pair_separation (5/8) (totalTriple X j) (totalTriple X k)
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

theorem coefficient_differences_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 *
      ((202/125 : ℝ) * euclideanSq D + (2424/5 : ℝ) * frobeniusSq U) := by
  obtain ⟨j,k,l,hjk,hjl,hkl,hlo,hhi⟩ := exists_ordered_indices a
  have hs := ordered_spread_bound hX a b U D hD j k l hjk hjl hkl hlo hhi
  have hd := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end Hl32Curvature
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl32Curvature
open HlawkaSchatten.DiagonalConstruction
open Hl32Norm
open Hl32Coefficients Hl32Pairs

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

theorem canceled_pair_decomposition {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (j i : Fin 3) :
    pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i =
      pairRadial X a j i + pairError X U j i := by
  have ho := pair_indices_off j
  have hl := entryBox_off_lower hX (pairLeft j) j ho.1
  have hr := entryBox_off_lower hX (pairRight j) j ho.2
  have hden : X (pairLeft j) j + X (pairRight j) j ≠ 0 := by linarith
  simp only [pairRadial, pairError, pairDifference, pairTriple_eq_indices, Pi.add_apply, hZ]
  field_simp
  ring

theorem radial_pair_component_sq {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (j i : Fin 3) :
    pairRadial X a j i ^ 2 ≤ (1121/1000 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have ho := pair_indices_off j
  have hl := entryBox_off_lower hX (pairLeft j) j ho.1
  have hr := entryBox_off_lower hX (pairRight j) j ho.2
  have hc := weighted_component_bound (X (pairLeft j) j) (X (pairRight j) j)
    (X (pairLeft j) i) (X (pairRight j) i) (1121/1000)
    (by linarith) (by linarith)
    (entryBox_column_bounds hX (pairLeft j) i).2
    (entryBox_column_bounds hX (pairRight j) i).2
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1121/1000)).mpr hc
  rw [sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (pairDifference a j))
  simpa only [pairRadial, mul_pow, mul_comm] using hm

theorem radial_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (j : Fin 3) :
    radialPairSq X a j ≤ 2 * (1121/1000 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i _ ↦ radial_pair_component_sq hX a j i)
  simpa [radialPairSq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
    mul_assoc] using hh

theorem error_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (U : Triple) (j : Fin 3) :
    errorPairSq X U j ≤ 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j))) := by
  have hlarge := entryBox_pair_large hX j
  have heta (i : Fin 3) (hij : i ≠ j) : |pairTriple X j i / pairTriple X j j| ≤ 1 := by
    rw [abs_div, div_le_iff₀ (by linarith : 0 < |pairTriple X j j|)]
    linarith [entryBox_pair_small hX j i hij]
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

theorem error_pairs_sq_bound {X : Triple} (hX : X ∈ entryBox) (U : Triple) :
    (∑ j, errorPairSq X U j) ≤ 16 * frobeniusSq U := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ error_pair_sq_bound hX U j)
  have hs : (∑ j, 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j)))) =
      16 * frobeniusSq U := by
    simp only [pairLeft, pairRight, frobeniusSq, Fin.sum_univ_three]
    simp
    ring
  rwa [hs] at hh

theorem canceled_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i) (j : Fin 3) :
    canceledPairSq X Z j ≤ (101 / 100 : ℝ) * radialPairSq X a j + 101 * errorPairSq X U j := by
  unfold canceledPairSq radialPairSq errorPairSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [canceled_pair_decomposition hX Z U a hZ j i]
  exact young_pair_sq _ _

theorem canceled_pairs_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, canceledPairSq X Z j) ≤ 9 * euclideanSq D + 4200 * frobeniusSq U := by
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ radial_pair_sq_bound hX a j)
  rw [← Finset.mul_sum] at hr
  have he := error_pairs_sq_bound hX U
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ canceled_pair_sq_bound hX Z U a hZ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hc
  have hr' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 101 / 100)
  have hd := coefficient_differences_bound hX a b U D hD
  have hp : (∑ j, canceledPairSq X Z j) ≤ (1 : ℝ) *
      ((101 / 100 : ℝ) * 2 * (1121/1000 : ℝ) ^ 2 * (∑ j, pairDifference a j ^ 2) +
        101 * (∑ j, errorPairSq X U j)) := by linarith
  simpa only [one_mul] using weighted_pair_bound (∑ j, canceledPairSq X Z j) 1
    (euclideanSq D) (frobeniusSq U)
    ((202/125 : ℝ) * euclideanSq D + (2424/5 : ℝ) * frobeniusSq U)
    (∑ j, pairDifference a j ^ 2) (∑ j, errorPairSq X U j)
    (by norm_num) (euclideanSq_nonneg D) (frobeniusSq_nonneg U) le_rfl hd he hp

theorem pair_hessian_sum_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      upperPair p * (9 * euclideanSq D + 4200 * frobeniusSq U) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ pair_hessian_canceled_bound hp hX Z j)
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    ∑ j, upperPair p * canceledPairSq X Z j at hh
  rw [← Finset.mul_sum] at hh
  have hpred : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ upperPair p := by unfold upperPair; positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (canceled_pairs_sq_bound hX Z U a b D hZ hD) hcoef)

end Hl32Curvature
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl32Curvature
open HlawkaSchatten.DiagonalConstruction
open Hl32Norm
open Hl32Coefficients

theorem deficitHessian_nonneg {p K : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50)
    (hKlo : (448 / 1000 : ℝ) * p ≤ K) (hKhi : K ≤ p / 2)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) :
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
      normHessian_lower_generic hp2 (X j) (Z j) (5/8) (1121/1000)
        (by norm_num) (by norm_num)
        (fun i ↦ (entryBox_column_bounds hX j i).1)
        (fun i ↦ (entryBox_column_bounds hX j i).2)
  have hcols : lowerColumn p * frobeniusSq U ≤ ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerTotal p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower_generic hp2 _ _ (633/1000) (1617/1000)
      (by norm_num) (by norm_num)
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hweight : (432 / 500 : ℝ) * p ≤ 2 * K - 1 := by linarith
  have hpos1 := mul_le_mul_of_nonneg_left hcols (show 0 ≤ (432 / 500 : ℝ) * p by positivity)
  have hpos2 := mul_le_mul_of_nonneg_right hweight hcols0
  have hpairs := pair_hessian_sum_bound hp2 hX Z U a b D hZ hD
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p / 2 by linarith)
  have hneg2 := mul_le_mul_of_nonneg_right hKhi hpair0
  have hD0 := euclideanSq_nonneg D
  have hU0 := frobeniusSq_nonneg U
  have hmarginD := mul_le_mul_of_nonneg_right (total_comparison hp hp').le hD0
  have hdpos : 0 ≤ upperPair p := by
    have hpred : 0 ≤ p - 1 := by linarith
    unfold upperPair
    positivity
  have hmarginUp := mul_le_mul_of_nonneg_left (column_comparison hp).le hp0
  have hmarginUcoef : 4200 * (p / 2) * upperPair p ≤ (432 / 500 : ℝ) * p * lowerColumn p := by
    nlinarith [mul_nonneg hp0 hdpos]
  have hmarginU := mul_le_mul_of_nonneg_right hmarginUcoef hU0
  unfold deficitHessian
  nlinarith

end Hl32Curvature

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl32Curvature
open HlawkaSchatten.DiagonalConstruction
open Hl32Norm

theorem convex_entryBox : Convex ℝ entryBox := by
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
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
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


theorem convexOn_tripleDeficit {p K : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50)
    (hK : (448 / 1000 : ℝ) * p ≤ K) (hKp : K ≤ p / 2) :
    ConvexOn ℝ entryBox (tripleDeficit p K) := by
  refine ⟨convex_entryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ entryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_entryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
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
      exact deficitHessian_nonneg hp hp' hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end Hl32Curvature

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.convex_box32 : ∀ p K : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p ≤ K → K ≤ p / 2 →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(1065 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625 / 1000 : ℝ)
      else (849 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121 / 1000 : ℝ)}
      (tripleDeficit p K) := by
  intro p K hp hp' hK hKp
  exact Hl32Curvature.convexOn_tripleDeficit hp hp' hK hKp

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ p K : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p ≤ K → K ≤ p / 2 →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(1065 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625 / 1000 : ℝ)
      else (849 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121 / 1000 : ℝ)}
      (tripleDeficit p K) := by
  exact HlawkaSchatten.DiagonalCutoff32.convex_box32
