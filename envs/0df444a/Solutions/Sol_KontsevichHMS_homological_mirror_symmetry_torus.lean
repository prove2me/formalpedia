-- Prove2me | solution 1 for KontsevichHMS.homological_mirror_symmetry_torus
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:41:19.307002+00:00
-- url     : https://prove2.me/submissions/b7ed8fa9-4270-4213-9f11-a768609a231a

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane
import Definitions.Def_KontsevichHMS_DbCoh

-- Work/HMSAdditiveCoefficients.lean

-- From Branes.lean

set_option autoImplicit false
noncomputable section

namespace HMSAdditive
open scoped Real
open KontsevichHMS KontsevichHMS.Brane

def B1 : Brane where
  dir := (1, -1)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (1/2, 0)
  grading := 3/4
  grading_dir := ⟨-(Real.sqrt 2 / 2), by exact neg_ne_zero.mpr (by positivity), by
    have e : π * (3/4) = π - π/4 := by ring
    rw [e, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ext <;> simp⟩
  conn := 0

def B2 : Brane where
  dir := (0, 1)
  dir_primitive := ⟨0, 1, by norm_num⟩
  base := (0, 0)
  grading := 1/2
  grading_dir := ⟨1, one_ne_zero, by
    have e : π * (1/2) = π/2 := by ring
    rw [e, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ext <;> simp⟩
  conn := 0

def B3 : Brane where
  dir := (1, 1)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (0, 0)
  grading := 1/4
  grading_dir := ⟨Real.sqrt 2 / 2, by positivity, by
    have e : π * (1/4) = π/4 := by ring
    rw [e, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ext <;> simp⟩
  conn := 0

def B4 (t : ℝ) : Brane where
  dir := (1, 0)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (0, 0)
  grading := 0
  grading_dir := ⟨1, one_ne_zero, by
    rw [mul_zero, Real.cos_zero, Real.sin_zero]
    ext <;> simp⟩
  conn := -t

lemma all_transverse (t : ℝ) :
    Transverse B1 B2 ∧ Transverse B2 B3 ∧ Transverse B3 (B4 t) ∧
    Transverse B1 B3 ∧ Transverse B2 (B4 t) ∧ Transverse B1 (B4 t) := by
  norm_num [Transverse, det2, dirR, B1, B2, B3, B4]

lemma all_maslov_zero (t : ℝ) :
    maslov B1 B2 = 0 ∧ maslov B2 B3 = 0 ∧ maslov B3 (B4 t) = 0 ∧
    maslov B1 B3 = 0 ∧ maslov B2 (B4 t) = 0 ∧ maslov B1 (B4 t) = 0 := by
  norm_num [maslov, B1, B2, B3, B4]

end HMSAdditive


-- From Gaussian.lean

set_option autoImplicit false

noncomputable section

namespace HMSAdditive

open Set

def oddGaussianTerm (A : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-A * (2 * (n : ℝ) + 1) ^ 2 / 16)

def oddGaussian (A : ℝ) : ℝ := ∑' n : ℕ, oddGaussianTerm A n

lemma odd_sq_lower (n : ℕ) : 1 + 8 * (n : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    push_cast
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

lemma exp_two_bounds : 5 < Real.exp 2 ∧ Real.exp 2 < 8 := by
  have h₁ : (5 : ℝ) / 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h₂ : Real.exp 1 < (11 : ℝ) / 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    convert Real.exp_add (1 : ℝ) 1 using 1 <;> norm_num
  rw [he]
  constructor <;> nlinarith [Real.exp_pos 1]

lemma geometric_exp_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c) ^ n) := by
  apply summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _))
  simpa using (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))

lemma oddGaussianTerm_le (A : ℝ) (hA : 2 ≤ A) (n : ℕ) :
    oddGaussianTerm A n ≤ Real.exp (-1) ^ n := by
  rw [oddGaussianTerm, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hs := odd_sq_lower n
  have hmul : 2 * (2 * (n : ℝ) + 1) ^ 2 ≤ A * (2 * (n : ℝ) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma oddGaussian_summable (A : ℝ) (hA : 2 ≤ A) :
    Summable (oddGaussianTerm A) :=
  (geometric_exp_summable (c := 1) (by norm_num)).of_nonneg_of_le
    (fun n => (Real.exp_pos _).le) (oddGaussianTerm_le A hA)

lemma oddGaussian_continuous : ContinuousOn oddGaussian (Icc 2 4) := by
  apply continuousOn_tsum
    (fun n => by unfold oddGaussianTerm; fun_prop)
    (geometric_exp_summable (c := 1) (by norm_num))
  intro n A hA
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < oddGaussianTerm A n from Real.exp_pos _)]
  exact oddGaussianTerm_le A hA.1 n

lemma oddGaussian_two_gt : 1 < oddGaussian 2 := by
  have hs := oddGaussian_summable 2 (by norm_num)
  have hlow := Summable.sum_le_tsum ({0, 1} : Finset ℕ)
    (fun n _ => (Real.exp_pos (-2 * (2 * (n : ℝ) + 1) ^ 2 / 16)).le) hs
  have h₀ : (7 : ℝ) / 8 ≤ Real.exp (-(1 / 8 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 8 : ℝ))
    linarith
  have h₁ : (1 : ℝ) / 8 < Real.exp (-(9 / 8 : ℝ)) := by
    have he : (1 : ℝ) / 8 < Real.exp (-2) := by
      rw [Real.exp_neg]
      exact (lt_inv_comm₀ (by norm_num) (Real.exp_pos 2)).mpr (by
        norm_num
        exact exp_two_bounds.2)
    exact lt_trans he (Real.exp_lt_exp.mpr (by norm_num))
  norm_num [oddGaussianTerm, oddGaussian] at hlow ⊢
  norm_num at h₀ h₁
  linarith

lemma oddGaussian_four_le :
    oddGaussian 4 ≤ Real.exp (-(1 / 4 : ℝ)) * (1 - Real.exp (-2))⁻¹ := by
  have hgeo := hasSum_geometric_of_lt_one (le_of_lt (Real.exp_pos (-2)))
    (Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0))
  have hb : ∀ n : ℕ, oddGaussianTerm 4 n ≤ Real.exp (-(1 / 4 : ℝ)) * Real.exp (-2) ^ n := by
    intro n
    rw [oddGaussianTerm, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [odd_sq_lower n]
  exact (Summable.tsum_le_tsum hb (oddGaussian_summable 4 (by norm_num))
    (hgeo.mul_left (Real.exp (-(1 / 4 : ℝ)))).summable).trans_eq
      (hgeo.mul_left (Real.exp (-(1 / 4 : ℝ)))).tsum_eq

lemma oddGaussian_four_lt : oddGaussian 4 < 1 := by
  have h₀ : Real.exp (-(1 / 4 : ℝ)) < (4 : ℝ) / 5 := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have := Real.add_one_lt_exp (by norm_num : (1 / 4 : ℝ) ≠ 0)
    norm_num at *
    linarith
  have h₁ : Real.exp (-2) < (1 : ℝ) / 5 := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)).mpr
    norm_num
    exact exp_two_bounds.1
  have hd : 0 < 1 - Real.exp (-2) := by linarith
  apply lt_of_le_of_lt oddGaussian_four_le
  rw [← div_eq_mul_inv, div_lt_iff₀ hd]
  linarith

 theorem exists_normalized_area :
    ∃ A : ℝ, 2 < A ∧ A < 4 ∧ oddGaussian A = 1 := by
  obtain ⟨A, hA, he⟩ := intermediate_value_Ioo' (by norm_num : (2 : ℝ) ≤ 4)
    oddGaussian_continuous ⟨oddGaussian_four_lt, oddGaussian_two_gt⟩
  exact ⟨A, hA.1, hA.2, he⟩

end HMSAdditive


-- From Connection.lean

set_option autoImplicit false
noncomputable section

namespace HMSAdditive
open scoped Real
open Set

def connectionTerm (A t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-A * ((n : ℝ) + 1) ^ 2 / 2) * Real.cos (2 * π * ((n : ℝ) + 1) * t)

def connectionSeries (A t : ℝ) : ℝ := 2 * ∑' n : ℕ, connectionTerm A t n

lemma connectionTerm_norm_le (A t : ℝ) (hA : 2 ≤ A) (n : ℕ) :
    ‖connectionTerm A t n‖ ≤ Real.exp (-1) ^ n := by
  rw [connectionTerm, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-A * ((n : ℝ) + 1) ^ 2 / 2) ≤ Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hA (sq_nonneg ((n : ℝ) + 1))
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  exact (mul_le_of_le_one_right (Real.exp_pos _).le (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)).trans he

lemma connection_summable (A t : ℝ) (hA : 2 ≤ A) : Summable (connectionTerm A t) :=
  (geometric_exp_summable (c := 1) (by norm_num)).of_norm_bounded
    (connectionTerm_norm_le A t hA)

lemma connection_continuous (A : ℝ) (hA : 2 ≤ A) : Continuous (connectionSeries A) := by
  apply continuous_const.mul
  apply continuous_tsum (fun n => by unfold connectionTerm; fun_prop)
    (geometric_exp_summable (c := 1) (by norm_num))
  exact fun n t => connectionTerm_norm_le A t hA n

lemma connection_zero_pos (A : ℝ) (hA : 2 ≤ A) : 0 < connectionSeries A 0 := by
  have hs := connection_summable A 0 hA
  have he : 0 < connectionTerm A 0 0 := by simp [connectionTerm, Real.exp_pos]
  have hle := hs.le_tsum 0 (fun n _ => by simp [connectionTerm, (Real.exp_pos _).le])
  unfold connectionSeries
  linarith

lemma connection_tail_bound (A : ℝ) (hA : 2 ≤ A) (n : ℕ) :
    connectionTerm A (1 / 4) (n + 2) ≤
      (Real.exp (-2 * A) * Real.exp (-1)) * Real.exp (-1) ^ n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm : connectionTerm A (1 / 4) (n + 2) ≤
      Real.exp (-A * ((n : ℝ) + 3) ^ 2 / 2) := by
    unfold connectionTerm
    push_cast
    have hcos := Real.cos_le_one (2 * π * ((n : ℝ) + 2 + 1) * (1 / 4))
    have h := mul_le_of_le_one_right (Real.exp_pos (-A * ((n : ℝ) + 2 + 1)^2/2)).le hcos
    convert h using 1 <;> congr 1 <;> ring
  apply hnorm.trans
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ ((n : ℝ) + 3) ^ 2 - 4 := by nlinarith [sq_nonneg (n : ℝ)]
  have hmul := mul_le_mul_of_nonneg_right hA hp
  nlinarith [sq_nonneg (n : ℝ)]

lemma connection_quarter_neg (A : ℝ) (hA : 2 ≤ A) :
    connectionSeries A (1 / 4) < 0 := by
  have hs := connection_summable A (1 / 4) hA
  have hz : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hz1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := (hasSum_geometric_of_lt_one hz hz1).mul_left
    (Real.exp (-2 * A) * Real.exp (-1))
  have htail : (∑' n : ℕ, connectionTerm A (1 / 4) (n + 2)) ≤
      (Real.exp (-2 * A) * Real.exp (-1)) * (1 - Real.exp (-1))⁻¹ := by
    exact (Summable.tsum_le_tsum (connection_tail_bound A hA)
      ((summable_nat_add_iff 2).mpr hs) hgeo.summable).trans_eq hgeo.tsum_eq
  have hsmall : (Real.exp (-2 * A) * Real.exp (-1)) *
      (1 - Real.exp (-1))⁻¹ < Real.exp (-2 * A) := by
    rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith : 0 < 1 - Real.exp (-1))]
    have he := Real.exp_neg_one_lt_half
    nlinarith [Real.exp_pos (-2 * A)]
  have hsum := hs.sum_add_tsum_nat_add 2
  have h0 : connectionTerm A (1 / 4) 0 = 0 := by
    unfold connectionTerm
    norm_num
    have he : 2 * π * (1 / 4) = π / 2 := by ring
    rw [he, Real.cos_pi_div_two]
  have h1 : connectionTerm A (1 / 4) 1 = -Real.exp (-2 * A) := by
    unfold connectionTerm
    norm_num
    have he : 2 * π * 2 * (1 / 4) = π := by ring
    rw [he, Real.cos_pi]
    congr 1
    ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] at hsum
  unfold connectionSeries
  linarith

 theorem exists_zero_connection (A : ℝ) (hA : 2 ≤ A) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / 4 ∧ connectionSeries A t = 0 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (connection_continuous A hA).continuousOn
    ⟨connection_quarter_neg A hA, connection_zero_pos A hA⟩
  exact ⟨t, ht.1, ht.2, he⟩

end HMSAdditive


-- From Nonvanishing.lean

set_option autoImplicit false
noncomputable section

namespace HMSAdditive
open scoped Real

def oddCosineTerm (A t : ℝ) (n : ℕ) : ℝ :=
  oddGaussianTerm A n * Real.cos (π * t * (2 * (n : ℝ) + 1))

def oddCosineSeries (A t : ℝ) : ℝ := 2 * ∑' n : ℕ, oddCosineTerm A t n

lemma oddCosine_summable (A t : ℝ) (hA : 2 ≤ A) : Summable (oddCosineTerm A t) := by
  apply (oddGaussian_summable A hA).of_norm_bounded
  intro n
  rw [oddCosineTerm, norm_mul, Real.norm_eq_abs,
    abs_of_pos (show 0 < oddGaussianTerm A n from Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

lemma odd_sq_tail_lower (n : ℕ) : 9 + 16 * (n : ℝ) ≤ (2 * ((n : ℝ) + 1) + 1)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

lemma oddCosine_tail_bound (A t : ℝ) (hA : 2 ≤ A) (n : ℕ) :
    ‖oddCosineTerm A t (n + 1)‖ ≤
      Real.exp (-(9 / 8 : ℝ)) * Real.exp (-2) ^ n := by
  have he : oddGaussianTerm A (n + 1) ≤
      Real.exp (-(9 / 8 : ℝ)) * Real.exp (-2) ^ n := by
    rw [oddGaussianTerm, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    have hs := odd_sq_tail_lower n
    have hmul := mul_le_mul_of_nonneg_right hA (sq_nonneg (2 * ((n : ℝ) + 1) + 1))
    nlinarith
  rw [oddCosineTerm, norm_mul, Real.norm_eq_abs,
    abs_of_pos (show 0 < oddGaussianTerm A (n + 1) from Real.exp_pos _)]
  exact (mul_le_of_le_one_right (Real.exp_pos _).le (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)).trans he

lemma oddCosine_tail_small (A t : ℝ) (hA : 2 ≤ A) :
    ‖∑' n : ℕ, oddCosineTerm A t (n + 1)‖ < 1 / 2 := by
  have hgeo := (hasSum_geometric_of_lt_one (Real.exp_pos (-2)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0))).mul_left
      (Real.exp (-(9 / 8 : ℝ)))
  apply (tsum_of_norm_bounded hgeo (oddCosine_tail_bound A t hA)).trans_lt
  have he1 : Real.exp (-(9 / 8 : ℝ)) < (2 : ℝ) / 5 := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have hgt : (5 : ℝ) / 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have he := Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 9 / 8)
    norm_num
    linarith
  have he2 : Real.exp (-2) < (1 : ℝ) / 5 := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    norm_num
    exact exp_two_bounds.1
  rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith : 0 < 1 - Real.exp (-2))]
  linarith

lemma oddCosine_first_large (A t : ℝ) (hA : A < 4) (ht0 : 0 ≤ t) (ht : t < 1 / 4) :
    21 / 40 < oddCosineTerm A t 0 := by
  have hexp : (3 : ℝ) / 4 < Real.exp (-A / 16) := by
    have hlow := Real.add_one_le_exp (-(1 / 4 : ℝ))
    have hmono := Real.exp_lt_exp.mpr (show -(1 / 4 : ℝ) < -A / 16 by linarith)
    linarith
  have hcos : (7 : ℝ) / 10 < Real.cos (π * t) := by
    have hm := Real.cos_lt_cos_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht0)
      (show π / 4 ≤ π by linarith [Real.pi_pos])
      (show π * t < π / 4 by nlinarith [Real.pi_pos])
    rw [Real.cos_pi_div_four] at hm
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hp := mul_pos (sub_pos.mpr hexp) (sub_pos.mpr hcos)
  simp only [oddCosineTerm, oddGaussianTerm, Nat.cast_zero, mul_zero, zero_add, one_pow, mul_one]
  nlinarith

 theorem oddCosineSeries_pos (A t : ℝ) (hA0 : 2 ≤ A) (hA : A < 4)
    (ht0 : 0 ≤ t) (ht : t < 1 / 4) : 0 < oddCosineSeries A t := by
  have hhead := oddCosine_first_large A t hA ht0 ht
  have htail := oddCosine_tail_small A t hA0
  rw [Real.norm_eq_abs, abs_lt] at htail
  have he := (oddCosine_summable A t hA0).tsum_eq_zero_add
  unfold oddCosineSeries
  rw [he]
  linarith

end HMSAdditive


-- From Geometry.lean

set_option autoImplicit false
noncomputable section
namespace HMSAdditive
open scoped Real
open KontsevichHMS KontsevichHMS.Brane

lemma coe_int_sub {x y : ℝ} (h : (x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ))) :
    ∃ n : ℤ, x = y + n := by
  have h2 : ((x - y : ℝ) : AddCircle (1:ℝ)) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).1 h2
  refine ⟨n, ?_⟩
  simp at hn
  linarith

lemma coe_shift (x : ℝ) (k : ℤ) :
    (((x + k : ℝ)) : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) := by
  rw [AddCircle.coe_add]
  have : ((k : ℝ) : AddCircle (1:ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).2 ⟨k, by simp⟩
  rw [this, add_zero]

lemma proj_int {x y : ℝ × ℝ} (h : proj x = proj y) :
    ∃ m n : ℤ, x.1 = y.1 + m ∧ x.2 = y.2 + n := by
  simp only [proj, Prod.mk.injEq] at h
  obtain ⟨m, hm⟩ := coe_int_sub h.1
  obtain ⟨n, hn⟩ := coe_int_sub h.2
  exact ⟨m, n, hm, hn⟩

lemma proj_unique {x y : ℝ × ℝ} (h : proj x = proj y)
    (hx1 : x.1 ∈ Set.Ico (0:ℝ) 1) (hx2 : x.2 ∈ Set.Ico (0:ℝ) 1)
    (hy1 : y.1 ∈ Set.Ico (0:ℝ) 1) (hy2 : y.2 ∈ Set.Ico (0:ℝ) 1) : x = y := by
  simp only [proj, Prod.mk.injEq] at h
  have h1 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (by simpa using hx1) (by simpa using hy1)).1 h.1
  have h2 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (by simpa using hx2) (by simpa using hy2)).1 h.2
  exact Prod.ext h1 h2


variable (t : ℝ)

lemma proj_int_pt (x y : ℝ) (m n : ℤ) : proj (x + m, y + n) = proj (x, y) := by
  simp only [proj, coe_shift]

lemma proj_zero_int (n : ℤ) : proj (0, (n:ℝ)) = proj (0, 0) := by
  simpa using proj_int_pt 0 0 0 n

lemma mem_line {b : Brane} {x : ℝ × ℝ} (t : ℝ) (g : ℤ × ℤ)
    (h : x = b.base + t • b.dirR + ((g.1 : ℝ), (g.2 : ℝ))) : proj x ∈ b.line :=
  ⟨x, ⟨t, g, h⟩, rfl⟩

lemma p12_mem : proj (0, 1/2) ∈ isect B1 B2 :=
  ⟨mem_line (-1/2) (0, 0) (by ext <;> simp [B1, dirR] <;> norm_num),
   mem_line (1/2) (0, 0) (by ext <;> simp [B2, dirR])⟩

lemma q23_mem : proj (0, 0) ∈ isect B2 B3 :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B2, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B3, dirR])⟩

lemma q34_mem : proj (0, 0) ∈ isect B3 (B4 t) :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B3, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma q24_mem : proj (0, 0) ∈ isect B2 (B4 t) :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B2, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma u14_mem : proj (1/2, 0) ∈ isect B1 (B4 t) :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B1, dirR]),
   mem_line (1/2) (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma r13_mem : proj (1/4, 1/4) ∈ isect B1 B3 :=
  ⟨mem_line (-1/4) (0, 0) (by ext <;> simp [B1, dirR] <;> norm_num),
   mem_line (1/4) (0, 0) (by ext <;> simp [B3, dirR])⟩

noncomputable def F123 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1/2), (0, (n:ℝ)), ((1/2 - n)/2, (1/2 + n)/2))

noncomputable def F134 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((1/4, 1/4), ((n:ℝ), (n:ℝ)), (1/2 - n, (n:ℝ)))

noncomputable def F234 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 0), ((n:ℝ), (n:ℝ)), (0, (n:ℝ)))

noncomputable def F124 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1/2), (0, (n:ℝ)), (1/2 - n, (n:ℝ)))

lemma char123 (r : Torus) :
    ∀ T ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F123 n ∧ 2 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B2, B3] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F123] <;> linarith

lemma char134 (r : Torus) :
    ∀ T ∈ triangles B1 B3 (B4 t) (proj (1/4, 1/4)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F134 n ∧ 4 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B3, B4] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F134] <;> linarith

lemma char234 (r : Torus) :
    ∀ T ∈ triangles B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F234 n ∧ 1 * n + 0 ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B2, B3, B4] at d1 d2 d3 hm hn
  have hQ1 : Q1 = n := by linarith
  have hQ2 : Q2 = n := by linarith
  have hR1 : R1 = 0 := by linarith
  have hR2 : R2 = n := by linarith
  subst hQ1 hQ2 hR1 hR2
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [det2] at hpos
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F234]

lemma char124 (r : Torus) :
    ∀ T ∈ triangles B1 B2 (B4 t) (proj (0, 1/2)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F124 n ∧ 2 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B2, B4] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F124] <;> linarith


lemma r_cases (n : ℤ) (r : Torus) (h : proj ((1/2 - n)/2, (1/2 + n)/2) = r) :
    r ∈ ({proj (1/4, 1/4), proj (3/4, 3/4)} : Set Torus) := by
  subst h
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    have e : (((1:ℝ)/2 - ((2 * j : ℤ) : ℝ)) / 2, ((1:ℝ)/2 + ((2 * j : ℤ) : ℝ)) / 2)
        = (1/4 + ((-j : ℤ) : ℝ), 1/4 + ((j : ℤ) : ℝ)) := by
      push_cast; ext <;> ring
    rw [e, proj_int_pt]
  · right
    have e : (((1:ℝ)/2 - ((2 * j + 1 : ℤ) : ℝ)) / 2, ((1:ℝ)/2 + ((2 * j + 1 : ℤ) : ℝ)) / 2)
        = (3/4 + ((-j - 1 : ℤ) : ℝ), 3/4 + ((j : ℤ) : ℝ)) := by
      push_cast; ext <;> ring
    rw [Set.mem_singleton_iff, e, proj_int_pt]


lemma r13_other_mem : proj (3/4, 3/4) ∈ isect B1 B3 :=
  ⟨mem_line (1/4) (0, 1) (by ext <;> simp [B1, dirR] <;> norm_num),
   mem_line (3/4) (0, 0) (by ext <;> simp [B3, dirR])⟩

lemma r13_ne : proj ((1:ℝ)/4, 1/4) ≠ proj (3/4, 3/4) := by
  intro h
  obtain ⟨m, n, hm, hn⟩ := proj_int h
  have hm' : (m : ℝ) = -(1/2:ℝ) := by norm_num at hm; linarith
  have hlt : m < 0 := by exact_mod_cast (show (m : ℝ) < 0 by linarith)
  have hgt : -1 < m := by exact_mod_cast (show (-1 : ℝ) < m by linarith)
  omega

lemma F123_injective : Function.Injective F123 := by
  intro n m h
  have hh := congrArg (fun T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => T.2.1.2) h
  simpa [F123] using hh

lemma F123_mem (n : ℤ) :
    F123 n ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0))
      (proj ((1/2-(n:ℝ))/2, (1/2+(n:ℝ))/2)) := by
  have hn : (2 * (n : ℝ) - 1) ≠ 0 := by
    exact_mod_cast (show 2 * n - 1 ≠ 0 by omega)
  refine ⟨rfl, by norm_num [F123], by norm_num [F123], ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact proj_zero_int n
  all_goals dsimp [F123, det2, dirR, B1, B2, B3]
  all_goals try ring
  all_goals nlinarith [sq_pos_of_ne_zero hn]

lemma F123_even_mem (n : ℤ) :
    F123 (2*n) ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4)) := by
  have he : (((1:ℝ)/2 - ((2*n:ℤ):ℝ))/2, ((1:ℝ)/2 + ((2*n:ℤ):ℝ))/2) =
      (1/4 + ((-n:ℤ):ℝ), 1/4 + (n:ℝ)) := by push_cast; ext <;> ring
  simpa only [he, proj_int_pt] using F123_mem (2*n)

lemma F123_odd_mem (n : ℤ) :
    F123 (2*n+1) ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (3/4, 3/4)) := by
  have he : (((1:ℝ)/2 - ((2*n+1:ℤ):ℝ))/2, ((1:ℝ)/2 + ((2*n+1:ℤ):ℝ))/2) =
      (3/4 + ((-n-1:ℤ):ℝ), 3/4 + (n:ℝ)) := by push_cast; ext <;> ring
  simpa only [he, proj_int_pt] using F123_mem (2*n+1)

lemma char123_even (T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (hT : T ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4))) :
    ∃ n : ℤ, T = F123 (2*n) := by
  obtain ⟨n, rfl, hn⟩ := char123 _ T hT
  obtain ⟨j, k, hj, hk⟩ := proj_int hT.2.2.2.2.1
  dsimp [F123] at hj
  refine ⟨-j, ?_⟩
  have he : n = 2 * -j := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    linarith
  rw [he]

lemma char123_odd (T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (hT : T ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (3/4, 3/4))) :
    ∃ n : ℤ, T = F123 (2*n+1) := by
  obtain ⟨n, rfl, hn⟩ := char123 _ T hT
  obtain ⟨j, k, hj, hk⟩ := proj_int hT.2.2.2.2.1
  dsimp [F123] at hj
  refine ⟨-j-1, ?_⟩
  have he : n = 2 * (-j-1)+1 := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    linarith
  rw [he]

noncomputable def triangles123EvenEquiv : ℤ ≃
    triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4)) :=
  Equiv.ofBijective (fun n => ⟨F123 (2*n), F123_even_mem n⟩) ⟨by
    intro n m h
    have := F123_injective (congrArg Subtype.val h)
    omega, by
    intro T
    obtain ⟨n, hn⟩ := char123_even T.val T.property
    exact ⟨n, Subtype.ext hn.symm⟩⟩

noncomputable def triangles123OddEquiv : ℤ ≃
    triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (3/4, 3/4)) :=
  Equiv.ofBijective (fun n => ⟨F123 (2*n+1), F123_odd_mem n⟩) ⟨by
    intro n m h
    have := F123_injective (congrArg Subtype.val h)
    omega, by
    intro T
    obtain ⟨n, hn⟩ := char123_odd T.val T.property
    exact ⟨n, Subtype.ext hn.symm⟩⟩

noncomputable def F134other (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((3/4, 3/4), ((n:ℝ), (n:ℝ)), (3/2 - n, (n:ℝ)))

lemma char134other (r : Torus) :
    ∀ T ∈ triangles B1 B3 (B4 t) (proj (3/4, 3/4)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F134other n ∧ 4 * n - 3 ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B3, B4] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F134other] <;> linarith

lemma F134_injective : Function.Injective F134 := by
  intro n m h
  have hh := congrArg (fun T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => T.2.1.2) h
  simpa [F134] using hh

lemma F134other_injective : Function.Injective F134other := by
  intro n m h
  have hh := congrArg (fun T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => T.2.1.2) h
  simpa [F134other] using hh

lemma F234_injective : Function.Injective F234 := by
  intro n m h
  have hh := congrArg (fun T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => T.2.1.2) h
  simpa [F234] using hh

lemma F134_mem (n : ℤ) :
    F134 n ∈ triangles B1 B3 (B4 t) (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) := by
  have hn : (4 * (n : ℝ) - 1) ≠ 0 := by
    exact_mod_cast (show 4 * n - 1 ≠ 0 by omega)
  refine ⟨rfl, by norm_num [F134], by norm_num [F134], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F134, zero_add] using proj_int_pt 0 0 n n
  · simpa only [F134, Int.cast_neg, zero_add, sub_eq_add_neg] using proj_int_pt (1/2) 0 (-n) n
  all_goals dsimp [F134, det2, dirR, B1, B3, B4]
  all_goals try ring
  all_goals nlinarith [sq_pos_of_ne_zero hn]

lemma F134other_mem (n : ℤ) :
    F134other n ∈ triangles B1 B3 (B4 t) (proj (3/4, 3/4)) (proj (0, 0)) (proj (1/2, 0)) := by
  have hn : (4 * (n : ℝ) - 3) ≠ 0 := by
    exact_mod_cast (show 4 * n - 3 ≠ 0 by omega)
  refine ⟨rfl, by norm_num [F134other], by norm_num [F134other], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F134other, zero_add] using proj_int_pt 0 0 n n
  · have he : (3/2 - (n:ℝ), (n:ℝ)) = (1/2 + ((1-n:ℤ):ℝ), 0 + (n:ℝ)) := by
      push_cast; ext <;> ring
    change proj (3/2 - (n:ℝ), (n:ℝ)) = _
    rw [he, proj_int_pt]
  all_goals dsimp [F134other, det2, dirR, B1, B3, B4]
  all_goals try ring
  all_goals nlinarith [sq_pos_of_ne_zero hn]

lemma F234_mem (n : ℤ) (hn : n ≠ 0) :
    F234 n ∈ triangles B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) (proj (0, 0)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨rfl, by norm_num [F234], by norm_num [F234], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F234, zero_add] using proj_int_pt 0 0 n n
  · exact proj_zero_int n
  all_goals dsimp [F234, det2, dirR, B2, B3, B4]
  all_goals try ring
  all_goals nlinarith [sq_pos_of_ne_zero hn']

noncomputable def triangles134Equiv : ℤ ≃
    triangles B1 B3 (B4 t) (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) :=
  Equiv.ofBijective (fun n => ⟨F134 n, F134_mem t n⟩) ⟨by
    intro n m h
    exact F134_injective (congrArg Subtype.val h), by
    intro T
    obtain ⟨n, hn, _⟩ := char134 t _ T.val T.property
    exact ⟨n, Subtype.ext hn.symm⟩⟩

noncomputable def triangles134otherEquiv : ℤ ≃
    triangles B1 B3 (B4 t) (proj (3/4, 3/4)) (proj (0, 0)) (proj (1/2, 0)) :=
  Equiv.ofBijective (fun n => ⟨F134other n, F134other_mem t n⟩) ⟨by
    intro n m h
    exact F134other_injective (congrArg Subtype.val h), by
    intro T
    obtain ⟨n, hn, _⟩ := char134other t _ T.val T.property
    exact ⟨n, Subtype.ext hn.symm⟩⟩

noncomputable def triangles234Equiv : {n : ℤ // n ≠ 0} ≃
    triangles B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) (proj (0, 0)) :=
  Equiv.ofBijective (fun n => ⟨F234 n.val, F234_mem t n.val n.property⟩) ⟨by
    intro n m h
    exact Subtype.ext (F234_injective (congrArg Subtype.val h)), by
    intro T
    obtain ⟨n, hn, hne⟩ := char234 t _ T.val T.property
    exact ⟨⟨n, by simpa using hne⟩, Subtype.ext hn.symm⟩⟩

end HMSAdditive

-- From Reindex.lean

set_option autoImplicit false
noncomputable section
namespace HMSAdditive

lemma oddGaussian_lattice_hasSum (A : ℝ) (hA : 2 ≤ A) :
    HasSum (fun n : ℤ => Real.exp (-A * (4 * (n : ℝ) + 1)^2 / 16)) (oddGaussian A) := by
  have hs := oddGaussian_summable A hA
  have he : Summable (fun n : ℕ => oddGaussianTerm A (2*n)) :=
    hs.comp_injective (by intro n m h; change 2*n = 2*m at h; omega)
  have ho : Summable (fun n : ℕ => oddGaussianTerm A (2*n+1)) :=
    hs.comp_injective (by intro n m h; change 2*n+1 = 2*m+1 at h; omega)
  have hp : HasSum (fun n : ℕ => Real.exp (-A * (4 * ((n : ℤ) : ℝ) + 1)^2 / 16))
      (∑' n : ℕ, oddGaussianTerm A (2*n)) := by
    convert he.hasSum using 1
    ext n
    congr 1
    simp only [oddGaussianTerm, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast]
    ring
  have hm : HasSum (fun n : ℕ => Real.exp (-A * (4 * (((-((n : ℤ)+1)) : ℤ) : ℝ) + 1)^2 / 16))
      (∑' n : ℕ, oddGaussianTerm A (2*n+1)) := by
    convert ho.hasSum using 1
    ext n
    simp only [oddGaussianTerm]
    congr 1
    push_cast
    ring
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => Real.exp (-A * (4 * (n : ℝ) + 1)^2 / 16)) hp hm
  have hh := tsum_even_add_odd he ho
  rw [hh] at h
  exact h

lemma oddGaussian_lattice_neg_hasSum (A : ℝ) (hA : 2 ≤ A) :
    HasSum (fun n : ℤ => Real.exp (-A * (4 * (n : ℝ) - 1)^2 / 16)) (oddGaussian A) := by
  have h := (Equiv.neg ℤ).hasSum_iff.mpr (oddGaussian_lattice_hasSum A hA)
  convert h using 1
  ext n
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
  congr 1
  ring

end HMSAdditive


-- From Weights.lean

set_option autoImplicit false
noncomputable section
namespace HMSAdditive
open scoped Real
open KontsevichHMS KontsevichHMS.Brane

lemma weight123 (A : ℝ) (n : ℤ) :
    triangleWeight A B1 B2 B3 (F123 n) =
      (Real.exp (-A * (2 * (n : ℝ) - 1)^2 / 16) : ℂ) := by
  simp only [triangleWeight, B1, B2, B3, zero_mul, zero_add, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one, Complex.ofReal_exp]
  congr 1
  unfold F123 det2
  simp only [Prod.mk_sub_mk]
  push_cast
  ring

lemma coeff123_even (A : ℝ) (hA : 2 ≤ A) :
    mTwoCoeff A B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4)) =
      (oddGaussian A : ℂ) := by
  unfold mTwoCoeff
  rw [← triangles123EvenEquiv.tsum_eq]
  change (∑' n : ℤ, triangleWeight A B1 B2 B3 (F123 (2*n))) = _
  simp_rw [weight123]
  have he : (fun n : ℤ => Real.exp (-A * (2 * ((2*n : ℤ) : ℝ)-1)^2/16)) =
      (fun n : ℤ => Real.exp (-A * (4 * (n:ℝ)-1)^2/16)) := by
    ext n
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_tsum, he, (oddGaussian_lattice_neg_hasSum A hA).tsum_eq]

lemma coeff123_odd (A : ℝ) (hA : 2 ≤ A) :
    mTwoCoeff A B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (3/4, 3/4)) =
      (oddGaussian A : ℂ) := by
  unfold mTwoCoeff
  rw [← triangles123OddEquiv.tsum_eq]
  change (∑' n : ℤ, triangleWeight A B1 B2 B3 (F123 (2*n+1))) = _
  simp_rw [weight123]
  have he : (fun n : ℤ => Real.exp (-A * (2 * ((2*n+1 : ℤ) : ℝ)-1)^2/16)) =
      (fun n : ℤ => Real.exp (-A * (4 * (n:ℝ)+1)^2/16)) := by
    ext n
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_tsum, he, (oddGaussian_lattice_hasSum A hA).tsum_eq]

lemma coeff123_other (A : ℝ) (r : Torus)
    (hr : r ≠ proj (1/4, 1/4)) (hr' : r ≠ proj (3/4, 3/4)) :
    mTwoCoeff A B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r = 0 := by
  letI : IsEmpty (triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r) := ⟨by
    intro T
    obtain ⟨n, hn, _⟩ := char123 r T.val T.property
    have hp := T.property.2.2.2.2.1
    rw [hn] at hp
    have hcases := r_cases n r hp
    exact hcases.elim hr (fun h => hr' h)⟩
  exact tsum_empty

lemma weight134 (A t : ℝ) (n : ℤ) :
    triangleWeight A B1 B3 (B4 t) (F134 n) =
      (Real.exp (-A * (4 * (n : ℝ) - 1)^2 / 16) : ℂ) *
        Complex.exp ((π * t * (4 * (n : ℝ) - 1) : ℝ) * Complex.I) := by
  unfold triangleWeight
  congr 1
  · rw [Complex.ofReal_exp]
    congr 1
    unfold F134 det2
    simp only [Prod.mk_sub_mk]
    push_cast
    ring
  · congr 1
    simp [B1, B3, B4, param, dirR, F134]
    push_cast
    ring

lemma weight134other (A t : ℝ) (n : ℤ) :
    triangleWeight A B1 B3 (B4 t) (F134other n) =
      (Real.exp (-A * (4 * (n : ℝ) - 3)^2 / 16) : ℂ) *
        Complex.exp ((π * t * (4 * (n : ℝ) - 3) : ℝ) * Complex.I) := by
  unfold triangleWeight
  congr 1
  · rw [Complex.ofReal_exp]
    congr 1
    unfold F134other det2
    simp only [Prod.mk_sub_mk]
    push_cast
    ring
  · congr 1
    simp [B1, B3, B4, param, dirR, F134other]
    push_cast
    ring

lemma weight234 (A t : ℝ) (n : ℤ) :
    triangleWeight A B2 B3 (B4 t) (F234 n) =
      (Real.exp (-A * (n : ℝ)^2 / 2) : ℂ) *
        Complex.exp ((2 * π * t * (n : ℝ) : ℝ) * Complex.I) := by
  unfold triangleWeight
  congr 1
  · rw [Complex.ofReal_exp]
    congr 1
    unfold F234 det2
    simp only [Prod.mk_sub_mk]
    push_cast
    ring
  · congr 1
    simp [B2, B3, B4, param, dirR, F234]
    push_cast
    ring

end HMSAdditive

-- From Fourier.lean

set_option autoImplicit false
noncomputable section
namespace HMSAdditive
open scoped Real

universe u

lemma even_lattice_hasSum {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℝ → E) (heven : ∀ x, f (-x) = f x)
    (hs : Summable (fun n : ℕ => f (2 * (n : ℝ) + 1))) :
    HasSum (fun n : ℤ => f (4 * (n : ℝ) + 1)) (∑' n : ℕ, f (2 * (n : ℝ) + 1)) := by
  let g : ℕ → E := fun n => f (2 * (n : ℝ) + 1)
  have he : Summable (fun n : ℕ => g (2*n)) :=
    hs.comp_injective (by intro n m h; change 2*n = 2*m at h; omega)
  have ho : Summable (fun n : ℕ => g (2*n+1)) :=
    hs.comp_injective (by intro n m h; change 2*n+1 = 2*m+1 at h; omega)
  have hp : HasSum (fun n : ℕ => f (4 * ((n : ℤ) : ℝ) + 1)) (∑' n : ℕ, g (2*n)) := by
    convert he.hasSum using 1
    ext n
    dsimp [g]
    congr 1
    push_cast
    ring
  have hm : HasSum (fun n : ℕ => f (4 * (((-((n : ℤ)+1)) : ℤ) : ℝ) + 1))
      (∑' n : ℕ, g (2*n+1)) := by
    convert ho.hasSum using 1
    ext n
    dsimp [g]
    have heq : 4 * (((-((n : ℤ)+1)) : ℤ) : ℝ) + 1 = -(2 * ((2*n+1:ℕ):ℝ)+1) := by
      push_cast; ring
    rw [heq, heven]
  have h := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => f (4*(n:ℝ)+1)) hp hm
  rw [tsum_even_add_odd he ho] at h
  exact h

lemma even_lattice_neg_hasSum {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℝ → E) (heven : ∀ x, f (-x) = f x)
    (hs : Summable (fun n : ℕ => f (2 * (n : ℝ) + 1))) :
    HasSum (fun n : ℤ => f (4 * (n : ℝ) - 1)) (∑' n : ℕ, f (2 * (n : ℝ) + 1)) := by
  have h := (Equiv.neg ℤ).hasSum_iff.mpr (even_lattice_hasSum f heven hs)
  convert h using 1
  ext n
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
  rw [show 4 * -(n : ℝ) + 1 = -(4 * (n : ℝ) - 1) by ring, heven]

def gaussianPhase (c θ x : ℝ) : ℂ :=
  (Real.exp (-c * x^2) : ℂ) * Complex.exp ((θ * x : ℝ) * Complex.I)

lemma gaussianPhase_norm (c θ x : ℝ) : ‖gaussianPhase c θ x‖ = Real.exp (-c*x^2) := by
  rw [gaussianPhase, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma gaussianPhase_pair (c θ x : ℝ) :
    gaussianPhase c θ x + gaussianPhase c θ (-x) =
      (2 * Real.exp (-c*x^2) * Real.cos (θ*x) : ℝ) := by
  have heuler (y : ℝ) : Complex.exp ((y : ℂ) * Complex.I) =
      (Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [gaussianPhase, neg_sq, mul_neg]
  rw [heuler, heuler]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  push_cast
  ring

def signedNat (n : ℕ ⊕ ℕ) : {z : ℤ // z ≠ 0} :=
  match n with
  | Sum.inl n => ⟨(n:ℤ)+1, by omega⟩
  | Sum.inr n => ⟨-((n:ℤ)+1), by omega⟩

noncomputable def signedNatEquiv : (ℕ ⊕ ℕ) ≃ {z : ℤ // z ≠ 0} :=
  Equiv.ofBijective signedNat ⟨by
    intro n m h
    have hh := congrArg Subtype.val h
    cases n <;> cases m <;> dsimp [signedNat] at hh <;> first | congr 1 <;> omega | omega, by
    intro z
    by_cases hz : 0 < z.val
    · exact ⟨Sum.inl (z.val.toNat-1), Subtype.ext (by dsimp [signedNat]; omega)⟩
    · exact ⟨Sum.inr ((-z.val).toNat-1), Subtype.ext (by dsimp [signedNat]; have := z.property; omega)⟩⟩

lemma gaussianPhase_positive_summable (A t : ℝ) (hA : 2 ≤ A) :
    Summable (fun n : ℕ => gaussianPhase (A/2) (2*π*t) ((n:ℝ)+1)) := by
  apply (geometric_exp_summable (c := 1) (by norm_num)).of_norm_bounded
  intro n
  rw [gaussianPhase_norm]
  have h := connectionTerm_norm_le A 0 hA n
  simp only [connectionTerm, mul_zero, Real.cos_zero, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h
  convert h using 1 <;> congr 1 <;> ring

lemma gaussianPhase_negative_summable (A t : ℝ) (hA : 2 ≤ A) :
    Summable (fun n : ℕ => gaussianPhase (A/2) (2*π*t) (-((n:ℝ)+1))) := by
  apply (geometric_exp_summable (c := 1) (by norm_num)).of_norm_bounded
  intro n
  rw [gaussianPhase_norm, neg_sq]
  have h := connectionTerm_norm_le A 0 hA n
  simp only [connectionTerm, mul_zero, Real.cos_zero, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h
  convert h using 1 <;> congr 1 <;> ring

lemma gaussianPhase_nonzero_tsum (A t : ℝ) (hA : 2 ≤ A) :
    (∑' n : {z : ℤ // z ≠ 0}, gaussianPhase (A/2) (2*π*t) (n.val : ℝ)) =
      (connectionSeries A t : ℂ) := by
  have hp := gaussianPhase_positive_summable A t hA
  have hm := gaussianPhase_negative_summable A t hA
  rw [← signedNatEquiv.tsum_eq]
  change (∑' n : ℕ ⊕ ℕ, gaussianPhase (A/2) (2*π*t) ((signedNat n).val : ℝ)) = _
  have hsum := HasSum.sum
    (f := Sum.elim (fun n : ℕ => gaussianPhase (A/2) (2*π*t) ((n:ℝ)+1))
      (fun n : ℕ => gaussianPhase (A/2) (2*π*t) (-((n:ℝ)+1)))) hp.hasSum hm.hasSum
  have heq : (fun n : ℕ ⊕ ℕ => gaussianPhase (A/2) (2*π*t) ((signedNat n).val : ℝ)) =
      Sum.elim (fun n : ℕ => gaussianPhase (A/2) (2*π*t) ((n:ℝ)+1))
        (fun n : ℕ => gaussianPhase (A/2) (2*π*t) (-((n:ℝ)+1))) := by
    funext n
    cases n <;> simp [signedNat]
  rw [heq, hsum.tsum_eq, ← hp.tsum_add hm]
  simp_rw [gaussianPhase_pair]
  rw [← Complex.ofReal_tsum]
  congr 1
  unfold connectionSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold connectionTerm
  rw [show -(A/2) * ((n:ℝ)+1)^2 = -A*((n:ℝ)+1)^2/2 by ring,
    show 2*π*t*((n:ℝ)+1) = 2*π*((n:ℝ)+1)*t by ring]
  ring

lemma gaussianPhase_lattice_summable (A t : ℝ) (hA : 2 ≤ A) :
    Summable (fun n : ℤ => gaussianPhase (A/16) (π*t) (4*(n:ℝ)-1)) := by
  apply (oddGaussian_lattice_neg_hasSum A hA).summable.of_norm_bounded
  intro n
  rw [gaussianPhase_norm]
  apply le_of_eq
  congr 1
  ring

lemma gaussianPhase_lattice_neg_summable (A t : ℝ) (hA : 2 ≤ A) :
    Summable (fun n : ℤ => gaussianPhase (A/16) (π*t) (-(4*(n:ℝ)-1))) := by
  apply (oddGaussian_lattice_neg_hasSum A hA).summable.of_norm_bounded
  intro n
  rw [gaussianPhase_norm, neg_sq]
  apply le_of_eq
  congr 1
  ring

lemma gaussianPhase_lattice_pair_tsum (A t : ℝ) (hA : 2 ≤ A) :
    (∑' n : ℤ, gaussianPhase (A/16) (π*t) (4*(n:ℝ)-1)) +
      (∑' n : ℤ, gaussianPhase (A/16) (π*t) (4*(n:ℝ)-3)) =
      (oddCosineSeries A t : ℂ) := by
  have hp := gaussianPhase_lattice_summable A t hA
  have hm := gaussianPhase_lattice_neg_summable A t hA
  have hshift : (∑' n : ℤ, gaussianPhase (A/16) (π*t) (4*(n:ℝ)-3)) =
      ∑' n : ℤ, gaussianPhase (A/16) (π*t) (-(4*(n:ℝ)-1)) := by
    rw [← (Equiv.subLeft (1 : ℤ)).tsum_eq]
    apply tsum_congr
    intro n
    simp only [Equiv.subLeft_apply]
    congr 1
    push_cast
    ring
  rw [hshift, ← hp.tsum_add hm]
  simp_rw [gaussianPhase_pair]
  rw [← Complex.ofReal_tsum]
  congr 1
  let f : ℝ → ℝ := fun x => Real.exp (-(A/16)*x^2) * Real.cos (π*t*x)
  have heven : ∀ x, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [neg_sq, mul_neg, Real.cos_neg]
  have hs : Summable (fun n : ℕ => f (2*(n:ℝ)+1)) := by
    convert oddCosine_summable A t hA using 1
    ext n
    dsimp [f, oddCosineTerm, oddGaussianTerm]
    congr 2
    ring
  have hlat := even_lattice_neg_hasSum f heven hs
  have hlat2 := hlat.mul_left 2
  have hassoc : (fun n : ℤ => 2 * Real.exp (-(A/16)*(4*(n:ℝ)-1)^2) *
      Real.cos (π*t*(4*(n:ℝ)-1))) = (fun n : ℤ => 2 * f (4*(n:ℝ)-1)) := by
    funext n
    dsimp [f]
    ring
  rw [hassoc, hlat2.tsum_eq]
  unfold oddCosineSeries
  congr 1
  apply tsum_congr
  intro n
  dsimp [f, oddCosineTerm, oddGaussianTerm]
  congr 2
  ring

end HMSAdditive


-- From Coefficients.lean

set_option autoImplicit false
noncomputable section
namespace HMSAdditive
open scoped Real
open KontsevichHMS KontsevichHMS.Brane

lemma coeff234 (A t : ℝ) (hA : 2 ≤ A) :
    mTwoCoeff A B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) (proj (0, 0)) =
      (connectionSeries A t : ℂ) := by
  unfold mTwoCoeff
  rw [← (triangles234Equiv t).tsum_eq]
  change (∑' n : {z : ℤ // z ≠ 0}, triangleWeight A B2 B3 (B4 t) (F234 n.val)) = _
  rw [← gaussianPhase_nonzero_tsum A t hA]
  apply tsum_congr
  intro n
  rw [weight234]
  unfold gaussianPhase
  congr 2 <;> ring

lemma coeff234_other (A t : ℝ) (r : Torus) (hr : r ≠ proj (0, 0)) :
    mTwoCoeff A B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) r = 0 := by
  letI : IsEmpty (triangles B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) r) := ⟨by
    intro T
    obtain ⟨n, hn, _⟩ := char234 t r T.val T.property
    have hp := T.property.2.2.2.2.1
    rw [hn] at hp
    exact hr (hp.symm.trans (proj_zero_int n))⟩
  exact tsum_empty

lemma coeff134_sum (A t : ℝ) (hA : 2 ≤ A) :
    mTwoCoeff A B1 B3 (B4 t) (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) +
      mTwoCoeff A B1 B3 (B4 t) (proj (3/4, 3/4)) (proj (0, 0)) (proj (1/2, 0)) =
      (oddCosineSeries A t : ℂ) := by
  unfold mTwoCoeff
  rw [← (triangles134Equiv t).tsum_eq, ← (triangles134otherEquiv t).tsum_eq]
  change (∑' n : ℤ, triangleWeight A B1 B3 (B4 t) (F134 n)) +
    (∑' n : ℤ, triangleWeight A B1 B3 (B4 t) (F134other n)) = _
  rw [← gaussianPhase_lattice_pair_tsum A t hA]
  congr 1
  · apply tsum_congr
    intro n
    rw [weight134]
    unfold gaussianPhase
    congr 2 <;> ring
  · apply tsum_congr
    intro n
    rw [weight134other]
    unfold gaussianPhase
    congr 2 <;> ring

def p12 : isect B1 B2 := ⟨proj (0, 1/2), p12_mem⟩
def p23 : isect B2 B3 := ⟨proj (0, 0), q23_mem⟩
def p34 (t : ℝ) : isect B3 (B4 t) := ⟨proj (0, 0), q34_mem t⟩
def p13 : isect B1 B3 := ⟨proj (1/4, 1/4), r13_mem⟩
def p13other : isect B1 B3 := ⟨proj (3/4, 3/4), r13_other_mem⟩
def p14 (t : ℝ) : isect B1 (B4 t) := ⟨proj (1/2, 0), u14_mem t⟩

lemma p13_ne : p13 ≠ p13other := by
  intro h
  exact r13_ne (congrArg Subtype.val h)

lemma normalized_coeff123 (A : ℝ) (hA : 2 ≤ A) (hnorm : oddGaussian A = 1)
    (r : isect B1 B3) :
    mTwoCoeff A B1 B2 B3 p12.val p23.val r.val =
      (Finsupp.single p13 (1 : ℂ) + Finsupp.single p13other 1 : isect B1 B3 →₀ ℂ) r := by
  classical
  by_cases h : r = p13
  · subst r
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne p13_ne, add_zero]
    change mTwoCoeff A B1 B2 B3 (proj (0,1/2)) (proj (0,0)) (proj (1/4,1/4)) = 1
    rw [coeff123_even A hA, hnorm, Complex.ofReal_one]
  · by_cases h' : r = p13other
    · subst r
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne p13_ne.symm, Finsupp.single_eq_same, zero_add]
      change mTwoCoeff A B1 B2 B3 (proj (0,1/2)) (proj (0,0)) (proj (3/4,3/4)) = 1
      rw [coeff123_odd A hA, hnorm, Complex.ofReal_one]
    · have hr : r.val ≠ proj (1/4, 1/4) := fun he => h (Subtype.ext he)
      have hr' : r.val ≠ proj (3/4, 3/4) := fun he => h' (Subtype.ext he)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h', add_zero]
      exact coeff123_other A r.val hr hr'

lemma zero_coeff234 (A t : ℝ) (hA : 2 ≤ A) (hzero : connectionSeries A t = 0)
    (r : isect B2 (B4 t)) :
    mTwoCoeff A B2 B3 (B4 t) p23.val (p34 t).val r.val = 0 := by
  by_cases hr : r.val = proj (0, 0)
  · change mTwoCoeff A B2 B3 (B4 t) (proj (0, 0)) (proj (0, 0)) r.val = _
    rw [hr, coeff234 A t hA, hzero, Complex.ofReal_zero]
  · exact coeff234_other A t r.val hr

lemma nonzero_coeff134_sum (A t : ℝ) (hA0 : 2 ≤ A) (hA : A < 4)
    (ht0 : 0 ≤ t) (ht : t < 1/4) :
    mTwoCoeff A B1 B3 (B4 t) p13.val (p34 t).val (p14 t).val +
      mTwoCoeff A B1 B3 (B4 t) p13other.val (p34 t).val (p14 t).val ≠ 0 := by
  change mTwoCoeff A B1 B3 (B4 t) (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) +
    mTwoCoeff A B1 B3 (B4 t) (proj (3/4, 3/4)) (proj (0, 0)) (proj (1/2, 0)) ≠ 0
  rw [coeff134_sum A t hA0, Complex.ofReal_ne_zero]
  exact ne_of_gt (oddCosineSeries_pos A t hA0 hA ht0 ht)

theorem coefficient_obstruction : ∃ A t : ℝ, 0 < A ∧
    (∀ r : isect B1 B3,
      mTwoCoeff A B1 B2 B3 p12.val p23.val r.val =
        (Finsupp.single p13 (1 : ℂ) + Finsupp.single p13other 1 : isect B1 B3 →₀ ℂ) r) ∧
    (∀ r : isect B2 (B4 t),
      mTwoCoeff A B2 B3 (B4 t) p23.val (p34 t).val r.val = 0) ∧
    (mTwoCoeff A B1 B3 (B4 t) p13.val (p34 t).val (p14 t).val +
      mTwoCoeff A B1 B3 (B4 t) p13other.val (p34 t).val (p14 t).val ≠ 0) := by
  obtain ⟨A, hA0, hA, hnorm⟩ := exists_normalized_area
  obtain ⟨t, ht0, ht, hzero⟩ := exists_zero_connection A hA0.le
  exact ⟨A, t, lt_trans (by norm_num) hA0,
    normalized_coeff123 A hA0.le hnorm,
    zero_coeff234 A t hA0.le hzero,
    nonzero_coeff134_sum A t hA0.le hA ht0.le ht⟩

end HMSAdditive



-- Work/HMSShiftZero.lean

set_option autoImplicit false
noncomputable section
namespace HMSShiftZero
open CategoryTheory
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

def unshiftHom (X Y : C) : (X ⟶ Y⟦(0 : ℤ)⟧) ≃+ (X ⟶ Y) where
  toFun f := f ≫ (shiftFunctorZero C ℤ).hom.app Y
  invFun f := f ≫ (shiftFunctorZero C ℤ).inv.app Y
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp only [Preadditive.add_comp]

theorem unshift_product {X Y Z : C} (f : X ⟶ Y⟦(0 : ℤ)⟧)
    (g : Y ⟶ Z⟦(0 : ℤ)⟧) :
    unshiftHom X Z
      (f ≫ g⟦(0 : ℤ)⟧' ≫ (shiftFunctorAdd' C (0 : ℤ) 0 0 (add_zero (0 : ℤ))).inv.app Z) =
      unshiftHom X Y f ≫ unshiftHom Y Z g := by
  change (f ≫ g⟦(0 : ℤ)⟧' ≫
    (shiftFunctorAdd' C (0 : ℤ) 0 0 (add_zero (0 : ℤ))).inv.app Z) ≫
      (shiftFunctorZero C ℤ).hom.app Z = _
  rw [shiftFunctorAdd'_add_zero_inv_app]
  have hn := (shiftFunctorZero C ℤ).hom.naturality g
  simpa only [Functor.id_map,Category.assoc,unshiftHom,AddEquiv.coe_mk,Equiv.coe_fn_mk]
    using congrArg (fun h => f ≫ h ≫ (shiftFunctorZero C ℤ).hom.app Z) hn

theorem product_of_coefficients {I J K : Type w} {X Y Z : C}
    (e₁₂ : (I →₀ ℂ) ≃+ (X ⟶ Y⟦(0 : ℤ)⟧))
    (e₂₃ : (J →₀ ℂ) ≃+ (Y ⟶ Z⟦(0 : ℤ)⟧))
    (e₁₃ : (K →₀ ℂ) ≃+ (X ⟶ Z⟦(0 : ℤ)⟧))
    (a : I →₀ ℂ) (b : J →₀ ℂ) (ξ : K →₀ ℂ)
    (hξ : ∀ k, e₁₃.symm
      (e₁₂ a ≫ (e₂₃ b)⟦(0 : ℤ)⟧' ≫
        (shiftFunctorAdd' C (0 : ℤ) 0 0 (add_zero (0 : ℤ))).inv.app Z) k = ξ k) :
    unshiftHom X Y (e₁₂ a) ≫ unshiftHom Y Z (e₂₃ b) = unshiftHom X Z (e₁₃ ξ) := by
  rw [← unshift_product]
  apply congrArg (unshiftHom X Z)
  apply e₁₃.symm.injective
  exact (Finsupp.ext hξ).trans (e₁₃.symm_apply_apply ξ).symm

def normalizeEquiv {I : Type w} {X Y : C} {n : ℤ}
    (e : (I →₀ ℂ) ≃+ (X ⟶ Y⟦n⟧)) (hn : n = 0) : (I →₀ ℂ) ≃+ (X ⟶ Y) := by
  subst n
  exact e.trans (unshiftHom X Y)

def productVector {I J K : Type w} {X Y Z : C} {n₁₂ n₂₃ n₁₃ : ℤ}
    (e₁₂ : (I →₀ ℂ) ≃+ (X ⟶ Y⟦n₁₂⟧))
    (e₂₃ : (J →₀ ℂ) ≃+ (Y ⟶ Z⟦n₂₃⟧))
    (e₁₃ : (K →₀ ℂ) ≃+ (X ⟶ Z⟦n₁₃⟧))
    (hμ : n₂₃ + n₁₂ = n₁₃) (a : I →₀ ℂ) (b : J →₀ ℂ) : K →₀ ℂ :=
  e₁₃.symm (e₁₂ a ≫ (e₂₃ b)⟦n₁₂⟧' ≫ (shiftFunctorAdd' C n₂₃ n₁₂ n₁₃ hμ).inv.app Z)

theorem normalize_product {I J K : Type w} {X Y Z : C} {n₁₂ n₂₃ n₁₃ : ℤ}
    (e₁₂ : (I →₀ ℂ) ≃+ (X ⟶ Y⟦n₁₂⟧))
    (e₂₃ : (J →₀ ℂ) ≃+ (Y ⟶ Z⟦n₂₃⟧))
    (e₁₃ : (K →₀ ℂ) ≃+ (X ⟶ Z⟦n₁₃⟧))
    (h₁₂ : n₁₂ = 0) (h₂₃ : n₂₃ = 0) (h₁₃ : n₁₃ = 0)
    (hμ : n₂₃ + n₁₂ = n₁₃) (a : I →₀ ℂ) (b : J →₀ ℂ) :
    normalizeEquiv e₁₂ h₁₂ a ≫ normalizeEquiv e₂₃ h₂₃ b =
      normalizeEquiv e₁₃ h₁₃ (productVector e₁₂ e₂₃ e₁₃ hμ a b) := by
  subst n₁₂
  subst n₂₃
  subst n₁₃
  exact product_of_coefficients e₁₂ e₂₃ e₁₃ a b _ (fun _ => rfl)

/-- An additive comparison already forces the coefficient contradiction when
the first product has two unit coefficients and the second product vanishes. -/
theorem additive_contradiction {I K : Type w} {X Y Z W : C}
    (e : (I →₀ ℂ) ≃+ (X ⟶ Z)) (ω : (K →₀ ℂ) ≃+ (X ⟶ W))
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (i j : I) (k : K)
    (a b : K →₀ ℂ)
    (hfg : f ≫ g = e (Finsupp.single i 1 + Finsupp.single j 1))
    (hgh : g ≫ h = 0)
    (ha : e (Finsupp.single i 1) ≫ h = ω a)
    (hb : e (Finsupp.single j 1) ≫ h = ω b)
    (hn : a k + b k ≠ 0) : False := by
  have hz : ω (a+b) = 0 := by
    calc
      ω (a+b) = ω a + ω b := ω.map_add a b
      _ = (e (Finsupp.single i 1) + e (Finsupp.single j 1)) ≫ h := by
        rw [Preadditive.add_comp,ha,hb]
      _ = e (Finsupp.single i 1 + Finsupp.single j 1) ≫ h := by rw [map_add]
      _ = (f ≫ g) ≫ h := by rw [hfg]
      _ = f ≫ (g ≫ h) := Category.assoc _ _ _
      _ = 0 := by rw [hgh]; simp
  have he : a+b = 0 := ω.injective (hz.trans ω.map_zero.symm)
  apply hn
  have hk := congrArg (fun t : K →₀ ℂ => t k) he
  simpa using hk

end HMSShiftZero

-- Work/HMSMain.lean

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open KontsevichHMS KontsevichHMS.Brane HMSAdditive HMSShiftZero
open scoped KontsevichHMS

theorem solution : ¬ (∀ (area : ℝ) (harea : 0 < area),
    ∃ (E : Scheme.{0}) (f : E ⟶ Spec (CommRingCat.of ℂ)),
      IsProper f ∧ SmoothOfRelativeDimension 1 f ∧
      ∃ Φ : Brane → DerivedCategory (SchemeModules E),
        (∀ b, IsBoundedCoherent E (Φ b)) ∧
        (∀ b₁ b₂, Transverse b₁ b₂ → ∀ d : ℤ, d ≠ maslov b₁ b₂ →
          ∀ g : Φ b₁ ⟶ (Φ b₂)⟦d⟧, g = 0) ∧
        ∃ ψ : ∀ b₁ b₂, Transverse b₁ b₂ →
            ((↥(isect b₁ b₂) →₀ ℂ) ≃+ (Φ b₁ ⟶ (Φ b₂)⟦maslov b₁ b₂⟧)),
          ∀ (b₁ b₂ b₃ : Brane) (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃)
            (h₁₃ : Transverse b₁ b₃)
            (hμ : maslov b₂ b₃ + maslov b₁ b₂ = maslov b₁ b₃)
            (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (r : ↥(isect b₁ b₃)),
            (ψ b₁ b₃ h₁₃).symm
                (ψ b₁ b₂ h₁₂ (Finsupp.single p 1) ≫
                  ((ψ b₂ b₃ h₂₃ (Finsupp.single q 1))⟦maslov b₁ b₂⟧') ≫
                  (shiftFunctorAdd' (DerivedCategory (SchemeModules E))
                      (maslov b₂ b₃) (maslov b₁ b₂) (maslov b₁ b₃) hμ).inv.app (Φ b₃)) r
              = mTwoCoeff area b₁ b₂ b₃ p q r) := by
  intro hall
  obtain ⟨A, t, hA, h123, h234, h134⟩ := HMSAdditive.coefficient_obstruction
  obtain ⟨E, f, hproper, hsmooth, Φ, hbounded, hvanish, ψ, hprod⟩ := hall A hA
  obtain ⟨t12, t23, t34, t13, t24, t14⟩ := HMSAdditive.all_transverse t
  obtain ⟨d12, d23, d34, d13, d24, d14⟩ := HMSAdditive.all_maslov_zero t
  have μ123 : maslov B2 B3 + maslov B1 B2 = maslov B1 B3 := by rw [d12, d23, d13]; rfl
  have μ234 : maslov B3 (B4 t) + maslov B2 B3 = maslov B2 (B4 t) := by rw [d23, d34, d24]; rfl
  have μ134 : maslov B3 (B4 t) + maslov B1 B3 = maslov B1 (B4 t) := by rw [d13, d34, d14]; rfl
  let e12 := normalizeEquiv (ψ B1 B2 t12) d12
  let e23 := normalizeEquiv (ψ B2 B3 t23) d23
  let e34 := normalizeEquiv (ψ B3 (B4 t) t34) d34
  let e13 := normalizeEquiv (ψ B1 B3 t13) d13
  let e24 := normalizeEquiv (ψ B2 (B4 t) t24) d24
  let e14 := normalizeEquiv (ψ B1 (B4 t) t14) d14
  let v123 := productVector (ψ B1 B2 t12) (ψ B2 B3 t23) (ψ B1 B3 t13) μ123
    (Finsupp.single p12 1) (Finsupp.single p23 1)
  let v234 := productVector (ψ B2 B3 t23) (ψ B3 (B4 t) t34) (ψ B2 (B4 t) t24) μ234
    (Finsupp.single p23 1) (Finsupp.single (p34 t) 1)
  let a := productVector (ψ B1 B3 t13) (ψ B3 (B4 t) t34) (ψ B1 (B4 t) t14) μ134
    (Finsupp.single p13 1) (Finsupp.single (p34 t) 1)
  let b := productVector (ψ B1 B3 t13) (ψ B3 (B4 t) t34) (ψ B1 (B4 t) t14) μ134
    (Finsupp.single p13other 1) (Finsupp.single (p34 t) 1)
  have hv123 : v123 = Finsupp.single p13 1 + Finsupp.single p13other 1 := by
    apply Finsupp.ext
    intro r
    exact (hprod B1 B2 B3 t12 t23 t13 μ123 p12 p23 r).trans (h123 r)
  have hv234 : v234 = 0 := by
    apply Finsupp.ext
    intro r
    exact (hprod B2 B3 (B4 t) t23 t34 t24 μ234 p23 (p34 t) r).trans (h234 r)
  have hfg : e12 (Finsupp.single p12 1) ≫ e23 (Finsupp.single p23 1) =
      e13 (Finsupp.single p13 1 + Finsupp.single p13other 1) := by
    have hh := normalize_product (ψ B1 B2 t12) (ψ B2 B3 t23) (ψ B1 B3 t13)
      d12 d23 d13 μ123 (Finsupp.single p12 1) (Finsupp.single p23 1)
    change e12 (Finsupp.single p12 1) ≫ e23 (Finsupp.single p23 1) = e13 v123 at hh
    rw [hv123] at hh
    exact hh
  have hgh : e23 (Finsupp.single p23 1) ≫ e34 (Finsupp.single (p34 t) 1) = 0 := by
    have hh := normalize_product (ψ B2 B3 t23) (ψ B3 (B4 t) t34) (ψ B2 (B4 t) t24)
      d23 d34 d24 μ234 (Finsupp.single p23 1) (Finsupp.single (p34 t) 1)
    change e23 (Finsupp.single p23 1) ≫ e34 (Finsupp.single (p34 t) 1) = e24 v234 at hh
    rw [hv234, map_zero] at hh
    exact hh
  have ha : e13 (Finsupp.single p13 1) ≫ e34 (Finsupp.single (p34 t) 1) = e14 a :=
    normalize_product (ψ B1 B3 t13) (ψ B3 (B4 t) t34) (ψ B1 (B4 t) t14)
      d13 d34 d14 μ134 (Finsupp.single p13 1) (Finsupp.single (p34 t) 1)
  have hb : e13 (Finsupp.single p13other 1) ≫ e34 (Finsupp.single (p34 t) 1) = e14 b :=
    normalize_product (ψ B1 B3 t13) (ψ B3 (B4 t) t34) (ψ B1 (B4 t) t14)
      d13 d34 d14 μ134 (Finsupp.single p13other 1) (Finsupp.single (p34 t) 1)
  have hn : a (p14 t) + b (p14 t) ≠ 0 := by
    have ha' : a (p14 t) = mTwoCoeff A B1 B3 (B4 t) p13 (p34 t) (p14 t) :=
      hprod B1 B3 (B4 t) t13 t34 t14 μ134 p13 (p34 t) (p14 t)
    have hb' : b (p14 t) = mTwoCoeff A B1 B3 (B4 t) p13other (p34 t) (p14 t) :=
      hprod B1 B3 (B4 t) t13 t34 t14 μ134 p13other (p34 t) (p14 t)
    rw [ha', hb']
    exact h134
  exact additive_contradiction e13 e14 (e12 (Finsupp.single p12 1))
    (e23 (Finsupp.single p23 1)) (e34 (Finsupp.single (p34 t) 1))
    p13 p13other (p14 t) a b hfg hgh ha hb hn


#print axioms solution
