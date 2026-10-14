-- Prove2me | solution 1 for HighDimStat.RandomMatrices.thresholded_covariance_estimation_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T23:25:27.153132+00:00
-- url     : https://prove2.me/submissions/3de9f75c-4411-4e5d-aa49-ccd6db1c43f9

-- Complete checked reconstruction of the native thresholded covariance estimation theorem with exact constants 8 and 16.
-- Licensed under Apache 2.0.
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin CoshSeries

open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

noncomputable def coshTerm (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)

lemma coshTerm_nonneg (x : ℝ) (k : ℕ) : 0 ≤ coshTerm x k := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg x) k

lemma coshTerm_zero (x : ℝ) : coshTerm x 0 = 1 := by
  simp [coshTerm]

lemma coshTerm_summable (x : ℝ) : Summable (coshTerm x) :=
  (Real.hasSum_cosh x).summable

lemma sum_coshTerm_le (x : ℝ) (s : Finset ℕ) :
    ∑ k ∈ s, coshTerm x k ≤ Real.cosh x := by
  rw [Real.cosh_eq_tsum]
  exact (coshTerm_summable x).sum_le_tsum s (fun k _ => coshTerm_nonneg x k)

lemma sum_coshTerm_le_sub_one (x : ℝ) (s : Finset ℕ) (hs : 0 ∉ s) :
    ∑ k ∈ s, coshTerm x k ≤ Real.cosh x - 1 := by
  have h := sum_coshTerm_le x (insert 0 s)
  rw [Finset.sum_insert hs, coshTerm_zero] at h
  linarith

lemma pair_ge_of_product {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (h : r ^ 2 * b ^ 2 ≤ a * c) :
    2 * r * b ≤ a + c := by
  apply (sq_le_sq₀ (by positivity) (add_nonneg ha hc)).mp
  nlinarith [sq_nonneg (a - c)]

lemma cosh_fourth_lower (x : ℝ) : x ^ 4 / 12 ≤ Real.cosh x - 1 := by
  have h := sum_coshTerm_le_sub_one x ({1, 2, 3} : Finset ℕ) (by decide)
  norm_num [coshTerm] at h
  have hpair : x ^ 4 / 24 ≤ x ^ 2 / 2 + x ^ 6 / 720 := by
    have hsq := sq_nonneg (x ^ 2 - 15)
    have hx := sq_nonneg x
    nlinarith [mul_nonneg hx hsq]
  linarith

end HighDimStat.RandomMatrices.Proof
-- End CoshSeries

-- Begin CoshPairs

namespace HighDimStat.RandomMatrices.Proof

lemma coshTerm_adj_product (x : ℝ) (j : ℕ) :
    coshTerm x j * coshTerm x (j + 2) *
        ((2 * (j : ℝ) + 4) * (2 * j + 3)) =
      coshTerm x (j + 1) ^ 2 * ((2 * (j : ℝ) + 2) * (2 * j + 1)) := by
  unfold coshTerm
  rw [show 2 * (j + 2) = 2 * j + 4 by omega,
    show 2 * (j + 1) = 2 * j + 2 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, pow_add]
  have hf : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma coshTerm_outer_product (x : ℝ) (j : ℕ) :
    coshTerm x j * coshTerm x (j + 4) *
        ((2 * (j : ℝ) + 8) * (2 * j + 7) * (2 * j + 6) * (2 * j + 5)) =
      coshTerm x (j + 2) ^ 2 *
        ((2 * (j : ℝ) + 4) * (2 * j + 3) * (2 * j + 2) * (2 * j + 1)) := by
  unfold coshTerm
  rw [show 2 * (j + 4) = 2 * j + 8 by omega,
    show 2 * (j + 2) = 2 * j + 4 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, pow_add]
  have hf : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma cosh_adjacent_pair_lower (x : ℝ) (n : ℕ) :
    (4 / 3 : ℝ) * coshTerm x (n + 3) ≤
      coshTerm x (n + 2) + coshTerm x (n + 4) := by
  have hr := coshTerm_adj_product x (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_ofNat] at hr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hG : 0 < (2 * ((n : ℝ) + 2) + 4) * (2 * (n + 2) + 3) := by positivity
  have hc : 4 * ((2 * ((n : ℝ) + 2) + 4) * (2 * (n + 2) + 3)) ≤
      9 * ((2 * ((n : ℝ) + 2) + 2) * (2 * (n + 2) + 1)) := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hp : (2 / 3 : ℝ) ^ 2 * coshTerm x (n + 3) ^ 2 ≤
      coshTerm x (n + 2) * coshTerm x (n + 4) := by
    apply (mul_le_mul_iff_left₀ hG).mp
    nlinarith [mul_nonneg (sq_nonneg (coshTerm x (n + 3))) (sub_nonneg.mpr hc)]
  have hh := pair_ge_of_product (coshTerm_nonneg x (n + 2))
    (coshTerm_nonneg x (n + 3)) (coshTerm_nonneg x (n + 4))
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hp
  linarith

lemma cosh_outer_pair_lower (x : ℝ) (n : ℕ) :
    (1 / 3 : ℝ) * coshTerm x (n + 3) ≤
      coshTerm x (n + 1) + coshTerm x (n + 5) := by
  have hr := coshTerm_outer_product x (n + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at hr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hG : 0 < (2 * ((n : ℝ) + 1) + 8) * (2 * (n + 1) + 7) *
      (2 * (n + 1) + 6) * (2 * (n + 1) + 5) := by positivity
  have hc : (2 * ((n : ℝ) + 1) + 8) * (2 * (n + 1) + 7) *
      (2 * (n + 1) + 6) * (2 * (n + 1) + 5) ≤
      36 * ((2 * ((n : ℝ) + 1) + 4) * (2 * (n + 1) + 3) *
        (2 * (n + 1) + 2) * (2 * (n + 1) + 1)) := by
    have hh : 0 ≤ 560 * (n : ℝ) ^ 4 + 4912 * n ^ 3 + 15412 * n ^ 2 +
        19796 * n + 7920 := by positivity
    nlinarith only [hh]
  have hp : (1 / 6 : ℝ) ^ 2 * coshTerm x (n + 3) ^ 2 ≤
      coshTerm x (n + 1) * coshTerm x (n + 5) := by
    apply (mul_le_mul_iff_left₀ hG).mp
    nlinarith [mul_nonneg (sq_nonneg (coshTerm x (n + 3))) (sub_nonneg.mpr hc)]
  have hh := pair_ge_of_product (coshTerm_nonneg x (n + 1))
    (coshTerm_nonneg x (n + 3)) (coshTerm_nonneg x (n + 5))
    (by norm_num : (0 : ℝ) ≤ 1 / 6) hp
  linarith

end HighDimStat.RandomMatrices.Proof
-- End CoshPairs

-- Begin CoshLower

open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma cosh_high_lower_shift (x : ℝ) (n : ℕ) :
    (8 / 3 : ℝ) * coshTerm x (n + 3) ≤ Real.cosh x - 1 := by
  let s := (Finset.range 5).image (fun i => n + 1 + i)
  have hzero : 0 ∉ s := by
    simp only [s, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    omega
  have h := sum_coshTerm_le_sub_one x s hzero
  rw [show (∑ k ∈ s, coshTerm x k) =
      ∑ i ∈ Finset.range 5, coshTerm x (n + 1 + i) by
        exact Finset.sum_image (by intro a _ b _ hab; dsimp at hab; omega)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero,
    Nat.add_assoc, Nat.reduceAdd, zero_add] at h
  have ha := cosh_adjacent_pair_lower x n
  have ho := cosh_outer_pair_lower x n
  linarith

lemma cosh_high_lower (x : ℝ) (k : ℕ) (hk : 3 ≤ k) :
    (8 / 3 : ℝ) * (x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) ≤
      Real.cosh x - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [coshTerm, Nat.add_comm] using cosh_high_lower_shift x n

end HighDimStat.RandomMatrices.Proof
-- End CoshLower

-- Begin FactorialRatio

open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma sum_log_factorial_interval (k j : ℕ) :
    (∑ i ∈ Finset.range j, Real.log ((k + i + 1 : ℕ) : ℝ)) =
      Real.log ((k + j).factorial : ℝ) - Real.log (k.factorial : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show k + (j + 1) = (k + j) + 1 by omega, Nat.factorial_succ,
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      ring

lemma sum_shift_difference (f : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, f (i + 1)) =
      (∑ i ∈ Finset.range k, f i) + f k - f 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

lemma log_factorial_ratio_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((2 * k).factorial : ℝ) - Real.log (k.factorial : ℝ) ≤
      Real.log 2 + (k : ℝ) * Real.log (4 * (k : ℝ)) - k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hmono : MonotoneOn Real.log (Set.Icc (k : ℝ) ((k : ℝ) + k)) := by
    intro a ha b _ hab
    exact Real.log_le_log (lt_of_lt_of_le hkR ha.1) hab
  have hint := hmono.sum_le_integral (a := k)
  rw [integral_log] at hint
  have hshift := sum_shift_difference (fun i => Real.log ((k + i : ℕ) : ℝ)) k
  have hsum := sum_log_factorial_interval k k
  have h2 : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) hkR.ne'
  have h4 : Real.log (4 * (k : ℝ)) = 2 * Real.log 2 + Real.log k := by
    rw [Real.log_mul (by norm_num) hkR.ne']
    have h := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at h
    linarith
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_zero] at hshift hsum
  rw [show k + k = 2 * k by omega] at hsum
  have heq : (k : ℝ) + k = 2 * k := by ring
  rw [heq, h2] at hint
  rw [heq, h2] at hshift
  simp only [add_assoc] at hsum
  nlinarith [hsum]

lemma factorial_exp_bound (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) * Real.exp k ≤
      2 * (k.factorial : ℝ) * (4 * (k : ℝ)) ^ k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hh := log_factorial_ratio_le k hk
  have he := Real.exp_le_exp.mpr (show
      Real.log ((2 * k).factorial : ℝ) - Real.log (k.factorial : ℝ) + k ≤
        Real.log 2 + (k : ℝ) * Real.log (4 * k) by linarith)
  rw [Real.exp_add, Real.exp_sub, Real.exp_log (by positivity),
    Real.exp_log (by positivity), Real.exp_add, Real.exp_log (by norm_num),
    Real.exp_nat_mul, Real.exp_log (by positivity)] at he
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  calc
    ((2 * k).factorial : ℝ) * Real.exp k =
        ((((2 * k).factorial : ℝ) / k.factorial) * Real.exp k) * k.factorial := by
          field_simp
    _ ≤ (2 * (4 * (k : ℝ)) ^ k) * k.factorial :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by ring

end HighDimStat.RandomMatrices.Proof
-- End FactorialRatio

-- Begin SubgaussianCosh

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : Ω → ℝ}

lemma normalized_abs_pow_integrable (h : HasSubgaussianMGF X 1 P) (k : ℕ) :
    Integrable (fun ω => |X ω| ^ k) P := by
  simpa only [Real.norm_eq_abs, ENNReal.coe_natCast] using
    (h.memLp (k : ℝ≥0)).integrable_norm_pow'

omit [IsProbabilityMeasure P] in
lemma normalized_cosh_integrable (h : HasSubgaussianMGF X 1 P) (t : ℝ) :
    Integrable (fun ω => Real.cosh (t * X ω)) P := by
  simp only [Real.cosh_eq]
  have hn := h.integrable_exp_mul (-t)
  simp only [neg_mul] at hn
  exact ((h.integrable_exp_mul t).add hn).div_const 2

omit [IsProbabilityMeasure P] in
lemma normalized_cosh_integral (h : HasSubgaussianMGF X 1 P) (t : ℝ) :
    (∫ ω, Real.cosh (t * X ω) ∂P) ≤ Real.exp (t ^ 2 / 2) := by
  have hp := h.mgf_le t
  have hm := h.mgf_le (-t)
  simp only [mgf, NNReal.coe_one, one_mul, neg_sq, neg_mul] at hp hm
  simp only [Real.cosh_eq]
  rw [integral_div, integral_add (h.integrable_exp_mul t)]
  · linarith
  · simpa only [neg_mul] using h.integrable_exp_mul (-t)

end HighDimStat.RandomMatrices.Proof
-- End SubgaussianCosh

-- Begin FourthMoment

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma normalized_fourth_moment (h : HasSubgaussianMGF X 1 P) :
    (∫ ω, |X ω| ^ 4 ∂P) ≤ 6 := by
  have hi := normalized_abs_pow_integrable h 4
  have hc := normalized_cosh_integrable h (Real.sqrt 2)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
    norm_num
  have hp (ω : Ω) : |X ω| ^ 4 / 3 ≤ Real.cosh (Real.sqrt 2 * X ω) - 1 := by
    have hh := cosh_fourth_lower (Real.sqrt 2 * X ω)
    rw [mul_pow, hs4] at hh
    have ha : |X ω| ^ 4 = X ω ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
    rw [ha]
    linarith
  have hint := integral_mono (hi.div_const 3) (hc.sub (integrable_const 1)) hp
  simp only [Pi.sub_apply] at hint
  rw [integral_div, integral_sub hc (integrable_const 1)] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hc' := normalized_cosh_integral h (Real.sqrt 2)
  rw [hs] at hc'
  norm_num at hc'
  have he := Real.exp_one_lt_three
  linarith

lemma abs_product_le_fourths (a b : ℝ) :
    |a * b| ≤ (|a| ^ 4 + |b| ^ 4 + 2) / 4 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| ^ 2 - 1),
    sq_nonneg (|b| ^ 2 - 1)]

omit [IsProbabilityMeasure P] in
lemma normalized_product_integrable (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) : Integrable (fun ω => X ω * Y ω) P := by
  have hx : MemLp X 2 P := by simpa using hX.memLp 2
  have hy : MemLp Y 2 P := by simpa using hY.memLp 2
  exact hx.integrable_mul hy

lemma normalized_product_abs_mean_le_seven_half (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) :
    |∫ ω, X ω * Y ω ∂P| ≤ 7 / 2 := by
  have hX4 := normalized_abs_pow_integrable hX 4
  have hY4 := normalized_abs_pow_integrable hY 4
  have hXY := normalized_product_integrable hX hY
  have hi := integral_mono hXY.abs
    (((hX4.add hY4).add (integrable_const 2)).div_const 4)
    (fun ω => abs_product_le_fourths (X ω) (Y ω))
  simp only [Pi.add_apply] at hi
  have hsum : Integrable (fun ω => |X ω| ^ 4 + |Y ω| ^ 4) P := hX4.add hY4
  rw [integral_div, integral_add hsum (integrable_const 2),
    integral_add hX4 hY4] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hx := normalized_fourth_moment hX
  have hy := normalized_fourth_moment hY
  have habs : |∫ ω, X ω * Y ω ∂P| ≤ ∫ ω, |X ω * Y ω| ∂P :=
    abs_integral_le_integral_abs
  linarith

end HighDimStat.RandomMatrices.Proof
-- End FourthMoment

-- Begin EvenMoments

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : Ω → ℝ}

lemma normalized_even_moment_high (hX : HasSubgaussianMGF X 1 P)
    (k : ℕ) (hk : 3 ≤ k) :
    (∫ ω, |X ω| ^ (2 * k) ∂P) ≤ 3 * (k.factorial : ℝ) * 2 ^ (k - 2) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let t := Real.sqrt (2 * (k : ℝ))
  let F : ℝ := (2 * k).factorial
  let B : ℝ := (2 * (k : ℝ)) ^ k
  have hF : 0 < F := by dsimp [F]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have ht : t ^ 2 = 2 * (k : ℝ) := Real.sq_sqrt (by positivity)
  have htp : t ^ (2 * k) = B := by rw [pow_mul, ht]
  have hi := normalized_abs_pow_integrable hX (2 * k)
  have hc := normalized_cosh_integrable hX t
  have hp (ω : Ω) : ((8 / 3 : ℝ) * B / F) * |X ω| ^ (2 * k) ≤
      Real.cosh (t * X ω) - 1 := by
    have hh := cosh_high_lower (t * X ω) k hk
    rw [mul_pow, htp] at hh
    have ha : |X ω| ^ (2 * k) = X ω ^ (2 * k) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [ha]
    convert hh using 1
    dsimp [F]
    ring
  have hint := integral_mono (hi.const_mul ((8 / 3 : ℝ) * B / F))
    (hc.sub (integrable_const 1)) hp
  simp only [Pi.sub_apply] at hint
  rw [integral_const_mul, integral_sub hc (integrable_const 1)] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hcg := normalized_cosh_integral hX t
  have harg : 2 * (k : ℝ) / 2 = k := by ring
  rw [ht, harg] at hcg
  have hpre : ((8 / 3 : ℝ) * B / F) * (∫ ω, |X ω| ^ (2 * k) ∂P) ≤
      Real.exp k := by linarith
  have hmul := mul_le_mul_of_nonneg_right hpre hF.le
  have he : (8 / 3 : ℝ) * B * (∫ ω, |X ω| ^ (2 * k) ∂P) ≤
      F * Real.exp k := by
    have hFeq : ((8 / 3 : ℝ) * B / F) *
        (∫ ω, |X ω| ^ (2 * k) ∂P) * F =
        (8 / 3 : ℝ) * B * (∫ ω, |X ω| ^ (2 * k) ∂P) := by field_simp
    rw [hFeq] at hmul
    simpa [mul_comm] using hmul
  have hf := factorial_exp_bound k (by omega)
  have hp4 : (4 * (k : ℝ)) ^ k = 2 ^ k * B := by
    dsimp [B]
    rw [← mul_pow]
    congr 1
    ring
  rw [hp4] at hf
  have hfinal : (8 / 3 : ℝ) * (∫ ω, |X ω| ^ (2 * k) ∂P) ≤
      2 * (k.factorial : ℝ) * 2 ^ k := by
    apply (mul_le_mul_iff_left₀ hB).mp
    dsimp [F] at he
    nlinarith [he.trans hf]
  have hpow : (2 : ℝ) ^ k = 4 * 2 ^ (k - 2) := by
    conv_lhs => rw [show k = (k - 2) + 2 by omega]
    rw [pow_add]
    ring
  rw [hpow] at hfinal
  linarith

lemma normalized_even_moment (hX : HasSubgaussianMGF X 1 P)
    (k : ℕ) (hk : 2 ≤ k) :
    (∫ ω, |X ω| ^ (2 * k) ∂P) ≤ 3 * (k.factorial : ℝ) * 2 ^ (k - 2) := by
  rcases eq_or_lt_of_le hk with rfl | hk'
  · norm_num
    exact normalized_fourth_moment hX
  · exact normalized_even_moment_high hX k (by omega)

end HighDimStat.RandomMatrices.Proof
-- End EvenMoments

-- Begin ProductMoments

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices.Proof

lemma abs_product_pow_le_even (a b : ℝ) (k : ℕ) :
    |a * b| ^ k ≤ (|a| ^ (2 * k) + |b| ^ (2 * k)) / 2 := by
  rw [abs_mul, mul_pow]
  have ha : |a| ^ (2 * k) = (|a| ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hb : |b| ^ (2 * k) = (|b| ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  rw [ha, hb]
  nlinarith [sq_nonneg (|a| ^ k - |b| ^ k)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma normalized_product_abs_pow_integrable (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) (k : ℕ) :
    Integrable (fun ω => |X ω * Y ω| ^ k) P := by
  have hx := normalized_abs_pow_integrable hX (2 * k)
  have hy := normalized_abs_pow_integrable hY (2 * k)
  have hmX := hX.aestronglyMeasurable
  have hmY := hY.aestronglyMeasurable
  apply ((hx.add hy).div_const 2).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact abs_product_pow_le_even (X ω) (Y ω) k

lemma normalized_product_moment (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) (k : ℕ) (hk : 2 ≤ k) :
    (∫ ω, |X ω * Y ω| ^ k ∂P) ≤ 3 * (k.factorial : ℝ) * 2 ^ (k - 2) := by
  have hx := normalized_abs_pow_integrable hX (2 * k)
  have hy := normalized_abs_pow_integrable hY (2 * k)
  have hi := integral_mono (normalized_product_abs_pow_integrable hX hY k)
    ((hx.add hy).div_const 2) (fun ω => abs_product_pow_le_even (X ω) (Y ω) k)
  simp only [Pi.add_apply] at hi
  rw [integral_div, integral_add hx hy] at hi
  have hxm := normalized_even_moment hX k hk
  have hym := normalized_even_moment hY k hk
  linarith

end HighDimStat.RandomMatrices.Proof
-- End ProductMoments

-- Begin ProductCoefficient

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma product_coefficient_integrable (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => (t * (X ω * Y ω)) ^ k / (k.factorial : ℝ)) P := by
  have hi := ((normalized_product_abs_pow_integrable hX hY k).const_mul (|t| ^ k)).div_const
    (k.factorial : ℝ)
  have hmX := hX.aestronglyMeasurable
  have hmY := hY.aestronglyMeasurable
  apply hi.mono' (by fun_prop)
  filter_upwards [] with ω
  simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, mul_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (k.factorial : ℝ) from Nat.cast_nonneg _), le_refl]

lemma normalized_product_coefficient_le (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) (t : ℝ) (n : ℕ) :
    (∫ ω, (t * (X ω * Y ω)) ^ (n + 2) / ((n + 2).factorial : ℝ) ∂P) ≤
      3 * t ^ 2 * (2 * |t|) ^ n := by
  have hm := normalized_product_moment hX hY (n + 2) (by omega)
  have hi := normalized_product_abs_pow_integrable hX hY (n + 2)
  have hupper := (hi.const_mul (|t| ^ (n + 2))).div_const ((n + 2).factorial : ℝ)
  have hpoint (ω : Ω) :
      (t * (X ω * Y ω)) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
      (|t| ^ (n + 2) * |X ω * Y ω| ^ (n + 2)) / ((n + 2).factorial : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    simpa only [abs_pow, abs_mul, mul_pow] using
      le_abs_self ((t * (X ω * Y ω)) ^ (n + 2))
  have hint := integral_mono (product_coefficient_integrable hX hY t (n + 2)) hupper hpoint
  have heupper : (∫ ω, (|t| ^ (n + 2) * |X ω * Y ω| ^ (n + 2)) /
      ((n + 2).factorial : ℝ) ∂P) =
      |t| ^ (n + 2) * (∫ ω, |X ω * Y ω| ^ (n + 2) ∂P) /
        ((n + 2).factorial : ℝ) := by rw [integral_div, integral_const_mul]
  rw [heupper] at hint
  calc
    (∫ ω, (t * (X ω * Y ω)) ^ (n + 2) / ((n + 2).factorial : ℝ) ∂P) ≤
        |t| ^ (n + 2) * (∫ ω, |X ω * Y ω| ^ (n + 2) ∂P) /
          ((n + 2).factorial : ℝ) := hint
    _ ≤ |t| ^ (n + 2) * (3 * ((n + 2).factorial : ℝ) * 2 ^ n) /
          ((n + 2).factorial : ℝ) := by
      gcongr
      simpa using hm
    _ = 3 * t ^ 2 * (2 * |t|) ^ n := by
      rw [pow_add, mul_pow, sq_abs]
      have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
      field_simp

end HighDimStat.RandomMatrices.Proof
-- End ProductCoefficient

-- Begin GaussianSquare

open MeasureTheory ProbabilityTheory Real

namespace HighDimStat.RandomMatrices.Proof

lemma gaussian_square_density (t z : ℝ) :
    gaussianPDFReal 0 1 z * exp (t * z ^ 2) =
      (sqrt (2 * π))⁻¹ * exp (-(1 / 2 - t) * z ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

lemma gaussian_square_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℝ => exp (t * z ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun z => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussian_square_density]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1 / 2 - t)).const_mul _

lemma gaussian_square_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : ℝ, exp (t * z ^ 2) ∂gaussianReal 0 1) =
      1 / sqrt (1 - 2 * t) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have h : 0 < 1 - 2 * t := by linarith
  have hb : 0 < 1 / 2 - t := by linarith
  have hs : 0 < sqrt (1 - 2 * t) := sqrt_pos.2 h
  have hp : 0 < sqrt (2 * π) := sqrt_pos.2 (mul_pos (by norm_num) pi_pos)
  have he : π / (1 / 2 - t) = (2 * π) / (1 - 2 * t) := by field_simp
  rw [he, sqrt_div (le_of_lt (mul_pos (by norm_num) pi_pos))]
  field_simp

end HighDimStat.RandomMatrices.Proof
-- End GaussianSquare

-- Begin GaussianMixture

open MeasureTheory ProbabilityTheory Real

namespace HighDimStat.RandomMatrices.Proof

lemma gaussian_linear_integral (a : ℝ) :
    (∫ z : ℝ, exp (a * z) ∂gaussianReal 0 1) = exp (a ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) a
  simpa [mgf] using h

lemma subgaussian_square_mgf_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hm : Measurable X) (hX : HasSubgaussianMGF X 1 P)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    Integrable (fun ω => exp (t * X ω ^ 2)) P ∧
      (∫ ω, exp (t * X ω ^ 2) ∂P) ≤ 1 / sqrt (1 - 2 * t) := by
  let G := gaussianReal 0 1
  let F : ℝ × Ω → ℝ := fun z => exp (sqrt (2 * t) * z.1 * X z.2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hs : sqrt (2 * t) ^ 2 = 2 * t := sq_sqrt (by positivity)
  have hbound (z : ℝ) : (∫ ω, F (z, ω) ∂P) ≤ exp (t * z ^ 2) := by
    have h := hX.mgf_le (sqrt (2 * t) * z)
    simp only [NNReal.coe_one, one_mul, mgf] at h
    convert h using 1
    congr 1
    rw [mul_pow, hs]
    ring
  have hnonneg (z : ℝ × Ω) : 0 ≤ F z := (exp_pos _).le
  have hinner : Integrable (fun z => ∫ ω, F (z, ω) ∂P) G := by
    apply (gaussian_square_integrable ht').mono'
      hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => hnonneg (z, ω))]
      exact hbound z
  have hprod : Integrable F (G.prod P) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ fun z => hX.integrable_exp_mul (sqrt (2 * t) * z)
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hinner
  have hid (ω : Ω) : (∫ z, F (z, ω) ∂G) = exp (t * X ω ^ 2) := by
    have h := gaussian_linear_integral (sqrt (2 * t) * X ω)
    have he : (sqrt (2 * t) * X ω) ^ 2 / 2 = t * X ω ^ 2 := by
      rw [mul_pow, hs]; ring
    rw [he] at h
    convert h using 1
    congr 1
    funext z
    dsimp [F]
    congr 1
    ring
  constructor
  · simpa only [hid] using hprod.integral_prod_right
  · calc
      (∫ ω, exp (t * X ω ^ 2) ∂P) = ∫ ω, ∫ z, F (z, ω) ∂G ∂P := by simp only [hid]
      _ = ∫ z, ∫ ω, F (z, ω) ∂P ∂G := (integral_integral_swap hprod).symm
      _ ≤ ∫ z, exp (t * z ^ 2) ∂G := integral_mono hinner (gaussian_square_integrable ht') hbound
      _ = _ := gaussian_square_integral ht'

lemma subgaussian_square_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasSubgaussianMGF X 1 P) {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    Integrable (fun ω => exp (t * X ω ^ 2)) P ∧
      (∫ ω, exp (t * X ω ^ 2) ∂P) ≤ 1 / sqrt (1 - 2 * t) := by
  let Y := hX.aemeasurable.mk X
  have he : X =ᵐ[P] Y := hX.aemeasurable.ae_eq_mk
  have h := subgaussian_square_mgf_measurable hX.aemeasurable.measurable_mk
    (hX.congr he) ht ht'
  have he' : (fun ω => exp (t * X ω ^ 2)) =ᵐ[P] (fun ω => exp (t * Y ω ^ 2)) :=
    he.fun_comp fun x => exp (t * x ^ 2)
  exact ⟨h.1.congr he'.symm, (integral_congr_ae he').trans_le h.2⟩

end HighDimStat.RandomMatrices.Proof
-- End GaussianMixture

-- Begin ProductExponential

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma half_square_exp_memLp (hX : HasSubgaussianMGF X 1 P)
    {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1 / 2) :
    MemLp (fun ω => Real.exp (q / 2 * X ω ^ 2)) 2 P := by
  have hm := hX.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  convert (subgaussian_square_mgf hX hq hq').1 using 1
  funext ω
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma product_abs_exp_integrable (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1 / 2) :
    Integrable (fun ω => Real.exp (q * |X ω * Y ω|)) P := by
  have hXY := (half_square_exp_memLp hX hq hq').integrable_mul
    (half_square_exp_memLp hY hq hq')
  have hmX := hX.aestronglyMeasurable
  have hmY := hY.aestronglyMeasurable
  apply hXY.mono' (by fun_prop)
  filter_upwards [] with ω
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : |X ω * Y ω| ≤ (X ω ^ 2 + Y ω ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|X ω| - |Y ω|), sq_abs (X ω), sq_abs (Y ω)]
  nlinarith [mul_le_mul_of_nonneg_left hh hq]

lemma product_exp_integrable (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) {t : ℝ} (ht : |t| < 1 / 2) :
    Integrable (fun ω => Real.exp (t * (X ω * Y ω))) P := by
  have hmX := hX.aestronglyMeasurable
  have hmY := hY.aestronglyMeasurable
  apply (product_abs_exp_integrable hX hY (abs_nonneg t) ht).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (le_abs_self (t * (X ω * Y ω)) |>.trans_eq (abs_mul _ _))

end HighDimStat.RandomMatrices.Proof
-- End ProductExponential

-- Begin ExponentialSeries

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma real_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

lemma integral_exp_hasSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z P) {t : ℝ}
    (habs : Integrable (fun ω => Real.exp (|t * Z ω|)) P) :
    HasSum (fun n : ℕ => ∫ ω, (t * Z ω) ^ n / (n.factorial : ℝ) ∂P)
      (∫ ω, Real.exp (t * Z ω) ∂P) := by
  apply hasSum_integral_of_dominated_convergence
    (fun n ω => |t * Z ω| ^ n / (n.factorial : ℝ))
  · intro n
    fun_prop
  · intro n
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _), le_refl]
  · exact ae_of_all _ fun ω => (real_exp_hasSum |t * Z ω|).summable
  · convert habs using 1
    funext ω
    exact (real_exp_hasSum |t * Z ω|).tsum_eq
  · exact ae_of_all _ fun ω => real_exp_hasSum (t * Z ω)

end HighDimStat.RandomMatrices.Proof
-- End ExponentialSeries

-- Begin ProductMGF

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma normalized_product_mgf_bound (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) {t : ℝ} (ht : |t| < 1 / 2) :
    (∫ ω, Real.exp (t * (X ω * Y ω)) ∂P) ≤
      Real.exp (t * (∫ ω, X ω * Y ω ∂P) + 3 * t ^ 2 / (1 - 2 * |t|)) := by
  have habs : Integrable (fun ω => Real.exp (|t * (X ω * Y ω)|)) P := by
    simpa only [abs_mul] using product_abs_exp_integrable hX hY (abs_nonneg t) ht
  have hs := integral_exp_hasSum (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable) habs
  simp only [Pi.mul_apply] at hs
  have htail := (hasSum_nat_add_iff' 2).2 hs
  have hfirst : (∑ i ∈ Finset.range 2,
      ∫ ω, (t * (X ω * Y ω)) ^ i / (i.factorial : ℝ) ∂P) =
      1 + t * (∫ ω, X ω * Y ω ∂P) := by
    norm_num [Finset.sum_range_succ, integral_const_mul]
  rw [hfirst] at htail
  have hr0 : 0 ≤ 2 * |t| := by positivity
  have hr1 : 2 * |t| < 1 := by linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (3 * t ^ 2)
  have hle := hasSum_le (normalized_product_coefficient_le hX hY t) htail hg
  have hb : (∫ ω, Real.exp (t * (X ω * Y ω)) ∂P) ≤
      1 + t * (∫ ω, X ω * Y ω ∂P) + 3 * t ^ 2 / (1 - 2 * |t|) := by
    simp only [div_eq_mul_inv] at *
    linarith
  have he := Real.add_one_le_exp
    (t * (∫ ω, X ω * Y ω ∂P) + 3 * t ^ 2 / (1 - 2 * |t|))
  linarith

lemma normalized_centered_product_mgf (hX : HasSubgaussianMGF X 1 P)
    (hY : HasSubgaussianMGF Y 1 P) {t : ℝ} (ht : |t| < 1 / 2) :
    Integrable (fun ω => Real.exp
      (t * (X ω * Y ω - ∫ z, X z * Y z ∂P))) P ∧
      (∫ ω, Real.exp (t * (X ω * Y ω - ∫ z, X z * Y z ∂P)) ∂P) ≤
        Real.exp (3 * t ^ 2 / (1 - 2 * |t|)) := by
  let m := ∫ z, X z * Y z ∂P
  have heq : (fun ω => Real.exp (t * (X ω * Y ω - m))) =
      (fun ω => Real.exp (-t * m) * Real.exp (t * (X ω * Y ω))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun ω => Real.exp (t * (X ω * Y ω - m))) P ∧ _
  constructor
  · rw [heq]
    exact (product_exp_integrable hX hY ht).const_mul _
  · change (∫ ω, Real.exp (t * (X ω * Y ω - m)) ∂P) ≤ _
    rw [heq, integral_const_mul]
    calc
      Real.exp (-t * m) * (∫ ω, Real.exp (t * (X ω * Y ω)) ∂P) ≤
          Real.exp (-t * m) * Real.exp (t * m + 3 * t ^ 2 / (1 - 2 * |t|)) :=
        mul_le_mul_of_nonneg_left (normalized_product_mgf_bound hX hY ht) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end HighDimStat.RandomMatrices.Proof
-- End ProductMGF

-- Begin IndependentMGF

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma independent_mgf_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    (hI : iIndepFun X P) (hm : ∀ i, AEMeasurable (X i) P)
    (t : ℝ) (hi : ∀ i, Integrable (fun ω => exp (t * X i ω)) P) :
    Integrable (fun ω => exp (t * ∑ i, X i ω)) P ∧
      (∫ ω, exp (t * ∑ i, X i ω) ∂P) = ∏ i, ∫ ω, exp (t * X i ω) ∂P := by
  have he : ∀ ω, exp (t * ∑ i, X i ω) = ∏ i, exp (t * X i ω) := by
    intro ω
    rw [Finset.mul_sum, Real.exp_sum]
  have hp := hI.integral_fun_prod_comp hm
    (f := fun _ x => exp (t * x)) (fun _ => by fun_prop)
  have heq : (∫ ω, exp (t * ∑ i, X i ω) ∂P) =
      ∏ i, ∫ ω, exp (t * X i ω) ∂P := by simpa only [he] using hp
  refine ⟨?_, heq⟩
  by_contra hn
  rw [integral_undef hn] at heq
  have hpos : 0 < ∏ i, ∫ ω, exp (t * X i ω) ∂P :=
    Finset.prod_pos fun i _ => integral_exp_pos (hi i)
  linarith

lemma independent_chernoff {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hI : iIndepFun X P) (hm : ∀ i, AEMeasurable (X i) P)
    {t b r : ℝ} (ht : 0 ≤ t)
    (hi : ∀ i, Integrable (fun ω => exp (t * X i ω)) P)
    (hb : ∀ i, (∫ ω, exp (t * X i ω) ∂P) ≤ exp b) :
    P.real {ω | r ≤ ∑ i, X i ω} ≤ exp (-t * r + n * b) := by
  obtain ⟨h_int, h_eq⟩ := independent_mgf_sum hI hm t hi
  have h := measure_ge_le_exp_mul_mgf r ht h_int
  change P.real {ω | r ≤ ∑ i, X i ω} ≤ _ at h
  rw [mgf, h_eq] at h
  calc
    P.real {ω | r ≤ ∑ i, X i ω} ≤ exp (-t * r) * ∏ i, ∫ ω, exp (t * X i ω) ∂P := h
    _ ≤ exp (-t * r) * ∏ _ : Fin n, exp b := by
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      exact Finset.prod_le_prod (fun i _ => integral_nonneg (fun ω => (exp_pos (t * X i ω)).le))
        (fun i _ => hb i)
    _ = exp (-t * r + n * b) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← exp_nat_mul, ← exp_add]

end HighDimStat.RandomMatrices.Proof
-- End IndependentMGF

-- Begin BernsteinTail

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma bernstein_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hI : iIndepFun X P)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hmgf : ∀ i t, |t| < 1 / 2 →
      Integrable (fun ω => exp (t * X i ω)) P ∧
        (∫ ω, exp (t * X i ω) ∂P) ≤ exp (3 * t ^ 2 / (1 - 2 * |t|)))
    {v : ℝ} (hv : 0 < v) :
    P.real {ω | v ≤ (1 / (n : ℝ)) * ∑ i, X i ω} ≤
      exp (-((n : ℝ) * v ^ 2 / (12 + 4 * v))) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let t := v / (6 + 2 * v)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : |t| < 1 / 2 := by
    rw [abs_of_nonneg ht]
    dsimp [t]
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have h := independent_chernoff hI hm ht
    (fun i => (hmgf i t ht').1) (fun i => (hmgf i t ht').2) (r := n * v)
  have he : {ω | v ≤ (1 / (n : ℝ)) * ∑ i, X i ω} =
      {ω | (n : ℝ) * v ≤ ∑ i, X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, one_div, ← div_eq_inv_mul, le_div_iff₀ hn0]
    rw [mul_comm]
  rw [he]
  convert h using 1
  congr 1
  rw [abs_of_nonneg ht]
  have hd : 6 + 2 * v ≠ 0 := ne_of_gt (by positivity)
  have hd' : 12 + 4 * v ≠ 0 := ne_of_gt (by positivity)
  have hh : 1 - 2 * t = 6 / (6 + 2 * v) := by dsimp [t]; field_simp; ring
  rw [hh]
  dsimp [t]
  field_simp
  ring

lemma bernstein_two_sided_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hI : iIndepFun X P)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hmgf : ∀ i t, |t| < 1 / 2 →
      Integrable (fun ω => exp (t * X i ω)) P ∧
        (∫ ω, exp (t * X i ω) ∂P) ≤ exp (3 * t ^ 2 / (1 - 2 * |t|)))
    {v : ℝ} (hv : 0 < v) :
    P.real {ω | v ≤ |(1 / (n : ℝ)) * ∑ i, X i ω|} ≤
      2 * exp (-((n : ℝ) * v ^ 2 / (12 + 4 * v))) := by
  have hpos := bernstein_upper_tail hn hI hm hmgf hv
  have hneg := bernstein_upper_tail hn
    (hI.comp (fun _ x => -x) (fun _ => measurable_neg)) (fun i => (hm i).neg)
    (X := fun i ω => -X i ω) ?_ hv
  · have he : {ω | v ≤ |(1 / (n : ℝ)) * ∑ i, X i ω|} =
        {ω | v ≤ (1 / (n : ℝ)) * ∑ i, X i ω} ∪
        {ω | v ≤ (1 / (n : ℝ)) * ∑ i, -X i ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, Finset.sum_neg_distrib, mul_neg]
    rw [he]
    exact (measureReal_union_le _ _).trans (by linarith)
  · intro i t ht
    have h := hmgf i (-t) (by simpa using ht)
    simpa only [neg_mul, mul_neg, abs_neg, neg_sq] using h

end HighDimStat.RandomMatrices.Proof
-- End BernsteinTail

-- Begin EntryTail

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma normalized_entry_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ} (hn : 0 < n)
    {x : Fin n → Ω → Fin d → ℝ} (hI : iIndepFun x P)
    (hm : ∀ i, AEMeasurable (x i) P)
    (hX : ∀ i j, HasSubgaussianMGF (fun ω => x i ω j) 1 P)
    (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hc : ∀ i j k, (∫ ω, x i ω j * x i ω k ∂P) = Sig j k)
    (j k : Fin d) {v : ℝ} (hv : 0 < v) :
    P.real {ω | v ≤ |sampleCovariance (fun i => x i ω) j k - Sig j k|} ≤
      2 * exp (-((n : ℝ) * v ^ 2 / (12 + 4 * v))) := by
  let Z : Fin n → Ω → ℝ := fun i ω => x i ω j * x i ω k - Sig j k
  have hZI : iIndepFun Z P := hI.comp (fun _ y => y j * y k - Sig j k) (fun _ => by fun_prop)
  have hZm : ∀ i, AEMeasurable (Z i) P := by
    intro i
    exact ((measurable_pi_apply j).comp_aemeasurable (hm i)).mul
      ((measurable_pi_apply k).comp_aemeasurable (hm i)) |>.sub_const _
  have h := bernstein_two_sided_tail hn hZI hZm (fun i t ht => ?_) hv
  · convert h using 1
    congr 1
    ext ω
    dsimp [sampleCovariance, Z]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
  · simpa only [hc i j k] using normalized_centered_product_mgf (hX i j) (hX i k) ht

end HighDimStat.RandomMatrices.Proof
-- End EntryTail

-- Begin SquareTail

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma square_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hI : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) 1 P)
    {u : ℝ} (hu : 1 < u) :
    P.real {ω | u ≤ (1 / (n : ℝ)) * ∑ i, X i ω ^ 2} ≤
      exp (-((n : ℝ) * (u - 1 - log u) / 2)) := by
  have hu0 : 0 < u := by linarith
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let t := (u - 1) / (2 * u)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t < 1 / 2 := by dsimp [t]; apply (div_lt_iff₀ (by positivity)).2; linarith
  have he : 1 - 2 * t = 1 / u := by dsimp [t]; field_simp ; ring_nf
  have hs : 0 < sqrt (1 - 2 * t) := sqrt_pos.2 (by linarith)
  let b := log (1 / sqrt (1 - 2 * t))
  have hb : exp b = 1 / sqrt (1 - 2 * t) := exp_log (by positivity)
  have h := independent_chernoff
    (hI.comp (fun _ x => x ^ 2) (fun _ => by fun_prop))
    (fun i => (hX i).aemeasurable.pow_const 2) ht
    (fun i => (subgaussian_square_mgf (hX i) ht ht').1)
    (b := b) (r := n * u)
    (fun i => by rw [hb]; exact (subgaussian_square_mgf (hX i) ht ht').2)
  have hev : {ω | u ≤ (1 / (n : ℝ)) * ∑ i, X i ω ^ 2} =
      {ω | (n : ℝ) * u ≤ ∑ i, X i ω ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, one_div, ← div_eq_inv_mul, le_div_iff₀ hn0]
    rw [mul_comm]
  rw [hev]
  convert h using 1
  congr 1
  have hblog : b = log u / 2 := by
    dsimp [b]
    rw [he, log_div one_ne_zero (ne_of_gt (sqrt_pos.2 (one_div_pos.mpr hu0))), log_one,
      log_sqrt (by positivity), log_div one_ne_zero hu0.ne', log_one]
    ring_nf
  rw [hblog]
  dsimp [t]
  field_simp ; ring_nf

end HighDimStat.RandomMatrices.Proof
-- End SquareTail

-- Begin MatrixDomination

namespace HighDimStat.RandomMatrices.Proof

open scoped BigOperators

lemma euclidean_norm_le_of_abs_le {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, |x i| ≤ |y i|) : ‖x‖ ≤ ‖y‖ := by
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (abs_nonneg _) (h i) 2

lemma opNorm_le_of_entrywise {d : ℕ} (M A : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hA : ∀ i j, 0 ≤ A i j)
    (h : ∀ i j, |M i j| ≤ c * A i j) : opNorm M ≤ c * opNorm A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc (norm_nonneg _))
  intro x
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => |x j|)
  have hy : ‖y‖ = ‖x‖ := by simp [EuclideanSpace.norm_eq, y, Real.norm_eq_abs]
  have hp : ∀ i, |((Matrix.toEuclideanCLM (𝕜 := ℝ)) M x) i| ≤
      |(c • (Matrix.toEuclideanCLM (𝕜 := ℝ)) A y) i| := by
    intro i
    change |∑ j, M i j * x j| ≤ |c * ∑ j, A i j * abs (x j)|
    rw [abs_of_nonneg (mul_nonneg hc (Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (abs_nonneg _)))]
    calc
      |∑ j, M i j * x j| ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, c * A i j * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
      _ = c * ∑ j, A i j * |x j| := by rw [Finset.mul_sum]; congr 1; ext j; ring
  calc
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) M x‖ ≤ ‖c • (Matrix.toEuclideanCLM (𝕜 := ℝ)) A y‖ :=
      euclidean_norm_le_of_abs_le _ _ hp
    _ = c * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) A y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c * (opNorm A * ‖y‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hc
    _ = (c * opNorm A) * ‖x‖ := by rw [hy]; ring

lemma adjacency_nonneg {d : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    0 ≤ adjacencyMatrix Sig i j := by simp [adjacencyMatrix]; split_ifs <;> norm_num

lemma adjacency_ne_zero {d : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig ≠ 0) :
    adjacencyMatrix Sig ≠ 0 := by
  intro h
  apply hSig
  ext i j
  change Sig i j = 0
  have hh := congrFun (congrFun h i) j
  simpa [adjacencyMatrix] using hh

lemma opNorm_pos_of_ne_zero {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M ≠ 0) :
    0 < opNorm M := by
  apply norm_pos_iff.mpr
  intro h
  apply hM
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective (by simpa using h)

end HighDimStat.RandomMatrices.Proof
-- End MatrixDomination

-- Begin ThresholdStrict

namespace HighDimStat.RandomMatrices.Proof

lemma threshold_entry_zero {d : ℕ} (S Sig : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    (h : ∀ i j, |S i j - Sig i j| < lam) (i j : Fin d) (hz : Sig i j = 0) :
    (thresholdMatrix lam S - Sig) i j = 0 := by
  have hij := h i j
  simp only [hz, sub_zero] at hij
  simp [thresholdMatrix, hz, not_lt_of_ge (le_of_lt hij)]

lemma threshold_entry_lt {d : ℕ} (S Sig : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    (hlam : 0 < lam) (h : ∀ i j, |S i j - Sig i j| < lam) (i j : Fin d) :
    |(thresholdMatrix lam S - Sig) i j| < 2 * lam := by
  simp only [Matrix.sub_apply, thresholdMatrix, Matrix.of_apply]
  split_ifs with hij
  · exact lt_trans (h i j) (by linarith)
  · have he : |Sig i j| ≤ |S i j| + |S i j - Sig i j| := by
      have := abs_sub_le (Sig i j) (S i j) 0
      simpa [abs_sub_comm, add_comm] using this
    simp only [zero_sub, abs_neg]
    have hs := le_of_not_gt hij
    nlinarith [h i j]

lemma threshold_norm_lt {d : ℕ} [Nonempty (Fin d)]
    (S Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig ≠ 0) (lam : ℝ)
    (hlam : 0 < lam) (h : ∀ i j, |S i j - Sig i j| < lam) :
    opNorm (thresholdMatrix lam S - Sig) < 2 * opNorm (adjacencyMatrix Sig) * lam := by
  classical
  let E := thresholdMatrix lam S - Sig
  let c := Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d × Fin d)).Nonempty)
    (fun ij => |E ij.1 ij.2|)
  have hc : 0 ≤ c := by
    obtain ⟨i⟩ := ‹Nonempty (Fin d)›
    exact le_trans (abs_nonneg (E i i)) (Finset.le_sup' (fun ij => |E ij.1 ij.2|) (Finset.mem_univ (i, i)))
  have hclt : c < 2 * lam := by
    dsimp only [c]
    rw [Finset.sup'_lt_iff]
    intro ij _
    exact threshold_entry_lt S Sig lam hlam h ij.1 ij.2
  have he : ∀ i j, |E i j| ≤ c * adjacencyMatrix Sig i j := by
    intro i j
    by_cases hz : Sig i j = 0
    · simp [E, threshold_entry_zero S Sig lam h i j hz, adjacencyMatrix, hz]
    · simpa [adjacencyMatrix, hz] using
        (Finset.le_sup' (fun ij => |E ij.1 ij.2|) (Finset.mem_univ (i, j)))
  have hp := opNorm_pos_of_ne_zero _ (adjacency_ne_zero Sig hSig)
  calc
    opNorm E ≤ c * opNorm (adjacencyMatrix Sig) :=
      opNorm_le_of_entrywise E _ c hc (adjacency_nonneg Sig) he
    _ < (2 * lam) * opNorm (adjacencyMatrix Sig) := mul_lt_mul_of_pos_right hclt hp
    _ = 2 * opNorm (adjacencyMatrix Sig) * lam := by ring

end HighDimStat.RandomMatrices.Proof
-- End ThresholdStrict

-- Begin DiagonalSafe

open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma sample_entry_le_diagonal_average {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (j k : Fin d) :
    |sampleCovariance x j k| ≤ (sampleCovariance x j j + sampleCovariance x k k) / 2 := by
  simp only [sampleCovariance, Matrix.of_apply, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  have h : |∑ i, x i j * x i k| ≤ (∑ i, x i j * x i j + ∑ i, x i k * x i k) / 2 := by
    calc
      |∑ i, x i j * x i k| ≤ ∑ i, |x i j * x i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (x i j * x i j + x i k * x i k) / 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (x i j - x i k), sq_nonneg (x i j + x i k)]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / (n : ℝ))
  nlinarith

lemma threshold_sample_eq_zero {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (lam : ℝ) (h : ∀ j, sampleCovariance x j j ≤ lam) :
    thresholdMatrix lam (sampleCovariance x) = 0 := by
  ext j k
  have he := sample_entry_le_diagonal_average x j k
  have hb : |sampleCovariance x j k| ≤ lam := by linarith [h j, h k]
  simp [thresholdMatrix, not_lt_of_ge hb]

lemma covariance_opNorm_bound {d : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ i j, |Sig i j| ≤ 7 / 2) :
    opNorm Sig ≤ (7 / 2) * opNorm (adjacencyMatrix Sig) := by
  apply opNorm_le_of_entrywise Sig _ _ (by norm_num) (adjacency_nonneg Sig)
  intro i j
  by_cases hz : Sig i j = 0
  · simp [adjacencyMatrix, hz]
  · simpa [adjacencyMatrix, hz] using h i j

lemma diagonal_safe {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig ≠ 0)
    (hSigB : ∀ i j, |Sig i j| ≤ 7 / 2) (lam : ℝ) (hlam : 2 ≤ lam)
    (h : ∀ j, sampleCovariance x j j ≤ lam) :
    opNorm (thresholdMatrix lam (sampleCovariance x) - Sig) <
      2 * opNorm (adjacencyMatrix Sig) * lam := by
  rw [threshold_sample_eq_zero x lam h, zero_sub]
  have hn : opNorm (-Sig) = opNorm Sig := by simp [opNorm]
  rw [hn]
  have hp := opNorm_pos_of_ne_zero _ (adjacency_ne_zero Sig hSig)
  have hb := covariance_opNorm_bound Sig hSigB
  nlinarith

end HighDimStat.RandomMatrices.Proof
-- End DiagonalSafe

-- Begin MatrixEvents

open MeasureTheory
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma bad_event_entry_union {Ω : Type*} {n d : ℕ} [Nonempty (Fin d)]
    (x : Fin n → Ω → Fin d → ℝ) (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hSig : Sig ≠ 0) {lam : ℝ} (hlam : 0 < lam) :
    {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ⊆
      ⋃ ij : Fin d × Fin d, {ω | lam ≤ |sampleCovariance (fun i => x i ω) ij.1 ij.2 - Sig ij.1 ij.2|} := by
  classical
  intro ω hω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_contra! hn
  have hs := threshold_norm_lt (sampleCovariance (fun i => x i ω)) Sig hSig lam hlam
    (fun i j => hn (i, j))
  exact (not_lt_of_ge hω) hs

lemma bad_event_diagonal_union {Ω : Type*} {n d : ℕ}
    (x : Fin n → Ω → Fin d → ℝ) (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hSig : Sig ≠ 0) (hSigB : ∀ i j, |Sig i j| ≤ 7 / 2)
    {lam : ℝ} (hlam : 2 ≤ lam) :
    {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ⊆
      ⋃ j : Fin d, {ω | lam ≤ sampleCovariance (fun i => x i ω) j j} := by
  classical
  intro ω hω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_contra! hn
  have hs := diagonal_safe (fun i => x i ω) Sig hSig hSigB lam hlam (fun j => (hn j).le)
  exact (not_lt_of_ge hω) hs

lemma measure_bad_entry_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ} [Nonempty (Fin d)]
    (x : Fin n → Ω → Fin d → ℝ) (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hSig : Sig ≠ 0) {lam B : ℝ} (hlam : 0 < lam)
    (hB : ∀ j k, P.real {ω | lam ≤ |sampleCovariance (fun i => x i ω) j k - Sig j k|} ≤ B) :
    P.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤ d ^ 2 * B := by
  calc
    _ ≤ P.real (⋃ ij : Fin d × Fin d,
        {ω | lam ≤ |sampleCovariance (fun i => x i ω) ij.1 ij.2 - Sig ij.1 ij.2|}) :=
      measureReal_mono (bad_event_entry_union x Sig hSig hlam)
    _ ≤ ∑ ij : Fin d × Fin d, P.real
        {ω | lam ≤ |sampleCovariance (fun i => x i ω) ij.1 ij.2 - Sig ij.1 ij.2|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin d × Fin d, B := Finset.sum_le_sum fun ij _ => hB ij.1 ij.2
    _ = _ := by simp [pow_two]

lemma measure_bad_diagonal_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
    (x : Fin n → Ω → Fin d → ℝ) (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hSig : Sig ≠ 0) (hSigB : ∀ i j, |Sig i j| ≤ 7 / 2)
    {lam B : ℝ} (hlam : 2 ≤ lam)
    (hB : ∀ j, P.real {ω | lam ≤ sampleCovariance (fun i => x i ω) j j} ≤ B) :
    P.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤ d * B := by
  calc
    _ ≤ P.real (⋃ j : Fin d, {ω | lam ≤ sampleCovariance (fun i => x i ω) j j}) :=
      measureReal_mono (bad_event_diagonal_union x Sig hSig hSigB hlam)
    _ ≤ ∑ j : Fin d, P.real {ω | lam ≤ sampleCovariance (fun i => x i ω) j j} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin d, B := Finset.sum_le_sum fun j _ => hB j
    _ = _ := by simp

end HighDimStat.RandomMatrices.Proof
-- End MatrixEvents

-- Begin ScalarRegime

namespace HighDimStat.RandomMatrices.Proof

lemma product_rate_lower {a δ : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 2) (hd : 0 < δ) :
    a ^ 2 / 32 + min δ (δ ^ 2) / 16 ≤
      (a + δ) ^ 2 / (12 + 4 * (a + δ)) := by
  have hden : 0 < 12 + 4 * (a + δ) := by positivity
  apply (le_div_iff₀ hden).2
  by_cases h : δ ≤ 1
  · rw [min_eq_right (by nlinarith : δ ^ 2 ≤ δ)]
    have h1 : 0 ≤ a ^ 2 * (20 - 4 * a) := mul_nonneg (sq_nonneg a) (by linarith)
    have h2 : 0 ≤ 4 * a * δ * (16 - a - 2 * δ) :=
      mul_nonneg (by positivity) (by linarith)
    have h3 : 0 ≤ 8 * δ ^ 2 * (1 - δ) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  · have hδ : 1 ≤ δ := le_of_lt (lt_of_not_ge h)
    rw [min_eq_left (by nlinarith : δ ≤ δ ^ 2)]
    have h1 : 0 ≤ a ^ 2 * (20 - 4 * a) := mul_nonneg (sq_nonneg a) (by linarith)
    have h2 : 0 ≤ 4 * a * δ * (14 - a) := mul_nonneg (by positivity) (by linarith)
    have h3 : 0 ≤ 24 * δ * (δ - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith

lemma log_two_le : Real.log 2 ≤ (7 / 8 : ℝ) := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  have he : Real.log 2 = Real.log (4 / 3) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  linarith

lemma square_rate_lower {u δ : ℝ} (hu : 2 ≤ u) (hu8 : u ≤ 8) (hd : 0 < δ) :
    u ^ 2 / 64 + min δ (δ ^ 2) / 16 ≤
      (u + δ - 1 - Real.log (u + δ)) / 2 := by
  have hup : 0 < u := by linarith
  have hl := Real.log_le_sub_one_of_pos (show 0 < u / 2 by positivity)
  rw [Real.log_div (ne_of_gt hup) (by norm_num)] at hl
  have hh : (u - 2) * (14 - u) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  have hbase : u ^ 2 / 64 ≤ (u - 1 - Real.log u) / 2 := by
    have := log_two_le
    nlinarith
  have hr := Real.log_le_sub_one_of_pos (show 0 < (u + δ) / u by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hup)] at hr
  have hdiv : δ / u ≤ δ / 2 := div_le_div_of_nonneg_left (le_of_lt hd) (by norm_num) hu
  have he : (u + δ) / u - 1 = δ / u := by field_simp; ring
  rw [he] at hr
  have hm : min δ (δ ^ 2) ≤ δ := min_le_left _ _
  linarith

end HighDimStat.RandomMatrices.Proof
-- End ScalarRegime

-- Begin RegimeCancellation

open Real

namespace HighDimStat.RandomMatrices.Proof

lemma entry_exponential_cancel {n d r m : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hr : 2 * log d / n + m / 16 ≤ r) :
    d ^ 2 * (2 * exp (-n * r)) ≤ 2 * exp (-(n / 16) * m) := by
  have he : d ^ 2 = exp (2 * log d) := by
    rw [show 2 * log d = log d + log d by ring, exp_add, exp_log hd]
    ring
  have hh := mul_le_mul_of_nonneg_left hr hn.le
  have hc : n * (2 * log d / n + m / 16) = 2 * log d + n * m / 16 := by
    field_simp
  rw [hc] at hh
  rw [he]
  calc
    exp (2 * log d) * (2 * exp (-n * r)) = 2 * exp (2 * log d - n * r) := by
      rw [sub_eq_add_neg, exp_add]; simp only [neg_mul]; ring
    _ ≤ 2 * exp (-(n / 16) * m) := by gcongr; nlinarith

lemma diagonal_exponential_cancel {n d r m : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hr : log d / n + m / 16 ≤ r) :
    d * exp (-n * r) ≤ exp (-(n / 16) * m) := by
  have hh := mul_le_mul_of_nonneg_left hr hn.le
  have hc : n * (log d / n + m / 16) = log d + n * m / 16 := by
    field_simp
  rw [hc] at hh
  calc
    d * exp (-n * r) = exp (log d - n * r) := by rw [sub_eq_add_neg, exp_add, exp_log hd]; simp only [neg_mul]
    _ ≤ exp (-(n / 16) * m) := by apply exp_le_exp.mpr; nlinarith

end HighDimStat.RandomMatrices.Proof
-- End RegimeCancellation

-- Begin NormalizedBound

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma normalized_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
    (hn : 0 < n) (hd : 1 ≤ d)
    {x : Fin n → Ω → Fin d → ℝ} (hI : iIndepFun x P)
    (hm : ∀ i, AEMeasurable (x i) P)
    (hX : ∀ i j, HasSubgaussianMGF (fun ω => x i ω j) 1 P)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig ≠ 0)
    (hc : ∀ i j k, (∫ ω, x i ω j * x i ω k ∂P) = Sig j k)
    (hlog : log (d : ℝ) < n) {δ : ℝ} (hδ : 0 < δ) :
    let lam := 8 * sqrt (log (d : ℝ) / n) + δ
    P.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let q : ℝ := log (d : ℝ) / n
  let a : ℝ := 8 * sqrt q
  have hq0 : 0 ≤ q := div_nonneg (log_nonneg (by exact_mod_cast hd)) hn0.le
  have hq1 : q < 1 := (div_lt_one hn0).2 hlog
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 64 * q := by dsimp [a]; rw [mul_pow, sq_sqrt hq0]; norm_num
  have hlam : 0 < a + δ := by positivity
  change P.real {ω | 2 * opNorm (adjacencyMatrix Sig) * (a + δ) ≤
    opNorm (thresholdMatrix (a + δ) (sampleCovariance (fun i => x i ω)) - Sig)} ≤ _
  by_cases hq : q ≤ 1 / 16
  · have ha : a ≤ 2 := by nlinarith
    have hb := measure_bad_entry_bound x Sig hSig hlam
      (fun j k => normalized_entry_tail hn hI hm hX Sig hc j k hlam)
    have hr := product_rate_lower ha0 ha hδ
    have hr' : 2 * log (d : ℝ) / n + min δ (δ ^ 2) / 16 ≤
        (a + δ) ^ 2 / (12 + 4 * (a + δ)) := by
      have hqq : 2 * log (d : ℝ) / n = 2 * q := by dsimp [q]; ring_nf
      rw [hqq]
      nlinarith
    have he := entry_exponential_cancel hn0 hd0 hr'
    have heq : -((n : ℝ) * (a + δ) ^ 2 / (12 + 4 * (a + δ))) =
        -(n : ℝ) * ((a + δ) ^ 2 / (12 + 4 * (a + δ))) := by ring_nf
    rw [heq] at hb
    have hb' := hb.trans he
    exact hb'.trans (by nlinarith [exp_pos (-((n : ℝ) / 16) * min δ (δ ^ 2))])
  · have ha : 2 ≤ a := by nlinarith
    have ha8 : a ≤ 8 := by nlinarith
    have hSigB : ∀ j k, |Sig j k| ≤ 7 / 2 := by
      intro j k
      rw [← hc ⟨0, hn⟩ j k]
      exact normalized_product_abs_mean_le_seven_half (hX ⟨0, hn⟩ j) (hX ⟨0, hn⟩ k)
    have ht (j : Fin d) :
        P.real {ω | a + δ ≤ sampleCovariance (fun i => x i ω) j j} ≤
          exp (-((n : ℝ) * (a + δ - 1 - log (a + δ)) / 2)) := by
      have h := square_mean_tail hn
        (hI.comp (fun _ y => y j) (fun _ => measurable_pi_apply j))
        (fun i => hX i j) (by linarith : 1 < a + δ)
      simpa only [sampleCovariance, Matrix.of_apply, sq, Function.comp_apply] using h
    have hb := measure_bad_diagonal_bound x Sig hSig hSigB (by linarith : 2 ≤ a + δ) ht
    have hr := square_rate_lower ha ha8 hδ
    have hr' : log (d : ℝ) / n + min δ (δ ^ 2) / 16 ≤
        (a + δ - 1 - log (a + δ)) / 2 := by change q + _ ≤ _; nlinarith
    have he := diagonal_exponential_cancel hn0 hd0 hr'
    have hb' : P.real {ω | 2 * opNorm (adjacencyMatrix Sig) * (a + δ) ≤
        opNorm (thresholdMatrix (a + δ) (sampleCovariance (fun i => x i ω)) - Sig)} ≤
        exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by
      apply hb.trans
      convert he using 1
      congr 2
      ring_nf
    exact hb'.trans (by nlinarith [exp_pos (-((n : ℝ) / 16) * min δ (δ ^ 2))])

end HighDimStat.RandomMatrices.Proof
-- End NormalizedBound

-- Begin MatrixScaling

open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma sampleCovariance_smul {n d : ℕ} (a : ℝ) (x : Fin n → Fin d → ℝ) :
    sampleCovariance (fun i j => a * x i j) = a ^ 2 • sampleCovariance x := by
  ext j k
  simp only [sampleCovariance, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (1 / (n : ℝ)) * ∑ i, a * x i j * (a * x i k) =
        (1 / (n : ℝ)) * ∑ i, a ^ 2 * (x i j * x i k) := by congr 1; apply Finset.sum_congr rfl; intros; ring
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma thresholdMatrix_smul {d : ℕ} (a lam : ℝ) (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    thresholdMatrix (a * lam) (a • M) = a • thresholdMatrix lam M := by
  ext i j
  simp only [thresholdMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    abs_mul, abs_of_pos ha, mul_lt_mul_iff_right₀ ha]
  split_ifs <;> simp

lemma adjacencyMatrix_smul {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ) : adjacencyMatrix (a • M) = adjacencyMatrix M := by
  ext i j
  simp [adjacencyMatrix, ha]

lemma opNorm_smul {d : ℕ} (a : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    opNorm (a • M) = |a| * opNorm M := by
  rw [opNorm, map_smul, norm_smul, Real.norm_eq_abs]
  rfl

end HighDimStat.RandomMatrices.Proof
-- End MatrixScaling

-- Begin Normalization

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace HighDimStat.RandomMatrices.Proof

lemma normalized_subgaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {σ : ℝ} (hσ : σ ≠ 0)
    (h : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) P ∧
      (∫ ω, exp (t * X ω) ∂P) ≤ exp (σ ^ 2 * t ^ 2 / 2)) :
    HasSubgaussianMGF (fun ω => X ω / σ) 1 P := by
  constructor
  · intro t
    convert (h (t / σ)).1 using 1
    funext ω
    congr 1
    ring
  · intro t
    have hb := (h (t / σ)).2
    simp only [mgf, NNReal.coe_one, one_mul]
    convert hb using 1
    · congr 1
      funext ω
      congr 1
      ring
    · congr 1
      field_simp

lemma normalized_covariance_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} (X : Ω → Fin d → ℝ) (σ : ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ)
    (hc : ∀ j k, (∫ ω, X ω j * X ω k ∂P) = Sig j k) (j k : Fin d) :
    (∫ ω, (X ω j / σ) * (X ω k / σ) ∂P) = ((σ ^ 2)⁻¹ • Sig) j k := by
  have he : (fun ω => (X ω j / σ) * (X ω k / σ)) =
      (fun ω => (σ ^ 2)⁻¹ * (X ω j * X ω k)) := by funext ω; simp [div_eq_mul_inv]; ring
  rw [he, integral_const_mul, hc]
  rfl

lemma original_sample_of_normalized {n d : ℕ} (x : Fin n → Fin d → ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) :
    sampleCovariance x = σ ^ 2 • sampleCovariance (fun i j => x i j / σ) := by
  have h := sampleCovariance_smul σ (fun i j => x i j / σ)
  have he : (fun i j => σ * (x i j / σ)) = x := by
    funext i j
    field_simp
  rwa [he] at h

lemma bad_event_normalization {Ω : Type*} {n d : ℕ}
    (x : Fin n → Ω → Fin d → ℝ) (Sig : Matrix (Fin d) (Fin d) ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) (lam : ℝ) :
    {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} =
    {ω | 2 * opNorm (adjacencyMatrix ((σ ^ 2)⁻¹ • Sig)) * (lam / σ ^ 2) ≤
      opNorm (thresholdMatrix (lam / σ ^ 2)
        (sampleCovariance (fun i j => x i ω j / σ)) - (σ ^ 2)⁻¹ • Sig)} := by
  have hs : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
  have hsn : σ ^ 2 ≠ 0 := ne_of_gt hs
  have hSig : Sig = σ ^ 2 • ((σ ^ 2)⁻¹ • Sig) := by rw [smul_smul, mul_inv_cancel₀ hsn, one_smul]
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [adjacencyMatrix_smul _ (inv_ne_zero hsn)]
  have hsample := original_sample_of_normalized (fun i => x i ω) hσ
  have hthr : thresholdMatrix lam (sampleCovariance (fun i => x i ω)) =
      σ ^ 2 • thresholdMatrix (lam / σ ^ 2) (sampleCovariance (fun i j => x i ω j / σ)) := by
    rw [hsample, ← thresholdMatrix_smul _ _ hs]
    congr 1
    field_simp
  have herr : thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig =
      σ ^ 2 • (thresholdMatrix (lam / σ ^ 2)
        (sampleCovariance (fun i j => x i ω j / σ)) - (σ ^ 2)⁻¹ • Sig) := by
    rw [hthr, smul_sub]
    congr 1
  rw [herr, opNorm_smul, abs_of_pos hs]
  have he : 2 * opNorm (adjacencyMatrix Sig) * lam =
      σ ^ 2 * (2 * opNorm (adjacencyMatrix Sig) * (lam / σ ^ 2)) := by
    field_simp
  rw [he, mul_le_mul_iff_right₀ hs]

end HighDimStat.RandomMatrices.Proof
-- End Normalization

-- Begin RootAssembly

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

/-- **Theorem 6.23** (Thresholding-based covariance estimation), Wainwright, *High-Dimensional
Statistics* (2019), p. 181, Eq. (6.53). Let `{xᵢ}` be an i.i.d. sequence of zero-mean random
vectors in `ℝ^d` (`d ≥ 1`) with a **nonzero** covariance matrix `Σ`, and suppose each
component `x_{ij}` is sub-Gaussian with parameter at most `σ`. If `n > log d`, then for any
`δ > 0`, the thresholded sample covariance matrix `Tλn(Σ̂)` with `λn/σ² = 8√(log d/n) + δ`
satisfies `P[|||Tλn(Σ̂)-Σ|||₂ ≥ 2|||A|||₂λn] ≤ 8e^{-(n/16)min{δ,δ²}}`, where `A` is the
adjacency matrix of the sparsity graph of `Σ`.

Corrections: (i) the retired version allowed `d = 0`, where `Real.log 0 = 0` makes `n > log d`
vacuous and both operator norms on `ℝ⁰` vanish, so the event `0 ≤ 0` is certain; (ii) to the
printed source: the same collapse happens for every `d ≥ 1` when `Σ = 0` (data identically
zero a.s., which is sub-Gaussian with any `σ > 0`): then `A = 0`, `Tλn(Σ̂) = 0`, the event
`|||0 − 0|||₂ ≥ 0` is certain, and the printed inequality fails for `n` large. The book's proof
bounds `P[|||Σ̂ − Σ|||_max ≥ λn/2]` and then uses `|Tλn(Σ̂) − Σ| ≤ (3/2)λn A` entrywise on the
complement, which yields the printed non-strict event exactly when `A ≠ 0`, i.e. `Σ ≠ 0`; the
hypothesis `hSig : Sig ≠ 0` (which also forces `d ≥ 1`) therefore excludes precisely the
degenerate instance. -/
theorem thresholded_covariance_estimation_bound_v2 {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n) (hd : 1 ≤ d) (hSig : Sig ≠ 0)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ) :
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by
  have _hMean := hMean0
  have hσ : σ ≠ 0 := by
    intro hz
    rw [hz] at hlam
    simp only [zero_pow (by decide : 2 ≠ 0), div_zero] at hlam
    have hs := Real.sqrt_nonneg (Real.log (d : ℝ) / n)
    linarith
  let z : Fin n → Ω → Fin d → ℝ := fun i ω j => x i ω j / σ
  let S : Matrix (Fin d) (Fin d) ℝ := (σ ^ 2)⁻¹ • Sig
  have hS : S ≠ 0 := by
    intro hz
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => σ ^ 2 • M) hz
    simp [S, smul_smul, pow_ne_zero 2 hσ] at hh
    exact hSig hh
  have hzI : iIndepFun z Prob :=
    hIndep.comp (fun _ y j => y j / σ) (fun _ => by fun_prop)
  have hzm : ∀ i, AEMeasurable (z i) Prob := by
    intro i
    exact (show Measurable (fun y : Fin d → ℝ => fun j => y j / σ) by fun_prop).comp_aemeasurable
      (hIdent i).aemeasurable_fst
  have hzX : ∀ i j, HasSubgaussianMGF (fun ω => z i ω j) 1 Prob := by
    intro i j
    have hb := Proof.normalized_subgaussian hσ (hSubG j)
    have hi := (hIdent i).comp (show Measurable (fun y : Fin d → ℝ => y j / σ) by fun_prop)
    exact hb.congr_identDistrib hi.symm
  have hzc : ∀ i j k, (∫ ω, z i ω j * z i ω k ∂Prob) = S j k := by
    intro i j k
    have hi := (hIdent i).comp
      (show Measurable (fun y : Fin d → ℝ => (y j / σ) * (y k / σ)) by fun_prop)
    exact hi.integral_eq.trans (Proof.normalized_covariance_integral (x ⟨0, hn0⟩) σ Sig hCov j k)
  have h := Proof.normalized_covariance_bound hn0 hd hzI hzm hzX S hS hzc hnd hδ
  rw [Proof.bad_event_normalization x Sig hσ lam, hlam]
  exact h


end HighDimStat.RandomMatrices
-- End RootAssembly

-- Begin Solution

open MeasureTheory ProbabilityTheory HighDimStat.RandomMatrices

theorem solution {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n) (hd : 1 ≤ d) (hSig : Sig ≠ 0)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ) :
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by
  exact thresholded_covariance_estimation_bound_v2 x Sig σ hn0 hd hSig hIndep hIdent hMean0 hCov hSubG hnd δ hδ lam hlam
-- End Solution
