-- Prove2me | solution 1 for NamikiStretch.Lossy.eq_20_coherent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T04:24:35.159984+00:00
-- url     : https://prove2.me/submissions/aefd17db-656f-4566-97e4-23d4f9aa9bbf

import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory Finset Filter
open scoped Topology
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

lemma normSq_sub_star (α β : ℂ) :
    Complex.normSq (α - star β) =
      Complex.normSq α + Complex.normSq β - 2 * (α * β).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.mul_re]
  ring

lemma exp_ident (α β : ℂ) :
    Complex.exp (α * β) * star (Complex.exp (α * β)) = ((Real.exp (2 * (α * β).re) : ℝ) : ℂ) := by
  have h_conj : (starRingEnd ℂ) (Complex.exp (α * β)) = Complex.exp ((starRingEnd ℂ) (α * β)) :=
    (Complex.exp_conj (x := α * β)).symm
  change Complex.exp (α * β) * (starRingEnd ℂ) (Complex.exp (α * β)) = _
  rw [h_conj, ← Complex.exp_add]
  have h_add : α * β + (starRingEnd ℂ) (α * β) = (((2 * (α * β).re : ℝ) : ℂ)) :=
    Complex.add_conj (α * β)
  rw [h_add]
  exact (Complex.ofReal_exp (2 * (α * β).re)).symm

lemma exp_combined (α β : ℂ) :
    (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    Complex.exp (α * β) * star (Complex.exp (α * β)) =
      ((Real.exp (-Complex.normSq (α - star β)) : ℝ) : ℂ) := by
  have h1 : (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) =
    ((Real.exp (-(Complex.normSq α + Complex.normSq β)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  have h2 : (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    Complex.exp (α * β) * star (Complex.exp (α * β)) =
    ((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
    (Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ)) *
    (Complex.exp (α * β) * star (Complex.exp (α * β))) := by ring
  rw [h2, h1, exp_ident]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  rw [normSq_sub_star]
  ring

lemma sqrt_fact_sq (b : ℕ) :
    ((Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ) ^ 2 = (b.factorial : ℂ) := by
  have hb : 0 ≤ (b.factorial : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hb]
  push_cast; rfl

lemma sqrt_div_fact_eq (b : ℕ) :
    (Real.sqrt (b.factorial : ℝ) : ℂ) / (b.factorial : ℂ) =
      1 / (Real.sqrt (b.factorial : ℝ) : ℂ) := by
  have hb : 0 < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
  have hb_ne : (Real.sqrt (b.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hb).ne'
  have hbf_ne : (b.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero b
  have hsq := sqrt_fact_sq b
  field_simp
  linear_combination hsq

lemma sqrt_fact_mul_div_cancel (n b : ℕ) :
    ((Real.sqrt ((n.factorial : ℝ) * (b.factorial : ℝ)) : ℝ) : ℂ) / (Real.sqrt (n.factorial : ℝ) : ℂ) =
      (Real.sqrt (b.factorial : ℝ) : ℂ) := by
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn_ne : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  rw [Real.sqrt_mul (Nat.cast_nonneg n.factorial)]
  push_cast
  rw [mul_div_cancel_left₀ _ hn_ne]

lemma exp_neg_add_div_two (α β : ℂ) :
    (Real.exp (-Complex.normSq β / 2) : ℂ) * (Real.exp (-Complex.normSq α / 2) : ℂ) =
      ((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  ring

lemma sum_range_min (n b : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ range (min n b + 1), f j) =
      ∑ j ∈ range (b + 1), if j ≤ n then f j else 0 := by
  rw [sum_ite]
  have h_filter : (filter (fun j => j ≤ n) (range (b + 1))) = range (min n b + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [h_filter, sum_const_zero, add_zero]

lemma term_factor (α β : ℂ) (b n j : ℕ) (hj : j ≤ n) :
    β ^ (n - j) * (-star β) ^ (b - j) /
        ((j.factorial : ℂ) * ((n - j).factorial : ℂ) * ((b - j).factorial : ℂ)) * α ^ n =
      (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) *
        ((α * β) ^ (n - j) / ((n - j).factorial : ℂ)) := by
  have h_split : α ^ n = α ^ j * α ^ (n - j) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hj]
  have h_prod : (α * β) ^ (n - j) = α ^ (n - j) * β ^ (n - j) := mul_pow α β (n - j)
  rw [h_split, h_prod]
  ring

lemma disp_mul_coh_eq (α β : ℂ) (b n : ℕ) :
    displacementMatrix β n b * coherentCoefficient α n =
      (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) * Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ)) *
        ∑ j ∈ range (b + 1),
          if j ≤ n then
            (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) *
              ((α * β) ^ (n - j) / ((n - j).factorial : ℂ))
          else 0 := by
  dsimp only [displacementMatrix, coherentCoefficient]
  rw [sum_range_min]
  have h_pref :
    (((Real.exp (-Complex.normSq β / 2) * Real.sqrt ((n.factorial : ℝ) * (b.factorial : ℝ)) : ℝ) : ℂ)) *
      (∑ j ∈ range (b + 1), if j ≤ n then
        β ^ (n - j) * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((n - j).factorial : ℂ) * ((b - j).factorial : ℂ))
      else 0) *
      (((Real.exp (-Complex.normSq α / 2) : ℂ) * α ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ))) =
    (((Real.exp (-Complex.normSq β / 2) : ℂ) * (Real.exp (-Complex.normSq α / 2) : ℂ)) *
     (((Real.sqrt ((n.factorial : ℝ) * (b.factorial : ℝ)) : ℝ) : ℂ) / (Real.sqrt (n.factorial : ℝ) : ℂ))) *
      ((∑ j ∈ range (b + 1), if j ≤ n then
        β ^ (n - j) * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((n - j).factorial : ℂ) * ((b - j).factorial : ℂ))
      else 0) * α ^ n) := by
    rw [Complex.ofReal_mul]
    ring
  rw [h_pref]
  rw [exp_neg_add_div_two, sqrt_fact_mul_div_cancel]
  rw [← Complex.ofReal_mul, sum_mul]
  congr 1
  apply sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [term_factor α β b n j hj]
  · rw [zero_mul]

noncomputable def Sb (α β : ℂ) (k : ℕ) : ℂ :=
  (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) / Real.sqrt (k.factorial : ℝ) : ℝ) : ℂ) *
    Complex.exp (α * β) * (α - star β) ^ k)

lemma sum_C_eq (b : ℕ) (α β : ℂ) :
    (∑ j ∈ range (b + 1), α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) =
      (α - star β) ^ b / (b.factorial : ℂ) := by
  have h_bin : (α - star β) ^ b = ∑ j ∈ range (b + 1), (b.choose j : ℂ) * α ^ j * (-star β) ^ (b - j) := by
    rw [sub_eq_add_neg, add_pow]
    apply sum_congr rfl
    intro j _
    ring
  rw [h_bin, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hj_le : j ≤ b := Nat.lt_succ_iff.mp hj
  have h_ch : (b.choose j : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj_le).ne'
  have h_fact : (b.factorial : ℂ) = (b.choose j : ℂ) * ((j.factorial : ℂ) * ((b - j).factorial : ℂ)) := by
    rw [← mul_assoc]
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj_le).symm
  rw [h_fact]
  have h_mul : (b.choose j : ℂ) * α ^ j * (-star β) ^ (b - j) =
      (b.choose j : ℂ) * (α ^ j * (-star β) ^ (b - j)) := by ring
  rw [h_mul, mul_div_mul_left _ _ h_ch]

lemma cexp_hasSum (z : ℂ) : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

lemma rexp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma hasSum_ite_le (k : ℕ) (h : ℕ → ℂ) {g : ℂ} (H : HasSum h g) :
    HasSum (fun n : ℕ => if k ≤ n then h (n - k) else 0) g := by
  have h_add : HasSum (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℂ))) g := by
    have h_eq : (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℂ))) = h := by
      funext n
      have hk : k ≤ n + k := Nat.le_add_left k n
      have hsub : n + k - k = n := Nat.add_sub_cancel n k
      simp only [hk, hsub, ↓reduceIte]
    rw [h_eq]
    exact H
  have h_shift := (hasSum_nat_add_iff (f := fun n => if k ≤ n then h (n - k) else 0) k).mp h_add
  have h_sum_zero : (∑ i ∈ range k, (if k ≤ i then h (i - k) else (0 : ℂ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [if_neg (by omega)]
  rw [h_sum_zero, add_zero] at h_shift
  exact h_shift

lemma hasSum_ite_le_real (k : ℕ) (h : ℕ → ℝ) {g : ℝ} (H : HasSum h g) :
    HasSum (fun n : ℕ => if k ≤ n then h (n - k) else 0) g := by
  have h_add : HasSum (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℝ))) g := by
    have h_eq : (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℝ))) = h := by
      funext n
      have hk : k ≤ n + k := Nat.le_add_left k n
      have hsub : n + k - k = n := Nat.add_sub_cancel n k
      simp only [hk, hsub, ↓reduceIte]
    rw [h_eq]
    exact H
  have h_shift := (hasSum_nat_add_iff (f := fun n => if k ≤ n then h (n - k) else 0) k).mp h_add
  have h_sum_zero : (∑ i ∈ range k, (if k ≤ i then h (i - k) else (0 : ℝ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [if_neg (by omega)]
  rw [h_sum_zero, add_zero] at h_shift
  exact h_shift

lemma hasSum_disp_coh (α β : ℂ) (b : ℕ) :
    HasSum (fun n => displacementMatrix β n b * coherentCoefficient α n) (Sb α β b) := by
  have h_fun_eq : (fun n => displacementMatrix β n b * coherentCoefficient α n) =
      fun n => (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) * Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ)) *
        ∑ j ∈ range (b + 1),
          if j ≤ n then
            (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) *
              ((α * β) ^ (n - j) / ((n - j).factorial : ℂ))
          else 0 := by
    funext n
    exact disp_mul_coh_eq α β b n
  rw [h_fun_eq]
  have h_term : ∀ j ∈ range (b + 1),
    HasSum (fun n => if j ≤ n then
      (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) *
        ((α * β) ^ (n - j) / ((n - j).factorial : ℂ))
    else 0)
    ((α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) * Complex.exp (α * β)) := by
    intro j _
    let C_j := (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ)))
    have H : HasSum (fun m => C_j * ((α * β) ^ m / (m.factorial : ℂ))) (C_j * Complex.exp (α * β)) :=
      (cexp_hasSum (α * β)).mul_left C_j
    exact hasSum_ite_le j (fun m => C_j * ((α * β) ^ m / (m.factorial : ℂ))) H
  have h_sum := hasSum_sum h_term
  have h_all := h_sum.mul_left (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) * Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ))
  rw [← sum_mul, sum_C_eq] at h_all
  suffices eq : (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) * Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ)) *
      ((α - star β) ^ b / (b.factorial : ℂ) * Complex.exp (α * β)) = Sb α β b by
    rw [eq] at h_all
    exact h_all
  dsimp only [Sb]
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  have h_div := sqrt_div_fact_eq b
  have h_rw : (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) * ↑√↑b.factorial) *
      ((α - star β) ^ b / ↑b.factorial * Complex.exp (α * β))) =
    ((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) : ℂ) *
      (↑√↑b.factorial / ↑b.factorial)) * Complex.exp (α * β) * (α - star β) ^ b := by ring
  rw [h_rw, h_div]
  ring

lemma norm_term_le (C_j : ℂ) (z : ℂ) (j n : ℕ) :
    ‖(if j ≤ n then C_j * (z ^ (n - j) / ((n - j).factorial : ℂ)) else 0)‖ ≤
      if j ≤ n then ‖C_j‖ * (‖z‖ ^ (n - j) / ((n - j).factorial : ℝ)) else 0 := by
  split_ifs with hj
  · rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  · simp

lemma summable_disp_coh (α β : ℂ) (b : ℕ) :
    Summable (fun n => ‖displacementMatrix β n b * coherentCoefficient α n‖) := by
  let Prefactor : ℂ := (((Real.exp (-(Complex.normSq α + Complex.normSq β) / 2) * Real.sqrt (b.factorial : ℝ) : ℝ) : ℂ))
  let C_term := fun j : ℕ => (α ^ j * (-star β) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ)))
  have h_summable_j : ∀ j ∈ range (b + 1),
    Summable (fun n => if j ≤ n then ‖C_term j‖ * (‖α * β‖ ^ (n - j) / ((n - j).factorial : ℝ)) else 0) := by
    intro j _
    have H := (rexp_hasSum ‖α * β‖).mul_left ‖C_term j‖
    exact (hasSum_ite_le_real j _ H).summable
  have h_sum_summable : Summable (fun n => ∑ j ∈ range (b + 1),
    if j ≤ n then ‖C_term j‖ * (‖α * β‖ ^ (n - j) / ((n - j).factorial : ℝ)) else 0) :=
    summable_sum (fun j hj => h_summable_j j hj)
  have h_bound_summable : Summable (fun n => ‖Prefactor‖ * ∑ j ∈ range (b + 1),
    if j ≤ n then ‖C_term j‖ * (‖α * β‖ ^ (n - j) / ((n - j).factorial : ℝ)) else 0) :=
    h_sum_summable.mul_left ‖Prefactor‖
  have h_le : ∀ n : ℕ, ‖displacementMatrix β n b * coherentCoefficient α n‖ ≤
      ‖Prefactor‖ * ∑ j ∈ range (b + 1),
        if j ≤ n then ‖C_term j‖ * (‖α * β‖ ^ (n - j) / ((n - j).factorial : ℝ)) else 0 := by
    intro n
    rw [disp_mul_coh_eq α β b n]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h_tri := norm_sum_le (range (b + 1)) (fun j => if j ≤ n then
      C_term j * ((α * β) ^ (n - j) / ((n - j).factorial : ℂ)) else 0)
    apply h_tri.trans
    apply sum_le_sum
    intro j _
    exact norm_term_le (C_term j) (α * β) j n
  exact .of_nonneg_of_le (fun _ => norm_nonneg _) h_le h_bound_summable

lemma Sb_mul_star (α β : ℂ) (b b' : ℕ) :
    Sb α β b * star (Sb α β b') =
      ((Real.exp (-Complex.normSq (α - star β)) : ℝ) : ℂ) *
      ((α - star β) ^ b * star ((α - star β) ^ b')) /
      ((Real.sqrt (b.factorial : ℝ) : ℂ) * (Real.sqrt (b'.factorial : ℝ) : ℂ)) := by
  have hb_pos : (Real.sqrt (b.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos b)).ne'
  have hb'_pos : (Real.sqrt (b'.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos b')).ne'
  dsimp only [Sb]
  simp only [Complex.ofReal_div, star_mul', star_div₀, Complex.conj_ofReal, Complex.star_def, map_pow, neg_div]
  have h_exp := exp_combined α β
  rw [Complex.star_def] at h_exp
  field_simp
  simp only [neg_div] at h_exp
  rw [← sq] at h_exp
  linear_combination
    ((α - (starRingEnd ℂ) β) ^ b * (starRingEnd ℂ) (α - (starRingEnd ℂ) β) ^ b') * h_exp

lemma target_eq (ξ : ℝ) (α β : ℂ) (b b' : ℕ) :
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    let C : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) * ξ ^ (b + b') : ℝ) : ℂ)
    w * coherentDensity ((ξ : ℂ) * (α - star β)) b b' = C * (Sb α β b * star (Sb α β b')) := by
  intro w C
  have hw : w = (((1 - ξ ^ 2) / (2 * Real.pi) * ξ ^ 0 : ℝ) : ℂ) *
      ((Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ) := by
    dsimp [w]; rw [← Complex.ofReal_mul]; congr 1; ring
  have hw_orig : w = (((1 - ξ ^ 2) / (2 * Real.pi) : ℝ) : ℂ) *
      ((Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ) := by
    dsimp [w]; rw [← Complex.ofReal_mul]
  have hC : C = (((1 - ξ ^ 2) / (2 * Real.pi) : ℝ) : ℂ) *
      (((ξ ^ (b + b') : ℝ) : ℂ)) := by
    dsimp [C]; rw [← Complex.ofReal_mul]
  rw [hw_orig, hC, mul_assoc, mul_assoc]
  congr 1
  rw [Sb_mul_star]
  have h_normSq : Complex.normSq ((ξ : ℂ) * (α - star β)) =
      ξ ^ 2 * Complex.normSq (α - star β) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, sq]
  have hb_pos : (Real.sqrt (b.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos b)).ne'
  have hb'_pos : (Real.sqrt (b'.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos b')).ne'
  have h_exp_mul : Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - (starRingEnd ℂ) β)) *
    (Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2)) *
     Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2))) =
    Real.exp (-Complex.normSq (α - (starRingEnd ℂ) β)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h_exp : (Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - (starRingEnd ℂ) β)) : ℂ) *
    (Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2)) : ℂ) ^ 2 =
    (Real.exp (-Complex.normSq (α - (starRingEnd ℂ) β)) : ℂ) := by
    have h_sq : (Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2)) : ℂ) ^ 2 =
      (Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2)) : ℂ) *
      (Real.exp (-(ξ ^ 2 * Complex.normSq (α - (starRingEnd ℂ) β) / 2)) : ℂ) := sq _
    rw [h_sq, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact congr_arg Complex.ofReal h_exp_mul
  dsimp only [coherentDensity, coherentCoefficient]
  simp only [Complex.star_def] at h_normSq ⊢
  rw [h_normSq]
  simp only [map_mul, map_div₀, map_pow, Complex.conj_ofReal, mul_pow, neg_div, neg_mul]
  field_simp
  have h_pow : ((ξ ^ (b + b') : ℝ) : ℂ) = (ξ : ℂ) ^ b * (ξ : ℂ) ^ b' := by
    push_cast; exact pow_add (ξ : ℂ) b b'
  simp only [neg_mul] at h_exp
  linear_combination
    ((ξ : ℂ) ^ b * (α - (starRingEnd ℂ) β) ^ b * (ξ : ℂ) ^ b' * (starRingEnd ℂ) (α - (starRingEnd ℂ) β) ^ b') * h_exp -
    ((α - (starRingEnd ℂ) β) ^ b * (starRingEnd ℂ) (α - (starRingEnd ℂ) β) ^ b' * (Real.exp (-Complex.normSq (α - (starRingEnd ℂ) β)) : ℂ)) * h_pow

lemma bellTerm_zero (ξ : ℝ) (α β : ℂ) (b b' : ℕ) (x : ℕ × ℕ × ℕ × ℕ)
    (h_ne : x.2.2.1 ≠ b ∨ x.2.2.2 ≠ b') :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b') x = 0 := by
  intro ρα
  dsimp only [bellTerm, tmsvKernel]
  have h_tmsv : (if x.2.2.1 = b ∧ x.2.2.2 = b' then (((1 - ξ ^ 2) * ξ ^ (x.2.2.1 + x.2.2.2) : ℝ) : ℂ) else 0) = 0 := by
    split_ifs with h
    · cases h_ne with
      | inl h1 => exact (h1 h.1).elim
      | inr h2 => exact (h2 h.2).elim
    · rfl
  rw [h_tmsv]
  ring

lemma bellTerm_eq (ξ : ℝ) (α β : ℂ) (b b' : ℕ) (n n' : ℕ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let C : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) * ξ ^ (b + b') : ℝ) : ℂ)
    bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b') (n, n', b, b') =
      C * (displacementMatrix β n b * coherentCoefficient α n *
        star (displacementMatrix β n' b' * coherentCoefficient α n')) := by
  intro ρα C
  dsimp only [bellTerm, tmsvKernel, ρα, coherentDensity, C]
  simp only [and_self, ↓reduceIte]
  simp only [star_mul']
  have h_rw : (((1 - ξ ^ 2) / (2 * Real.pi) * ξ ^ (b + b') : ℝ) : ℂ) =
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (((1 - ξ ^ 2) * ξ ^ (b + b') : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    ring
  rw [h_rw]
  ring

lemma hasSum_2d_mul (f g : ℕ → ℂ) (A B : ℂ)
    (hf : HasSum f A) (hg : HasSum g B)
    (sf : Summable fun n => ‖f n‖) (sg : Summable fun n => ‖g n‖) :
    HasSum (fun p : ℕ × ℕ => f p.1 * g p.2) (A * B) := by
  have s_prod : Summable (fun p : ℕ × ℕ => f p.1 * g p.2) :=
    summable_mul_of_summable_norm (f := f) (g := g) sf sg
  exact HasSum.mul hf hg s_prod

theorem eq_20_coherent (ξ : ℝ) (_hξ0 : 0 < ξ) (_hξ1 : ξ < 1) (α β : ℂ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    ∀ b b' : ℕ, HasSum (bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b'))
      (w * coherentDensity ((ξ : ℂ) * (α - star β)) b b') := by
  intro ρα w b b'
  let C : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) * ξ ^ (b + b') : ℝ) : ℂ)
  have h1 := hasSum_disp_coh α β b
  have h2 := (hasSum_disp_coh α β b').star
  have s1 := summable_disp_coh α β b
  have s2 : Summable (fun n' => ‖star (displacementMatrix β n' b' * coherentCoefficient α n')‖) := by
    simp only [norm_star]
    exact summable_disp_coh α β b'
  have h_2d : HasSum (fun p : ℕ × ℕ =>
      displacementMatrix β p.1 b * coherentCoefficient α p.1 *
        star (displacementMatrix β p.2 b' * coherentCoefficient α p.2))
      (Sb α β b * star (Sb α β b')) :=
    hasSum_2d_mul
      (fun n => displacementMatrix β n b * coherentCoefficient α n)
      (fun n' => star (displacementMatrix β n' b' * coherentCoefficient α n'))
      (Sb α β b) (star (Sb α β b')) h1 h2 s1 s2
  have h_2d_C := h_2d.mul_left C
  have h_target := target_eq ξ α β b b'
  dsimp only [w, C] at h_target ⊢
  rw [h_target]
  let g : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun p => (p.1, p.2, b, b')
  have hg : Function.Injective g := by
    intro ⟨n1, n1'⟩ ⟨n2, n2'⟩ h
    cases h
    rfl
  have h_range : ∀ x ∉ Set.range g, bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b') x = 0 := by
    intro x hx
    apply bellTerm_zero
    by_contra! h
    apply hx
    exact ⟨(x.1, x.2.1), by dsimp [g]; rw [← h.1, ← h.2]⟩
  rw [← hg.hasSum_iff h_range]
  have h_comp : (bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b') ∘ g) =
      fun p : ℕ × ℕ => C * (displacementMatrix β p.1 b * coherentCoefficient α p.1 *
        star (displacementMatrix β p.2 b' * coherentCoefficient α p.2)) := by
    funext ⟨n, n'⟩
    exact bellTerm_eq ξ α β b b' n n'
  rw [h_comp]
  exact h_2d_C

end NamikiStretch.Lossy

open NamikiStretch.Lossy QAlgorithms.Papers.Independent.Frontier30.P21

theorem solution (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (α β : ℂ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    ∀ b b' : ℕ, HasSum (bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b'))
      (w * coherentDensity ((ξ : ℂ) * (α - star β)) b b') :=
  eq_20_coherent ξ hξ0 hξ1 α β
