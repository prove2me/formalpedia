-- Prove2me | solution 1 for NymanBeurling.moebius_polynomial_critical_strip_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-21T11:41:36.019351+00:00
-- url     : https://prove2.me/submissions/f947e235-8703-4df2-b33b-6dbbd66ebc88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_moebius_polynomial_fixed_line_bound

private theorem norm_weighted_range_le
    (a : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hw0 : w 0 ≤ 1)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_antitone : ∀ i, w (i + 1) ≤ w i)
    (hS : ∀ k, ‖∑ i ∈ Finset.range k, a i‖ ≤ B)
    (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w i • a i‖ ≤ B := by
  cases n with
  | zero => simpa using hB
  | succ n =>
      rw [Finset.sum_range_by_parts]
      simp only [Nat.add_sub_cancel_right]
      have hterm : ‖w n • ∑ i ∈ Finset.range (n + 1), a i‖ ≤ w n * B := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg n)]
        exact mul_le_mul_of_nonneg_left (hS (n + 1)) (hw_nonneg n)
      have hsum :
          ‖∑ i ∈ Finset.range n, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ ≤
            ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := by
        calc
          _ ≤ ∑ i ∈ Finset.range n, ‖(w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hw_antitone i))]
            have hwi : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hw_antitone i)
            convert mul_le_mul_of_nonneg_left (hS (i + 1)) hwi using 1 <;> ring
      calc
        ‖w n • ∑ i ∈ Finset.range (n + 1), a i -
              ∑ i ∈ Finset.range n, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ ≤
            ‖w n • ∑ i ∈ Finset.range (n + 1), a i‖ +
              ‖∑ i ∈ Finset.range n, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ := by
          simpa using norm_sub_le
            (w n • ∑ i ∈ Finset.range (n + 1), a i)
            (∑ i ∈ Finset.range n, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j)
        _ ≤ w n * B + ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B := add_le_add hterm hsum
        _ = w 0 * B := by
          rw [← Finset.sum_mul, Finset.sum_range_sub']
          ring
        _ ≤ B := by nlinarith [mul_nonneg hB (sub_nonneg.mpr hw0)]

private theorem moebius_term_shift (d : ℕ) (hd : 0 < d) (s₀ : ℂ) (δ : ℝ) :
    ((d : ℝ) ^ (-δ)) • ((ArithmeticFunction.moebius d : ℂ) / (d : ℂ) ^ s₀) =
      (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) ^ (s₀ + (δ : ℂ)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hdr : (0 : ℝ) ≤ d := by positivity
  rw [Complex.real_smul, Complex.ofReal_cpow hdr, Complex.ofReal_neg, Complex.cpow_neg,
    Complex.cpow_add _ _ hd0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  push_cast
  ring

private theorem range_sum_eq_Ioc (f : ℕ → ℂ) (N : ℕ) (h0 : f 0 = 0) :
    ∑ d ∈ Finset.range (N + 1), f d = ∑ d ∈ Finset.Ioc 0 N, f d := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_insert (by simp), h0, zero_add]

theorem solution : NymanBeurling.MoebiusPolynomialBoundaryBound := by
  unfold NymanBeurling.MoebiusPolynomialBoundaryBound
  intro η hη β hβ
  obtain ⟨C, hC, hline⟩ :=
    NymanBeurling.moebius_polynomial_fixed_line_bound η hη β hβ
  refine ⟨C, hC, ?_⟩
  intro N σ t hσ
  let s₀ : ℂ := (((1 / 2 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  let δ : ℝ := σ - (1 / 2 + η)
  let a : ℕ → ℂ := fun d =>
    if d = 0 then 0 else (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) ^ s₀
  let w : ℕ → ℝ := fun d => if d = 0 then 1 else (d : ℝ) ^ (-δ)
  let B : ℝ := C * (1 + |t|) ^ β
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hw0 : w 0 ≤ 1 := by simp [w]
  have hwnonneg : ∀ d, 0 ≤ w d := by
    intro d
    by_cases hd : d = 0
    · simp [w, hd]
    · simp only [w, if_neg hd]
      exact Real.rpow_nonneg (by positivity) _
  have hwantitone : ∀ d, w (d + 1) ≤ w d := by
    intro d
    cases d with
    | zero => simp [w]
    | succ d =>
        have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
        have hle : ((d + 1 : ℕ) : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ (d + 1))
        have hδneg : -δ ≤ 0 := by linarith
        simpa [w, Nat.succ_eq_add_one, Nat.add_assoc] using
          (Real.rpow_le_rpow_of_nonpos hpos hle hδneg)
  have hpartial : ∀ k, ‖∑ d ∈ Finset.range k, a d‖ ≤ B := by
    intro k
    cases k with
    | zero => simpa using hB
    | succ k =>
        rw [range_sum_eq_Ioc a k (by simp [a])]
        have heq : (∑ d ∈ Finset.Ioc 0 k, a d) =
            NymanBeurling.moebiusDirichletPolynomial k s₀ := by
          unfold NymanBeurling.moebiusDirichletPolynomial
          apply Finset.sum_congr rfl
          intro d hd
          have hd0 : d ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hd).1
          simp [a, hd0]
        rw [heq]
        exact hline k t
  have hs : s₀ + (δ : ℂ) = (σ : ℂ) + (t : ℂ) * Complex.I := by
    dsimp [s₀, δ]
    push_cast
    ring
  have hweighted :
      (∑ d ∈ Finset.range (N + 1), w d • a d) =
        NymanBeurling.moebiusDirichletPolynomial N ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [range_sum_eq_Ioc (fun d => w d • a d) N (by simp [a, w])]
    unfold NymanBeurling.moebiusDirichletPolynomial
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
    simp only [a, w, if_neg hd0]
    rw [moebius_term_shift d hdpos s₀ δ, hs]
  have h := norm_weighted_range_le a w B hB hw0 hwnonneg hwantitone hpartial (N + 1)
  rw [hweighted] at h
  exact h
