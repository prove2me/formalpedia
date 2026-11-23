-- Prove2me | solution 1 for GlobalTheory.landau_exp_summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:40.205223+00:00
-- url     : https://prove2.me/submissions/fb020349-4e27-46b6-8a78-ace416984586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Theorems.Thm_GlobalTheory_hasSum_tuple_prod_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (ι : Type) (a l : ι → ℝ) (F : ℂ → ℂ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ l i) → Differentiable ℂ F →
    (∀ s : ℂ, 1 < s.re → ∃ g : ℂ, HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s)) g ∧
      F s = Complex.exp g) → Summable a := by
  intro ι a l F ha hl hF hD
  let b : (Σ n : ℕ, Fin n → ι) → ℝ := fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)
  let L : (Σ n : ℕ, Fin n → ι) → ℝ := fun p => ∑ k, l (p.2 k)
  have hb : ∀ p, 0 ≤ b p := fun p =>
    div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _)
  have hL : ∀ p, 0 ≤ L p := fun p => Finset.sum_nonneg fun k _ => hl _

  have hA : ∀ s : ℂ, 1 < s.re →
      HasSum (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s)) (F s) := by
    intro s hs
    obtain ⟨g, hg, hFg⟩ := hD s hs
    rw [hFg]
    have H := _root_.GlobalTheory.hasSum_tuple_prod_exp _ g hg
    have heq : (fun p : (Σ n : ℕ, Fin n → ι) =>
        (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * s)) / (p.1.factorial : ℂ)) =
        fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s) := by
      funext p
      have hsum : ∑ k, (-(l (p.2 k) : ℂ) * s) = -(L p : ℂ) * s := by
        simp only [L, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hsum]
      simp only [b, Complex.ofReal_div, Complex.ofReal_prod, Complex.ofReal_natCast]
      ring
    rw [heq] at H
    exact H
  have hB : ∀ σ : ℝ, 1 < σ → Summable fun p => b p * Real.exp (-(L p * σ)) := by
    intro σ hσ
    have H := (hA σ (by simpa using hσ)).summable
    have heq : (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * (σ : ℂ))) =
        fun p => ((b p * Real.exp (-(L p * σ)) : ℝ) : ℂ) := by
      funext p
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [heq] at H
    exact Complex.summable_ofReal.mp H
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
    intro x
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp x

  let T : ℝ → (Σ n : ℕ, Fin n → ι) × ℕ → ℝ := fun t q =>
    b q.1 * Real.exp (-(2 * L q.1)) * ((L q.1 * t) ^ q.2 / (q.2.factorial : ℝ))
  have hT : ∀ t, 0 ≤ t → ∀ q, 0 ≤ T t q := by
    intro t ht q
    have := hL q.1
    exact mul_nonneg (mul_nonneg (hb _) (Real.exp_pos _).le) (by positivity)
  have hfib : ∀ t p, HasSum (fun n => T t (p, n)) (b p * Real.exp (-(L p * (2 - t)))) := by
    intro t p
    have H := (hexpR (L p * t)).mul_left (b p * Real.exp (-(2 * L p)))
    rw [show -(L p * (2 - t)) = -(2 * L p) + L p * t by ring, Real.exp_add, ← mul_assoc]
    exact H
  have hK : ∀ t, 0 ≤ t → ∀ n, Summable fun p => T t (p, n) := by
    intro t ht n
    refine Summable.of_nonneg_of_le (fun p => hT t ht (p, n)) (fun p => ?_)
      ((hB (7 / 4) (by norm_num)).mul_left ((4 * t) ^ n))
    have hLp := hL p
    have h1 : (L p * t) ^ n / (n.factorial : ℝ) = (4 * t) ^ n * ((L p / 4) ^ n / n.factorial) := by
      rw [show L p * t = (4 * t) * (L p / 4) by ring, mul_pow, mul_div_assoc]
    have h2 : (L p / 4) ^ n / (n.factorial : ℝ) ≤ Real.exp (L p / 4) :=
      Real.pow_div_factorial_le_exp _ (by positivity) n
    have h3 : b p * Real.exp (-(2 * L p)) * ((4 * t) ^ n * Real.exp (L p / 4)) =
        (4 * t) ^ n * (b p * Real.exp (-(L p * (7 / 4)))) := by
      rw [show -(L p * (7 / 4)) = -(2 * L p) + L p / 4 by ring, Real.exp_add]
      ring
    change b p * Real.exp (-(2 * L p)) * ((L p * t) ^ n / (n.factorial : ℝ)) ≤ _
    rw [h1, ← h3]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) n))
      (mul_nonneg (hb p) (Real.exp_pos _).le)
  have hK2 : ∀ t, 0 ≤ t → t < 1 → Summable (T t) := by
    intro t ht ht1
    rw [summable_prod_of_nonneg (fun q => hT t ht q)]
    refine ⟨fun p => (hfib t p).summable, ?_⟩
    simp only [fun p => (hfib t p).tsum_eq]
    exact hB (2 - t) (by linarith)
  have hK2' : ∀ t, 0 ≤ t → t < 1 →
      Summable fun n => ∑' p, T t (p, n) := by
    intro t ht ht1
    have hs : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T t q.swap :=
      (hK2 t ht ht1).prod_symm
    exact ((summable_prod_of_nonneg (fun q => hT t ht q.swap)).mp hs).2

  let r : ℕ → ℝ := fun n => ∑' p, T 1 (p, n)
  let c : ℕ → ℂ := fun n => (-1) ^ n * (r n : ℂ)
  have hr : ∀ n, 0 ≤ r n := fun n => tsum_nonneg fun p => hT 1 zero_le_one (p, n)
  have hrad : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_
    have hρ1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    have hρ0 : (0 : ℝ) ≤ ρ := ρ.2
    refine FormalMultilinearSeries.le_radius_of_bound _
      (∑' m, ∑' p, T ρ (p, m)) fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm_eq_mul,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
    have hcn : ‖c n‖ = r n := by
      simp only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n)]
    have hrn : r n * (ρ : ℝ) ^ n = ∑' p, T ρ (p, n) := by
      simp only [r, ← tsum_mul_right]
      congr 1
      funext p
      simp only [T]
      rw [mul_pow, mul_pow, one_pow]
      ring
    rw [hcn, hrn]
    exact (hK2' ρ hρ0 hρ1).le_tsum n fun m _ => tsum_nonneg fun p => hT ρ hρ0 (p, m)
  have hps : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ c) 2 1 := by
    refine ⟨hrad, one_pos, fun {y} hy => ?_⟩
    have hy1 : ‖y‖ < 1 := by
      simpa [EMetric.mem_ball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] using hy
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    let E : (Σ n : ℕ, Fin n → ι) × ℕ → ℂ := fun q =>
      ((b q.1 * Real.exp (-(2 * L q.1)) : ℝ) : ℂ) * ((-(L q.1 : ℂ) * y) ^ q.2 / (q.2.factorial : ℂ))
    have hEn : ∀ q, ‖E q‖ = T ‖y‖ q := by
      intro q
      simp only [E, T, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real,
        Complex.norm_natCast, Real.norm_eq_abs]
      rw [abs_of_nonneg (hb q.1), Real.abs_exp, abs_of_nonneg (hL q.1)]
    have hEs : Summable E := by
      refine Summable.of_norm ?_
      simp only [hEn]
      exact hK2 ‖y‖ (norm_nonneg _) hy1
    have hfibE : ∀ p, HasSum (fun n => E (p, n))
        ((b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y))) := by
      intro p
      have H := (hexpC (-(L p : ℂ) * y)).mul_left ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ)
      have heq : ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ) * Complex.exp (-(L p : ℂ) * y) =
          (b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y)) := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
        push_cast
        ring_nf
      rw [heq] at H
      exact H
    have hre : 1 < (2 + y).re := by
      have := Complex.abs_re_le_norm y
      rw [Complex.add_re]
      norm_num
      linarith [abs_le.mp this]
    have hEsum : ∑' q, E q = F (2 + y) :=
      (hEs.hasSum.prod_fiberwise hfibE).unique (hA _ hre)
    have hsw : HasSum (fun q : ℕ × (Σ n : ℕ, Fin n → ι) => E q.swap) (F (2 + y)) := by
      have ht : ∑' q : ℕ × (Σ n : ℕ, Fin n → ι), E q.swap = ∑' q, E q := by
        rw [← (Equiv.prodComm (Σ n : ℕ, Fin n → ι) ℕ).tsum_eq]
        simp
      rw [← hEsum, ← ht]
      exact hEs.prod_symm.hasSum
    refine HasSum.prod_fiberwise (g := fun n => c n * y ^ n) hsw fun n => ?_
    have H := (hsw.summable.prod_factor n).hasSum
    have hterm : ∀ p, E (p, n) = ((T 1 (p, n) : ℝ) : ℂ) * ((-1) ^ n * y ^ n) := by
      intro p
      simp only [E, T]
      push_cast
      ring
    have hval : ∑' p, E (n, p).swap = c n * y ^ n := by
      simp only [Prod.swap_prod_mk, hterm]
      rw [tsum_mul_right, ← Complex.ofReal_tsum]
      simp only [c, r]
      ring
    rw [hval] at H
    exact H

  have hent := hF.hasFPowerSeriesOnBall 2 (R := 1) one_pos
  have hpeq := hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hent.hasFPowerSeriesAt
  rw [← hpeq] at hent
  have H0 := hent.hasSum (y := -2) (EMetric.mem_ball.mpr (edist_lt_top _ _))
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at H0
  have hterm : ∀ n, c n * (-2) ^ n = ((∑' p, T 2 (p, n) : ℝ) : ℂ) := by
    intro n
    have h2 : ∀ p, T 2 (p, n) = T 1 (p, n) * 2 ^ n := by
      intro p
      simp only [T]
      rw [mul_pow, mul_pow, one_pow]
      ring
    simp only [h2, tsum_mul_right, c, r]
    push_cast
    rw [show ((-2 : ℂ)) ^ n = (-1) ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
    ring_nf
    rw [mul_comm n 2, pow_mul]
    norm_num
  simp only [hterm] at H0
  have hS2 : Summable fun n => ∑' p, T 2 (p, n) := Complex.summable_ofReal.mp H0.summable
  have hall : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T 2 q.swap :=
    (summable_prod_of_nonneg (fun q => hT 2 (by norm_num) q.swap)).mpr
      ⟨fun n => hK 2 (by norm_num) n, hS2⟩
  have hall' : Summable (T 2) := by
    have := hall.prod_symm
    simpa using this
  have hbsum : Summable b := by
    have := ((summable_prod_of_nonneg (hT 2 (by norm_num))).mp hall').2
    simp only [fun p => (hfib 2 p).tsum_eq, sub_self, mul_zero, neg_zero, Real.exp_zero,
      mul_one] at this
    exact this

  let j : ι → (Σ n : ℕ, Fin n → ι) := fun i => ⟨1, fun _ => i⟩
  have hj : Function.Injective j := by
    intro i i' h
    simp only [j, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact congrFun h 0
  have hbj : b ∘ j = a := by
    funext i
    simp [b, j]
  rw [← hbj]
  exact hbsum.comp_injective hj
end _root_.GlobalTheory
end GlobalTheory
