-- Prove2me | solution 1 for GuthMaynard.van_der_corput_b_process
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T19:02:48.230852+00:00
-- url     : https://prove2.me/submissions/9ef43e13-49e6-4f23-9191-ee791ad297b9

import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Mathlib
section
namespace GuthMaynard.SubWeyl
/-!
# Blueprint: `μ(1/2) ≤ 27/164` (exponent pair `A B A³ B (0,1) = (11/82, 57/82)`)

Route (Titchmarsh, *The theory of the Riemann zeta-function*, Theorems 5.13 and 4.9; see
`BRIEF.md` next to the copy of this file in the mission folder):

* Part W: Weyl differencing (the A-process) and Abel's inequality;
* Part A: the `k`-th derivative test (Theorem 5.13), by induction on `k`;
* Part B: derivative tests for integrals (Lemmas 4.2, 4.4) and stationary phase (Lemma 4.6);
* Part C: truncated Poisson summation (Lemma 4.7);
* Part T: the B-process (Theorem 4.9);
* Part D: the shifted phase `phi` and its dual phase (calculus);
* Part S: the shifted sums `∑ e(phi t h n)` (B-process, then the fifth-derivative test);
* Part L: the blocks `t^{43/100} ≤ N ≤ t^{1/2}` (A-process and exponent bookkeeping);
* Part M: the blocks `N ≤ t^{43/100}` (trivial bound and fourth-derivative test);
* Part Z: `ζ(1/2+it)` in terms of blocks `∑_{N<n≤N'} n^{it}` with `N ≤ √t`.

Conventions: `e x = exp(2πix)`, written as in `ExponentialSums.vdC_second_derivative`; sums over
`Finset.Ioc a b` with `a b : ℕ`; a function with its derivatives is a tuple of functions with
`HasDerivAt` on the closed interval. Everything after "Assembly" is proved from the stubs.
-/
/-- `e(x) = exp(2πix)`, in the shape of `ExponentialSums.vdC_second_derivative`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartW
open Finset
/-!
# Part W: Weyl differencing (the A-process) and Abel's inequality
-/

end GuthMaynard.SubWeyl.PartW
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part W: Weyl differencing and Abel's inequality -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartW
open Finset

end GuthMaynard.SubWeyl.PartW
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartA
open Finset
/-!
# Part A: the `k`-th derivative test (Titchmarsh, Theorem 5.13)

Induction on `k`. Base `k = 2`: `ExponentialSums.vdC_second_derivative` (second differences are
values of `F 2` by the mean value theorem twice; the last term of the sum is peeled off).
Step `k → k+1` (`K = 2^{k-1}`, `α = 1/(2K-2)`, `α' = 1/(4K-2)`): Weyl differencing with
`H = ⌈λ^{-1/(2K-1)}⌉`, the induction hypothesis for the phases `x ↦ F j (x+h) - F j x`
(with `λ` replaced by `hλ`, same `R`), `∑_{h<H} h^α ≤ H·H^α`, `∑_{h<H} h^{-α} ≤ 2H·H^{-α}`.
-/
/-! ### The function `e` -/

/-! ### Mean value theorem -/

/-! ### The statement proved by induction -/

/-! ### Base case `k = 2` -/

/-! ### Sums of powers -/

/-! ### The arithmetic of the induction step -/

/-! ### The induction step -/

end GuthMaynard.SubWeyl.PartA
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part A: the `k`-th derivative test -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-!
# Part B: derivative tests for integrals and stationary phase (Titchmarsh, Lemmas 4.2, 4.4, 4.6)
-/
/-! ### The function `e` -/
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

theorem hasDerivAt_e_comp (G : ℝ → ℝ) (G' x : ℝ) (h : HasDerivAt G G' x) :
    HasDerivAt (fun y => e (G y)) (e (G x) * (2 * Real.pi * G' * Complex.I)) x := by
  unfold e
  have h1 : HasDerivAt (fun y : ℝ => ((2 * Real.pi * G y : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * G' : ℝ) : ℂ) * Complex.I) x :=
    ((h.const_mul (2 * Real.pi)).ofReal_comp).mul_const Complex.I
  convert h1.cexp using 1
  push_cast
  ring

theorem norm_e_sub_le_two (x y : ℝ) : ‖e x - e y‖ ≤ 2 := by
  calc ‖e x - e y‖ ≤ ‖e x‖ + ‖e y‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_e, norm_e]; norm_num

theorem norm_e_sub_le (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have h1 : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, ← e_add, mul_one]
    congr 2
    ring
  have h2 : ‖e (x - y) - 1‖ ≤ 2 * Real.pi * |x - y| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos] at this
    refine le_trans (le_of_eq ?_) this
    unfold e
    rw [mul_comm]
  rw [h1, norm_mul, norm_e, one_mul]
  exact h2

/-! ### Abel summation and a second mean value bound -/
theorem abel_identity (v : ℕ → ℝ) (P : ℕ → ℂ) (Q : ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (v (i + 1) : ℂ) * (P (i + 1) - P i) =
      ∑ i ∈ Finset.range n, ((v (i + 1) - v i : ℝ) : ℂ) * (Q - P i) - (v n : ℂ) * (Q - P n) +
        (v 0 : ℂ) * (Q - P 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

theorem abel_discrete (v : ℕ → ℝ) (P : ℕ → ℂ) (n : ℕ) (D : ℝ)
    (hD : ∀ i ≤ n, ∀ j ≤ n, ‖P i - P j‖ ≤ D)
    (hv : ∀ i ≤ n, 0 ≤ v i)
    (hmono : (∀ i < n, v i ≤ v (i + 1)) ∨ (∀ i < n, v (i + 1) ≤ v i)) :
    ‖∑ i ∈ Finset.range n, (v (i + 1) : ℂ) * (P (i + 1) - P i)‖ ≤ D * max (v 0) (v n) ∧
      ∑ i ∈ Finset.range n, |v (i + 1) - v i| ≤ max (v 0) (v n) := by
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have hv0 := hv 0 (Nat.zero_le _)
  have hvn := hv n le_rfl
  rcases hmono with hm | hm
  · constructor
    · rw [abel_identity v P (P n) n]
      have h1 : ‖∑ i ∈ Finset.range n, ((v (i + 1) - v i : ℝ) : ℂ) * (P n - P i)‖ ≤
          ∑ i ∈ Finset.range n, (v (i + 1) - v i) * D := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hm i hi'))]
        exact mul_le_mul_of_nonneg_left (hD n le_rfl i hi'.le) (sub_nonneg.mpr (hm i hi'))
      have h2 : ∑ i ∈ Finset.range n, (v (i + 1) - v i) * D = (v n - v 0) * D := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
      have h3 : ‖(v 0 : ℂ) * (P n - P 0)‖ ≤ v 0 * D := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0]
        exact mul_le_mul_of_nonneg_left (hD n le_rfl 0 (Nat.zero_le _)) hv0
      calc _ = ‖∑ i ∈ Finset.range n, ((v (i + 1) - v i : ℝ) : ℂ) * (P n - P i) +
              (v 0 : ℂ) * (P n - P 0)‖ := by rw [sub_self, mul_zero, sub_zero]
        _ ≤ _ := norm_add_le _ _
        _ ≤ (v n - v 0) * D + v 0 * D := by linarith
        _ = D * v n := by ring
        _ ≤ D * max (v 0) (v n) := mul_le_mul_of_nonneg_left (le_max_right _ _) hD0
    · rw [Finset.sum_congr rfl (fun i hi =>
        abs_of_nonneg (sub_nonneg.mpr (hm i (Finset.mem_range.mp hi)))), Finset.sum_range_sub]
      exact le_trans (by linarith) (le_max_right _ _)
  · constructor
    · rw [abel_identity v P (P 0) n]
      have h1 : ‖∑ i ∈ Finset.range n, ((v (i + 1) - v i : ℝ) : ℂ) * (P 0 - P i)‖ ≤
          ∑ i ∈ Finset.range n, (v i - v (i + 1)) * D := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hm i hi')), neg_sub]
        exact mul_le_mul_of_nonneg_left (hD 0 (Nat.zero_le _) i hi'.le)
          (sub_nonneg.mpr (hm i hi'))
      have h2 : ∑ i ∈ Finset.range n, (v i - v (i + 1)) * D = (v 0 - v n) * D := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
      have h3 : ‖(v n : ℂ) * (P 0 - P n)‖ ≤ v n * D := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hvn]
        exact mul_le_mul_of_nonneg_left (hD 0 (Nat.zero_le _) n le_rfl) hvn
      calc _ = ‖∑ i ∈ Finset.range n, ((v (i + 1) - v i : ℝ) : ℂ) * (P 0 - P i) -
              (v n : ℂ) * (P 0 - P n)‖ := by rw [sub_self, mul_zero, add_zero]
        _ ≤ _ := norm_sub_le _ _
        _ ≤ (v 0 - v n) * D + v n * D := by linarith
        _ = D * v 0 := by ring
        _ ≤ D * max (v 0) (v n) := mul_le_mul_of_nonneg_left (le_max_left _ _) hD0
    · rw [Finset.sum_congr rfl (fun i hi => (abs_sub_comm _ _).trans
        (abs_of_nonneg (sub_nonneg.mpr (hm i (Finset.mem_range.mp hi))))), Finset.sum_range_sub']
      exact le_trans (by linarith) (le_max_left _ _)

/-- A bound of second-mean-value type: a monotone nonnegative weight against a derivative. -/
theorem abel_integral_bound (a b : ℝ) (hab : a ≤ b) (w : ℝ → ℝ) (Φ φ : ℝ → ℂ) (M D : ℝ)
    (hwc : ContinuousOn w (Icc a b))
    (hmono : MonotoneOn w (Icc a b) ∨ AntitoneOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hwM : ∀ x ∈ Icc a b, w x ≤ M)
    (hΦ : ∀ x ∈ Icc a b, HasDerivAt Φ (φ x) x) (hφ : ContinuousOn φ (Icc a b))
    (hD : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖Φ x - Φ y‖ ≤ D) :
    ‖∫ x in a..b, (w x : ℂ) * φ x‖ ≤ M * D := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a ha)
  have hM0 : 0 ≤ M := (hw0 a ha).trans (hwM a ha)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD a ha a ha)
  have key : ∀ n : ℕ, 0 < n →
      ‖∫ x in a..b, (w x : ℂ) * φ x‖ ≤ M * D + M * K * (b - a) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set h : ℝ := (b - a) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) hn'.le
    set p : ℕ → ℝ := fun i => a + i * h with hp
    have hp0 : p 0 = a := by simp [hp]
    have hpn : p n = b := by
      simp only [hp, hh]
      field_simp
      ring
    have hpmono : Monotone p := fun i j hij => by
      simp only [hp]
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      nlinarith
    have hpmem : ∀ i ≤ n, p i ∈ Icc a b := fun i hi =>
      ⟨hp0 ▸ hpmono (Nat.zero_le i), hpn ▸ hpmono hi⟩
    have hpstep : ∀ i, p (i + 1) - p i = h := fun i => by
      simp only [hp]
      push_cast
      ring
    have hsub : ∀ i < n, Icc (p i) (p (i + 1)) ⊆ Icc a b := fun i hi =>
      Icc_subset_Icc (hpmem i hi.le).1 (hpmem (i + 1) hi).2
    have hsubu : ∀ i < n, uIcc (p i) (p (i + 1)) ⊆ Icc a b := fun i hi => by
      rw [uIcc_of_le (hpmono (Nat.le_succ i))]
      exact hsub i hi
    have hwC : ContinuousOn (fun x => (w x : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn hwc
    have hcont : ContinuousOn (fun x => (w x : ℂ) * φ x) (Icc a b) := hwC.mul hφ
    have hint : ∀ i < n, IntervalIntegrable (fun x => (w x : ℂ) * φ x) volume (p i) (p (i + 1)) :=
      fun i hi => (hcont.mono (hsubu i hi)).intervalIntegrable
    have hsplit : ∫ x in a..b, (w x : ℂ) * φ x =
        ∑ i ∈ Finset.range n, ∫ t in p i..p (i + 1), (w t : ℂ) * φ t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hint, hp0, hpn]
    have hpiece : ∀ i < n, ∫ t in p i..p (i + 1), (w t : ℂ) * φ t =
        (w (p (i + 1)) : ℂ) * (Φ (p (i + 1)) - Φ (p i)) +
          ∫ t in p i..p (i + 1), ((w t - w (p (i + 1)) : ℝ) : ℂ) * φ t := by
      intro i hi
      have hφi : IntervalIntegrable φ volume (p i) (p (i + 1)) :=
        (hφ.mono (hsubu i hi)).intervalIntegrable
      have hftc : ∫ t in p i..p (i + 1), φ t = Φ (p (i + 1)) - Φ (p i) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΦ t (hsubu i hi ht)) hφi
      have hci : ContinuousOn (fun t => ((w t - w (p (i + 1)) : ℝ) : ℂ) * φ t) (Icc a b) :=
        (Complex.continuous_ofReal.comp_continuousOn (hwc.sub continuousOn_const)).mul hφ
      rw [← hftc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (hφi.const_mul _) (hci.mono (hsubu i hi)).intervalIntegrable]
      refine intervalIntegral.integral_congr fun t _ => ?_
      push_cast
      ring
    have herr : ∀ i < n, ‖∫ t in p i..p (i + 1), ((w t - w (p (i + 1)) : ℝ) : ℂ) * φ t‖ ≤
        |w (p (i + 1)) - w (p i)| * K * h := by
      intro i hi
      have hle := hpmono (Nat.le_succ i)
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := p i) (b := p (i + 1))
        (C := |w (p (i + 1)) - w (p i)| * K)
        (f := fun t => ((w t - w (p (i + 1)) : ℝ) : ℂ) * φ t) ?_
      · rwa [hpstep, abs_of_nonneg hh0] at this
      · intro t ht
        rw [uIoc_of_le hle] at ht
        have ht' : t ∈ Icc (p i) (p (i + 1)) := ⟨ht.1.le, ht.2⟩
        have htab := hsub i hi ht'
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul ?_ (hK t htab) (norm_nonneg _) (abs_nonneg _)
        rcases hmono with hm | hm
        · have h1 := hm (hpmem i hi.le) htab ht'.1
          have h2 := hm htab (hpmem (i + 1) hi) ht'.2
          rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · have h1 := hm (hpmem i hi.le) htab ht'.1
          have h2 := hm htab (hpmem (i + 1) hi) ht'.2
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
    obtain ⟨hA1, hA2⟩ := abel_discrete (fun i => w (p i)) (fun i => Φ (p i)) n D
      (fun i hi j hj => hD _ (hpmem i hi) _ (hpmem j hj)) (fun i hi => hw0 _ (hpmem i hi))
      (by
        rcases hmono with hm | hm
        · exact Or.inl fun i hi => hm (hpmem i hi.le) (hpmem (i + 1) hi) (hpmono (Nat.le_succ i))
        · exact Or.inr fun i hi => hm (hpmem i hi.le) (hpmem (i + 1) hi) (hpmono (Nat.le_succ i)))
    have hmax : max (w (p 0)) (w (p n)) ≤ M :=
      max_le (hwM _ (hpmem 0 (Nat.zero_le _))) (hwM _ (hpmem n le_rfl))
    rw [hsplit, Finset.sum_congr rfl (fun i hi => hpiece i (Finset.mem_range.mp hi)),
      Finset.sum_add_distrib]
    have hE : ‖∑ i ∈ Finset.range n, ∫ t in p i..p (i + 1),
        ((w t - w (p (i + 1)) : ℝ) : ℂ) * φ t‖ ≤ M * K * h := by
      refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
        herr i (Finset.mem_range.mp hi))).trans ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hA2.trans hmax) hK0) hh0
    have e1 : M * K * h = M * K * (b - a) / n := by
      rw [hh]
      ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ D * max (w (p 0)) (w (p n)) + M * K * h := add_le_add hA1 hE
      _ ≤ M * D + M * K * (b - a) / n := by
          rw [← e1]
          nlinarith [mul_le_mul_of_nonneg_left hmax hD0]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (M * K * (b - a) / ε)
  have hq : 0 ≤ M * K * (b - a) / ε :=
    div_nonneg (mul_nonneg (mul_nonneg hM0 hK0) (sub_nonneg.mpr hab)) hε.le
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hq hn
  have hn1 : 0 < n := by exact_mod_cast hn0
  refine (key n hn1).trans ?_
  have : M * K * (b - a) / n ≤ ε := by
    rw [div_le_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hn
    linarith
  linarith

/-! ### Lemma 4.2 -/
theorem first_deriv_pos (G G1 : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (G1 x) x)
    (hcont : ContinuousOn G1 (Icc a b))
    (hmono : MonotoneOn G1 (Icc a b) ∨ AntitoneOn G1 (Icc a b))
    (hlow : ∀ x ∈ Icc a b, m ≤ G1 x) :
    ‖∫ x in a..b, e (G x)‖ ≤ 1 / (Real.pi * m) := by
  have hpos : ∀ x ∈ Icc a b, 0 < G1 x := fun x hx => hm.trans_le (hlow x hx)
  have hGc : ContinuousOn G (Icc a b) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have key := abel_integral_bound a b hab (fun x => (G1 x)⁻¹)
    (fun x => e (G x) / (2 * Real.pi * Complex.I)) (fun x => (G1 x : ℂ) * e (G x))
    (1 / m) (1 / Real.pi) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have heq : ∫ x in a..b, e (G x) =
        ∫ x in a..b, (((G1 x)⁻¹ : ℝ) : ℂ) * ((G1 x : ℂ) * e (G x)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hab] at hx
      have : (G1 x : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx).ne'
      push_cast
      field_simp
    rw [heq]
    refine key.trans (le_of_eq ?_)
    ring
  · exact hcont.inv₀ fun x hx => (hpos x hx).ne'
  · rcases hmono with h | h
    · exact Or.inr fun x hx y hy hxy => inv_anti₀ (hpos x hx) (h hx hy hxy)
    · exact Or.inl fun x hx y hy hxy => inv_anti₀ (hpos y hy) (h hx hy hxy)
  · exact fun x hx => (inv_pos.mpr (hpos x hx)).le
  · exact fun x hx => by
      rw [one_div]
      exact inv_anti₀ hm (hlow x hx)
  · intro x hx
    have := (hasDerivAt_e_comp G (G1 x) x (hG x hx)).div_const (2 * Real.pi * Complex.I)
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero]
    have heq : (G1 x : ℂ) * e (G x) =
        e (G x) * (2 * Real.pi * (G1 x : ℂ) * Complex.I) / (2 * Real.pi * Complex.I) := by
      rw [eq_div_iff hpi]
      ring
    rw [heq]
    exact this
  · exact (Complex.continuous_ofReal.comp_continuousOn hcont).mul
      (continuous_e.comp_continuousOn hGc)
  · intro x _ y _
    rw [← sub_div, norm_div]
    have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      simp
    rw [h2, div_le_iff₀ Real.two_pi_pos]
    have := norm_e_sub_le_two (G x) (G y)
    have hpi := Real.pi_pos
    have : 1 / Real.pi * (2 * Real.pi) = 2 := by field_simp
    linarith [norm_e_sub_le_two (G x) (G y)]

theorem first_deriv_sharp (G G1 : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (G1 x) x)
    (hcont : ContinuousOn G1 (Icc a b))
    (hmono : MonotoneOn G1 (Icc a b) ∨ AntitoneOn G1 (Icc a b))
    (hlow : ∀ x ∈ Icc a b, m ≤ |G1 x|) :
    ‖∫ x in a..b, e (G x)‖ ≤ 1 / (Real.pi * m) := by
  have hsign : (∀ x ∈ Icc a b, m ≤ G1 x) ∨ (∀ x ∈ Icc a b, G1 x ≤ -m) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := hcon
    have hx2 : G1 x ≤ -m := by
      rcases le_abs'.mp (hlow x hx) with h | h <;> linarith
    have hy2 : m ≤ G1 y := by
      rcases le_abs'.mp (hlow y hy) with h | h <;> linarith
    have hsub : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
    have h0 : (0 : ℝ) ∈ uIcc (G1 x) (G1 y) := by
      rw [uIcc_of_le (by linarith)]
      constructor <;> linarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
    have := hlow z (hsub hz)
    rw [hz0, abs_zero] at this
    linarith
  rcases hsign with hs | hs
  · exact first_deriv_pos G G1 a b m hab hm hG hcont hmono hs
  · have key := first_deriv_pos (fun x => -G x) (fun x => -G1 x) a b m hab hm
      (fun x hx => (hG x hx).neg) hcont.neg
      (by
        rcases hmono with h | h
        · exact Or.inr h.neg
        · exact Or.inl h.neg)
      (fun x hx => by linarith [hs x hx])
    have hconj : ∫ x in a..b, e (-G x) = (starRingEnd ℂ) (∫ x in a..b, e (G x)) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        ← integral_conj]
      simp only [e_neg]
    rw [hconj, RCLike.norm_conj] at key
    exact key

theorem integral_first_deriv_test (G G1 : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G1 x) x)
    (hcont : ContinuousOn G1 (Set.Icc a b))
    (hmono : MonotoneOn G1 (Set.Icc a b) ∨ AntitoneOn G1 (Set.Icc a b))
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ |G1 x|) :
    ‖∫ x in a..b, e (G x)‖ ≤ 1 / m := by
  refine (first_deriv_sharp G G1 a b m hab hm hG hcont hmono hlow).trans ?_
  have h3 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact one_div_le_one_div_of_le hm (le_mul_of_one_le_left hm.le h3)

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part B: integrals -/
alias integral_first_deriv_test := GuthMaynard.SubWeyl.PartB.integral_first_deriv_test

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-! ### Monotonicity from derivatives -/
theorem monotoneOn_of_hasDerivAt_nonneg (f f' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, 0 ≤ f' x) :
    MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_)
  rw [(hf x (interior_subset hx)).deriv]
  exact hf' x (interior_subset hx)

theorem hd_lin (c L x : ℝ) : HasDerivAt (fun x => L * (x - c)) L x := by
  have := ((hasDerivAt_id x).sub_const c).const_mul L
  rw [mul_one] at this
  exact this

theorem hd_sq (c L x : ℝ) : HasDerivAt (fun x => L * (x - c) ^ 2 / 2) (L * (x - c)) x := by
  have h := (((hasDerivAt_pow 2 (x - c)).comp x ((hasDerivAt_id x).sub_const c)).const_mul
    L).div_const 2
  have e1 : L * (((2 : ℕ) : ℝ) * (x - c) ^ (2 - 1) * 1) / 2 = L * (x - c) := by
    norm_num
    ring
  rw [e1] at h
  exact h

theorem hd_cu (c L x : ℝ) :
    HasDerivAt (fun x => L * (x - c) ^ 3 / 6) (L * (x - c) ^ 2 / 2) x := by
  have h := (((hasDerivAt_pow 3 (x - c)).comp x ((hasDerivAt_id x).sub_const c)).const_mul
    L).div_const 6
  have e1 : L * (((3 : ℕ) : ℝ) * (x - c) ^ (3 - 1) * 1) / 6 = L * (x - c) ^ 2 / 2 := by
    norm_num
    ring
  rw [e1] at h
  exact h

theorem growth_of_deriv_ge (f f' : ℝ → ℝ) (a b r : ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, r ≤ f' x)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    r * (y - x) ≤ f y - f x := by
  have hm := monotoneOn_of_hasDerivAt_nonneg (fun t => f t - r * (t - 0)) (fun t => f' t - r) a b
    (fun t ht => (hf t ht).sub (hd_lin 0 r t))
    (fun t ht => sub_nonneg.mpr (hf' t ht))
  have := hm hx hy hxy
  simp only [sub_zero] at this
  linarith

/-! ### Lemma 4.4 -/
theorem exists_pivot (G1 G2 : ℝ → ℝ) (a b r : ℝ) (hab : a ≤ b) (hr : 0 < r)
    (hG1 : ∀ x ∈ Icc a b, HasDerivAt G1 (G2 x) x) (hlow : ∀ x ∈ Icc a b, r ≤ G2 x) :
    ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, r * |x - c| ≤ |G1 x| := by
  have gr := growth_of_deriv_ge G1 G2 a b r hG1 hlow
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  by_cases h1 : 0 ≤ G1 a
  · refine ⟨a, ha, fun x hx => ?_⟩
    have h := gr a x ha hx hx.1
    have hnn : 0 ≤ r * (x - a) := mul_nonneg hr.le (sub_nonneg.mpr hx.1)
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), abs_of_nonneg (by linarith)]
    linarith
  · by_cases h2 : G1 b ≤ 0
    · refine ⟨b, hb, fun x hx => ?_⟩
      have h := gr x b hx hb hx.2
      have hnn : 0 ≤ r * (b - x) := mul_nonneg hr.le (sub_nonneg.mpr hx.2)
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2), abs_of_nonpos (by linarith)]
      linarith
    · have hcont : ContinuousOn G1 (Icc a b) :=
        fun x hx => (hG1 x hx).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcont
        (show (0 : ℝ) ∈ Icc (G1 a) (G1 b) from ⟨by linarith, by linarith⟩)
      refine ⟨c, hc, fun x hx => ?_⟩
      rcases le_total c x with hcx | hxc
      · have h := gr c x hc hx hcx
        have hnn : 0 ≤ r * (x - c) := mul_nonneg hr.le (sub_nonneg.mpr hcx)
        rw [abs_of_nonneg (sub_nonneg.mpr hcx), abs_of_nonneg (by linarith)]
        linarith
      · have h := gr x c hx hc hxc
        have hnn : 0 ≤ r * (c - x) := mul_nonneg hr.le (sub_nonneg.mpr hxc)
        rw [abs_of_nonpos (sub_nonpos.mpr hxc), abs_of_nonpos (by linarith)]
        linarith

theorem integral_second_deriv_test (G G1 G2 : ℝ → ℝ) (a b r : ℝ) (hab : a ≤ b) (hr : 0 < r)
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G1 x) x)
    (hG1 : ∀ x ∈ Set.Icc a b, HasDerivAt G1 (G2 x) x)
    (hlow : ∀ x ∈ Set.Icc a b, r ≤ G2 x) :
    ‖∫ x in a..b, e (G x)‖ ≤ 4 / Real.sqrt r := by
  obtain ⟨c, hc, hpiv⟩ := exists_pivot G1 G2 a b r hab hr hG1 hlow
  have hmonoG1 : MonotoneOn G1 (Icc a b) :=
    monotoneOn_of_hasDerivAt_nonneg G1 G2 a b hG1 (fun x hx => hr.le.trans (hlow x hx))
  have hcontG1 : ContinuousOn G1 (Icc a b) :=
    fun x hx => (hG1 x hx).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (fun x => e (G x)) (Icc a b) :=
    continuous_e.comp_continuousOn (fun x hx => (hG x hx).continuousAt.continuousWithinAt)
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  obtain ⟨η, hη⟩ : ∃ η, η = 1 / Real.sqrt r := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hrη : r * η = Real.sqrt r := by
    rw [hη, mul_one_div]
    exact Real.div_sqrt
  obtain ⟨p, hp⟩ : ∃ p, p = max a (c - η) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = min b (c + η) := ⟨_, rfl⟩
  have hap : a ≤ p := hp ▸ le_max_left _ _
  have hpc : p ≤ c := hp ▸ max_le hc.1 (by linarith)
  have hcq : c ≤ q := hq ▸ le_min hc.2 (by linarith)
  have hqb : q ≤ b := hq ▸ min_le_left _ _
  have hpI : p ∈ Icc a b := ⟨hap, by linarith [hc.2]⟩
  have hqI : q ∈ Icc a b := ⟨by linarith [hc.1], hqb⟩
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hbI : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hint : ∀ u v, u ∈ Icc a b → v ∈ Icc a b →
      IntervalIntegrable (fun x => e (G x)) volume u v :=
    fun u v hu hv => (hGc.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  have hsplit : ∫ x in a..b, e (G x) =
      (∫ x in a..p, e (G x)) + (∫ x in p..q, e (G x)) + ∫ x in q..b, e (G x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _ haI hpI) (hint _ _ hpI hqI),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _ haI hqI) (hint _ _ hqI hbI)]
  have h1 : ‖∫ x in a..p, e (G x)‖ ≤ 1 / Real.sqrt r := by
    rcases le_total (c - η) a with h | h
    · have hpa : p = a := hp ▸ max_eq_left h
      rw [hpa, intervalIntegral.integral_same, norm_zero]
      positivity
    · have hpe : p = c - η := hp ▸ max_eq_right h
      have hsub : Icc a p ⊆ Icc a b := Icc_subset_Icc le_rfl hpI.2
      rw [← hrη]
      refine integral_first_deriv_test G G1 a p (r * η) hap (by positivity)
        (fun x hx => hG x (hsub hx)) (hcontG1.mono hsub) (Or.inl (hmonoG1.mono hsub))
        (fun x hx => ?_)
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hr.le) (hpiv x (hsub hx))
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]
  have h2 : ‖∫ x in q..b, e (G x)‖ ≤ 1 / Real.sqrt r := by
    rcases le_total b (c + η) with h | h
    · have hqa : q = b := hq ▸ min_eq_left h
      rw [hqa, intervalIntegral.integral_same, norm_zero]
      positivity
    · have hqe : q = c + η := hq ▸ min_eq_right h
      have hsub : Icc q b ⊆ Icc a b := Icc_subset_Icc hqI.1 le_rfl
      rw [← hrη]
      refine integral_first_deriv_test G G1 q b (r * η) hqb (by positivity)
        (fun x hx => hG x (hsub hx)) (hcontG1.mono hsub) (Or.inl (hmonoG1.mono hsub))
        (fun x hx => ?_)
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hr.le) (hpiv x (hsub hx))
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]
  have h3 : ‖∫ x in p..q, e (G x)‖ ≤ 2 / Real.sqrt r := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q) (C := 1)
      (f := fun x => e (G x)) (fun x _ => (norm_e _).le)
    rw [abs_of_nonneg (by linarith)] at this
    have hpl : c - η ≤ p := hp ▸ le_max_right _ _
    have hqu : q ≤ c + η := hq ▸ min_le_right _ _
    have e2 : 2 / Real.sqrt r = 2 * η := by
      rw [hη]
      ring
    rw [e2]
    linarith
  rw [hsplit]
  calc _ ≤ _ := norm_add₃_le
    _ ≤ 1 / Real.sqrt r + 2 / Real.sqrt r + 1 / Real.sqrt r := add_le_add (add_le_add h1 h3) h2
    _ = 4 / Real.sqrt r := by ring

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl
alias integral_second_deriv_test := GuthMaynard.SubWeyl.PartB.integral_second_deriv_test

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-! ### The Fresnel integral -/
/-- The truncated Fresnel integral `∫_0^T e(u²/2) du`. -/
noncomputable def fres (T : ℝ) : ℂ := ∫ u in (0 : ℝ)..T, e (u ^ 2 / 2)

theorem fres_integrable (u v : ℝ) :
    IntervalIntegrable (fun u : ℝ => e (u ^ 2 / 2)) volume u v :=
  (continuous_e.comp (by fun_prop)).intervalIntegrable _ _

theorem fres_sub (T T' : ℝ) : fres T' - fres T = ∫ u in T..T', e (u ^ 2 / 2) := by
  unfold fres
  rw [intervalIntegral.integral_interval_sub_left (fres_integrable _ _) (fres_integrable _ _)]

theorem fres_sub_le_inv (T T' : ℝ) (hT : 0 < T) (hTT' : T ≤ T') :
    ‖fres T' - fres T‖ ≤ 1 / T := by
  rw [fres_sub]
  refine integral_first_deriv_test (fun u => u ^ 2 / 2) (fun u => u) T T' T hTT' hT
    (fun x _ => ?_) continuous_id.continuousOn (Or.inl (monotone_id.monotoneOn _)) (fun x hx => ?_)
  · have h := hd_sq 0 1 x
    simp only [sub_zero, one_mul] at h
    exact h
  · rw [abs_of_pos (hT.trans_le hx.1)]
    exact hx.1

theorem fres_sub_le_one (T T' : ℝ) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    ‖fres T' - fres T‖ ≤ 1 := by
  rw [fres_sub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T') (C := 1)
    (f := fun u : ℝ => e (u ^ 2 / 2)) (fun x _ => (norm_e _).le)
  rw [abs_of_nonneg (sub_nonneg.mpr hTT')] at this
  linarith

theorem fres_sub_le (T T' : ℝ) (hT : 0 ≤ T) (hTT' : T ≤ T') :
    ‖fres T' - fres T‖ ≤ 4 / (T + 1) := by
  have hpos : 0 < T + 1 := by linarith
  have hnn := norm_nonneg (fres T' - fres T)
  rw [le_div_iff₀ hpos]
  rcases le_total 1 T with h1 | h1
  · have hT0 : 0 < T := by linarith
    have := fres_sub_le_inv T T' hT0 hTT'
    rw [le_div_iff₀ hT0] at this
    nlinarith
  · rcases le_total T' 1 with h2 | h2
    · have := fres_sub_le_one T T' hTT' (by linarith)
      nlinarith
    · have a1 := fres_sub_le_inv 1 T' one_pos h2
      have a2 := fres_sub_le_one T 1 h1 (by linarith)
      have : ‖fres T' - fres T‖ ≤ 2 := by
        calc ‖fres T' - fres T‖ = ‖(fres T' - fres 1) + (fres 1 - fres T)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
          _ ≤ 2 := by
              norm_num at a1
              linarith
      nlinarith

/-- The Fresnel constant `∫_0^∞ e(u²/2) du` (which is `e^{πi/4}/2`). -/
noncomputable def fresJ : ℂ := Filter.limUnder Filter.atTop (fun n : ℕ => fres n)

theorem fres_tendsto : Filter.Tendsto (fun n : ℕ => fres n) Filter.atTop (nhds fresJ) := by
  have hc : CauchySeq (fun n : ℕ => fres n) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 4 * (1 / ((N : ℝ) + 1)))
      (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm]
      have hmono : ∀ k : ℕ, N ≤ k → 4 / ((k : ℝ) + 1) ≤ 4 * (1 / ((N : ℝ) + 1)) := by
        intro k hk
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      rcases le_total n m with h | h
      · rw [← norm_neg, neg_sub]
        exact (fres_sub_le n m (Nat.cast_nonneg n) (by exact_mod_cast h)).trans (hmono n hn)
      · exact (fres_sub_le m n (Nat.cast_nonneg m) (by exact_mod_cast h)).trans (hmono m hm)
    · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)
      rwa [mul_zero] at this
  exact hc.tendsto_limUnder

theorem fresJ_sub_le (T : ℝ) (hT : 0 ≤ T) : ‖fresJ - fres T‖ ≤ 4 / (T + 1) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ‖fres n - fres T‖) Filter.atTop
      (nhds ‖fresJ - fres T‖) := (fres_tendsto.sub_const _).norm
  refine le_of_tendsto h1 ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn
  exact fres_sub_le T n hT ((Nat.le_ceil T).trans (by exact_mod_cast hn))

theorem norm_fresJ_le : ‖fresJ‖ ≤ 4 := by
  have := fresJ_sub_le 0 le_rfl
  have h0 : fres 0 = 0 := by
    unfold fres
    exact intervalIntegral.integral_same
  rw [h0, sub_zero] at this
  norm_num at this
  exact this

theorem integral_quadratic (A c d Gc : ℝ) (hA : 0 < A) :
    ∫ x in c..(c + d), e (Gc + A * (x - c) ^ 2 / 2) =
      e Gc * ((1 / Real.sqrt A : ℝ) : ℂ) * fres (Real.sqrt A * d) := by
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have h1 : ∀ x : ℝ, e (Gc + A * (x - c) ^ 2 / 2) =
      e Gc * e ((Real.sqrt A * x - Real.sqrt A * c) ^ 2 / 2) := by
    intro x
    rw [← e_add, ← mul_sub, mul_pow, Real.sq_sqrt hA.le]
  have h2 := intervalIntegral.integral_comp_mul_sub (f := fun v : ℝ => e (v ^ 2 / 2)) (a := c)
    (b := c + d) hs.ne' (Real.sqrt A * c)
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, h2, sub_self,
    show Real.sqrt A * (c + d) - Real.sqrt A * c = Real.sqrt A * d by ring, Complex.real_smul]
  unfold fres
  push_cast
  ring

/-! ### Taylor's theorem to third order -/
theorem taylor_step (f f' g g' : ℝ → ℝ) (c b : ℝ)
    (hf : ∀ x ∈ Icc c b, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Icc c b, HasDerivAt g (g' x) x)
    (h : ∀ x ∈ Icc c b, |f' x| ≤ g' x) (hfc : f c = 0) (hgc : g c = 0) :
    ∀ x ∈ Icc c b, |f x| ≤ g x := by
  intro x hx
  have hc : c ∈ Icc c b := left_mem_Icc.mpr (hx.1.trans hx.2)
  have m1 := monotoneOn_of_hasDerivAt_nonneg (fun t => g t - f t) (fun t => g' t - f' t) c b
    (fun t ht => (hg t ht).sub (hf t ht))
    (fun t ht => by linarith [(abs_le.mp (h t ht)).2]) hc hx hx.1
  have m2 := monotoneOn_of_hasDerivAt_nonneg (fun t => g t + f t) (fun t => g' t + f' t) c b
    (fun t ht => (hg t ht).add (hf t ht))
    (fun t ht => by linarith [(abs_le.mp (h t ht)).1]) hc hx hx.1
  simp only [hfc, hgc] at m1 m2
  rw [abs_le]
  constructor <;> linarith

theorem taylor_bound (G G1 G2 G3 : ℝ → ℝ) (b c L : ℝ)
    (hG : ∀ x ∈ Icc c b, HasDerivAt G (G1 x) x)
    (hG1 : ∀ x ∈ Icc c b, HasDerivAt G1 (G2 x) x)
    (hG2 : ∀ x ∈ Icc c b, HasDerivAt G2 (G3 x) x)
    (hb3 : ∀ x ∈ Icc c b, |G3 x| ≤ L) (hc : G1 c = 0) :
    ∀ x ∈ Icc c b, |G x - (G c + G2 c * (x - c) ^ 2 / 2)| ≤ L * (x - c) ^ 3 / 6 := by
  have s1 := taylor_step (fun x => G2 x - G2 c) G3 (fun x => L * (x - c)) (fun _ => L) c b
    (fun x hx => (hG2 x hx).sub_const _) (fun x _ => hd_lin c L x) hb3 (by simp) (by simp)
  have s2 := taylor_step (fun x => G1 x - G2 c * (x - c)) (fun x => G2 x - G2 c)
    (fun x => L * (x - c) ^ 2 / 2) (fun x => L * (x - c)) c b
    (fun x hx => (hG1 x hx).sub (hd_lin c (G2 c) x)) (fun x _ => hd_sq c L x) s1
    (by simp [hc]) (by simp)
  have s3 := taylor_step (fun x => G x - (G c + G2 c * (x - c) ^ 2 / 2))
    (fun x => G1 x - G2 c * (x - c)) (fun x => L * (x - c) ^ 3 / 6)
    (fun x => L * (x - c) ^ 2 / 2) c b
    (fun x hx => (hG x hx).sub ((hd_sq c (G2 c) x).const_add (G c))) (fun x _ => hd_cu c L x) s2
    (by simp) (by simp)
  exact s3

/-! ### Lemma 4.6 -/
/-- One half of the stationary phase lemma: the integral from the stationary point `c` to `b`.
Here `ε = λ₂^{-4/5} λ₃^{1/5}`. -/
theorem stationary_half (R : ℝ) (hR : 1 ≤ R) (G G1 G2 G3 : ℝ → ℝ) (b c lam2 lam3 ε : ℝ)
    (hcb : c ≤ b) (h2 : 0 < lam2) (h3 : 0 < lam3) (hε : 0 < ε) (hε5 : ε ^ 5 * lam2 ^ 4 = lam3)
    (hG : ∀ x ∈ Icc c b, HasDerivAt G (G1 x) x)
    (hG1 : ∀ x ∈ Icc c b, HasDerivAt G1 (G2 x) x)
    (hG2 : ∀ x ∈ Icc c b, HasDerivAt G2 (G3 x) x)
    (hb2 : ∀ x ∈ Icc c b, lam2 ≤ G2 x ∧ G2 x ≤ R * lam2)
    (hb3 : ∀ x ∈ Icc c b, |G3 x| ≤ R * lam3) (hc : G1 c = 0) :
    ‖(∫ x in c..b, e (G x)) - fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c)‖ ≤
      (2 * R + 5) * ε + 4 * R / (|G1 b| + Real.sqrt lam2) := by
  have hcc : c ∈ Icc c b := left_mem_Icc.mpr hcb
  have hbb : b ∈ Icc c b := right_mem_Icc.mpr hcb
  have hA : lam2 ≤ G2 c := (hb2 c hcc).1
  have hA0 : 0 < G2 c := h2.trans_le hA
  have hsA : 0 < Real.sqrt (G2 c) := Real.sqrt_pos.mpr hA0
  have hs2 : 0 < Real.sqrt lam2 := Real.sqrt_pos.mpr h2
  have hs2A : Real.sqrt lam2 ≤ Real.sqrt (G2 c) := Real.sqrt_le_sqrt hA
  have hR0 : 0 < R := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 1 / (lam2 * ε) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  have hlδ : lam2 * δ = 1 / ε := by
    rw [hδ]
    field_simp
  have h3δ : lam3 * δ ^ 4 = ε := by
    rw [hδ, ← hε5]
    field_simp
  obtain ⟨d, hd⟩ : ∃ d, d = min (b - c) δ := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ le_min (sub_nonneg.mpr hcb) hδ0.le
  have hdb : d ≤ b - c := hd ▸ min_le_left _ _
  have hdδ : d ≤ δ := hd ▸ min_le_right _ _
  have hq : c + d ∈ Icc c b := ⟨by linarith, by linarith⟩
  have hGc : ContinuousOn (fun x => e (G x)) (Icc c b) :=
    continuous_e.comp_continuousOn fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have hint : ∀ u v, u ∈ Icc c b → v ∈ Icc c b →
      IntervalIntegrable (fun x => e (G x)) volume u v :=
    fun u v hu hv => (hGc.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  have hQint : ∀ u v : ℝ,
      IntervalIntegrable (fun x => e (G c + G2 c * (x - c) ^ 2 / 2)) volume u v :=
    fun u v => (continuous_e.comp (by fun_prop)).intervalIntegrable _ _
  have hgr := growth_of_deriv_ge G1 G2 c b lam2 hG1 (fun x hx => (hb2 x hx).1)
  have hG1b : G1 b ≤ R * lam2 * (b - c) := by
    have := growth_of_deriv_ge (fun x => -G1 x) (fun x => -G2 x) c b (-(R * lam2))
      (fun x hx => (hG1 x hx).neg) (fun x hx => by linarith [(hb2 x hx).2]) c b hcc hbb hcb
    rw [hc] at this
    linarith
  have hG1b0 : 0 ≤ G1 b := by
    have := hgr c b hcc hbb hcb
    rw [hc] at this
    linarith [mul_nonneg h2.le (sub_nonneg.mpr hcb)]
  -- the comparison with the quadratic phase on `[c, c + d]`
  have hT1 : ‖(∫ x in c..(c + d), e (G x)) -
      ∫ x in c..(c + d), e (G c + G2 c * (x - c) ^ 2 / 2)‖ ≤ 2 * R * ε := by
    rw [← intervalIntegral.integral_sub (hint _ _ hcc hq) (hQint _ _)]
    have tb := taylor_bound G G1 G2 G3 b c (R * lam3) hG hG1 hG2 hb3 hc
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := c + d)
      (C := 2 * Real.pi * (R * lam3 * δ ^ 3 / 6))
      (f := fun x => e (G x) - e (G c + G2 c * (x - c) ^ 2 / 2)) ?_
    · rw [add_sub_cancel_left, abs_of_nonneg hd0] at this
      refine this.trans ?_
      have hπ := Real.pi_le_four
      have e1 : lam3 * δ ^ 3 * d ≤ ε := by
        rw [← h3δ]
        nlinarith [mul_le_mul_of_nonneg_left hdδ (by positivity : 0 ≤ lam3 * δ ^ 3)]
      have e0 : 0 ≤ lam3 * δ ^ 3 * d := by positivity
      have e2 : R * (lam3 * δ ^ 3 * d) ≤ R * ε := mul_le_mul_of_nonneg_left e1 hR0.le
      have e3 : 0 ≤ R * (lam3 * δ ^ 3 * d) := by positivity
      calc 2 * Real.pi * (R * lam3 * δ ^ 3 / 6) * d
          = Real.pi / 3 * (R * (lam3 * δ ^ 3 * d)) := by ring
        _ ≤ 4 / 3 * (R * (lam3 * δ ^ 3 * d)) := by gcongr
        _ ≤ 4 / 3 * (R * ε) := by gcongr
        _ ≤ 2 * R * ε := by nlinarith [mul_pos hR0 hε]
    · intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hxI : x ∈ Icc c b := ⟨hx.1.le, by linarith [hx.2]⟩
      refine (norm_e_sub_le _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ((tb x hxI).trans ?_) Real.two_pi_pos.le
      have hxc0 : 0 ≤ x - c := by linarith [hx.1]
      have hxcδ : x - c ≤ δ := by linarith [hx.2]
      have hp3 : (x - c) ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hxc0 hxcδ 3
      have hL : 0 ≤ R * lam3 := by positivity
      have := mul_le_mul_of_nonneg_left hp3 hL
      linarith
  -- the tail of the integral
  have hT2 : ‖∫ x in (c + d)..b, e (G x)‖ ≤ ε := by
    rcases le_total (b - c) δ with h | h
    · have hcd : c + d = b := by
        rw [hd, min_eq_left h]
        ring
      rw [hcd, intervalIntegral.integral_same, norm_zero]
      exact hε.le
    · have hdd : d = δ := by rw [hd, min_eq_right h]
      have hsub : Icc (c + d) b ⊆ Icc c b := Icc_subset_Icc (by linarith) le_rfl
      have := integral_first_deriv_test G G1 (c + d) b (lam2 * δ) hq.2 (by positivity)
        (fun x hx => hG x (hsub hx))
        (fun x hx => (hG1 x (hsub hx)).continuousAt.continuousWithinAt)
        (Or.inl ((monotoneOn_of_hasDerivAt_nonneg G1 G2 c b hG1
          (fun x hx => h2.le.trans (hb2 x hx).1)).mono hsub))
        (fun x hx => ?_)
      · rwa [hlδ, one_div_one_div] at this
      · have hx' := hsub hx
        have g := hgr c x hcc hx' hx'.1
        rw [hc, sub_zero] at g
        have : lam2 * δ ≤ lam2 * (x - c) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.1]) h2.le
        exact (this.trans g).trans (le_abs_self _)
  -- the tail of the Fresnel integral
  have hT3 : ‖((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * (fres (Real.sqrt (G2 c) * d) - fresJ) *
      e (G c)‖ ≤ 4 * ε + 4 * R / (|G1 b| + Real.sqrt lam2) := by
    rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), norm_sub_rev]
    have hf := fresJ_sub_le (Real.sqrt (G2 c) * d) (by positivity)
    have hden : Real.sqrt (G2 c) * (Real.sqrt (G2 c) * d + 1) = G2 c * d + Real.sqrt (G2 c) := by
      rw [mul_add, ← mul_assoc, Real.mul_self_sqrt hA0.le, mul_one]
    have hb1 : 1 / Real.sqrt (G2 c) * ‖fresJ - fres (Real.sqrt (G2 c) * d)‖ ≤
        4 / (G2 c * d + Real.sqrt (G2 c)) := by
      calc _ ≤ 1 / Real.sqrt (G2 c) * (4 / (Real.sqrt (G2 c) * d + 1)) :=
            mul_le_mul_of_nonneg_left hf (by positivity)
        _ = 4 / (G2 c * d + Real.sqrt (G2 c)) := by
            rw [← hden]
            field_simp
    refine hb1.trans ?_
    have hterm2 : 0 ≤ 4 * R / (|G1 b| + Real.sqrt lam2) := by positivity
    rcases le_total (b - c) δ with h | h
    · have hdd : d = b - c := by rw [hd, min_eq_left h]
      have : 4 / (G2 c * d + Real.sqrt (G2 c)) ≤ 4 * R / (|G1 b| + Real.sqrt lam2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), abs_of_nonneg hG1b0]
        have t : lam2 * (b - c) ≤ G2 c * (b - c) :=
          mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hcb)
        have a1 : G1 b ≤ R * (G2 c * d) := by
          rw [hdd]
          calc G1 b ≤ R * lam2 * (b - c) := hG1b
            _ = R * (lam2 * (b - c)) := by ring
            _ ≤ R * (G2 c * (b - c)) := mul_le_mul_of_nonneg_left t hR0.le
        have a2 : Real.sqrt lam2 ≤ R * Real.sqrt (G2 c) :=
          le_trans hs2A (le_mul_of_one_le_left hsA.le hR)
        linarith
      linarith
    · have hdd : d = δ := by rw [hd, min_eq_right h]
      have : 4 / (G2 c * d + Real.sqrt (G2 c)) ≤ 4 * ε := by
        rw [div_le_iff₀ (by positivity)]
        have e1 : ε * (lam2 * δ) = 1 := by
          rw [hlδ]
          field_simp
        have e2 : lam2 * δ ≤ G2 c * d := by
          rw [hdd]
          exact mul_le_mul_of_nonneg_right hA hδ0.le
        nlinarith [mul_le_mul_of_nonneg_left e2 hε.le, mul_pos hε hsA]
      linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint c (c + d) hcc hq)
    (hint (c + d) b hq hbb)
  have hquad := integral_quadratic (G2 c) c d (G c) hA0
  have hid : (∫ x in c..b, e (G x)) - fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c) =
      ((∫ x in c..(c + d), e (G x)) - ∫ x in c..(c + d), e (G c + G2 c * (x - c) ^ 2 / 2)) +
        (∫ x in (c + d)..b, e (G x)) +
        ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * (fres (Real.sqrt (G2 c) * d) - fresJ) * e (G c) := by
    rw [← hsplit, hquad]
    ring
  rw [hid]
  calc _ ≤ _ := norm_add₃_le
    _ ≤ 2 * R * ε + ε + (4 * ε + 4 * R / (|G1 b| + Real.sqrt lam2)) :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = _ := by ring

theorem rpow_facts (lam2 lam3 : ℝ) (h2 : 0 < lam2) (h3 : 0 < lam3) :
    0 < lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ) ∧
      (lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ)) ^ 5 * lam2 ^ 4 = lam3 := by
  refine ⟨by positivity, ?_⟩
  have e1 : (lam2 ^ (-(4 / 5 : ℝ))) ^ 5 * lam2 ^ 4 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le, ← Real.rpow_natCast lam2 4,
      ← Real.rpow_add h2]
    norm_num
  have e2 : (lam3 ^ (1 / 5 : ℝ)) ^ 5 = lam3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h3.le]
    norm_num
  rw [mul_pow, e2]
  calc (lam2 ^ (-(4 / 5 : ℝ))) ^ 5 * lam3 * lam2 ^ 4
      = (lam2 ^ (-(4 / 5 : ℝ))) ^ 5 * lam2 ^ 4 * lam3 := by ring
    _ = lam3 := by rw [e1, one_mul]

theorem rpow_neg_half (x : ℝ) (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, inv_eq_one_div]

theorem stationary_phase (R : ℝ) (hR : 1 ≤ R) :
    ∃ κ : ℂ, ∃ C : ℝ, 0 < C ∧ ∀ (G G1 G2 G3 : ℝ → ℝ) (a b c lam2 lam3 : ℝ),
      a ≤ c → c ≤ b → 0 < lam2 → 0 < lam3 →
      (∀ x ∈ Set.Icc a b, HasDerivAt G (G1 x) x) →
      (∀ x ∈ Set.Icc a b, HasDerivAt G1 (G2 x) x) →
      (∀ x ∈ Set.Icc a b, HasDerivAt G2 (G3 x) x) →
      (∀ x ∈ Set.Icc a b, lam2 ≤ G2 x ∧ G2 x ≤ R * lam2) →
      (∀ x ∈ Set.Icc a b, |G3 x| ≤ R * lam3) →
      G1 c = 0 →
      ‖(∫ x in a..b, e (G x)) - κ * ((G2 c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * e (G c)‖ ≤
        C * (min (lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ)) (lam2 ^ (-(1 / 2 : ℝ))) +
          1 / (|G1 a| + Real.sqrt lam2) + 1 / (|G1 b| + Real.sqrt lam2)) := by
  refine ⟨2 * fresJ, 4 * R + 12, by linarith, ?_⟩
  intro G G1 G2 G3 a b c lam2 lam3 hac hcb h2 h3 hG hG1 hG2 hb2 hb3 hc
  have hca : c ∈ Icc a b := ⟨hac, hcb⟩
  have hA : lam2 ≤ G2 c := (hb2 c hca).1
  have hA0 : 0 < G2 c := h2.trans_le hA
  have hs2 : 0 < Real.sqrt lam2 := Real.sqrt_pos.mpr h2
  have hsA : 0 < Real.sqrt (G2 c) := Real.sqrt_pos.mpr hA0
  rw [rpow_neg_half _ hA0, rpow_neg_half _ h2]
  obtain ⟨hε0, hε5⟩ := rpow_facts lam2 lam3 h2 h3
  generalize lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ) = ε at hε0 hε5 ⊢
  have ht1 : 0 ≤ 1 / (|G1 a| + Real.sqrt lam2) := by positivity
  have ht2 : 0 ≤ 1 / (|G1 b| + Real.sqrt lam2) := by positivity
  have hC : 0 < 4 * R + 12 := by linarith
  have hGc : ContinuousOn (fun x => e (G x)) (Icc a b) :=
    continuous_e.comp_continuousOn fun x hx => (hG x hx).continuousAt.continuousWithinAt
  rcases le_total (1 / Real.sqrt lam2) ε with hcase | hcase
  · rw [min_eq_right hcase]
    have h44 := integral_second_deriv_test G G1 G2 a b lam2 (hac.trans hcb) h2 hG hG1
      (fun x hx => (hb2 x hx).1)
    have hmain : ‖2 * fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c)‖ ≤
        8 / Real.sqrt lam2 := by
      rw [norm_mul, norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Complex.norm_ofNat]
      have i1 : 1 / Real.sqrt (G2 c) ≤ 1 / Real.sqrt lam2 :=
        one_div_le_one_div_of_le hs2 (Real.sqrt_le_sqrt hA)
      have i2 := norm_fresJ_le
      calc 2 * ‖fresJ‖ * (1 / Real.sqrt (G2 c)) ≤ 2 * 4 * (1 / Real.sqrt lam2) := by gcongr
        _ = 8 / Real.sqrt lam2 := by ring
    have hx0 : 0 ≤ 1 / Real.sqrt lam2 := by positivity
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 4 / Real.sqrt lam2 + 8 / Real.sqrt lam2 := add_le_add h44 hmain
      _ = 12 * (1 / Real.sqrt lam2) := by ring
      _ ≤ _ := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * R) hx0, mul_nonneg hC.le ht1,
            mul_nonneg hC.le ht2]
  · rw [min_eq_left hcase]
    have hsubR : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
    have hr := stationary_half R hR G G1 G2 G3 b c lam2 lam3 ε hcb h2 h3 hε0 hε5
      (fun x hx => hG x (hsubR hx)) (fun x hx => hG1 x (hsubR hx))
      (fun x hx => hG2 x (hsubR hx)) (fun x hx => hb2 x (hsubR hx))
      (fun x hx => hb3 x (hsubR hx)) hc
    have hmem : ∀ y ∈ Icc c (2 * c - a), 2 * c - y ∈ Icc a b := fun y hy =>
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have e1 : (2 : ℝ) * c - c = c := by ring
    have e2 : (2 : ℝ) * c - (2 * c - a) = a := by ring
    have hl := stationary_half R hR (fun y => G (2 * c - y)) (fun y => -G1 (2 * c - y))
      (fun y => G2 (2 * c - y)) (fun y => -G3 (2 * c - y)) (2 * c - a) c lam2 lam3 ε
      (by linarith) h2 h3 hε0 hε5
      (fun y hy => (hG _ (hmem y hy)).comp_const_sub (2 * c) y)
      (fun y hy => by
        have := ((hG1 _ (hmem y hy)).comp_const_sub (2 * c) y).neg
        rwa [neg_neg] at this)
      (fun y hy => (hG2 _ (hmem y hy)).comp_const_sub (2 * c) y)
      (fun y hy => hb2 _ (hmem y hy))
      (fun y hy => by
        rw [abs_neg]
        exact hb3 _ (hmem y hy))
      (by rw [e1, hc, neg_zero])
    simp only [e1, e2, abs_neg] at hl
    have hrefl : ∫ y in c..(2 * c - a), e (G (2 * c - y)) = ∫ x in a..c, e (G x) := by
      have := intervalIntegral.integral_comp_sub_left (a := c) (b := 2 * c - a)
        (fun x => e (G x)) (2 * c)
      rw [e1, e2] at this
      exact this
    rw [hrefl] at hl
    have hint : ∀ u v, u ∈ Icc a b → v ∈ Icc a b →
        IntervalIntegrable (fun x => e (G x)) volume u v :=
      fun u v hu hv => (hGc.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint a c ⟨le_rfl, hac.trans hcb⟩ hca) (hint c b hca ⟨hac.trans hcb, le_rfl⟩)
    have hid : (∫ x in a..b, e (G x)) - 2 * fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c) =
        ((∫ x in a..c, e (G x)) - fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c)) +
          ((∫ x in c..b, e (G x)) - fresJ * ((1 / Real.sqrt (G2 c) : ℝ) : ℂ) * e (G c)) := by
      rw [← hsplit]
      ring
    rw [hid]
    have r1 : 4 * R / (|G1 a| + Real.sqrt lam2) = 4 * R * (1 / (|G1 a| + Real.sqrt lam2)) := by
      ring
    have r2 : 4 * R / (|G1 b| + Real.sqrt lam2) = 4 * R * (1 / (|G1 b| + Real.sqrt lam2)) := by
      ring
    rw [r1] at hl
    rw [r2] at hr
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ((2 * R + 5) * ε + 4 * R * (1 / (|G1 a| + Real.sqrt lam2))) +
          ((2 * R + 5) * ε + 4 * R * (1 / (|G1 b| + Real.sqrt lam2))) := add_le_add hl hr
      _ ≤ _ := by nlinarith

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl
alias stationary_phase := GuthMaynard.SubWeyl.PartB.stationary_phase

end GuthMaynard.SubWeyl
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.SubWeyl.PartC
open GuthMaynard.SubWeyl
/-!
# Part C: truncated Poisson summation (Titchmarsh, Lemma 4.7 with `η = 1/2`)

Euler–Maclaurin, the Fourier polynomial of the sawtooth with an `L²`-small remainder, the
first-derivative test (`integral_first_deriv_test`) for the frequencies near the range, and the
first-derivative test with the monotone amplitude `f'` for the far frequencies.
-/
/-! ### The sawtooth and its Fourier polynomial -/
/-- The sawtooth `ψ(x) = x - ⌊x⌋ - 1/2`. -/
noncomputable def saw (x : ℝ) : ℝ := x - ⌊x⌋ - 1 / 2

/-- `e(μx)`. -/
noncomputable def E (μ : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I)

/-- `2πiμ`. -/
noncomputable def dd (μ : ℤ) : ℂ := 2 * π * (μ : ℂ) * I

/-- The Fourier polynomial `∑_{1 ≤ |μ| ≤ K} e(μx)/(2πiμ)`. -/
noncomputable def P (K : ℕ) (x : ℝ) : ℂ := ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, E μ x / dd μ

/-- `ψ(x) + ∑_{1 ≤ |μ| ≤ K} e(μx)/(2πiμ)`, the remainder of the degree-`K` Fourier polynomial. -/
noncomputable def sawTail (K : ℕ) (x : ℝ) : ℂ := (saw x : ℂ) + P K x

lemma sawTail_eq (K : ℕ) (x : ℝ) : sawTail K x = (saw x : ℂ) + P K x := rfl

lemma ii_bdd {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded ?_ hf (M := M)
    (ae_of_all _ (fun x => hM x))
  rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

lemma saw_meas : Measurable (fun x => ((saw x : ℝ) : ℂ)) := by unfold saw; fun_prop

lemma norm_saw_le (x : ℝ) : ‖((saw x : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold saw; constructor <;> linarith

lemma ii_saw (a b : ℝ) : IntervalIntegrable (fun x => ((saw x : ℝ) : ℂ)) volume a b :=
  ii_bdd saw_meas.aestronglyMeasurable norm_saw_le a b

lemma saw_eq_on (n : ℤ) (x : ℝ) (h1 : (n : ℝ) ≤ x) (h2 : x < n + 1) : saw x = x - n - 1 / 2 := by
  unfold saw; rw [Int.floor_eq_iff.2 ⟨h1, h2⟩]

lemma sum_S {M : Type*} [AddCommMonoid M] (f : ℤ → M) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ = ∑ n ∈ range K, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have : (Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)).erase 0 =
        insert ((K : ℤ) + 1) (insert (-((K : ℤ) + 1)) ((Icc (-(K : ℤ)) K).erase 0)) := by
      ext μ; simp only [mem_erase, mem_Icc, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp only [mem_erase, mem_Icc, mem_insert]; omega),
      sum_insert (by simp only [mem_erase, mem_Icc]; omega), ih, sum_range_succ]
    abel

lemma sum_S_neg {M : Type*} [AddCommMonoid M] (f : ℤ → M) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f (-μ) = ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ := by
  rw [sum_S (fun μ => f (-μ)), sum_S]
  refine sum_congr rfl (fun n _ => ?_)
  simp only [neg_neg]; exact add_comm _ _

lemma sum_S_odd {G : Type*} [AddCommGroup G] (f : ℤ → G) (hf : ∀ μ, f (-μ) = -f μ) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ = 0 := by
  rw [sum_S]
  refine sum_eq_zero (fun n _ => ?_)
  rw [hf]; simp

lemma E_nat (μ : ℤ) (n : ℕ) : E μ ((n : ℕ) : ℝ) = 1 := by
  unfold E
  rw [← Complex.exp_int_mul_two_pi_mul_I (μ * n)]; congr 1; push_cast; ring

lemma hasDerivAt_E (μ : ℤ) (x : ℝ) : HasDerivAt (E μ) (E μ x * dd μ) x := by
  have h : HasDerivAt (fun y : ℝ => 2 * π * (μ : ℂ) * (y : ℂ) * I)
      (2 * π * (μ : ℂ) * ((1 : ℝ) : ℂ) * I) x :=
    ((hasDerivAt_id' x).ofReal_comp.const_mul (2 * π * (μ : ℂ))).mul_const I
  show HasDerivAt (fun y : ℝ => Complex.exp (2 * π * (μ : ℂ) * (y : ℂ) * I)) _ x
  convert h.cexp using 1
  unfold E dd; push_cast; ring

/-! ### The `L²` norm of the tail on `[0, 1]` -/
lemma dd_ne (μ : ℤ) (hμ : μ ≠ 0) : dd μ ≠ 0 := by
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [dd, hμ0, this, Complex.I_ne_zero]

lemma contE' (μ : ℤ) : Continuous (E μ) := by unfold E; fun_prop

lemma contP (K : ℕ) : Continuous (P K) := by
  unfold P; exact continuous_finsetSum _ (fun μ _ => (contE' μ).div_const _)

lemma E_add (μ ν : ℤ) (x : ℝ) : E μ x * E ν x = E (μ + ν) x := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma intE (j : ℤ) : ∫ x in (0 : ℝ)..1, E j x = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · subst hj; simp [E]
  · have hc : (2 * π * (j : ℂ) * I) ≠ 0 := dd_ne j hj
    have : ∀ x : ℝ, E j x = Complex.exp ((2 * π * (j : ℂ) * I) * (x : ℂ)) := by
      intro x; unfold E; ring_nf
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * (j : ℂ) * I) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I j]; congr 1; push_cast; ring
    rw [h1]; simp

lemma intSawE (μ : ℤ) (hμ : μ ≠ 0) :
    ∫ x in (0 : ℝ)..1, (saw x : ℂ) * E μ x = 1 / dd μ := by
  have hd := dd_ne μ hμ
  have hcongr : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * E μ x =
      ∫ x in (0 : ℝ)..1, ((x : ℂ) - 1 / 2) * E μ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    have := saw_eq_on 0 x (by exact_mod_cast hmem.1.le)
      (by have := lt_of_le_of_ne hmem.2 hx; push_cast; linarith)
    rw [this]; push_cast; ring
  rw [hcongr]
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (x : ℂ) - 1 / 2) 1 x := by
    intro x _
    exact (hasDerivAt_id x).ofReal_comp.sub_const _
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x => E μ x / dd μ) (E μ x) x := by
    intro x _
    have h2 : HasDerivAt (fun x => E μ x / dd μ) (E μ x * dd μ / dd μ) x :=
      (hasDerivAt_E μ x).div_const (dd μ)
    rwa [mul_div_cancel_right₀ _ hd] at h2
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
    ((contE' μ).intervalIntegrable _ _)]
  simp only [one_mul]
  rw [intervalIntegral.integral_div, intE, if_neg hμ]
  have h0 : E μ 0 = 1 := by simp [E]
  have h1 : E μ 1 = 1 := by
    have := E_nat μ 1; simpa [E] using this
  rw [h0, h1]; push_cast; field_simp; ring

lemma intSaw2 : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * (saw x : ℂ) = 1 / 12 := by
  have hcongr : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * (saw x : ℂ) =
      ∫ x in (0 : ℝ)..1, (((x - 1 / 2) ^ 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    have := saw_eq_on 0 x (by exact_mod_cast hmem.1.le)
      (by have := lt_of_le_of_ne hmem.2 hx; push_cast; linarith)
    rw [this]; push_cast; ring
  rw [hcongr, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) (1 / 2), integral_pow]
  norm_num

lemma conj_E (μ : ℤ) (x : ℝ) : (starRingEnd ℂ) (E μ x) = E (-μ) x := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  push_cast; ring

lemma conj_dd (μ : ℤ) : (starRingEnd ℂ) (dd μ) = dd (-μ) := by
  unfold dd
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  push_cast; ring

lemma conj_P (K : ℕ) (x : ℝ) : (starRingEnd ℂ) (P K x) = P K x := by
  unfold P
  rw [map_sum]
  simp_rw [map_div₀, conj_E, conj_dd]
  exact sum_S_neg (fun μ => E μ x / dd μ) K

lemma normSq_R (K : ℕ) (x : ℝ) : ((‖sawTail K x‖ ^ 2 : ℝ) : ℂ) = sawTail K x * sawTail K x := by
  have h := Complex.mul_conj' (sawTail K x)
  have hc : (starRingEnd ℂ) (sawTail K x) = sawTail K x := by
    rw [sawTail_eq, map_add, conj_P, Complex.conj_ofReal]
  rw [hc] at h
  rw [h]; push_cast; ring

lemma ii_sawsaw : IntervalIntegrable (fun x => (saw x : ℂ) * (saw x : ℂ)) volume 0 1 := by
  refine ii_bdd (f := fun x => (saw x : ℂ) * (saw x : ℂ))
    (saw_meas.mul saw_meas).aestronglyMeasurable (M := 1 * 1) (fun x => ?_) 0 1
  rw [norm_mul]
  exact mul_le_mul (norm_saw_le x) (norm_saw_le x) (norm_nonneg _) zero_le_one

lemma intR2 (K : ℕ) : ∫ x in (0 : ℝ)..1, sawTail K x * sawTail K x =
    1 / 12 + ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
  have hexp : ∀ x, sawTail K x * sawTail K x = (saw x : ℂ) * (saw x : ℂ) +
      (2 * ((saw x : ℂ) * P K x) + P K x * P K x) := by
    intro x; rw [sawTail_eq]; ring
  simp_rw [hexp]
  have ii2 : IntervalIntegrable (fun x => 2 * ((saw x : ℂ) * P K x)) volume 0 1 :=
    ((ii_saw 0 1).mul_continuousOn (contP K).continuousOn).const_mul 2
  have ii3 : IntervalIntegrable (fun x => P K x * P K x) volume 0 1 :=
    ((contP K).mul (contP K)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add ii_sawsaw (ii2.add ii3), intervalIntegral.integral_add ii2 ii3,
    intervalIntegral.integral_const_mul, intSaw2]
  have hSP : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * P K x =
      ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
    have : ∀ x, (saw x : ℂ) * P K x =
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * ((saw x : ℂ) * E μ x) := by
      intro x; unfold P; rw [mul_sum]; exact sum_congr rfl (fun μ _ => by ring)
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum
      (fun μ _ => ((ii_saw 0 1).mul_continuousOn (contE' μ).continuousOn).const_mul _)]
    refine sum_congr rfl (fun μ hμ => ?_)
    rw [intervalIntegral.integral_const_mul, intSawE μ (mem_erase.1 hμ).1]; ring
  have hPP : ∫ x in (0 : ℝ)..1, P K x * P K x =
      -∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
    have : ∀ x, P K x * P K x = ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0,
        ∑ ν ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (dd μ * dd ν)) * E (μ + ν) x := by
      intro x; unfold P; rw [sum_mul_sum]
      refine sum_congr rfl (fun μ _ => sum_congr rfl (fun ν _ => ?_))
      rw [← E_add]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum
      (f := fun μ x => ∑ ν ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (dd μ * dd ν)) * E (μ + ν) x)
      (fun μ _ => (continuous_finsetSum _ (fun ν _ => continuous_const.mul (contE' _))).intervalIntegrable 0 1)]
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun μ hμ => ?_)
    rw [intervalIntegral.integral_finsetSum (f := fun ν x => (1 / (dd μ * dd ν)) * E (μ + ν) x)
      (fun ν _ => (continuous_const.mul (contE' _)).intervalIntegrable 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, intE]
    rw [sum_eq_single (-μ)]
    · rw [if_pos (by ring)]
      have : dd (-μ) = -dd μ := by unfold dd; push_cast; ring
      rw [this]; ring
    · intro ν _ hne
      rw [if_neg (by omega)]; simp
    · intro h; exfalso; apply h
      simp only [mem_erase, mem_Icc] at hμ ⊢; omega
  rw [hSP, hPP]; ring

lemma sum_inv_dd2 (K : ℕ) : ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 =
    ((-(1 / (2 * π ^ 2)) * ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  rw [sum_S, Complex.ofReal_mul, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl (fun n _ => ?_)
  have key : ∀ m : ℂ, (2 * π * m * I) ^ 2 = -(4 * π ^ 2 * m ^ 2) := by
    intro m; ring_nf; rw [Complex.I_sq]; ring
  have hm : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold dd
  push_cast
  rw [key, key]
  field_simp
  ring

lemma zeta_tail (K : ℕ) : π ^ 2 / 6 ≤ ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 + 2 / ((K : ℝ) + 1) := by
  apply le_of_tendsto' hasSum_zeta_two.tendsto_sum_nat
  intro m
  have h1 : ∑ i ∈ range m, 1 / (i : ℝ) ^ 2 ≤ ∑ i ∈ range (m + (K + 1)), 1 / (i : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun _ _ _ => by positivity)
  rw [← sum_range_add_sum_Ico _ (show K + 1 ≤ m + (K + 1) by omega), sum_range_succ'] at h1
  have h2 : ∑ i ∈ Ico (K + 1) (m + (K + 1)), 1 / (i : ℝ) ^ 2 ≤ 2 / ((K : ℝ) + 1) := by
    have := sum_Ioo_inv_sq_le (α := ℝ) K (m + (K + 1))
    have e : Ioo K (m + (K + 1)) = Ico (K + 1) (m + (K + 1)) := by
      ext i; simp only [mem_Ioo, mem_Ico]; omega
    rw [e] at this
    simpa [one_div] using this
  push_cast at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    div_zero, add_zero] at h1
  linarith

lemma meas_sawTail (K : ℕ) : Measurable (sawTail K) := by
  unfold sawTail saw P E dd; fun_prop

lemma norm_E (μ : ℤ) (x : ℝ) : ‖E μ x‖ = 1 := by
  have : E μ x = Complex.exp (((2 * π * μ * x : ℝ) : ℂ) * I) := by unfold E; push_cast; ring_nf
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_dd_ge (μ : ℤ) (hμ : μ ≠ 0) : 1 ≤ ‖dd μ‖ := by
  unfold dd
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le]
  have : (1 : ℝ) ≤ |(μ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hμ
  nlinarith [Real.pi_gt_three]

lemma norm_sawTail_le (K : ℕ) (x : ℝ) :
    ‖sawTail K x‖ ≤ 1 + ((Icc (-(K : ℤ)) K).erase 0).card := by
  rw [sawTail_eq]
  refine (norm_add_le _ _).trans (add_le_add (norm_saw_le x) ?_)
  unfold P
  refine (norm_sum_le _ _).trans ?_
  have : ∀ μ ∈ (Icc (-(K : ℤ)) K).erase 0, ‖E μ x / dd μ‖ ≤ 1 := by
    intro μ hμ
    rw [norm_div, norm_E, div_le_one (by linarith [norm_dd_ge μ (mem_erase.1 hμ).1])]
    exact norm_dd_ge μ (mem_erase.1 hμ).1
  refine (sum_le_sum this).trans ?_
  simp

lemma iiN (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun x => ‖sawTail K x‖) volume a b :=
  ii_bdd (meas_sawTail K).norm.aestronglyMeasurable (fun x => by
    rw [norm_norm]; exact norm_sawTail_le K x) a b

lemma iiN2 (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun x => ‖sawTail K x‖ ^ 2) volume a b := by
  refine ii_bdd ((meas_sawTail K).norm.pow_const 2).aestronglyMeasurable
    (M := (1 + ((Icc (-(K : ℤ)) K).erase 0).card) ^ 2) (fun x => ?_) a b
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sawTail_le K x) 2

lemma int_normsq (K : ℕ) (hK : 1 ≤ K) : ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2 ≤ 1 / K := by
  have h : ((∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2 : ℝ) : ℂ) =
      ((1 / 12 + -(1 / (2 * π ^ 2)) * ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_R]
    rw [intR2, sum_inv_dd2]; push_cast; ring
  have h' := Complex.ofReal_injective h
  rw [h']
  have hz := zeta_tail K
  have hπ : 0 < π ^ 2 := by positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 : (1 / (2 * π ^ 2)) * (π ^ 2 / 6) = 1 / 12 := by field_simp; ring
  have e2 : (1 / (2 * π ^ 2)) * (2 / ((K : ℝ) + 1)) = 1 / (π ^ 2 * ((K : ℝ) + 1)) := by
    field_simp
  have m := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1 / (2 * π ^ 2) by positivity)
  rw [mul_add, e1, e2] at m
  have h3 : 1 / (π ^ 2 * ((K : ℝ) + 1)) ≤ 1 / (K : ℝ) :=
    one_div_le_one_div_of_le hK0 (by
      have : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right this (show (0:ℝ) ≤ K + 1 by positivity)])
  linarith

lemma int_norm (K : ℕ) (hK : 1 ≤ K) : ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ≤ 1 / Real.sqrt K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set r := Real.sqrt K with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hK0
  have hr2 : r ^ 2 = K := Real.sq_sqrt hK0.le
  have hpt : ∀ x, ‖sawTail K x‖ ≤ (r / 2) * ‖sawTail K x‖ ^ 2 + 1 / (2 * r) := by
    intro x
    set y := ‖sawTail K x‖
    rw [← sub_nonneg]
    have : (r / 2) * y ^ 2 + 1 / (2 * r) - y = (r * y - 1) ^ 2 / (2 * r) := by
      field_simp; ring
    rw [this]; positivity
  calc ∫ x in (0 : ℝ)..1, ‖sawTail K x‖
      ≤ ∫ x in (0 : ℝ)..1, ((r / 2) * ‖sawTail K x‖ ^ 2 + 1 / (2 * r)) :=
        intervalIntegral.integral_mono_on (by norm_num) (iiN K 0 1)
          (((iiN2 K 0 1).const_mul _).add intervalIntegrable_const) (fun x _ => hpt x)
    _ = (r / 2) * (∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2) + 1 / (2 * r) := by
        rw [intervalIntegral.integral_add ((iiN2 K 0 1).const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp
    _ ≤ (r / 2) * (1 / K) + 1 / (2 * r) := by gcongr; exact int_normsq K hK
    _ = 1 / r := by rw [← hr2]; field_simp; ring

lemma saw_periodic (x : ℝ) : saw (x + 1) = saw x := by
  unfold saw; rw [Int.floor_add_one]; push_cast; ring

lemma E_periodic (μ : ℤ) (x : ℝ) : E μ (x + 1) = E μ x := by
  unfold E
  have : 2 * π * (μ : ℂ) * (((x + 1 : ℝ)) : ℂ) * I = 2 * π * (μ : ℂ) * (x : ℂ) * I + μ * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma sawTail_periodic (K : ℕ) : Function.Periodic (fun x => ‖sawTail K x‖) 1 := by
  intro x
  simp only [sawTail_eq, P, saw_periodic, E_periodic]

lemma int_ab (K : ℕ) (a b : ℕ) (hab : a ≤ b) :
    ∫ x in (a : ℝ)..b, ‖sawTail K x‖ = ((b : ℝ) - a) * ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := (sawTail_periodic K).intervalIntegral_add_eq (b : ℝ) 0
    rw [zero_add] at this
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals (iiN K a b) (iiN K b (b + 1)), ih, this]
    ring

/-! ### The phase `e ∘ f` -/
lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e; exact Complex.norm_exp_ofReal_mul_I _

lemma cont_e : Continuous e := by
  unfold e; fun_prop

lemma hasDerivAt_e {G : ℝ → ℝ} {G' x : ℝ} (h : HasDerivAt G G' x) :
    HasDerivAt (fun y => e (G y)) (((2 * π * G' : ℝ) : ℂ) * I * e (G x)) x := by
  have h1 : HasDerivAt (fun y => 2 * π * G y) (2 * π * G') x := h.const_mul (2 * π)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  show HasDerivAt (fun y => Complex.exp (((2 * π * G y : ℝ) : ℂ) * I)) _ x
  convert h2 using 1
  rw [e]; ring

/-- The derivative of `e ∘ f`. -/
noncomputable def gd (f f1 : ℝ → ℝ) (x : ℝ) : ℂ := ((2 * π * f1 x : ℝ) : ℂ) * I * e (f x)

lemma contOn_f {f f1 : ℝ → ℝ} {A B : ℝ} (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f1 x) x) :
    ContinuousOn f (Set.Icc A B) :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt

lemma contOn_ef {f f1 : ℝ → ℝ} {A B : ℝ} (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f1 x) x) :
    ContinuousOn (fun x => e (f x)) (Set.Icc A B) :=
  fun x hx => (hasDerivAt_e (hf x hx)).continuousAt.continuousWithinAt

lemma contOn_gd {f f1 : ℝ → ℝ} {A B : ℝ} (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc A B)) : ContinuousOn (gd f f1) (Set.Icc A B) := by
  have h1 : ContinuousOn (fun x => ((2 * π * f1 x : ℝ) : ℂ)) (Set.Icc A B) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hc)
  exact (h1.mul continuousOn_const).mul (contOn_ef hf)

lemma ii_saw_gd {f f1 : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hf : ∀ x ∈ Set.Icc A B, HasDerivAt f (f1 x) x) (hc : ContinuousOn f1 (Set.Icc A B)) :
    IntervalIntegrable (fun x => ((saw x : ℝ) : ℂ) * gd f f1 x) volume A B :=
  (ii_saw A B).mul_continuousOn (by rw [Set.uIcc_of_le hAB]; exact contOn_gd hf hc)

lemma E_mul_e (μ : ℤ) (y x : ℝ) : E μ x * e y = e (y - ((-μ : ℤ) : ℝ) * x) := by
  unfold E e
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma e_sub_int (y : ℝ) (k : ℤ) (n : ℕ) : e (y - k * n) = e y := by
  have h : ((2 * π * (y - k * n) : ℝ) : ℂ) * I =
      ((2 * π * y : ℝ) : ℂ) * I + ((-(k * n) : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [e, e, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Euler–Maclaurin -/
lemma em_unit (f f1 : ℝ → ℝ) (n : ℕ)
    (hf : ∀ x ∈ Set.Icc (n : ℝ) (n + 1), HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc (n : ℝ) (n + 1))) :
    ∫ x in (n : ℝ)..(n + 1), ((saw x : ℝ) : ℂ) * gd f f1 x =
      (e (f n) + e (f (n + 1))) / 2 - ∫ x in (n : ℝ)..(n + 1), e (f x) := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hcongr : ∫ x in (n : ℝ)..(n + 1), ((saw x : ℝ) : ℂ) * gd f f1 x =
      ∫ x in (n : ℝ)..(n + 1), ((x : ℂ) - n - 1 / 2) * gd f f1 x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume ((n : ℝ) + 1)] with x hx hmem
    rw [Set.uIoc_of_le hle] at hmem
    have := saw_eq_on (n : ℤ) x (by exact_mod_cast hmem.1.le)
      (by push_cast; exact lt_of_le_of_ne hmem.2 hx)
    rw [this]; push_cast; ring
  rw [hcongr]
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun x : ℝ => (x : ℂ) - n - 1 / 2) 1 x := by
    intro x _
    exact ((hasDerivAt_id x).ofReal_comp.sub_const _).sub_const _
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun x => e (f x)) (gd f f1 x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hasDerivAt_e (hf x hx)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
    ((contOn_gd hf hc).intervalIntegrable_of_Icc hle)]
  simp only [one_mul]
  push_cast; ring

theorem em_identity (f f1 : ℝ → ℝ) (a : ℕ) : ∀ b : ℕ, a ≤ b →
    (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
    ContinuousOn f1 (Set.Icc (a : ℝ) b) →
    ∑ n ∈ Finset.Ioc a b, e (f n) =
      (∫ x in (a : ℝ)..b, e (f x))
        + (∫ x in (a : ℝ)..b, ((saw x : ℝ) : ℂ) * gd f f1 x)
        + (e (f b) - e (f a)) / 2 := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ _; simp
  | succ b hab ih =>
    intro hf hc
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hsub1 : Set.Icc (a : ℝ) b ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc le_rfl (by push_cast; linarith)
    have hsub2 : Set.Icc (b : ℝ) (b + 1) ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc habR (by push_cast; linarith)
    have hf1 : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x := fun x hx => hf x (hsub1 hx)
    have hf2 : ∀ x ∈ Set.Icc (b : ℝ) (b + 1), HasDerivAt f (f1 x) x := fun x hx => hf x (hsub2 hx)
    have hle : (b : ℝ) ≤ b + 1 := by linarith
    have e1 := intervalIntegral.integral_add_adjacent_intervals
        ((contOn_ef hf1).intervalIntegrable_of_Icc (μ := volume) habR)
        ((contOn_ef hf2).intervalIntegrable_of_Icc (μ := volume) hle)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
        (ii_saw_gd habR hf1 (hc.mono hsub1)) (ii_saw_gd hle hf2 (hc.mono hsub2))
    have e3 := em_unit f f1 b hf2 (hc.mono hsub2)
    rw [Finset.sum_Ioc_succ_top hab, ih hf1 (hc.mono hsub1)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← e1, ← e2, e3]
    ring

/-! ### The sawtooth expansion -/
lemma ibp_mu (f f1 : ℝ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc (a : ℝ) b)) (μ : ℤ) :
    ∫ x in (a : ℝ)..b, E μ x * gd f f1 x
      = e (f b) - e (f a) - dd μ * ∫ x in (a : ℝ)..b, e (f x - ((-μ : ℤ) : ℝ) * x) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hv : ∀ x ∈ Set.uIcc (a : ℝ) b, HasDerivAt (fun x => e (f x)) (gd f f1 x) x := by
    intro x hx
    rw [Set.uIcc_of_le habR] at hx
    exact hasDerivAt_e (hf x hx)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hasDerivAt_E μ x) hv
    (((contE' μ).mul continuous_const).intervalIntegrable _ _)
    ((contOn_gd hf hc).intervalIntegrable_of_Icc habR)]
  rw [E_nat, E_nat]
  have : ∀ x : ℝ, E μ x * dd μ * e (f x) = dd μ * e (f x - ((-μ : ℤ) : ℝ) * x) := by
    intro x; rw [← E_mul_e]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma tail_split (f f1 : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc a b)) (K : ℕ) :
    ∫ x in a..b, sawTail K x * gd f f1 x =
      (∫ x in a..b, ((saw x : ℝ) : ℂ) * gd f f1 x) +
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * ∫ x in a..b, E μ x * gd f f1 x := by
  have hg : ContinuousOn (gd f f1) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]; exact contOn_gd hf hc
  have hsplit : ∀ x : ℝ, sawTail K x * gd f f1 x = ((saw x : ℝ) : ℂ) * gd f f1 x +
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * (E μ x * gd f f1 x) := by
    intro x
    unfold sawTail P
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine sum_congr rfl (fun μ _ => ?_)
    ring
  have hcont : ∀ μ : ℤ, ContinuousOn (fun x : ℝ => (1 / dd μ) * (E μ x * gd f f1 x))
      (Set.uIcc a b) := fun μ =>
    continuousOn_const.mul ((contE' μ).continuousOn.mul hg)
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add ((ii_saw a b).mul_continuousOn hg)
      ((continuousOn_finsetSum _ (fun μ _ => hcont μ)).intervalIntegrable),
    intervalIntegral.integral_finsetSum (fun μ _ => (hcont μ).intervalIntegrable)]
  congr 1
  refine sum_congr rfl (fun μ _ => ?_)
  rw [intervalIntegral.integral_const_mul]

/-- The exact identity behind the lemma: Euler–Maclaurin and the sawtooth expansion, with the
frequencies `|ν| ≤ V` integrated back by parts. -/
lemma main_ident (f f1 : ℝ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc (a : ℝ) b)) (V K : ℕ) :
    ∑ n ∈ Finset.Ioc a b, e (f n) =
      ∑ ν ∈ Icc (-(V : ℤ)) V, (∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x))
      + (e (f b) - e (f a)) / 2
      + (∫ x in (a : ℝ)..b, sawTail K x * gd f f1 x)
      - ((∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x)
         - (∑ μ ∈ (Icc (-(V : ℤ)) V).erase 0,
            (1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x)) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have em := em_identity f f1 a b hab hf hc
  have hT := tail_split f f1 a b habR hf hc K
  have hI : ∀ μ ∈ (Icc (-(V : ℤ)) V).erase 0,
      (1 / dd μ) * (∫ x in (a : ℝ)..b, E μ x * gd f f1 x) =
      (e (f b) - e (f a)) / dd μ - ∫ x in (a : ℝ)..b, e (f x - ((-μ : ℤ) : ℝ) * x) := by
    intro μ hμ
    have hd := dd_ne μ (mem_erase.1 hμ).1
    rw [ibp_mu f f1 a b hab hf hc μ]
    field_simp
  have hodd := sum_S_odd (fun μ : ℤ => (e (f b) - e (f a)) / dd μ)
    (fun μ => by unfold dd; push_cast; ring) V
  have hneg := sum_S_neg (fun ν : ℤ => ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) V
  beta_reduce at hodd hneg
  have hV : ∑ μ ∈ (Icc (-(V : ℤ)) V).erase 0,
      (1 / dd μ) * (∫ x in (a : ℝ)..b, E μ x * gd f f1 x) =
      -∑ ν ∈ (Icc (-(V : ℤ)) V).erase 0, ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x) := by
    rw [sum_congr rfl hI, sum_sub_distrib, hodd, hneg]
    ring
  have h0mem : (0 : ℤ) ∈ Icc (-(V : ℤ)) V := by
    simp only [mem_Icc]; constructor <;> omega
  have h0 : ∑ ν ∈ Icc (-(V : ℤ)) V, (∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) =
      (∫ x in (a : ℝ)..b, e (f x)) +
        ∑ ν ∈ (Icc (-(V : ℤ)) V).erase 0, ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x) := by
    rw [← Finset.add_sum_erase _ _ h0mem]
    simp
  rw [em, h0, hT, hV]
  ring

/-! ### The tail term -/
theorem tail_term_le (f f1 : ℝ → ℝ) (a b K : ℕ) (hab : a ≤ b) (hK : 1 ≤ K) (Bd : ℝ)
    (hB : ∀ x ∈ Set.Icc (a : ℝ) b, |f1 x| ≤ Bd) :
    ‖∫ x in (a : ℝ)..b, sawTail K x * gd f f1 x‖ ≤
      2 * π * Bd * (b - a) / Real.sqrt K := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hle : ‖∫ x in (a : ℝ)..b, sawTail K x * gd f f1 x‖ ≤
      ∫ x in (a : ℝ)..b, ‖sawTail K x‖ * (2 * π * Bd) := by
    refine intervalIntegral.norm_integral_le_of_norm_le habR (ae_of_all _ (fun x hx => ?_))
      ((iiN K a b).mul_const _)
    have hx' : x ∈ Set.Icc (a : ℝ) b := ⟨hx.1.le, hx.2⟩
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold gd
    rw [norm_mul, norm_mul, Complex.norm_I, norm_e, Complex.norm_real, mul_one, mul_one,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    exact mul_le_mul_of_nonneg_left (hB x hx') (by positivity)
  refine hle.trans ?_
  rw [intervalIntegral.integral_mul_const, int_ab K a b hab]
  have := int_norm K hK
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hB a ⟨le_rfl, habR⟩)
  calc ((b : ℝ) - a) * (∫ x in (0 : ℝ)..1, ‖sawTail K x‖) * (2 * π * Bd)
      ≤ ((b : ℝ) - a) * (1 / Real.sqrt K) * (2 * π * Bd) := by gcongr
    _ = 2 * π * Bd * (b - a) / Real.sqrt K := by ring

/-! ### The first-derivative test with a monotone amplitude -/
lemma abel_sum (c Ψ : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ range n, c i * (Ψ i - Ψ (i + 1)) =
      c 0 * Ψ 0 - c n * Ψ n + ∑ i ∈ range n, (c (i + 1) - c i) * Ψ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring

/-- Second mean value theorem in the form needed: a monotone continuous amplitude `h` against
`φ` whose integrals over terminal subintervals are bounded by `M`. -/
lemma amp (h : ℝ → ℝ) (φ : ℝ → ℂ) (a b M : ℝ) (hab : a ≤ b)
    (hh : ContinuousOn h (Set.Icc a b)) (hmono : MonotoneOn h (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b)) (hφ1 : ∀ x ∈ Set.Icc a b, ‖φ x‖ ≤ 1)
    (hM : ∀ u ∈ Set.Icc a b, ‖∫ x in u..b, φ x‖ ≤ M) :
    ‖∫ x in a..b, ((h x : ℝ) : ℂ) * φ x‖ ≤ M * (|h a| + (h b - h a)) := by
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b hbmem)
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / (b - a + 1) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hε'le : ε' * (b - a) ≤ ε := by
    rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hh) ε' hε'0
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (b - a) / n := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hdδ : d < δ := by
    rw [hd, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  have hnd : (n : ℝ) * d = b - a := by rw [hd]; field_simp
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ i, x i = a + i * d := ⟨_, fun _ => rfl⟩
  have hx0 : x 0 = a := by rw [hx]; simp
  have hxn : x n = b := by rw [hx, hnd]; ring
  have hxstep : ∀ i, x (i + 1) - x i = d := by
    intro i; rw [hx, hx]; push_cast; ring
  have hxmono : ∀ i, x i ≤ x (i + 1) := fun i => by linarith [hxstep i]
  have hxmem : ∀ i ≤ n, x i ∈ Set.Icc a b := by
    intro i hi
    have h1 : (i : ℝ) ≤ n := by exact_mod_cast hi
    have h2 : (i : ℝ) * d ≤ n * d := mul_le_mul_of_nonneg_right h1 hd0
    have h3 : 0 ≤ (i : ℝ) * d := by positivity
    rw [hx]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℂ, ∀ u, Ψ u = ∫ y in u..b, φ y := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ i, c i = ((h (x i) : ℝ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℂ, ∀ i, R i =
      ∫ y in (x i)..(x (i + 1)), (((h y : ℝ) : ℂ) - c i) * φ y := ⟨_, fun _ => rfl⟩
  have iiφ : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, IntervalIntegrable φ volume u v :=
    fun u hu v hv => (hφ.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have hprod : ContinuousOn (fun y => ((h y : ℝ) : ℂ) * φ y) (Set.Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hh).mul hφ
  have iihφ : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      IntervalIntegrable (fun y => ((h y : ℝ) : ℂ) * φ y) volume u v :=
    fun u hu v hv => (hprod.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have hpiece : ∀ i < n, ∫ y in (x i)..(x (i + 1)), ((h y : ℝ) : ℂ) * φ y =
      c i * (Ψ (x i) - Ψ (x (i + 1))) + R i := by
    intro i hi
    have hu := hxmem i hi.le
    have hv := hxmem (i + 1) hi
    have h1 : Ψ (x i) - Ψ (x (i + 1)) = ∫ y in (x i)..(x (i + 1)), φ y := by
      have := intervalIntegral.integral_add_adjacent_intervals (iiφ _ hu _ hv) (iiφ _ hv _ hbmem)
      rw [hΨ, hΨ, ← this]; ring
    have ii1 : IntervalIntegrable (fun y => c i * φ y) volume (x i) (x (i + 1)) :=
      (iiφ _ hu _ hv).const_mul _
    have ii2 : IntervalIntegrable (fun y => (((h y : ℝ) : ℂ) - c i) * φ y) volume
        (x i) (x (i + 1)) := by
      have : (fun y => (((h y : ℝ) : ℂ) - c i) * φ y) =
          fun y => ((h y : ℝ) : ℂ) * φ y - c i * φ y := by
        ext y; ring
      rw [this]; exact (iihφ _ hu _ hv).sub ii1
    have e1 : ∫ y in (x i)..(x (i + 1)), ((h y : ℝ) : ℂ) * φ y =
        ∫ y in (x i)..(x (i + 1)), (c i * φ y + (((h y : ℝ) : ℂ) - c i) * φ y) :=
      intervalIntegral.integral_congr (fun y _ => by ring)
    rw [e1, intervalIntegral.integral_add ii1 ii2, intervalIntegral.integral_const_mul, hR, h1]
  have hRle : ∀ i < n, ‖R i‖ ≤ ε' * d := by
    intro i hi
    rw [hR]
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := x i) (b := x (i + 1))
      (C := ε') (f := fun y => (((h y : ℝ) : ℂ) - c i) * φ y) (by
        intro y hy
        rw [Set.uIoc_of_le (hxmono i)] at hy
        have hyI : y ∈ Set.Icc a b :=
          ⟨(hxmem i hi.le).1.trans hy.1.le, hy.2.trans (hxmem (i + 1) hi).2⟩
        have hdist : dist y (x i) < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
          linarith [hy.2, hxstep i]
        have hlt := hδh y hyI (x i) (hxmem i hi.le) hdist
        rw [Real.dist_eq] at hlt
        rw [norm_mul, hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        calc |h y - h (x i)| * ‖φ y‖ ≤ ε' * 1 :=
              mul_le_mul hlt.le (hφ1 y hyI) (norm_nonneg _) hε'0.le
          _ = ε' := mul_one _)
    rwa [abs_of_nonneg (by linarith [hxmono i]), hxstep i] at key
  have hsum : ∫ y in a..b, ((h y : ℝ) : ℂ) * φ y =
      ∑ i ∈ range n, ∫ y in (x i)..(x (i + 1)), ((h y : ℝ) : ℂ) * φ y := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun i hi => iihφ _ (hxmem i hi.le) _ (hxmem (i + 1) hi)), hx0, hxn]
  have hΨn : Ψ (x n) = 0 := by rw [hxn, hΨ]; simp
  have t0 : ‖c 0 * Ψ (x 0)‖ ≤ M * |h a| := by
    rw [norm_mul, hc, hx0, Complex.norm_real, Real.norm_eq_abs, hΨ, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM a hamem) (abs_nonneg _)
  have t1 : ‖∑ i ∈ range n, (c (i + 1) - c i) * Ψ (x (i + 1))‖ ≤ M * (h b - h a) := by
    calc ‖∑ i ∈ range n, (c (i + 1) - c i) * Ψ (x (i + 1))‖
        ≤ ∑ i ∈ range n, ‖(c (i + 1) - c i) * Ψ (x (i + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range n, (h (x (i + 1)) - h (x i)) * M := by
          refine sum_le_sum (fun i hi => ?_)
          have hi' := mem_range.1 hi
          have hmn : h (x i) ≤ h (x (i + 1)) :=
            hmono (hxmem i hi'.le) (hxmem (i + 1) hi') (hxmono i)
          rw [norm_mul, hc, hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 hmn), hΨ]
          exact mul_le_mul_of_nonneg_left (hM _ (hxmem (i + 1) hi')) (sub_nonneg.2 hmn)
      _ = M * (h b - h a) := by
          rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => h (x i)) n, hx0, hxn, mul_comm]
  have t2 : ‖∑ i ∈ range n, R i‖ ≤ ε := by
    calc ‖∑ i ∈ range n, R i‖ ≤ ∑ i ∈ range n, ‖R i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, ε' * d := sum_le_sum (fun i hi => hRle i (mem_range.1 hi))
      _ = ε' * (b - a) := by rw [sum_const, card_range, nsmul_eq_mul, ← hnd]; ring
      _ ≤ ε := hε'le
  rw [hsum, sum_congr rfl (fun i hi => hpiece i (mem_range.1 hi)), sum_add_distrib,
    show ∑ i ∈ range n, c i * (Ψ (x i) - Ψ (x (i + 1))) = _ from
      abel_sum c (fun i => Ψ (x i)) n, hΨn, mul_zero, sub_zero]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add t0 t1)) t2).trans (le_of_eq ?_)
  ring

/-- The first-derivative test for the phase `f(x) - cx` on terminal subintervals. -/
lemma phase_bound (f f1 : ℝ → ℝ) (a b c m : ℝ) (hm : 0 < m)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc a b)) (hmono : MonotoneOn f1 (Set.Icc a b))
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ |f1 x - c|) (u : ℝ) (hu : u ∈ Set.Icc a b) :
    ‖∫ x in u..b, e (f x - c * x)‖ ≤ 1 / m := by
  have hsub : Set.Icc u b ⊆ Set.Icc a b := Set.Icc_subset_Icc hu.1 le_rfl
  refine integral_first_deriv_test (fun x => f x - c * x) (fun x => f1 x - c) u b m hu.2 hm
    ?_ ?_ ?_ ?_
  · intro x hx
    have h2 : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id' x).const_mul c
    exact (hf x (hsub hx)).sub h2
  · exact (hc.mono hsub).sub continuousOn_const
  · left
    intro x hx y hy hxy
    exact sub_le_sub_right (hmono (hsub hx) (hsub hy) hxy) c
  · intro x hx
    exact hlow x (hsub hx)

lemma norm_dd (μ : ℤ) : ‖dd μ‖ = 2 * π * |(μ : ℝ)| := by
  unfold dd
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le, mul_one]

/-- The far frequencies: `(1/(2πiμ)) ∫ e(μx) (e∘f)'(x) dx ≪ μ^{-2}`. -/
lemma far_term (f f1 : ℝ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc (a : ℝ) b)) (hmono : MonotoneOn f1 (Set.Icc (a : ℝ) b))
    (Bd : ℝ) (hB : ∀ x ∈ Set.Icc (a : ℝ) b, |f1 x| ≤ Bd) (μ : ℤ) (hμ0 : μ ≠ 0)
    (hμ : 2 * Bd ≤ |(μ : ℝ)|) :
    ‖(1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x‖ ≤
      2 * (|f1 a| + (f1 b - f1 a)) / (μ : ℝ) ^ 2 := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hμpos : 0 < |(μ : ℝ)| := abs_pos.2 (by exact_mod_cast hμ0)
  have hm : 0 < |(μ : ℝ)| / 2 := by positivity
  have hrew : ∀ x : ℝ, E μ x * gd f f1 x =
      (2 * π * I) * (((f1 x : ℝ) : ℂ) * e (f x - ((-μ : ℤ) : ℝ) * x)) := by
    intro x
    rw [← E_mul_e]; unfold gd; push_cast; ring
  have hφc : ContinuousOn (fun x => e (f x - ((-μ : ℤ) : ℝ) * x)) (Set.Icc (a : ℝ) b) :=
    cont_e.comp_continuousOn ((contOn_f hf).sub (continuous_const.mul continuous_id).continuousOn)
  have hlow : ∀ x ∈ Set.Icc (a : ℝ) b, |(μ : ℝ)| / 2 ≤ |f1 x - ((-μ : ℤ) : ℝ)| := by
    intro x hx
    have h1 := hB x hx
    have h2 : |(μ : ℝ)| - |f1 x| ≤ |f1 x - ((-μ : ℤ) : ℝ)| := by
      have := abs_sub_abs_le_abs_sub ((μ : ℝ)) (-(f1 x))
      rw [abs_neg] at this
      have e : (μ : ℝ) - -(f1 x) = f1 x - ((-μ : ℤ) : ℝ) := by push_cast; ring
      rwa [e] at this
    linarith
  have hamp := amp f1 (fun x => e (f x - ((-μ : ℤ) : ℝ) * x)) a b (1 / (|(μ : ℝ)| / 2)) habR hc
    hmono hφc (fun x _ => (norm_e _).le)
    (fun u hu => phase_bound f f1 a b _ _ hm hf hc hmono hlow u hu)
  have hA : 0 ≤ |f1 a| + (f1 b - f1 a) :=
    add_nonneg (abs_nonneg _) (sub_nonneg.2 (hmono ⟨le_rfl, habR⟩ ⟨habR, le_rfl⟩ habR))
  simp_rw [hrew]
  rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, norm_div, norm_one, norm_dd,
    norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  calc 1 / (2 * π * |(μ : ℝ)|) * (2 * π * ‖∫ x in (a : ℝ)..b,
        ((f1 x : ℝ) : ℂ) * e (f x - ((-μ : ℤ) : ℝ) * x)‖)
      ≤ 1 / (2 * π * |(μ : ℝ)|) * (2 * π * (1 / (|(μ : ℝ)| / 2) * (|f1 a| + (f1 b - f1 a)))) := by
        gcongr
    _ = 2 * (|f1 a| + (f1 b - f1 a)) / (μ : ℝ) ^ 2 := by
        rw [← sq_abs (μ : ℝ)]
        field_simp

/-! ### Harmonic-type sums -/
lemma sum_harm {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hinj : Set.InjOn g S) (N : ℕ)
    (hg : ∀ x ∈ S, g x ≤ N) (f : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ S, f x ≤ if g x = 0 then A else B / g x) :
    ∑ x ∈ S, f x ≤ A + B * (1 + Real.log N) := by
  set F : ℕ → ℝ := fun j => if j = 0 then A else B / j with hF
  have hFnn : ∀ j, 0 ≤ F j := by
    intro j; simp only [hF]; split_ifs <;> positivity
  calc ∑ x ∈ S, f x ≤ ∑ x ∈ S, F (g x) := sum_le_sum hf
    _ = ∑ j ∈ S.image g, F j := (sum_image (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ j ∈ range (N + 1), F j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
          exact mem_range.mpr (Nat.lt_succ_of_le (hg x hx))
        · intro j _ _; exact hFnn j
    _ = A + B * (harmonic N : ℝ) := by
        rw [sum_range_succ', add_comm]
        congr 1
        simp only [hF, harmonic, Nat.add_one_ne_zero, if_false, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast, mul_sum, div_eq_mul_inv]
    _ ≤ A + B * (1 + Real.log N) := by
        gcongr
        exact harmonic_le_one_add_log N

lemma inv_half_le (j : ℕ) : 1 / ((j : ℝ) + 1 / 2) ≤ if j = 0 then 2 else 1 / (j : ℝ) := by
  split_ifs with h
  · subst h; norm_num
  · have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h
    exact one_div_le_one_div_of_le hj (by linarith)

lemma tail_sq (V K : ℕ) : ∑ n ∈ Ico V K, 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((V : ℝ) + 1) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) V (K + 1)
  have e : Ioo V (K + 1) = Ico (V + 1) (K + 1) := by
    ext i; simp only [mem_Ioo, mem_Ico]; omega
  rw [e, ← Finset.sum_Ico_add' (fun i : ℕ => (((i : ℝ)) ^ 2)⁻¹) V K 1] at h
  simpa [one_div] using h

/-- The frequencies near the range: those to the right of `f'(b) + 1/2`. -/
lemma near_right (f f1 : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc a b)) (hmono : MonotoneOn f1 (Set.Icc a b))
    (n0 : ℤ) (hn0 : f1 b + 1 / 2 ≤ n0) (V : ℕ) (hV : 0 ≤ n0) (S : Finset ℤ)
    (hS : ∀ ν ∈ S, n0 ≤ ν ∧ ν ≤ V) :
    ∑ ν ∈ S, ‖∫ x in a..b, e (f x - (ν : ℝ) * x)‖ ≤ 2 + 1 * (1 + Real.log V) := by
  refine sum_harm S (fun ν => (ν - n0).toNat) ?_ V ?_ _ 2 1 (by norm_num) (by norm_num) ?_
  · intro ν hν ν' hν' h
    have h1 := (hS ν hν).1
    have h2 := (hS ν' hν').1
    simp only at h
    omega
  · intro ν hν
    have h1 := hS ν hν
    show (ν - n0).toNat ≤ V
    omega
  · intro ν hν
    have h1 := hS ν hν
    have hj : (((ν - n0).toNat : ℕ) : ℝ) = (ν : ℝ) - n0 := by
      have : (((ν - n0).toNat : ℕ) : ℤ) = ν - n0 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hm : (0 : ℝ) < ((ν - n0).toNat : ℕ) + 1 / 2 := by positivity
    have hb := phase_bound f f1 a b (ν : ℝ) _ hm hf hc hmono (fun x hx => by
      have hx1 : f1 x ≤ f1 b := hmono hx ⟨hab, le_rfl⟩ hx.2
      rw [hj]
      exact le_abs.2 (Or.inr (by linarith))) a ⟨le_rfl, hab⟩
    simp only [one_div] at hb ⊢
    have := inv_half_le (ν - n0).toNat
    simp only [one_div] at this
    exact hb.trans this

/-- The frequencies near the range: those to the left of `f'(a) - 1/2`, when `f'(a) ≥ -1/2`. -/
lemma near_left (f f1 : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc a b)) (hmono : MonotoneOn f1 (Set.Icc a b))
    (h1 : -(1 / 2) ≤ f1 a) (V : ℕ) (S : Finset ℤ)
    (hS : ∀ ν ∈ S, -(V : ℤ) ≤ ν ∧ ν ≤ -1) :
    ∑ ν ∈ S, ‖∫ x in a..b, e (f x - (ν : ℝ) * x)‖ ≤ 2 + 1 * (1 + Real.log V) := by
  refine sum_harm S (fun ν => (-1 - ν).toNat) ?_ V ?_ _ 2 1 (by norm_num) (by norm_num) ?_
  · intro ν hν ν' hν' h
    have h1 := (hS ν hν).2
    have h2 := (hS ν' hν').2
    simp only at h
    omega
  · intro ν hν
    have h1 := hS ν hν
    show (-1 - ν).toNat ≤ V
    omega
  · intro ν hν
    have h2 := hS ν hν
    have hj : (((-1 - ν).toNat : ℕ) : ℝ) = -1 - (ν : ℝ) := by
      have : (((-1 - ν).toNat : ℕ) : ℤ) = -1 - ν := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hm : (0 : ℝ) < ((-1 - ν).toNat : ℕ) + 1 / 2 := by positivity
    have hb := phase_bound f f1 a b (ν : ℝ) _ hm hf hc hmono (fun x hx => by
      have hx1 : f1 a ≤ f1 x := hmono ⟨le_rfl, hab⟩ hx hx.1
      rw [hj]
      exact le_abs.2 (Or.inl (by linarith))) a ⟨le_rfl, hab⟩
    simp only [one_div] at hb ⊢
    have := inv_half_le (-1 - ν).toNat
    simp only [one_div] at this
    exact hb.trans this

/-! ### The normalized case `-1/2 ≤ f'(a) < 1/2` -/
lemma core (f f1 : ℝ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x)
    (hc : ContinuousOn f1 (Set.Icc (a : ℝ) b)) (hmono : MonotoneOn f1 (Set.Icc (a : ℝ) b))
    (h1 : -(1 / 2) ≤ f1 a) (h2 : f1 a < 1 / 2) :
    ‖∑ n ∈ Finset.Ioc a b, e (f n) -
        ∑ ν ∈ Finset.Ioo ⌊f1 a - 1 / 2⌋ ⌈f1 b + 1 / 2⌉,
          ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)‖ ≤
      20 * Real.log (f1 b - f1 a + 2) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hamem : (a : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨le_rfl, habR⟩
  have hbmem : (b : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨habR, le_rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = f1 b - f1 a := ⟨_, rfl⟩
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; exact sub_nonneg.2 (hmono hamem hbmem habR)
  have hBd : ∀ x ∈ Set.Icc (a : ℝ) b, |f1 x| ≤ Δ + 1 / 2 := by
    intro x hx
    have hx1 : f1 a ≤ f1 x := hmono hamem hx hx.1
    have hx2 : f1 x ≤ f1 b := hmono hx hbmem hx.2
    rw [abs_le]; constructor <;> linarith
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ, V = ⌈2 * Δ + 2⌉₊ := ⟨_, rfl⟩
  have hV1 : 2 * Δ + 2 ≤ V := by rw [hVdef]; exact Nat.le_ceil _
  have hV2 : (V : ℝ) < 2 * Δ + 3 := by
    rw [hVdef]
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Δ + 2 by positivity)
    linarith
  have hVpos : (1 : ℝ) ≤ V := by linarith
  have hm0 : ⌊f1 a - 1 / 2⌋ = -1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  obtain ⟨n0, hn0def⟩ : ∃ n0 : ℤ, n0 = ⌈f1 b + 1 / 2⌉ := ⟨_, rfl⟩
  have hn0a : f1 b + 1 / 2 ≤ n0 := by rw [hn0def]; exact Int.le_ceil _
  have hn0nn : 0 ≤ n0 := by rw [hn0def]; exact Int.ceil_nonneg (by linarith)
  have hn0V : n0 ≤ V := by
    rw [hn0def, Int.ceil_le]; push_cast; linarith
  rw [hm0, ← hn0def]
  have hsub : Ioo (-1 : ℤ) n0 ⊆ Icc (-(V : ℤ)) V := by
    intro ν hν; simp only [mem_Ioo, mem_Icc] at hν ⊢; omega
  -- the frequencies near the range
  have hnear : ‖∑ ν ∈ Icc (-(V : ℤ)) V \ Ioo (-1 : ℤ) n0,
      ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)‖ ≤ 6 + 2 * Real.log V := by
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun ν => n0 ≤ ν)]
    have hr := near_right f f1 a b habR hf hc hmono n0 hn0a V hn0nn
      ((Icc (-(V : ℤ)) V \ Ioo (-1 : ℤ) n0).filter (fun ν => n0 ≤ ν)) (by
        intro ν hν
        simp only [mem_filter, mem_sdiff, mem_Icc, mem_Ioo] at hν
        omega)
    have hl := near_left f f1 a b habR hf hc hmono h1 V
      ((Icc (-(V : ℤ)) V \ Ioo (-1 : ℤ) n0).filter (fun ν => ¬ n0 ≤ ν)) (by
        intro ν hν
        simp only [mem_filter, mem_sdiff, mem_Icc, mem_Ioo] at hν
        omega)
    linarith
  -- the far frequencies
  have hfar : ∀ K : ℕ, V ≤ K →
      ‖(∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x)
         - (∑ μ ∈ (Icc (-(V : ℤ)) V).erase 0,
            (1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x)‖ ≤ 4 := by
    intro K hVK
    obtain ⟨t, ht⟩ : ∃ t : ℤ → ℂ,
        ∀ μ, t μ = (1 / dd μ) * ∫ x in (a : ℝ)..b, E μ x * gd f f1 x := ⟨_, fun _ => rfl⟩
    simp only [← ht]
    rw [sum_S t K, sum_S t V, ← Finset.sum_Ico_eq_sub _ hVK]
    have hterm : ∀ μ : ℤ, (V : ℝ) + 1 ≤ |(μ : ℝ)| → ‖t μ‖ ≤ (2 * Δ + 1) / (μ : ℝ) ^ 2 := by
      intro μ hμ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [Int.cast_zero, abs_zero] at hμ
        linarith
      have hμR : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ0
      have hsq : 0 < (μ : ℝ) ^ 2 := by positivity
      rw [ht]
      refine (far_term f f1 a b hab hf hc hmono (Δ + 1 / 2) hBd μ hμ0 (by linarith)).trans ?_
      rw [div_le_div_iff_of_pos_right hsq]
      have : |f1 a| ≤ 1 / 2 := abs_le.2 ⟨h1, h2.le⟩
      rw [← hΔ]; linarith
    calc ‖∑ n ∈ Ico V K, (t ((n : ℤ) + 1) + t (-((n : ℤ) + 1)))‖
        ≤ ∑ n ∈ Ico V K, ‖t ((n : ℤ) + 1) + t (-((n : ℤ) + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico V K, 2 * (2 * Δ + 1) * (1 / ((n : ℝ) + 1) ^ 2) := by
          refine sum_le_sum (fun n hn => ?_)
          have hnV : (V : ℝ) ≤ n := by exact_mod_cast (mem_Ico.1 hn).1
          have ha1 := hterm ((n : ℤ) + 1) (by
            push_cast; rw [abs_of_nonneg (by positivity)]; linarith)
          have ha2 := hterm (-((n : ℤ) + 1)) (by
            push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; linarith)
          simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq]
            at ha1 ha2
          refine (norm_add_le _ _).trans ?_
          have : 2 * (2 * Δ + 1) * (1 / ((n : ℝ) + 1) ^ 2) =
              (2 * Δ + 1) / ((n : ℝ) + 1) ^ 2 + (2 * Δ + 1) / ((n : ℝ) + 1) ^ 2 := by ring
          linarith
      _ = 2 * (2 * Δ + 1) * ∑ n ∈ Ico V K, 1 / ((n : ℝ) + 1) ^ 2 := by rw [mul_sum]
      _ ≤ 2 * (2 * Δ + 1) * (2 / ((V : ℝ) + 1)) := by
          gcongr; exact tail_sq V K
      _ ≤ 4 := by
          rw [show 2 * (2 * Δ + 1) * (2 / ((V : ℝ) + 1)) = 4 * (2 * Δ + 1) / ((V : ℝ) + 1) by
            ring, div_le_iff₀ (by positivity)]
          linarith
  have hbd : ‖(e (f b) - e (f a)) / 2‖ ≤ 1 := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_sub_le (e (f b)) (e (f a))
    rw [norm_e, norm_e] at this
    linarith
  have hsd := Finset.sum_sdiff hsub (f := fun ν : ℤ => ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x))
  beta_reduce at hsd
  have hK : ∀ K : ℕ, V ≤ K → 1 ≤ K →
      ‖∑ n ∈ Finset.Ioc a b, e (f n) -
        ∑ ν ∈ Finset.Ioo (-1 : ℤ) n0, ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)‖ ≤
      11 + 2 * Real.log V + 2 * π * (Δ + 1 / 2) * (b - a) / Real.sqrt K := by
    intro K hVK hK1
    have htail := tail_term_le f f1 a b K hab hK1 (Δ + 1 / 2) hBd
    have hf' := hfar K hVK
    rw [main_ident f f1 a b hab hf hc V K, ← hsd]
    have hre : ∀ A B C D F : ℂ, A + B + C + D - F - B = A + C + D - F := by
      intro A B C D F; ring
    rw [hre]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hnear hbd)) htail)) hf').trans (le_of_eq ?_)
    ring
  have hlim : Filter.Tendsto (fun K : ℕ => 11 + 2 * Real.log V +
      2 * π * (Δ + 1 / 2) * (b - a) / Real.sqrt K) Filter.atTop
      (nhds (11 + 2 * Real.log V + 0)) := by
    refine tendsto_const_nhds.add ?_
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hD := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨max V 1, fun K hK' =>
    hK K (le_trans (le_max_left _ _) hK') (le_trans (le_max_right _ _) hK')⟩)
  have hlogV : Real.log V ≤ 2 * Real.log (Δ + 2) := by
    calc Real.log V ≤ Real.log ((Δ + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log (Δ + 2) := by rw [Real.log_pow]; norm_num
  have hlog2 : Real.log 2 ≤ Real.log (Δ + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hl2 := Real.log_two_gt_d9
  rw [← hΔ]
  linarith

/-! ### The lemma -/
/-- Titchmarsh, Lemma 4.7 with `η = 1/2`, for `f'` increasing: the frequencies are the
integers `ν` with `f'(a) - 1/2 < ν < f'(b) + 1/2`. -/
theorem truncated_poisson :
    ∃ C : ℝ, 0 < C ∧ ∀ (f f1 : ℝ → ℝ) (a b : ℕ), a ≤ b →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
      ContinuousOn f1 (Set.Icc (a : ℝ) b) →
      MonotoneOn f1 (Set.Icc (a : ℝ) b) →
      ‖∑ n ∈ Finset.Ioc a b, e (f n) -
          ∑ ν ∈ Finset.Ioo ⌊f1 a - 1 / 2⌋ ⌈f1 b + 1 / 2⌉,
            ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)‖ ≤
        C * Real.log (f1 b - f1 a + 2) := by
  refine ⟨20, by norm_num, fun f f1 a b hab hf hc hmono => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊f1 a + 1 / 2⌋ := ⟨_, rfl⟩
  have hk1 : (k : ℝ) ≤ f1 a + 1 / 2 := by rw [hk]; exact Int.floor_le _
  have hk2 : f1 a + 1 / 2 < k + 1 := by rw [hk]; exact Int.lt_floor_add_one _
  have key := core (fun x => f x - k * x) (fun x => f1 x - k) a b hab
    (fun x hx => by
      have h2 : HasDerivAt (fun y : ℝ => (k : ℝ) * y) k x := by
        simpa using (hasDerivAt_id' x).const_mul (k : ℝ)
      exact (hf x hx).sub h2)
    (hc.sub continuousOn_const)
    (fun x hx y hy hxy => sub_le_sub_right (hmono hx hy hxy) _)
    (by linarith) (by linarith)
  beta_reduce at key
  have hfl : ⌊f1 a - k - 1 / 2⌋ = ⌊f1 a - 1 / 2⌋ - k := by
    rw [show f1 a - k - 1 / 2 = f1 a - 1 / 2 - k by ring, Int.floor_sub_intCast]
  have hcl : ⌈f1 b - k + 1 / 2⌉ = ⌈f1 b + 1 / 2⌉ - k := by
    rw [show f1 b - k + 1 / 2 = f1 b + 1 / 2 - k by ring, Int.ceil_sub_intCast]
  have hsum1 : ∑ n ∈ Finset.Ioc a b, e (f n - k * n) = ∑ n ∈ Finset.Ioc a b, e (f n) :=
    sum_congr rfl (fun n _ => e_sub_int _ _ _)
  have hsum2 : ∑ ν ∈ Finset.Ioo (⌊f1 a - 1 / 2⌋ - k) (⌈f1 b + 1 / 2⌉ - k),
        ∫ x in (a : ℝ)..b, e (f x - k * x - (ν : ℝ) * x) =
      ∑ ν ∈ Finset.Ioo ⌊f1 a - 1 / 2⌋ ⌈f1 b + 1 / 2⌉,
        ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x) := by
    refine Finset.sum_nbij' (fun ν => ν + k) (fun ν => ν - k) ?_ ?_ ?_ ?_ ?_
    · intro ν hν; simp only [mem_Ioo] at hν ⊢; omega
    · intro ν hν; simp only [mem_Ioo] at hν ⊢; omega
    · intro ν _; simp
    · intro ν _; simp
    · intro ν _
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show e _ = e _
      congr 1; push_cast; ring
  rw [hfl, hcl, hsum1, hsum2] at key
  have e3 : f1 b - k - (f1 a - k) + 2 = f1 b - f1 a + 2 := by ring
  rw [e3] at key
  exact key

end GuthMaynard.SubWeyl.PartC
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part C: truncated Poisson summation -/
alias truncated_poisson := GuthMaynard.SubWeyl.PartC.truncated_poisson

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartT
/-!
# Part T: the B-process (Titchmarsh, Theorem 4.9)

`b_process` from `truncated_poisson`, `stationary_phase` and `integral_second_deriv_test`.
-/
lemma inv_le_log_step (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ 3 * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) =
      Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) :=
    Real.log_div (by positivity) (by positivity)
  have h2 : 1 - (((n : ℝ) + 2) / ((n : ℝ) + 1))⁻¹ ≤ Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) :=
    Real.one_sub_inv_le_log_of_pos (by positivity)
  have h3 : 1 - (((n : ℝ) + 2) / ((n : ℝ) + 1))⁻¹ = 1 / ((n : ℝ) + 2) := by
    field_simp
    ring
  have h4 : 1 / (n : ℝ) ≤ 3 * (1 / ((n : ℝ) + 2)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith

/-- One term of the endpoint sums. -/
lemma term_le (s : ℝ) (hs : 0 < s) (d : ℝ) (n : ℕ) (hd : (n : ℝ) ≤ |d|) :
    1 / (|d| + s) ≤ if n = 0 then 1 / s
      else 3 * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
  split_ifs with h
  · exact one_div_le_one_div_of_le hs (by linarith [abs_nonneg d])
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine le_trans ?_ (inv_le_log_step n hn)
    exact one_div_le_one_div_of_le hn' (by linarith)

lemma step_le (s : ℝ) (hs : 0 < s) (d : ℝ) (n : ℕ) (hd : (n : ℝ) ≤ |d|) (S0 : ℝ)
    (ih : S0 ≤ 1 / s + 3 * Real.log ((n : ℝ) + 1)) (h0 : n = 0 → S0 = 0) :
    1 / (|d| + s) + S0 ≤ 1 / s + 3 * Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
  have hc : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  rw [hc]
  have ht := term_le s hs d n hd
  by_cases h : n = 0
  · rw [if_pos h] at ht
    rw [h0 h]
    have : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  · rw [if_neg h] at ht
    linarith

/-- Endpoint sum at the left endpoint: all `ν > m ≥ t - 1`. -/
lemma sum_left (s : ℝ) (hs : 0 < s) (t : ℝ) (m : ℤ) (ht : t ≤ (m : ℝ) + 1) (n : ℕ) :
    ∑ ν ∈ Finset.Ioc m (m + n), 1 / (|t - (ν : ℝ)| + s) ≤
      1 / s + 3 * Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    rw [show Finset.Ioc m (m + ((0 : ℕ) : ℤ)) = ∅ by simp, Finset.sum_empty]
    have : 0 ≤ Real.log (((0 : ℕ) : ℝ) + 1) := Real.log_nonneg (by simp)
    positivity
  | succ n ih =>
    have hset : Finset.Ioc m (m + ((n + 1 : ℕ) : ℤ)) =
        insert (m + n + 1) (Finset.Ioc m (m + n)) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert (by simp)]
    refine step_le s hs _ n ?_ _ ih ?_
    · have : (n : ℝ) ≤ -(t - ((m + n + 1 : ℤ) : ℝ)) := by push_cast; linarith
      exact this.trans (neg_le_abs _)
    · intro h
      subst h
      simp

/-- Endpoint sum at the right endpoint: all `ν ≤ m + n ≤ t`. -/
lemma sum_right (s : ℝ) (hs : 0 < s) (t : ℝ) (n : ℕ) :
    ∀ m : ℤ, (m : ℝ) + n ≤ t →
      ∑ ν ∈ Finset.Ioc m (m + n), 1 / (|t - (ν : ℝ)| + s) ≤
        1 / s + 3 * Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    intro m _
    rw [show Finset.Ioc m (m + ((0 : ℕ) : ℤ)) = ∅ by simp, Finset.sum_empty]
    have : 0 ≤ Real.log (((0 : ℕ) : ℝ) + 1) := Real.log_nonneg (by simp)
    positivity
  | succ n ih =>
    intro m ht
    push_cast at ht
    have hset : Finset.Ioc m (m + ((n + 1 : ℕ) : ℤ)) =
        insert (m + 1) (Finset.Ioc (m + 1) (m + 1 + n)) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert (by simp)]
    refine step_le s hs _ n ?_ _ (ih (m + 1) (by push_cast; linarith)) ?_
    · have : (n : ℝ) ≤ t - ((m + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact this.trans (le_abs_self _)
    · intro h
      subst h
      simp

lemma mvt_bounds (g g' : ℝ → ℝ) (a b lo hi : ℝ)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hb : ∀ x ∈ Set.Icc a b, lo ≤ g' x ∧ g' x ≤ hi) (x y : ℝ) (hx : a ≤ x) (hxy : x ≤ y)
    (hy : y ≤ b) :
    lo * (y - x) ≤ g y - g x ∧ g y - g x ≤ hi * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  have hsub : ∀ z ∈ Set.Icc x y, z ∈ Set.Icc a b := fun z hz => ⟨hx.trans hz.1, hz.2.trans hy⟩
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' hlt
    (fun z hz => (hg z (hsub z hz)).continuousAt.continuousWithinAt)
    (fun z hz => hg z (hsub z (Set.Ioo_subset_Icc_self hz)))
  have hc' := hb c (hsub c (Set.Ioo_subset_Icc_self hc))
  have hpos : 0 < y - x := sub_pos.mpr hlt
  have h : g y - g x = g' c * (y - x) := by
    rw [hceq]
    field_simp
  rw [h]
  exact ⟨mul_le_mul_of_nonneg_right hc'.1 hpos.le, mul_le_mul_of_nonneg_right hc'.2 hpos.le⟩

lemma log_le_of_le (R L v : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hv : 0 < v) (hvL : v ≤ R * L + 2) :
    Real.log v ≤ (1 + 2 * R) * Real.log (2 + L) := by
  have h1 : Real.log v ≤ Real.log (R * (2 + L)) :=
    Real.log_le_log hv (by nlinarith)
  have h2 : Real.log (R * (2 + L)) = Real.log R + Real.log (2 + L) :=
    Real.log_mul (by linarith) (by linarith)
  have h3 : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h4 : (1 / 2 : ℝ) ≤ Real.log (2 + L) := by
    have := Real.log_two_gt_d9
    have h5 : Real.log 2 ≤ Real.log (2 + L) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  nlinarith

/-- The two index sets. -/
lemma index_sets (α β : ℝ) :
    Finset.Ioc ⌊α⌋ ⌊β⌋ ⊆ Finset.Ioo ⌊α - 1 / 2⌋ ⌈β + 1 / 2⌉ ∧
      Finset.Ioo ⌊α - 1 / 2⌋ ⌈β + 1 / 2⌉ \ Finset.Ioc ⌊α⌋ ⌊β⌋ ⊆ {⌊α⌋, ⌊β⌋ + 1} := by
  constructor
  · intro ν hν
    rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor] at hν
    rw [Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
    exact ⟨by linarith, by linarith⟩
  · intro ν hν
    rw [Finset.mem_sdiff, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil, Finset.mem_Ioc,
      Int.floor_lt, Int.le_floor] at hν
    obtain ⟨⟨h1, h2⟩, h3⟩ := hν
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : α < ν
    · right
      have h4 : β < ν := lt_of_not_ge fun h' => h3 ⟨h, h'⟩
      have h5 : ⌊β⌋ < ν := Int.floor_lt.mpr h4
      have h6 : (ν : ℝ) < ((⌊β⌋ + 2 : ℤ) : ℝ) := by
        push_cast
        linarith [Int.lt_floor_add_one β]
      have h7 : ν < ⌊β⌋ + 2 := by exact_mod_cast h6
      omega
    · left
      have h4 : ν ≤ ⌊α⌋ := Int.le_floor.mpr (not_lt.mp h)
      have h6 : ((⌊α⌋ : ℤ) : ℝ) < ((ν + 1 : ℤ) : ℝ) := by
        push_cast
        linarith [Int.floor_le α]
      have h7 : ⌊α⌋ < ν + 1 := by exact_mod_cast h6
      omega

/-- The Poisson frequencies without the stationary ones contribute `≤ 2·bd`. -/
lemma sum_diff_le (I : ℤ → ℂ) (α β bd : ℝ) (hI : ∀ ν, ‖I ν‖ ≤ bd) :
    ‖∑ ν ∈ Finset.Ioo ⌊α - 1 / 2⌋ ⌈β + 1 / 2⌉, I ν - ∑ ν ∈ Finset.Ioc ⌊α⌋ ⌊β⌋, I ν‖ ≤
      2 * bd := by
  obtain ⟨h1, h2⟩ := index_sets α β
  have hbd : 0 ≤ bd := (norm_nonneg _).trans (hI 0)
  rw [← Finset.sum_sdiff h1, add_sub_cancel_right]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ bd fun ν _ => hI ν).trans ?_
  rw [nsmul_eq_mul]
  have hc : (Finset.Ioo ⌊α - 1 / 2⌋ ⌈β + 1 / 2⌉ \ Finset.Ioc ⌊α⌋ ⌊β⌋).card ≤ 2 :=
    (Finset.card_le_card h2).trans Finset.card_le_two
  have hc' : (((Finset.Ioo ⌊α - 1 / 2⌋ ⌈β + 1 / 2⌉ \ Finset.Ioc ⌊α⌋ ⌊β⌋).card : ℕ) : ℝ) ≤ 2 := by
    exact_mod_cast hc
  exact mul_le_mul_of_nonneg_right hc' hbd

/-- Sum of the stationary-phase errors over `α < ν ≤ β`. -/
lemma sum_errors (R L α β s mn m1 m2 Lg : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hs : 0 < s)
    (hαβ : α ≤ β) (hβα : β - α ≤ R * L) (hmn : 0 ≤ mn) (hm1 : mn ≤ m1) (hm2 : mn ≤ m2)
    (hLg : Lg = Real.log (2 + L)) :
    ∑ ν ∈ Finset.Ioc ⌊α⌋ ⌊β⌋,
        (mn + 1 / (|α - (ν : ℝ)| + s) + 1 / (|β - (ν : ℝ)| + s)) ≤
      R * L * m1 + m2 + 2 * (1 / s + 3 * ((1 + 2 * R) * Lg)) := by
  have hfl : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_mono hαβ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊β⌋ = ⌊α⌋ + n :=
    ⟨(⌊β⌋ - ⌊α⌋).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  have hnR : ((⌊β⌋ : ℤ) : ℝ) = (⌊α⌋ : ℝ) + n := by rw [hn]; push_cast; ring
  have hn1 : (n : ℝ) ≤ R * L + 1 := by
    linarith [Int.floor_le β, Int.lt_floor_add_one α]
  have hcard : (Finset.Ioc ⌊α⌋ ⌊β⌋).card = n := by
    rw [Int.card_Ioc, hn]
    simp
  have hlog : Real.log ((n : ℝ) + 1) ≤ (1 + 2 * R) * Lg := by
    rw [hLg]
    exact log_le_of_le R L _ hR hL (by positivity) (by linarith)
  have hl := sum_left s hs α ⌊α⌋ (Int.lt_floor_add_one α).le n
  have hr := sum_right s hs β n ⌊α⌋ (by rw [← hnR]; exact Int.floor_le β)
  rw [← hn] at hl hr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  have hRL : 0 ≤ R * L := by positivity
  have h1 : (n : ℝ) * mn ≤ R * L * m1 + m2 := by
    calc (n : ℝ) * mn ≤ (R * L + 1) * mn := mul_le_mul_of_nonneg_right hn1 hmn
      _ = R * L * mn + mn := by ring
      _ ≤ R * L * m1 + m2 := add_le_add (mul_le_mul_of_nonneg_left hm1 hRL) hm2
  linarith

theorem b_process (R : ℝ) (hR : 1 ≤ R) :
    ∃ κ : ℂ, ∃ C : ℝ, 0 < C ∧ ∀ (f f1 f2 f3 : ℝ → ℝ) (X : ℤ → ℝ) (a b : ℕ) (lam2 lam3 : ℝ),
      a < b → 0 < lam2 → 0 < lam3 →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f1 (f2 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f2 (f3 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam2 ≤ f2 x ∧ f2 x ≤ R * lam2) →
      (∀ x ∈ Set.Icc (a : ℝ) b, |f3 x| ≤ R * lam3) →
      (∀ ν : ℤ, f1 a < ν → (ν : ℝ) ≤ f1 b → X ν ∈ Set.Icc (a : ℝ) b ∧ f1 (X ν) = ν) →
      ‖∑ n ∈ Finset.Ioc a b, e (f n) -
          κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
            ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * e (f (X ν) - (ν : ℝ) * X ν)‖ ≤
        C * (lam2 ^ (-(1 / 2 : ℝ)) + Real.log (2 + ((b : ℝ) - a) * lam2) +
          ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ)) := by
  obtain ⟨κ, Cs, hCs, hS⟩ := GuthMaynard.SubWeyl.stationary_phase R hR
  obtain ⟨Cp, hCp, hP⟩ := GuthMaynard.SubWeyl.truncated_poisson
  refine ⟨κ, (1 + 2 * R) * (Cp + 6 * Cs) + 8 + 3 * Cs + Cs * R, by positivity, ?_⟩
  intro f f1 f2 f3 X a b lam2 lam3 hab hl2 hl3 hf hf1 hf2 hb2 hb3 hX
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hba : 0 < (b : ℝ) - a := sub_pos.mpr hab'
  have hL : 0 ≤ ((b : ℝ) - a) * lam2 := by positivity
  have hs : 0 < Real.sqrt lam2 := Real.sqrt_pos.mpr hl2
  have hm2 : 1 / Real.sqrt lam2 = lam2 ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hl2.le, one_div]
  have hmv := mvt_bounds f1 f2 a b lam2 (R * lam2) hf1 hb2
  have hmono : MonotoneOn f1 (Set.Icc (a : ℝ) b) := by
    intro x hx y hy hxy
    have h1 := (hmv x y hx.1 hxy hy.2).1
    have h0 : 0 ≤ lam2 * (y - x) := mul_nonneg hl2.le (sub_nonneg.mpr hxy)
    linarith
  have hcont : ContinuousOn f1 (Set.Icc (a : ℝ) b) :=
    fun x hx => (hf1 x hx).continuousAt.continuousWithinAt
  obtain ⟨hlo, hhi⟩ := hmv a b le_rfl hab'.le le_rfl
  have hαβ : f1 a ≤ f1 b := by nlinarith
  have hβα : f1 b - f1 a ≤ R * (((b : ℝ) - a) * lam2) := by linarith
  -- Poisson
  have hPo := hP f f1 a b hab.le hf hcont hmono
  have hlogP : Real.log (f1 b - f1 a + 2) ≤
      (1 + 2 * R) * Real.log (2 + ((b : ℝ) - a) * lam2) :=
    log_le_of_le R _ _ hR hL (by linarith) (by linarith)
  -- phases
  have hG : ∀ ν : ℤ, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivAt (fun x => f x - (ν : ℝ) * x) ((fun x => f1 x - (ν : ℝ)) x) x := by
    intro ν x hx
    have h : HasDerivAt (fun x => f x - (ν : ℝ) * x) (f1 x - (ν : ℝ) * 1) x :=
      (hf x hx).sub ((hasDerivAt_id' x).const_mul (ν : ℝ))
    exact h.congr_deriv (by simp)
  have hG1 : ∀ ν : ℤ, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivAt (fun x => f1 x - (ν : ℝ)) (f2 x) x :=
    fun ν x hx => (hf1 x hx).sub_const _
  have hI2 : ∀ ν : ℤ, ‖∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)‖ ≤ 4 / Real.sqrt lam2 :=
    fun ν => GuthMaynard.SubWeyl.integral_second_deriv_test _ _ f2 a b lam2 hab'.le hl2
      (hG ν) (hG1 ν) (fun x hx => (hb2 x hx).1)
  have hdiff := sum_diff_le (fun ν : ℤ => ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x))
    (f1 a) (f1 b) _ hI2
  -- stationary phase
  have hst : ∀ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
      ‖(∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) -
          κ * (((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * e (f (X ν) - (ν : ℝ) * X ν))‖ ≤
        Cs * (min (lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ)) (lam2 ^ (-(1 / 2 : ℝ))) +
          1 / (|f1 a - (ν : ℝ)| + Real.sqrt lam2) + 1 / (|f1 b - (ν : ℝ)| + Real.sqrt lam2)) := by
    intro ν hν
    rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor] at hν
    obtain ⟨hXI, hXe⟩ := hX ν hν.1 hν.2
    have h := hS (fun x => f x - (ν : ℝ) * x) (fun x => f1 x - (ν : ℝ)) f2 f3 a b (X ν) lam2 lam3
      hXI.1 hXI.2 hl2 hl3 (hG ν) (hG1 ν) hf2 hb2 hb3 (by simp [hXe])
    rw [mul_assoc] at h
    exact h
  have hsum : ‖∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋, (∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) -
      κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
        ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * e (f (X ν) - (ν : ℝ) * X ν)‖ ≤
      Cs * (R * (((b : ℝ) - a) * lam2) * (lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ)) +
        lam2 ^ (-(1 / 2 : ℝ)) + 2 * (1 / Real.sqrt lam2 +
          3 * ((1 + 2 * R) * Real.log (2 + ((b : ℝ) - a) * lam2)))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hst).trans ?_)
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hCs.le
    exact sum_errors R _ (f1 a) (f1 b) _ _ _ _ _ hR hL hs hαβ hβα
      (le_min (by positivity) (by positivity)) (min_le_left _ _) (min_le_right _ _) rfl
  have hpow : lam2 * lam2 ^ (-(4 / 5 : ℝ)) = lam2 ^ (1 / 5 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one lam2]
    rw [← Real.rpow_add hl2]
    norm_num
  have hT : R * (((b : ℝ) - a) * lam2) * (lam2 ^ (-(4 / 5 : ℝ)) * lam3 ^ (1 / 5 : ℝ)) =
      R * (((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ)) := by
    rw [← hpow]
    ring
  rw [hT, hm2] at hsum
  rw [show (4 : ℝ) / Real.sqrt lam2 = 4 * (1 / Real.sqrt lam2) by ring, hm2] at hdiff
  have htri := norm_add₃_le
    (a := ∑ n ∈ Finset.Ioc a b, e (f n) -
      ∑ ν ∈ Finset.Ioo ⌊f1 a - 1 / 2⌋ ⌈f1 b + 1 / 2⌉, ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x))
    (b := ∑ ν ∈ Finset.Ioo ⌊f1 a - 1 / 2⌋ ⌈f1 b + 1 / 2⌉, (∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) -
      ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋, ∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x))
    (c := ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋, (∫ x in (a : ℝ)..b, e (f x - (ν : ℝ) * x)) -
      κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
        ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * e (f (X ν) - (ν : ℝ) * X ν))
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at htri
  refine htri.trans ?_
  have hm2p : 0 ≤ lam2 ^ (-(1 / 2 : ℝ)) := by positivity
  have hLgp : 0 ≤ Real.log (2 + ((b : ℝ) - a) * lam2) := Real.log_nonneg (by linarith)
  have hT3p : 0 ≤ ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ) := by positivity
  have hPo' := hPo.trans (mul_le_mul_of_nonneg_left hlogP hCp.le)
  generalize lam2 ^ (-(1 / 2 : ℝ)) = m2 at *
  generalize Real.log (2 + ((b : ℝ) - a) * lam2) = Lg at *
  generalize ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ) = T3 at *
  have k1 : 0 ≤ (1 + 2 * R) * (Cp + 6 * Cs) * (m2 + T3) := by positivity
  have k2 : 0 ≤ (8 + 3 * Cs) * (Lg + T3) := by positivity
  have k3 : 0 ≤ Cs * R * (m2 + Lg) := by positivity
  nlinarith [hPo', hdiff, hsum, k1, k2, k3]

end GuthMaynard.SubWeyl.PartT
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part T: the B-process -/
alias b_process := GuthMaynard.SubWeyl.PartT.b_process

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-!
# Part D: the shifted phase `phi` and its dual phase (calculus)
-/

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part D: the shifted phase and its dual -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-! ## The dual phase -/

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartS
open GuthMaynard.SubWeyl
/-!
# Part S: the shifted sums `∑ e(phi t h n)`

B-process (`b_process`, `R = 10`) on `[N, N']`, reindexing of the dual sum by `m = -ν`,
Abel's inequality (`abel_monotone`) for the amplitude, and the fifth-derivative test
(`kth_derivative_test`, `k = 5`) for the dual phase on `M/26 ≤ μ ≤ M`, `M = th/N²`.
-/
/-! ## Calculus of `phi1`, `phi2`, `xst` -/

/-! ## Reindexing the dual sum -/

/-! ## Monomial identities -/

/-! ## The dual sum -/

/-! ## The stub -/

end GuthMaynard.SubWeyl.PartS
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part S: the shifted sums -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartL
/-!
# Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` (A-process and exponent bookkeeping)
-/

end GuthMaynard.SubWeyl.PartL
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartM
/-!
# Part M: blocks with `N ≤ t^{43/100}` (fourth-derivative test)
-/

end GuthMaynard.SubWeyl.PartM
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part M: blocks with `N ≤ t^{43/100}` -/

end GuthMaynard.SubWeyl
end

section
open Complex Filter Topology Set
namespace GuthMaynard.SubWeyl.PartZ
/-!
# Part Z: `ζ(1/2+it)` in terms of dyadic blocks of `n^{it}` with `N² ≤ t`

`ζ(1/2+it) = ∑_{n ≤ t} n^{-1/2-it} + O(1)` (`Zeta0EqZeta` and Kusmin–Landau, copied from the
mission's `richert_zeta_bound` development); dyadic blocks and Abel's inequality; the blocks with
`N² > t` are turned into blocks with `N² ≤ t` by the B-process
`GuthMaynard.norm_sum_cpow_sub_dual_window_le`.
-/

/-! ## Conjugation -/

/-! ## The dual sum -/

/-! ## Every partial block `(N, R]`, `N ≤ t`, `R ≤ 2N` -/

/-! ## The dyadic decomposition -/

/-! ## The stub -/

end GuthMaynard.SubWeyl.PartZ
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part Z: `ζ(1/2+it)` and blocks of length at most `√t` -/

/-! ## Assembly (no `sorry` below) -/

end GuthMaynard.SubWeyl
end

section
open GuthMaynard
open GuthMaynard.SubWeyl
theorem solution (R : ℝ) (hR : 1 ≤ R) :
    ∃ κ : ℂ, ∃ C : ℝ, 0 < C ∧ ∀ (f f1 f2 f3 : ℝ → ℝ) (X : ℤ → ℝ) (a b : ℕ) (lam2 lam3 : ℝ),
      a < b → 0 < lam2 → 0 < lam3 →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f1 (f2 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f2 (f3 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam2 ≤ f2 x ∧ f2 x ≤ R * lam2) →
      (∀ x ∈ Set.Icc (a : ℝ) b, |f3 x| ≤ R * lam3) →
      (∀ ν : ℤ, f1 a < ν → (ν : ℝ) ≤ f1 b → X ν ∈ Set.Icc (a : ℝ) b ∧ f1 (X ν) = ν) →
      ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * Complex.I) -
          κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
            ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              Complex.exp (((2 * Real.pi * (f (X ν) - (ν : ℝ) * X ν) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (lam2 ^ (-(1 / 2 : ℝ)) + Real.log (2 + ((b : ℝ) - a) * lam2) +
          ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ)) :=
  GuthMaynard.SubWeyl.b_process R hR
