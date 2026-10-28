-- Prove2me | solution 1 for OAI.TraceReconstruction.actual_initial_oracles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:53:33.069176+00:00
-- url     : https://prove2.me/submissions/0a1ecff9-1dd5-4070-aea1-f0d4cecb2200

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_initial_pure_sigma_clipped_exists
import Theorems.Thm_OAI_TraceReconstruction_initial_sigma_clipped_exists

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/

theorem centralBinom_square_bound (n : ℕ) :
    ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hr : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc : 4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2) ≤
        16 * (n + 1) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
    have hh : ((n : ℝ) + 1) ^ 2 *
        ((n + 2) * ((n + 1).centralBinom : ℝ) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 * (16 * 16 ^ n) := by
      calc
        _ = (n + 2) * (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) ^ 2 := by ring
        _ = (4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2)) *
            (n.centralBinom : ℝ) ^ 2 := by rw [hr]; ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 3) * (n.centralBinom : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = (16 * ((n : ℝ) + 1) ^ 2) *
            (((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2) := by ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 2) * 16 ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
    have := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
    rw [pow_succ (16 : ℝ) n]
    convert this using 1 <;> push_cast <;> first | rfl | ring

theorem choose_odd_le_twice_central (n k : ℕ) :
    (2 * n + 1).choose k ≤ 2 * n.centralBinom := by
  cases k with
  | zero => simp only [Nat.choose_zero_right]; have := Nat.centralBinom_pos n; omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h₁ := Nat.choose_le_centralBinom k n
    have h₂ := Nat.choose_le_centralBinom (k + 1) n
    simpa [Nat.succ_eq_add_one, two_mul] using Nat.add_le_add h₁ h₂

theorem fairBinomial_square_bound (n k : ℕ) :
    ((n : ℝ) + 1) * fairBinomial n k ^ 2 ≤ 2 := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hcases with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hc : ((2 * m).choose k : ℝ) ≤ (m.centralBinom : ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom k m
    have hcs : ((2 * m).choose k : ℝ) ^ 2 ≤ (m.centralBinom : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m)) ^ 2 = 16 ^ m := by
      rw [← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity),
      sq_nonneg ((2 * m).choose k : ℝ)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hc : ((2 * m + 1).choose k : ℝ) ≤ 2 * (m.centralBinom : ℝ) :=
      by exact_mod_cast choose_odd_le_twice_central m k
    have hcs : ((2 * m + 1).choose k : ℝ) ^ 2 ≤ 4 * (m.centralBinom : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * m + 1).choose k : ℝ)) hc 2
      nlinarith
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
      rw [pow_add, mul_pow, ← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
      ring
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m + 1)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity)]


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

theorem series_summable (f : IntSeries) (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    Summable (fun z : ℤ => φ (f.coeff z)) :=
  summable_of_hasFiniteSupport (f.coeff.hasFiniteSupport.fun_comp hφ)

theorem seriesL1_nonneg (f : IntSeries) : 0 ≤ seriesL1 f :=
  tsum_nonneg fun _ => abs_nonneg _

theorem seriesL2Sq_nonneg (f : IntSeries) : 0 ≤ seriesL2Sq f :=
  tsum_nonneg fun _ => sq_nonneg _

theorem seriesL1_eq_sum (f : IntSeries) :
    seriesL1 f = ∑ z ∈ f.coeff.support, |f.coeff z| := by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]

theorem series_summable_shift (f : IntSeries) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) (a : ℤ) :
    Summable (fun z : ℤ => φ (f.coeff (a + z))) := by
  exact (Equiv.addLeft a).summable_iff.mpr (series_summable f φ hφ)

theorem series_sum_shift (f : IntSeries) (φ : ℝ → ℝ) (a : ℤ) :
    (∑' z : ℤ, φ (f.coeff (a + z))) = ∑' z : ℤ, φ (f.coeff z) :=
  (Equiv.addLeft a).tsum_eq (fun z => φ (f.coeff z))

theorem series_coeff_mul_abs_le (f g : IntSeries) (z : ℤ) :
    |(f * g).coeff z| ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun a => f.coeff a * g.coeff (-a + z)) f.coeff.support

theorem seriesL1_mul_le (f g : IntSeries) :
    seriesL1 (f * g) ≤ seriesL1 f * seriesL1 g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * |g.coeff (-a + z)|) :=
    (series_summable_shift g abs (by simp) (-a)).mul_left _
  calc
    seriesL1 (f * g) ≤ ∑' z : ℤ, ∑ a ∈ f.coeff.support,
        |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_le_tsum (series_coeff_mul_abs_le f g) (series_summable (f * g) abs (by simp))
        (summable_sum fun a _ => hh a)
    _ = ∑ a ∈ f.coeff.support, ∑' z : ℤ, |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_finsetSum fun a _ => hh a
    _ = (∑ a ∈ f.coeff.support, |f.coeff a|) * seriesL1 g := by
      simp_rw [tsum_mul_left, series_sum_shift]
      exact (Finset.sum_mul _ _ _).symm
    _ = seriesL1 f * seriesL1 g := by rw [seriesL1_eq_sum f]

theorem series_coeff_mul_sq_le (f g : IntSeries) (z : ℤ) :
    (f * g).coeff z ^ 2 ≤ seriesL1 f *
      ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, seriesL1_eq_sum]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _; exact abs_nonneg _
  · intro a _; positivity
  · intro a _
    rw [mul_pow, ← mul_assoc, ← sq, sq_abs]

theorem seriesL2Sq_mul_le (f g : IntSeries) :
    seriesL2Sq (f * g) ≤ seriesL1 f ^ 2 * seriesL2Sq g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * (g.coeff (-a + z)) ^ 2) :=
    (series_summable_shift g (fun x => x ^ 2) (by simp) (-a)).mul_left _
  calc
    seriesL2Sq (f * g) ≤ ∑' z : ℤ, seriesL1 f *
        ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 :=
      Summable.tsum_le_tsum (series_coeff_mul_sq_le f g)
        (series_summable (f * g) (fun x => x ^ 2) (by simp))
        ((summable_sum fun a _ => hh a).mul_left _)
    _ = seriesL1 f * ∑ a ∈ f.coeff.support,
        ∑' z : ℤ, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
      rw [tsum_mul_left, Summable.tsum_finsetSum fun a _ => hh a]
    _ = seriesL1 f ^ 2 * seriesL2Sq g := by
      simp_rw [tsum_mul_left, series_sum_shift g (fun x => x ^ 2)]
      rw [← Finset.sum_mul, ← seriesL1_eq_sum]
      unfold seriesL2Sq
      ring

theorem series_coeff_mul_bound (f g : IntSeries) (M : ℝ)
    (hg : ∀ z, |g.coeff z| ≤ M) (z : ℤ) :
    |(f * g).coeff z| ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| :=
      series_coeff_mul_abs_le f g z
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * M :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
    _ = seriesL1 f * M := by rw [← Finset.sum_mul, ← seriesL1_eq_sum]

/-! The probability generating series of the fair binomial kernel. -/

theorem fairSeries_add (m n : ℕ) : fairSeries (m + n) = fairSeries m * fairSeries n :=
  pow_add _ m n

theorem seriesL1_eq_sum_range (f : IntSeries) (n : ℕ)
    (hneg : ∀ z < 0, f.coeff z = 0)
    (hhigh : ∀ k : ℕ, n < k → f.coeff k = 0) :
    seriesL1 f = ∑ k ∈ Finset.range (n + 1), |f.coeff (k : ℤ)| := by
  let e : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  calc
    seriesL1 f = ∑ z ∈ (Finset.range (n + 1)).map e, |f.coeff z| := by
      apply tsum_eq_sum
      intro z hz
      by_cases h : 0 ≤ z
      · have heq : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have hh : n < z.toNat := by
          by_contra hn
          apply hz
          exact Finset.mem_map.mpr ⟨z.toNat, Finset.mem_range.mpr (by omega), heq⟩
        rw [← heq, hhigh _ hh, abs_zero]
      · rw [hneg z (by omega), abs_zero]
    _ = _ := Finset.sum_map _ e _

theorem firstDifference_coeff (f : IntSeries) (z : ℤ) :
    (firstDifference * f).coeff z = f.coeff z - f.coeff (z - 1) := by
  rw [firstDifference, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [neg_zero, add_zero, mul_one, sub_eq_add_neg]

theorem fairSeries_difference_coeff_zero (n : ℕ) :
    (firstDifference * fairSeries n).coeff 0 = fairBinomial n 0 := by
  rw [firstDifference_coeff]
  norm_num only [zero_sub]
  rw [fairSeries_coeff_neg n (-1) (by norm_num), sub_zero]
  exact fairSeries_coeff_nat n 0

theorem fairSeries_difference_coeff_succ (n k : ℕ) :
    (firstDifference * fairSeries n).coeff (↑(k + 1) : ℤ) =
      fairBinomial n (k + 1) - fairBinomial n k := by
  rw [firstDifference_coeff, fairSeries_coeff_nat]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, fairSeries_coeff_nat]

theorem fairBinomial_unimodal_left (n k : ℕ) (hk : k < n / 2) :
    fairBinomial n k ≤ fairBinomial n (k + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk

theorem fairBinomial_unimodal_right (n k : ℕ) (hk : n / 2 ≤ k) :
    fairBinomial n (k + 1) ≤ fairBinomial n k := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnk : n - k ≤ k + 1 := by omega
  have hmul := Nat.mul_le_mul_left (n.choose k) hnk
  rw [← Nat.choose_succ_right_eq] at hmul
  exact_mod_cast Nat.le_of_mul_le_mul_right hmul (by omega : 0 < k + 1)

theorem fairBinomial_variation (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), |fairBinomial n (k + 1) - fairBinomial n k|) =
      2 * fairBinomial n (n / 2) - fairBinomial n 0 := by
  have hmid : n / 2 ≤ n + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hmid]
  have hl : (∑ k ∈ Finset.range (n / 2),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n 0 := by
    rw [← Finset.sum_range_sub (fairBinomial n) (n / 2)]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr
      (fairBinomial_unimodal_left n k (Finset.mem_range.mp hk)))
  have hr : (∑ k ∈ Finset.Ico (n / 2) (n + 1),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n (n + 1) := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2) (n + 1),
          -(fairBinomial n (k + 1) - fairBinomial n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr
          (fairBinomial_unimodal_right n k (Finset.mem_Ico.mp hk).1))
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_Ico_sub _ hmid]; ring
  rw [hl, hr]
  have hzero : fairBinomial n (n + 1) = 0 := by simp [fairBinomial]
  rw [hzero]
  ring

theorem fairSeries_difference_L1 (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) = 2 * fairBinomial n (n / 2) := by
  rw [seriesL1_eq_sum_range _ (n + 1)]
  · rw [Finset.sum_range_succ', Nat.cast_zero, fairSeries_difference_coeff_zero,
      abs_of_nonneg (fairBinomial_nonneg n 0)]
    simp_rw [fairSeries_difference_coeff_succ]
    rw [fairBinomial_variation]
    ring
  · intro z hz
    rw [firstDifference_coeff, fairSeries_coeff_neg n z hz,
      fairSeries_coeff_neg n (z - 1) (by omega), sub_zero]
  · intro k hk
    have hkpos : 0 < k := by omega
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    rw [fairSeries_difference_coeff_succ]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt (by omega : n < v),
      Nat.choose_eq_zero_of_lt (by omega : n < v + 1)]

theorem binomialBound_nonneg (n : ℕ) : 0 ≤ binomialBound n := Real.sqrt_nonneg _

theorem fairBinomial_le_bound (n k : ℕ) : fairBinomial n k ≤ binomialBound n := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  simpa only [mul_comm] using fairBinomial_square_bound n k

theorem fairSeries_coeff_bound (n : ℕ) (z : ℤ) :
    |(fairSeries n).coeff z| ≤ binomialBound n := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat,
      abs_of_nonneg (fairBinomial_nonneg _ _)]
    exact fairBinomial_le_bound _ _
  · rw [fairSeries_coeff_neg n z (by omega), abs_zero]
    exact binomialBound_nonneg n

theorem fairSeries_L1 (n : ℕ) : seriesL1 (fairSeries n) = 1 := by
  rw [seriesL1_eq_sum_range _ n (fairSeries_coeff_neg n)]
  · simp_rw [fairSeries_coeff_nat, abs_of_nonneg (fairBinomial_nonneg _ _)]
    unfold fairBinomial
    rw [← Finset.sum_div]
    have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum, div_self (by positivity)]
  · intro k hk
    rw [fairSeries_coeff_nat]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt hk]

theorem seriesL2Sq_le_L1_mul_bound (f : IntSeries) (M : ℝ)
    (hf : ∀ z, |f.coeff z| ≤ M) : seriesL2Sq f ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑' z : ℤ, |f.coeff z| * M := by
      apply Summable.tsum_le_tsum
      · intro z
        calc
          f.coeff z ^ 2 = |f.coeff z| * |f.coeff z| := by rw [← sq, sq_abs]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)
      · exact series_summable f (fun x => x ^ 2) (by simp)
      · exact (series_summable f abs (by simp)).mul_right M
    _ = _ := tsum_mul_right

theorem fairSeries_L2Sq_bound (n : ℕ) : seriesL2Sq (fairSeries n) ≤ binomialBound n := by
  simpa only [fairSeries_L1, one_mul] using
    seriesL2Sq_le_L1_mul_bound (fairSeries n) (binomialBound n) (fairSeries_coeff_bound n)

theorem fairSeries_difference_L1_bound (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) ≤ 2 * binomialBound n := by
  rw [fairSeries_difference_L1]
  exact mul_le_mul_of_nonneg_left (fairBinomial_le_bound n (n / 2)) (by norm_num)

theorem seriesL1_single (z : ℤ) (r : ℝ) :
    seriesL1 (AddMonoidAlgebra.single z r) = |r| := by
  unfold seriesL1
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [apply_ite abs, abs_zero]
  exact tsum_ite_eq' z (fun _ : ℤ => |r|)

theorem seriesL1_one : seriesL1 (1 : IntSeries) = 1 := by
  change seriesL1 (AddMonoidAlgebra.single 0 1) = 1
  rw [seriesL1_single, abs_one]

theorem seriesL1_pow_le (f : IntSeries) (s : ℕ) : seriesL1 (f ^ s) ≤ seriesL1 f ^ s := by
  induction s with
  | zero => simp only [pow_zero, seriesL1_one, le_refl]
  | succ s ih =>
    rw [pow_succ, pow_succ]
    exact (seriesL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (seriesL1_nonneg f))

theorem fairSeries_mul_power (n s : ℕ) :
    firstDifference ^ s * fairSeries ((s + 1) * n) =
      (firstDifference * fairSeries n) ^ s * fairSeries n := by
  simp only [fairSeries, add_mul, one_mul, pow_add, pow_mul, mul_pow]
  ring

/-- Quantitative higher-order smoothing, with n trials assigned to each
    difference and one further group reserved for anti-concentration. -/
theorem binomial_difference_coeff_bound (n s : ℕ) (z : ℤ) :
    |(firstDifference ^ s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 * binomialBound n) ^ s * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (series_coeff_mul_bound _ _ _ (fairSeries_coeff_bound n) z).trans
  apply mul_le_mul_of_nonneg_right _ (binomialBound_nonneg n)
  exact (seriesL1_pow_le _ _).trans
    (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)

theorem binomial_difference_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (firstDifference ^ s * fairSeries ((s + 1) * n)) ≤
      ((2 * binomialBound n) ^ s) ^ 2 * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (seriesL1_nonneg _)
    exact (seriesL1_pow_le _ _).trans
      (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)
  · exact fairSeries_L2Sq_bound n
  · exact seriesL2Sq_nonneg _
  · positivity

theorem seriesL1_add_le (f g : IntSeries) :
    seriesL1 (f + g) ≤ seriesL1 f + seriesL1 g := by
  calc
    _ ≤ ∑' z : ℤ, (|f.coeff z| + |g.coeff z|) := by
      apply Summable.tsum_le_tsum
      · intro z
        simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
          abs_add_le (f.coeff z) (g.coeff z)
      · exact series_summable (f + g) abs (by simp)
      · exact (series_summable f abs (by simp)).add (series_summable g abs (by simp))
    _ = _ := (series_summable f abs (by simp)).tsum_add (series_summable g abs (by simp))

theorem seriesL1_zero : seriesL1 (0 : IntSeries) = 0 := by
  simp [seriesL1]

theorem seriesL1_sum_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∑ i ∈ A, f i) ≤ ∑ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, seriesL1_zero, le_refl]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (seriesL1_add_le _ _).trans (add_le_add le_rfl ih)

theorem seriesL1_prod_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∏ i ∈ A, f i) ≤ ∏ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, seriesL1_one, le_refl]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (seriesL1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (seriesL1_nonneg _))

theorem geomSeries_difference (k : ℕ) :
    geomSeries k * firstDifference = 1 - (AddMonoidAlgebra.single 1 1 : IntSeries) ^ k := by
  exact geom_sum_mul_neg _ _

theorem geomSeries_L1_le (k : ℕ) : seriesL1 (geomSeries k) ≤ k := by
  apply (seriesL1_sum_le _ _).trans
  simp only [AddMonoidAlgebra.single_pow, one_pow, seriesL1_single, abs_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, le_refl]

theorem prouhetSeries_factor (s : ℕ) :
    prouhetSeries s = prouhetQuotient s * firstDifference ^ s := by
  unfold prouhetSeries prouhetQuotient
  simp_rw [← geomSeries_difference]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]

theorem prouhetQuotient_L1_le (s : ℕ) :
    seriesL1 (prouhetQuotient s) ≤ (2 : ℝ) ^ (s * s) := by
  calc
    _ ≤ ∏ v ∈ Finset.range s, seriesL1 (geomSeries (2 ^ v)) := seriesL1_prod_le _ _
    _ ≤ ∏ _v ∈ Finset.range s, ((2 : ℝ) ^ s) := by
      apply Finset.prod_le_prod
      · intro v _; exact seriesL1_nonneg _
      · intro v hv
        apply (geomSeries_L1_le _).trans
        push_cast
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact (Finset.mem_range.mp hv).le
    _ = _ := by simp only [Finset.prod_const, Finset.card_range, ← pow_mul]

/-- Prouhet smoothing in an explicit finite-trial form.  The constants
    2^(s*s) and (2 sqrt(2/(n+1)))^s are exp(O(s^2)) after assigning
    n = floor(g/(s+1)) trials to each group.  No Fourier theorem or
    probabilistic estimate is assumed. -/
theorem prouhet_binomial_coeff_bound (n s : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (series_coeff_mul_bound _ _ _ (binomial_difference_coeff_bound n s) z).trans
  exact mul_le_mul_of_nonneg_right (prouhetQuotient_L1_le s)
    (by positivity [binomialBound_nonneg n])

theorem prouhet_binomial_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · exact pow_le_pow_left₀ (seriesL1_nonneg _) (prouhetQuotient_L1_le s) 2
  · exact binomial_difference_L2Sq_bound n s
  · exact seriesL2Sq_nonneg _
  · positivity

/-- Arbitrary trial counts are obtained by convolving with the independent
    unused trials; this cannot enlarge the coefficient or squared-L2 bounds. -/
theorem prouhet_binomial_coeff_bound_remainder (n s r : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n + r)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  simpa only [fairSeries_L1, one_mul] using
    series_coeff_mul_bound (fairSeries r) (prouhetSeries s * fairSeries ((s + 1) * n))
      _ (prouhet_binomial_coeff_bound n s) z

theorem prouhet_binomial_L2Sq_bound_remainder (n s r : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n + r)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  calc
    _ ≤ seriesL1 (fairSeries r) ^ 2 *
        seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) := seriesL2Sq_mul_le _ _
    _ ≤ _ := by simpa only [fairSeries_L1, one_pow, one_mul] using
        prouhet_binomial_L2Sq_bound n s

theorem signed_binomial_smoothing (g s : ℕ) :
    (∀ z : ℤ, |(prouhetSeries s * fairSeries g).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound (g / (s + 1))) ^ s *
        binomialBound (g / (s + 1)))) ∧
    (seriesL2Sq (prouhetSeries s * fairSeries g) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound (g / (s + 1))) ^ s) ^ 2 *
        binomialBound (g / (s + 1)))) := by
  have hg : (s + 1) * (g / (s + 1)) + g % (s + 1) = g := Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using prouhet_binomial_coeff_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) z
  · simpa only [hg] using prouhet_binomial_L2Sq_bound_remainder (g / (s + 1)) s
      (g % (s + 1))

theorem binomialBound_quotient_le (g s : ℕ) :
    binomialBound (g / (s + 1)) ≤
      Real.sqrt (2 * ((s : ℝ) + 1) / ((g : ℝ) + 1)) := by
  apply Real.sqrt_le_sqrt
  have hn : g + 1 ≤ (g / (s + 1) + 1) * (s + 1) := by
    have hmod := Nat.mod_lt g (by omega : 0 < s + 1)
    have hdiv := Nat.div_add_mod g (s + 1)
    nlinarith
  have hnr : (g : ℝ) + 1 ≤ ((g / (s + 1) : ℕ) + (1 : ℝ)) * ((s : ℝ) + 1) := by
    exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (g / (s + 1) : ℕ) + 1)
    (by positivity : (0 : ℝ) < g + 1)).mpr
  nlinarith


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

theorem binomialMass_harmonic_step (n k : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p * (binomialMass n p k / ((k : ℝ) + 1)) =
      binomialMass (n + 1) p (k + 1) := by
  have hc : ((n : ℝ) + 1) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold binomialMass
  rw [Nat.add_sub_add_right, pow_succ]
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * p ^ k * (1 - p) ^ (n - k) * p) hc]

theorem binomialMass_harmonic_identity (n : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * p *
      (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) =
    1 - (1 - p) ^ (n + 1) := by
  rw [Finset.mul_sum]
  simp_rw [binomialMass_harmonic_step]
  have h := sum_binomialMass (n + 1) p
  rw [Finset.sum_range_succ'] at h
  simp only [binomialMass, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    mul_one, one_mul, Nat.sub_zero] at h ⊢
  linarith

theorem binomialMass_harmonic_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1)) ≤
      1 / (((n : ℝ) + 1) * p) := by
  apply (le_div_iff₀ (mul_pos (by positivity) hp.1)).mpr
  rw [mul_comm, binomialMass_harmonic_identity]
  have h := pow_nonneg (sub_nonneg.mpr hp.2) (n + 1)
  linarith

/-- The weighted Cauchy--Schwarz step for mixing the fair estimates. -/
theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ S, w i * f i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * f i ^ 2 := by
  have heq (i : ι) : w i * f i = Real.sqrt (w i) * (Real.sqrt (w i) * f i) := by
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i)]
  simp_rw [heq]
  apply (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)).trans_eq
  simp only [mul_pow, Real.sq_sqrt (hw _)]

theorem mixed_binomialBound_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ≤
      Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  have hw (k : ℕ) := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
  have hs := weighted_sum_sq_le (Finset.range (n + 1)) (binomialMass n p)
    binomialBound hw
  rw [sum_binomialMass, one_mul] at hs
  have hb (k : ℕ) : binomialBound k ^ 2 = 2 / ((k : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  simp_rw [hb] at hs
  have heq : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (2 / ((k : ℝ) + 1))) =
      2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hs
  have hh := binomialMass_harmonic_le n hp
  have hp0 := hp.1
  have hbound : (∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k) ^ 2 ≤
      2 / (((n : ℝ) + 1) * p) := by
    calc
      _ ≤ 2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k / ((k : ℝ) + 1) := hs
      _ ≤ 2 * (1 / (((n : ℝ) + 1) * p)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hsr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (((n : ℝ) + 1) * p) by positivity)
  have hpos := Real.sqrt_nonneg (2 / (((n : ℝ) + 1) * p))
  nlinarith only [hbound, hsr, hpos]


theorem mixedFairSeries_expansion (n : ℕ) (p : ℝ) :
    mixedFairSeries n p =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k • fairSeries k := by
  rw [mixedFairSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_pow, one_pow, smul_mul_smul, mul_one, fairSeries, pow_one]
  rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  unfold binomialMass
  ring

theorem mixedFairSeries_eq_biased (n : ℕ) (p : ℝ) :
    mixedFairSeries n p = biasedSeries n (p / 2) := by
  unfold mixedFairSeries biasedSeries
  congr 1
  ext z
  simp only [fairSeries, pow_one, smul_add, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> first | omega | ring

theorem mixedFairSeries_coeff_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) (z : ℤ) :
    |(mixedFairSeries n p).coeff z| ≤ Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  rw [mixedFairSeries_expansion, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), |binomialMass n p k * (fairSeries k).coeff z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k := by
      apply Finset.sum_le_sum
      intro k _
      have hw := binomialMass_nonneg n k (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2⟩)
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (fairSeries_coeff_bound k z) hw
    _ ≤ _ := mixed_binomialBound_le n hp

/-- At success probabilities at most 1/2, this gives the sharp variance
    scale up to an absolute constant, using only the fair-coin estimate. -/
theorem biasedSeries_coeff_bound_low (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioc 0 (1 / 2)) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤ Real.sqrt (1 / (((n : ℝ) + 1) * p)) := by
  have h2p : 2 * p ∈ Set.Ioc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have h := mixedFairSeries_coeff_bound n h2p z
  rw [mixedFairSeries_eq_biased, show 2 * p / 2 = p by ring] at h
  have heq : 2 / (((n : ℝ) + 1) * (2 * p)) = 1 / (((n : ℝ) + 1) * p) := by
    field_simp
  rwa [heq] at h


theorem biasedSeries_sum (n : ℕ) (p : ℝ) :
    biasedSeries n p = ∑ k ∈ Finset.range (n + 1),
      AddMonoidAlgebra.single (k : ℤ) (binomialMass n p k) := by
  rw [biasedSeries, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  unfold binomialMass
  ring

theorem biasedSeries_coeff_nat (n k : ℕ) (p : ℝ) :
    (biasedSeries n p).coeff (k : ℤ) = binomialMass n p k := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
    · intro b _ hb
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · intro b hb
      have hbk : b ≠ k := by simp only [Finset.mem_range] at hb; omega
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hbk]

theorem biasedSeries_coeff_neg (n : ℕ) (p : ℝ) (z : ℤ) (hz : z < 0) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  have h : (b : ℤ) ≠ z := by omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem biasedSeries_coeff_high (n : ℕ) (p : ℝ) (z : ℤ) (hz : (n : ℤ) < z) :
    (biasedSeries n p).coeff z = 0 := by
  rw [biasedSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  have h : (b : ℤ) ≠ z := by simp only [Finset.mem_range] at hb; omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

theorem binomialMass_symm (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    binomialMass n (1 - p) (n - k) = binomialMass n p k := by
  unfold binomialMass
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk, show 1 - (1 - p) = p by ring]
  ring

theorem biasedSeries_coeff_reflect (n : ℕ) (p : ℝ) (z : ℤ) :
    (biasedSeries n (1 - p)).coeff ((n : ℤ) - z) = (biasedSeries n p).coeff z := by
  by_cases hz : z < 0
  · rw [biasedSeries_coeff_neg n p z hz,
      biasedSeries_coeff_high n (1 - p) _ (by omega)]
  by_cases hz' : (n : ℤ) < z
  · rw [biasedSeries_coeff_high n p z hz',
      biasedSeries_coeff_neg n (1 - p) _ (by omega)]
  have h0 : 0 ≤ z := by omega
  have hk : z.toNat ≤ n := by omega
  have hzN : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h0
  have hsub : (n : ℤ) - z = ((n - z.toNat : ℕ) : ℤ) := by omega
  rw [hsub, ← hzN, biasedSeries_coeff_nat, biasedSeries_coeff_nat]
  exact binomialMass_symm n z.toNat p hk

/-- Uniform nonfair-binomial anti-concentration.  This is the absolute
    variance-scale upper bound used in the manuscript's rank kernels. -/
theorem biasedSeries_coeff_bound (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(biasedSeries n p).coeff z| ≤
      Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p))) := by
  by_cases hlow : p ≤ 1 / 2
  · apply (biasedSeries_coeff_bound_low n ⟨hp.1, hlow⟩ z).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · have hn : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith [mul_nonneg hn (sq_nonneg p)]
  · have hq : 1 - p ∈ Set.Ioc 0 (1 / 2) := ⟨by linarith [hp.2], by linarith⟩
    rw [← biasedSeries_coeff_reflect n p z]
    apply (biasedSeries_coeff_bound_low n hq ((n : ℤ) - z)).trans
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]


theorem binomialMass_mul_index (n k : ℕ) (p : ℝ) :
    binomialMass (n + 1) p (k + 1) * ((k : ℝ) + 1) =
      ((n : ℝ) + 1) * p * binomialMass n p k := by
  have h := binomialMass_harmonic_step n k p
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [← h]
  field_simp

theorem binomialMass_index_sum (n : ℕ) (p : ℝ) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * F k) =
      ((n : ℝ) + 1) * p *
        ∑ k ∈ Finset.range (n + 1), binomialMass n p k * F (k + 1) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  simp_rw [binomialMass_mul_index]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binomialMass_mean (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) = (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [mul_one, sum_binomialMass, Nat.cast_add, Nat.cast_one] using
      binomialMass_index_sum n p (fun _ => 1)

theorem binomialMass_second_moment (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 + (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
    have h := binomialMass_index_sum n p (fun k => k)
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, binomialMass_mean,
      sum_binomialMass] at h
    calc
      _ = ∑ k ∈ Finset.range (n + 2), binomialMass (n + 1) p k * (k : ℝ) * (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [h]; ring

theorem binomialMass_variance (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * ((k : ℝ) - (n : ℝ) * p) ^ 2) =
      (n : ℝ) * p * (1 - p) := by
  calc
    _ = (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) ^ 2) -
        2 * (n : ℝ) * p * (∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ)) +
        ((n : ℝ) * p) ^ 2 * (∑ k ∈ Finset.range (n + 1), binomialMass n p k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [binomialMass_second_moment, binomialMass_mean, sum_binomialMass]; ring

theorem binomialMass_adjacent (n k : ℕ) (p : ℝ) (hk : k < n) :
    ((k : ℝ) + 1) * (1 - p) * binomialMass n p (k + 1) =
      ((n : ℝ) - k) * p * binomialMass n p k := by
  have hc : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using
      congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq n k)
  have hnk : n - k = (n - (k + 1)) + 1 := by omega
  unfold binomialMass
  rw [hnk, pow_succ, pow_succ]
  linear_combination p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p) * hc

theorem binomialMass_le_mode (n l k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) :
    binomialMass n p k ≤ binomialMass n p l := by
  have h0 (j : ℕ) := binomialMass_nonneg n j ⟨hp.1.le, hp.2.le⟩
  have hleft (j : ℕ) (hj : j < l) : binomialMass n p j ≤ binomialMass n p (j + 1) := by
    have hrec := binomialMass_adjacent n j p (by omega)
    have hjr : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
    have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp.2)
    have hdiff : ((j : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - j) * p := by
      nlinarith [hp.1]
    have := mul_le_mul_of_nonneg_right hdiff (h0 j)
    nlinarith only [hrec, this, hcoef]
  have hright (j : ℕ) (hj : l ≤ j) : binomialMass n p (j + 1) ≤ binomialMass n p j := by
    by_cases hjn : j < n
    · have hrec := binomialMass_adjacent n j p hjn
      have hjr : (l : ℝ) ≤ j := by exact_mod_cast hj
      have hcoef : (0 : ℝ) < ((j : ℝ) + 1) * (1 - p) := by
        exact mul_pos (by positivity) (sub_pos.mpr hp.2)
      have hdiff : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * (1 - p) := by
        nlinarith [hp.2]
      have := mul_le_mul_of_nonneg_right hdiff (h0 j)
      nlinarith only [hrec, this, hcoef]
    · have hjn' : n < j + 1 := by omega
      simp only [binomialMass, Nat.choose_eq_zero_of_lt hjn', Nat.cast_zero, zero_mul]
      exact h0 j
  rcases le_total k l with hk | hk
  · have haux : ∀ b : ℕ, k ≤ b → b ≤ l → binomialMass n p k ≤ binomialMass n p b := by
      intro b hkb
      induction b, hkb using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hb ih =>
        intro hbl
        exact (ih (by omega)).trans (hleft b (by omega))
    exact haux l hk le_rfl
  · induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hright j hj).trans ih


/-- A discrete law cannot have a very small maximum when its variance is bounded.
The explicit constant is deliberately loose, avoiding any use of Stirling. -/
theorem discrete_mode_lower (n l : ℕ) (f : ℕ → ℝ) (M v : ℝ)
    (hf : ∀ k, 0 ≤ f k) (hsum : ∑ k ∈ Finset.range (n + 1), f k = 1)
    (hmax : ∀ k, f k ≤ M)
    (hvar : ∑ k ∈ Finset.range (n + 1), f k * ((k : ℝ) - l) ^ 2 = v)
    (hv : 1 ≤ v) : 1 / (12 * Real.sqrt v) ≤ M := by
  classical
  let r : ℕ := ⌈2 * Real.sqrt v⌉₊
  have hv0 : 0 ≤ v := by linarith
  have hs : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hs2 := Real.sq_sqrt hv0
  have hrlo : 2 * Real.sqrt v ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 2 * Real.sqrt v + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrpos : (0 : ℝ) < r := by linarith
  have hM : 0 ≤ M := (hf 0).trans (hmax 0)
  let S := (Finset.range (n + 1)).filter (fun k => l - r ≤ k ∧ k ≤ l + r)
  have hcard : S.card ≤ 2 * r + 1 := by
    have hsub : S ⊆ Finset.Icc (l - r) (l + r) := by
      intro k hk
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hout (k : ℕ) (hk : ¬(l - r ≤ k ∧ k ≤ l + r)) :
      (r : ℝ) ^ 2 ≤ ((k : ℝ) - l) ^ 2 := by
    by_cases hleft : k < l - r
    · have hnat : k + r < l := by omega
      have hreal : (k : ℝ) + r < l := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((l : ℝ) - k - r)]
    · have hnat : l + r < k := by omega
      have hreal : (l : ℝ) + r < k := by exact_mod_cast hnat
      nlinarith [sq_nonneg ((k : ℝ) - l - r)]
  have hpoint (k : ℕ) : (r : ℝ) ^ 2 * f k ≤
      (if l - r ≤ k ∧ k ≤ l + r then (r : ℝ) ^ 2 * M else 0) +
        f k * ((k : ℝ) - l) ^ 2 := by
    split_ifs with hk
    · have := mul_le_mul_of_nonneg_left (hmax k) (sq_nonneg (r : ℝ))
      have := mul_nonneg (hf k) (sq_nonneg ((k : ℝ) - l))
      linarith
    · simpa only [zero_add, mul_comm] using mul_le_mul_of_nonneg_left (hout k hk) (hf k)
  have htotal := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (n + 1)) => hpoint k)
  rw [← Finset.mul_sum, hsum, mul_one, Finset.sum_add_distrib, hvar,
    ← Finset.sum_filter] at htotal
  change (r : ℝ) ^ 2 ≤ ∑ k ∈ S, (r : ℝ) ^ 2 * M + v at htotal
  rw [Finset.sum_const, nsmul_eq_mul] at htotal
  have hcardR : (S.card : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hcard
  have hbound := mul_le_mul_of_nonneg_right hcardR (mul_nonneg (sq_nonneg (r : ℝ)) hM)
  have htotal' : (r : ℝ) ^ 2 ≤ (2 * r + 1) * ((r : ℝ) ^ 2 * M) + v := by
    linarith
  have hrv : 4 * v ≤ (r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 2 * Real.sqrt v)]
  have hcancel : (3 : ℝ) / 4 ≤ (2 * r + 1) * M := by
    have hrr : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    nlinarith only [htotal', hrv, hrr]
  have hsize : 2 * (r : ℝ) + 1 ≤ 7 * Real.sqrt v := by linarith
  have hfinal := mul_le_mul_of_nonneg_right hsize hM
  apply (div_le_iff₀ (by positivity : 0 < 12 * Real.sqrt v)).mpr
  nlinarith only [hcancel, hfinal]

theorem binomialMass_mean_lower (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    1 / (12 * Real.sqrt ((n : ℝ) * p * (1 - p))) ≤ binomialMass n p l := by
  apply discrete_mode_lower n l (binomialMass n p)
    (binomialMass n p l) ((n : ℝ) * p * (1 - p))
  · intro k; exact binomialMass_nonneg n k ⟨hp.1.le, hp.2.le⟩
  · exact sum_binomialMass n p
  · intro k; exact binomialMass_le_mode n l k hp hl hmean
  · rw [← hmean]; exact binomialMass_variance n p
  · exact hv


theorem binomialMass_mean_inverse_sq (n l : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p)) :
    (binomialMass n p l)⁻¹ ^ 2 ≤ 144 * ((n : ℝ) * p * (1 - p)) := by
  have hs : 0 < Real.sqrt ((n : ℝ) * p * (1 - p)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hlow := binomialMass_mean_lower n l hp hl hmean hv
  have hpos : 0 < binomialMass n p l := lt_of_lt_of_le (by positivity) hlow
  have hi : (binomialMass n p l)⁻¹ ≤ 12 * Real.sqrt ((n : ℝ) * p * (1 - p)) := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have := (div_le_iff₀ (by positivity)).mp hlow
    nlinarith only [this]
  have his := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hi
  have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) * p * (1 - p) by linarith)
  nlinarith only [his, hs2]

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

theorem binomialMass_tilt (n k : ℕ) {p a : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ha : 0 < a) :
    binomialMass n p k * a ^ k =
      (1 - p + p * a) ^ n * binomialMass n (p * a / (1 - p + p * a)) k := by
  by_cases hk : k ≤ n
  · have hA : 0 < 1 - p + p * a := by positivity [sub_pos.mpr hp.2, hp.1]
    have hsub : 1 - p * a / (1 - p + p * a) = (1 - p) / (1 - p + p * a) := by
      field_simp; ring
    unfold binomialMass
    rw [hsub, div_pow, div_pow, mul_pow]
    have hpow : (1 - p + p * a) ^ n =
        (1 - p + p * a) ^ k * (1 - p + p * a) ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hpow]
    field_simp
  · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : n < k)]

theorem binomialMass_tilt_product (g h k : ℕ) {p a : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ha : 0 < a) :
    binomialMass g p k * binomialMass h p k =
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        (binomialMass g (p * a / (1 - p + p * a)) k *
          binomialMass h ((p / a) / (1 - p + p / a)) k) := by
  have h1 := binomialMass_tilt g k hp ha
  have h2 := binomialMass_tilt h k hp (inv_pos.mpr ha)
  have hid := congrArg₂ (· * ·) h1 h2
  simp only [inv_pow, ← div_eq_mul_inv] at hid
  have ha0 : a ^ k ≠ 0 := pow_ne_zero _ ha.ne'
  calc
    _ = (binomialMass g p k * a ^ k) * (binomialMass h p k / a ^ k) := by field_simp
    _ = _ := by convert hid using 1; ring

/-- Tilting on opposite sides retains an anti-concentration factor as well
as the Gaussian penalty for different numbers of trials. -/
theorem binomial_overlap_tilt_bound (g h : ℕ) {p a : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (ha : 0 < a) :
    (∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k) ≤
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        biasedBinomialBound g (p * a / (1 - p + p * a)) := by
  have hA : 0 < 1 - p + p * a := by positivity [sub_pos.mpr hp.2, hp.1]
  have hB : 0 < 1 - p + p / a := by positivity [sub_pos.mpr hp.2, hp.1]
  have hpA : p * a / (1 - p + p * a) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hA).mpr; linarith [hp.2]
  have hpB : (p / a) / (1 - p + p / a) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hB).mpr; linarith [hp.2]
  simp_rw [binomialMass_tilt_product g h _ hp ha, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.range (h + 1),
        biasedBinomialBound g (p * a / (1 - p + p * a)) *
          binomialMass h ((p / a) / (1 - p + p / a)) k := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (binomialMass_nonneg _ _ ⟨hpB.1.le, hpB.2.le⟩)
      have hb := biasedSeries_coeff_bound g hpA (k : ℤ)
      rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ ⟨hpA.1.le, hpA.2.le⟩)] at hb
      exact hb
    _ = _ := by rw [← Finset.mul_sum, sum_binomialMass, mul_one]


theorem binomial_tilt_variance {p t : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (ht : t ∈ Set.Icc 0 (1 / 4 : ℝ)) :
    p * (1 - p) / 2 ≤
      (p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))) := by
  have hA : 0 < 1 - p + p * (1 - t) := by
    have := hp.1; have := hp.2; have := ht.2
    positivity [sub_pos.mpr hp.2, show (0 : ℝ) < 1 - t by linarith]
  have hA1 : 1 - p + p * (1 - t) ≤ 1 := by nlinarith [mul_nonneg hp.1.le ht.1]
  have hAsq : (1 - p + p * (1 - t)) ^ 2 ≤ 1 := by nlinarith
  have hpq : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have heq : (p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))) =
      p * (1 - p) * (1 - t) / (1 - p + p * (1 - t)) ^ 2 := by
    field_simp; ring
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hh := mul_le_mul_of_nonneg_left hAsq hpq.le
  nlinarith [ht.2]

theorem binomial_tilt_normalizer (g h : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hhg : h ≤ g) (hS : 0 < g + h) :
    let t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h))
    ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  dsimp only
  set t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h)) with htdef
  have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
  have hgr : (h : ℝ) ≤ g := by exact_mod_cast hhg
  have hd : (0 : ℝ) ≤ (g : ℝ) - h := sub_nonneg.mpr hgr
  have ht0 : 0 ≤ t := div_nonneg hd (by positivity)
  have ht1 : t ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    nlinarith [show (0 : ℝ) ≤ h by positivity]
  have htlt : 0 < 1 - t := by linarith
  have hp0 : 0 < p := by linarith [hp.1]
  have hA : 0 < 1 - p + p * (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hB : 0 < 1 - p + p / (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hlogA : Real.log (1 - p + p * (1 - t)) ≤ -p * t := by
    have := Real.log_le_sub_one_of_pos hA
    nlinarith only [this]
  have hlogB : Real.log (1 - p + p / (1 - t)) ≤ p * t / (1 - t) := by
    have := Real.log_le_sub_one_of_pos hB
    have heq : 1 - p + p / (1 - t) - 1 = p * t / (1 - t) := by field_simp; ring
    rwa [heq] at this
  have hlog : Real.log ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      -(p * ((g : ℝ) - h) * t) + 2 * p * h * t ^ 2 := by
    rw [Real.log_mul (pow_pos hA _).ne' (pow_pos hB _).ne', Real.log_pow, Real.log_pow]
    have hb : (h : ℝ) * (p * t / (1 - t)) ≤ (h : ℝ) * (p * t + 2 * p * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ htlt).mpr
      have hh := mul_nonneg (mul_nonneg hp0.le (sq_nonneg t)) (show 0 ≤ 1 - 2 * t by linarith)
      nlinarith only [hh]
    have ha := mul_le_mul_of_nonneg_left hlogA (show (0 : ℝ) ≤ g by positivity)
    have hb' := mul_le_mul_of_nonneg_left hlogB (show (0 : ℝ) ≤ h by positivity)
    linarith
  have hht : 4 * (h : ℝ) * t ≤ (g : ℝ) - h := by
    rw [htdef, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    have hm := mul_nonneg (show (0 : ℝ) ≤ g by positivity) hd
    nlinarith only [hm]
  have hhalf : -(p * ((g : ℝ) - h) * t) + 2 * p * h * t ^ 2 ≤
      -(p * ((g : ℝ) - h) * t) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hht (mul_nonneg hp0.le ht0)
    nlinarith only [hm]
  have hlast : -(p * ((g : ℝ) - h) * t) / 2 ≤
      -((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h)) := by
    rw [htdef]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr
    field_simp
    have hm := mul_nonneg (show 0 ≤ 2 * p - 1 by linarith [hp.1]) (sq_nonneg ((g : ℝ) - h))
    nlinarith only [hm]
  have hexp := Real.exp_le_exp.mpr (hlog.trans (hhalf.trans hlast))
  rwa [Real.exp_log (mul_pos (pow_pos hA _) (pow_pos hB _))] at hexp


/-- The Gaussian cross-overlap estimate used by the conditional rank-kernel
square-sum argument. The constant is absolute, also as p tends to one. -/
theorem binomial_gaussian_overlap (g h : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hhg : h ≤ g) (hS : 0 < g + h) :
    (∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
        Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  let t : ℝ := ((g : ℝ) - h) / (4 * ((g : ℝ) + h))
  have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
  have hgr : (h : ℝ) ≤ g := by exact_mod_cast hhg
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hgr) (by positivity)
  have ht1 : t ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((g : ℝ) + h))).mpr
    nlinarith [show (0 : ℝ) ≤ h by positivity]
  have htlt : 0 < 1 - t := by linarith
  have hp0 : 0 < p := by linarith [hp.1]
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, hp.2⟩
  have hA : 0 < 1 - p + p * (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hB : 0 < 1 - p + p / (1 - t) := by positivity [sub_pos.mpr hp.2]
  have hv := binomial_tilt_variance hp' ⟨ht0, ht1⟩
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  have hx : 0 < (p * (1 - t) / (1 - p + p * (1 - t))) *
      (1 - p * (1 - t) / (1 - p + p * (1 - t))) := lt_of_lt_of_le (by positivity) hv
  have hb : biasedBinomialBound g (p * (1 - t) / (1 - p + p * (1 - t))) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) := by
    apply Real.sqrt_le_sqrt
    have hg : (0 : ℝ) < (g : ℝ) + 1 := by positivity
    apply (div_le_div_iff₀ (by nlinarith only [mul_pos hg hx]) (by nlinarith only [mul_pos hg hpq])).mpr
    have hm := mul_le_mul_of_nonneg_left hv hg.le
    nlinarith only [hm]
  have hn := binomial_tilt_normalizer g h hp hhg hS
  change ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤ _ at hn
  have he := binomial_overlap_tilt_bound g h hp' htlt
  apply he.trans
  have hbound := mul_le_mul hn hb (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  simpa only [mul_comm] using hbound


theorem sqrt_times_gaussian_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x + 1) * Real.exp (-x / 96) ≤ 16 := by
  have he : Real.exp (-x / 96) ^ 2 = 1 / Real.exp (x / 48) := by
    rw [pow_two, ← Real.exp_add]
    rw [show -x / 96 + -x / 96 = -(x / 48) by ring, Real.exp_neg, one_div]
  have hs : (Real.sqrt (x + 1) * Real.exp (-x / 96)) ^ 2 ≤ 256 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), he, mul_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hh := Real.add_one_le_exp (x / 48)
    nlinarith only [hh, hx]
  nlinarith only [hs]

theorem sqrt_recip_product_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 2 * b) :
    Real.sqrt (1 / a) * Real.sqrt (1 / b) ≤ 2 / a := by
  rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  field_simp
  nlinarith

theorem binomialMass_le_bound (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p k ≤ biasedBinomialBound n p := by
  have h := biasedSeries_coeff_bound n hp (k : ℤ)
  rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ ⟨hp.1.le, hp.2.le⟩)] at h
  exact h

/-- A uniform product-supremum estimate, including very unequal trial
counts. This justifies eliminating a largest gap in the rank kernel. -/
theorem binomial_product_sup (g h k : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) :
    binomialMass g p k * binomialMass h p k ≤
      32 / (((g : ℝ) + 1) * p * (1 - p)) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, hp.2⟩
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  have hpq1 : p * (1 - p) ≤ 1 := by nlinarith only [sq_nonneg (p - 1 / 2)]
  have hden : 0 < ((g : ℝ) + 1) * p * (1 - p) := by nlinarith only [mul_pos (show (0 : ℝ) < (g : ℝ) + 1 by positivity) hpq]
  by_cases hnear : g ≤ 2 * h
  · have hdenh : 0 < ((h : ℝ) + 1) * p * (1 - p) := by nlinarith only [mul_pos (show (0 : ℝ) < (h : ℝ) + 1 by positivity) hpq]
    have hgh : ((g : ℝ) + 1) * p * (1 - p) ≤ 2 * (((h : ℝ) + 1) * p * (1 - p)) := by
      have hcast : (g : ℝ) ≤ 2 * h := by exact_mod_cast hnear
      have hm := mul_le_mul_of_nonneg_right (show (g : ℝ) + 1 ≤ 2 * ((h : ℝ) + 1) by linarith) hpq.le
      nlinarith only [hm]
    calc
      _ ≤ biasedBinomialBound g p * biasedBinomialBound h p :=
        mul_le_mul (binomialMass_le_bound g k hp') (binomialMass_le_bound h k hp')
          (binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩) (Real.sqrt_nonneg _)
      _ ≤ 2 / (((g : ℝ) + 1) * p * (1 - p)) := sqrt_recip_product_le hden hdenh hgh
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hden.le
  · by_cases hk : k ≤ h
    · have hhg : h ≤ g := by omega
      have hS : 0 < g + h := by omega
      have hsum : binomialMass g p k * binomialMass h p k ≤
          ∑ j ∈ Finset.range (h + 1), binomialMass g p j * binomialMass h p j := by
        exact Finset.single_le_sum (s := Finset.range (h + 1)) (a := k) (fun j _ => mul_nonneg
          (binomialMass_nonneg g j ⟨hp0.le, hp.2.le⟩)
          (binomialMass_nonneg h j ⟨hp0.le, hp.2.le⟩)) (Finset.mem_range.mpr (by omega))
      have hgauss := binomial_gaussian_overlap g h hp hhg hS
      have hSr : (0 : ℝ) < (g : ℝ) + h := by exact_mod_cast hS
      have hfar : 2 * (h : ℝ) < g := by exact_mod_cast (show 2 * h < g by omega)
      have hexp : Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) ≤ Real.exp (-(g : ℝ) / 96) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((g : ℝ) + h)) (by norm_num : (0 : ℝ) < 96)).mpr
        have hn := mul_nonneg (show 0 ≤ (g : ℝ) - 2 * h by linarith) (show 0 ≤ 5 * (g : ℝ) - 3 * h by linarith)
        nlinarith only [hn, sq_nonneg (h : ℝ)]
      have hcoeff : Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) ≤
          (2 / (((g : ℝ) + 1) * p * (1 - p))) * Real.sqrt ((g : ℝ) + 1) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (by positivity), div_pow]
        have hgpos : (0 : ℝ) < (g : ℝ) + 1 := by positivity
        have hqpos : 0 < 1 - p := sub_pos.mpr hp.2
        field_simp
        have hm := mul_le_mul_of_nonneg_left hpq1 (show (0 : ℝ) ≤ (g : ℝ) + 1 by positivity)
        nlinarith only [hm, hpq1]
      calc
        _ ≤ Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
            Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := hsum.trans hgauss
        _ ≤ ((2 / (((g : ℝ) + 1) * p * (1 - p))) * Real.sqrt ((g : ℝ) + 1)) *
            Real.exp (-(g : ℝ) / 96) := mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by positivity)
        _ ≤ (2 / (((g : ℝ) + 1) * p * (1 - p))) * 16 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (sqrt_times_gaussian_le (by positivity)) (by positivity)
        _ = _ := by ring
    · simp [binomialMass, Nat.choose_eq_zero_of_lt (by omega : h < k)]
      positivity

end TraceReconstruction

namespace TraceReconstruction

/-- Exact moment generating function, including both endpoint channels. -/
theorem binomialMass_mgf (n : ℕ) (p t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) =
      (1 - p + p * Real.exp t) ^ n := by
  rw [add_comm (1 - p), add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [show t * (k : ℝ) = (k : ℝ) * t by ring, Real.exp_nat_mul, mul_pow]
  unfold binomialMass
  ring

theorem binomialMass_mgf_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) ≤
      Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := by
  rw [binomialMass_mgf]
  have hn : 0 ≤ 1 - p + p * Real.exp t := by positivity [sub_nonneg.mpr hp.2, hp.1]
  have he : 1 - p + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
    nlinarith only [Real.add_one_le_exp (p * (Real.exp t - 1))]
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) ^ n := pow_le_pow_left₀ hn he n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Exponential Markov bound for a finite nonnegative measure. -/
theorem finite_exp_markov {α : Type*} (S : Finset α) (w X : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (a t : ℝ) (ht : 0 ≤ t) :
    (∑ z ∈ S with a ≤ X z, w z) ≤
      Real.exp (-t * a) * ∑ z ∈ S, w z * Real.exp (t * X z) := by
  classical
  calc
    _ = ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * a)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_left_comm, ← Real.exp_add]
      simp
    _ ≤ ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := Finset.mem_filter.mp hz
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.2 ht)) (hw z h.1))
        (Real.exp_nonneg _)
    _ ≤ ∑ z ∈ S, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro z hz _
      positivity [hw z hz]
    _ = _ := by rw [Finset.mul_sum]

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem overlap_nonneg (P Q : FiniteLaw α) : 0 ≤ overlap P Q := by
  apply Finset.sum_nonneg
  intro a _
  exact le_min (P.nonneg a) (Q.nonneg a)

end FiniteLaw
end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem product_succ_expect (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      P.expect (fun a => (P.product n).expect (fun b => f (Fin.cons a b))) := by
  unfold expect product
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (∏ j, P.mass ((Fin.cons a b : Fin (n + 1) → α) j)) * f (Fin.cons a b) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem associated_product [Preorder α] (P : FiniteLaw α) (hP : P.Associated) (n : ℕ) :
    (P.product n).Associated := by
  induction n with
  | zero =>
    intro f g _ _
    simp [expect, product]
  | succ n ih =>
    intro f g hf hg
    rw [product_succ_expect, product_succ_expect, product_succ_expect]
    have hcons {a a' : α} {b b' : Fin n → α} (ha : a ≤ a') (hb : b ≤ b') :
        (Fin.cons a b : Fin (n + 1) → α) ≤ (Fin.cons a' b' : Fin (n + 1) → α) := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ha
      · exact hb i
    calc
      _ ≤ P.expect (fun a => (P.product n).expect (fun b => f (Fin.cons a b)) *
          (P.product n).expect (fun b => g (Fin.cons a b))) := by
        apply hP
        · intro a a' ha
          exact (P.product n).expect_mono (fun b => hf (hcons ha le_rfl))
        · intro a a' ha
          exact (P.product n).expect_mono (fun b => hg (hcons ha le_rfl))
      _ ≤ _ := by
        apply P.expect_mono
        intro a
        apply ih
        · intro b b' hb; exact hf (hcons le_rfl hb)
        · intro b b' hb; exact hg (hcons le_rfl hb)

/-- An elementary Paley--Zygmund bound at threshold 1/2, for a density. -/
theorem density_threshold_mass (P : FiniteLaw α) (f : α → ℝ)
    (hmean : P.expect f = 1) :
    (1 : ℝ) / 4 ≤
      (P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0)) * P.expect (fun a => f a ^ 2) := by
  classical
  let S : Finset α := Finset.univ.filter (fun a => 1 / 2 ≤ f a)
  have hsmall : (∑ a ∈ Finset.univ \ S, P.mass a * f a) ≤ 1 / 2 := by
    calc
      _ ≤ ∑ a ∈ Finset.univ \ S, P.mass a * (1 / 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have hnot : ¬ 1 / 2 ≤ f a := by simpa [S] using (Finset.mem_sdiff.mp ha).2
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hnot)) (P.nonneg a)
      _ ≤ ∑ a, P.mass a * (1 / 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        intro a _ _; positivity [P.nonneg a]
      _ = 1 / 2 := P.expect_const _
  have hlarge : 1 / 2 ≤ ∑ a ∈ S, P.mass a * f a := by
    have hsplit := Finset.sum_sdiff (Finset.subset_univ S) (f := fun a => P.mass a * f a)
    change (∑ a, P.mass a * f a) = 1 at hmean
    rw [hmean] at hsplit
    linarith
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := S)
    (r := fun a => P.mass a * f a) (f := P.mass) (g := fun a => P.mass a * f a ^ 2)
    (fun a _ => P.nonneg a) (fun a _ => by positivity [P.nonneg a])
    (fun a _ => by nlinarith)
  have ht : (∑ a ∈ S, P.mass a * f a ^ 2) ≤ P.expect (fun a => f a ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro a _ _; positivity [P.nonneg a]
  have hmass : P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0) = ∑ a ∈ S, P.mass a := by
    unfold expect S
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  rw [hmass]
  have hm := mul_le_mul_of_nonneg_left ht (Finset.sum_nonneg (s := S) (fun a _ => P.nonneg a))
  nlinarith

/-- The common-density overlap used for consecutive pure primitive runs. -/
theorem increasing_density_overlap [Preorder α] (P : FiniteLaw α) (hP : P.Associated)
    (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (hfm : Monotone f) (hgm : Monotone g)
    (hf1 : P.expect f = 1) (hg1 : P.expect g = 1) :
    (1 : ℝ) / 32 ≤ P.expect (fun a => min (f a) (g a)) *
      P.expect (fun a => f a ^ 2) * P.expect (fun a => g a ^ 2) := by
  let F : α → ℝ := fun a => if 1 / 2 ≤ f a then 1 else 0
  let G : α → ℝ := fun a => if 1 / 2 ≤ g a then 1 else 0
  have hF : Monotone F := by
    intro a b hab
    dsimp [F]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hfm hab)))
    · norm_num
    · rfl
  have hG : Monotone G := by
    intro a b hab
    dsimp [G]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hgm hab)))
    · norm_num
    · rfl
  have hcorr := hP F G hF hG
  have hpoint : ∀ a, (1 / 2 : ℝ) * (F a * G a) ≤ min (f a) (g a) := by
    intro a
    dsimp [F, G]
    split_ifs <;> simp only [mul_one, mul_zero]
    · exact le_min ‹_› ‹_›
    all_goals exact le_min (hf a) (hg a)
  have hint := P.expect_mono hpoint
  have heq : P.expect (fun a => (1 / 2 : ℝ) * (F a * G a)) =
      (1 / 2 : ℝ) * P.expect (fun a => F a * G a) := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  rw [heq] at hint
  have hfm2 : 0 ≤ P.expect (fun a => f a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hgm2 : 0 ≤ P.expect (fun a => g a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hff := density_threshold_mass P f hf1
  have hgg := density_threshold_mass P g hg1
  change 1 / 4 ≤ P.expect F * P.expect (fun a => f a ^ 2) at hff
  change 1 / 4 ≤ P.expect G * P.expect (fun a => g a ^ 2) at hgg
  have hmul := mul_le_mul hff hgg (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith :
    0 ≤ P.expect F * P.expect (fun a => f a ^ 2))
  have hcomb : (1 / 2 : ℝ) * (P.expect F * P.expect G) ≤
      P.expect (fun a => min (f a) (g a)) := by linarith
  have hmul2 := mul_le_mul_of_nonneg_right hcomb (mul_nonneg hfm2 hgm2)
  nlinarith only [hmul, hmul2]

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]

theorem sum_pairedHiddenMass (H : FiniteLaw α) (ω : ℝ) :
    (∑ z, pairedHiddenMass H ω z) = ω ^ 2 := by
  unfold pairedHiddenMass
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, H.total, mul_one]
  rw [← Finset.mul_sum, H.total, mul_one]

/-- Forgetting the report recovers conditional independence for each orientation. -/
theorem pairedFlag_simulation (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) (z : α × α) :
    (∑ c : Option Bool, pairedFlagMass P Q H ω b (c, z)) =
      (orientedProd P Q b).mass z := by
  cases b <;> simp [pairedFlagMass, Fintype.sum_option ]

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
theorem product_succ_expect_tail (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      (P.product n).expect (fun b => P.expect (fun a => f (Fin.cons a b))) := by
  rw [product_succ_expect]
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end TraceReconstruction.FiniteLaw
namespace TraceReconstruction
variable {α : Type*}

theorem multilinear_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (Z : α → ℝ)
    (x : Fin n → α) (a : α) :
    multilinear A Z (Fin.cons a x) =
      multilinear (fun σ => A (Fin.cons false σ)) Z x +
      Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x := by
  unfold multilinear
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem multilinearEnergy_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R =
      multilinearEnergy (fun σ => A (Fin.cons false σ)) R +
      R ^ 2 * multilinearEnergy (fun σ => A (Fin.cons true σ)) R := by
  unfold multilinearEnergy
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem monomial_weight {n : ℕ} (σ : Fin n → Bool) (R : ℝ) :
    (∏ j, if σ j then R ^ 2 else 1) = R ^ (2 * monomialDegree σ) := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, ← pow_mul, monomialDegree]

end TraceReconstruction

namespace TraceReconstruction
variable {α Ω : Type*} [Fintype Ω]

/-- The coefficient for the empty subset is exactly one, before or after averaging. -/
theorem averagedCoefficient_empty {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) :
    averagedCoefficient R θ (fun _ => false) = 1 := by
  simp [averagedCoefficient, selectionCoefficient, FiniteLaw.expect, R.total]

end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction

/-- Emitting the conditional mark, or silently erasing the block, gives
exactly the ordinary primitive-output probabilities. Silent erasure and an
emitted empty mark are distinct latent events. -/
theorem primitiveMark_simulation {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (b : Bool) (z : PrimitiveMark) :
    (if z = 0 then primitiveErasure q else 0) +
      (1 - primitiveErasure q) * primitiveMarkMass q b z =
        if b then defectPrimitiveMass q z else ordinaryPrimitiveMass q z := by
  unfold primitiveMarkMass
  rw [mul_div_cancel₀ _ (ne_of_gt (primitive_retain_pos hq))]
  ring

theorem primitive_score_centered {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    ∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z = 0 := by
  have hi := primitiveMarkMass_sum hq true
  simp_rw [primitive_score_identity hq, mul_add, mul_one, Finset.sum_add_distrib,
    primitiveMarkMass_sum hq false] at hi
  linarith

theorem primitive_score_variance_exact {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    (∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z ^ 2) =
      (1 / q - 2 * q + q ^ 2) / (1 - q ^ 2 / 2) := by
  have hq0 := ne_of_gt hq.1
  have hd := ne_of_gt (primitive_retain_pos hq)
  simp only [primitiveMarkMass, primitiveScore, ordinaryPrimitiveMass, primitiveErasure,
    Bool.false_eq_true, ↓reduceIte]
  simp [Fin.sum_univ_succ]
  field_simp
  ring

theorem primitive_score_variance_le {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    (∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z ^ 2) ≤ 2 / q := by
  rw [primitive_score_variance_exact hq]
  have hd : 0 < 1 - q ^ 2 / 2 := primitive_retain_pos hq
  apply (div_le_div_iff₀ hd hq.1).mpr
  rw [add_mul, sub_mul, one_div_mul_cancel (ne_of_gt hq.1)]
  have hpow : q ^ 3 ≤ q ^ 2 := by
    calc
      _ = q ^ 2 * q := by ring
      _ ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left hq.2.le (sq_nonneg _)
      _ = _ := mul_one _
  nlinarith only [hpow, sq_nonneg q]

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Kernels

Constrained rank-gap sums, correlated anchor kernels, window kernels, lattice Laplace sums, and geometric degree bounds.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

/-- Eliminate one output gap by its prescribed total before dropping the
other rank constraints. This is the exact finite summation step used in
the conditional rank-kernel estimate. -/
theorem constrained_sum_product_le (r L : ℕ)
    (f : Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf : ∀ i k, 0 ≤ f i k) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k, f 0 k ≤ M) :
    (∑ z : Fin (r + 1) → Fin (L + 1),
      if ∑ j, (z j).val = L then ∏ j, f j (z j) else 0) ≤
        M * ∏ i : Fin r, ∑ k, f i.succ k := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin (L + 1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hpoint (z : Fin r → Fin (L + 1)) :
      (∑ k : Fin (L + 1),
        if k.val + ∑ i, (z i).val = L then f 0 k * ∏ i, f i.succ (z i) else 0) ≤
          M * ∏ i, f i.succ (z i) := by
    by_cases hz : ∑ i, (z i).val ≤ L
    · let k₀ : Fin (L + 1) := ⟨L - ∑ i, (z i).val, by omega⟩
      have heq (k : Fin (L + 1)) : k.val + ∑ i, (z i).val = L ↔ k = k₀ := by
        change _ ↔ k = ⟨L - ∑ i, (z i).val, _⟩
        rw [Fin.ext_iff]
        simp only
        omega
      simp_rw [heq]
      rw [Fintype.sum_ite_eq']
      exact mul_le_mul_of_nonneg_right (hbound k₀) (Finset.prod_nonneg fun i _ => hf _ _)
    · have heq (k : Fin (L + 1)) : ¬ (k.val + ∑ i, (z i).val = L) := by omega
      simp_rw [ite_eq_right (heq _), Finset.sum_const_zero]
      exact mul_nonneg hM (Finset.prod_nonneg fun i _ => hf _ _)
  calc
    _ ≤ ∑ z : Fin r → Fin (L + 1), M * ∏ i, f i.succ (z i) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using hpoint z
    _ = _ := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (i : Fin r) (k : Fin (L + 1)) => f i.succ k)]

/-- The product of two rank kernels has one scalar denominator factor,
one uniform gap factor and independent one-dimensional cross-overlaps. -/
theorem constrained_cross_kernel_le (r L : ℕ)
    (f g : Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf : ∀ i k, 0 ≤ f i k) (hg : ∀ i k, 0 ≤ g i k)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ k, f 0 k * g 0 k ≤ M) :
    (∑ z : Fin (r + 1) → Fin (L + 1),
      if ∑ j, (z j).val = L then (∏ j, f j (z j)) * (∏ j, g j (z j)) else 0) ≤
        M * ∏ i : Fin r, ∑ k, f i.succ k * g i.succ k := by
  simp_rw [← Finset.prod_mul_distrib]
  exact constrained_sum_product_le r L (fun i k => f i k * g i k)
    (fun i k => mul_nonneg (hf i k) (hg i k)) M hM hbound

end TraceReconstruction

namespace TraceReconstruction

/-- Truncating output ranks cannot increase a binomial cross-overlap. -/
theorem binomial_overlap_truncate (g h L : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) :
    (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤
      ∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => binomialMass g p k * binomialMass h p k) (L + 1)]
  by_cases hL : L ≤ h
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    exact mul_nonneg (binomialMass_nonneg g k hp) (binomialMass_nonneg h k hp)
  · apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hhk : h < k := by
      simp only [Finset.mem_range, not_lt] at hk
      omega
    simp [binomialMass, Nat.choose_eq_zero_of_lt hhk]

/-- Gaussian cross-overlap with the prefactor attached to either prescribed
first length, removing the order restriction in the tilting proof. -/
theorem binomial_gaussian_overlap_general (g h L : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hS : 0 < g + h) :
    (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
        Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  by_cases hhg : h ≤ g
  · exact (binomial_overlap_truncate g h L ⟨hp0.le, hp.2.le⟩).trans
      (binomial_gaussian_overlap g h hp hhg hS)
  · have hgh : g ≤ h := by omega
    have ho := (binomial_overlap_truncate h g L ⟨hp0.le, hp.2.le⟩).trans
      (binomial_gaussian_overlap h g hp hgh (by omega))
    have hb : Real.sqrt (2 / (((h : ℝ) + 1) * p * (1 - p))) ≤
        Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by norm_num)
        (by nlinarith only [mul_pos (show (0 : ℝ) < (g : ℝ) + 1 by positivity) hpq])
      have hcast : (g : ℝ) ≤ h := by exact_mod_cast hgh
      have ht := mul_le_mul_of_nonneg_right (show (g : ℝ) + 1 ≤ (h : ℝ) + 1 by linarith) hpq.le
      nlinarith only [ht]
    have heq : -((h : ℝ) - g) ^ 2 / (16 * ((h : ℝ) + g)) =
        -((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h)) := by ring
    rw [heq] at ho
    exact (by simpa only [mul_comm] using ho :
      (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤ _).trans
        (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _))

end TraceReconstruction

open Filter
open scoped Topology


namespace TraceReconstruction

/-- Elementary discrete integral comparison, including the singular first cell. -/
theorem sum_inverse_sqrt (N : ℕ) :
    (∑ k ∈ Finset.range N, (Real.sqrt (k+1:ℝ))⁻¹) ≤ 2*Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ (N:ℝ) := by positivity
    have hp : 0 < Real.sqrt (N+1:ℝ) := Real.sqrt_pos.2 (by positivity)
    have hs : Real.sqrt (N:ℝ) ≤ Real.sqrt (N+1:ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h1 := Real.sq_sqrt hn
    have h2 := Real.sq_sqrt (show 0 ≤ (N+1:ℝ) by positivity)
    have hstep : (Real.sqrt (N+1:ℝ))⁻¹ ≤ 2*(Real.sqrt (N+1:ℝ)-Real.sqrt N) := by
      apply (inv_le_iff_one_le_mul₀ hp).2
      nlinarith [sq_nonneg (Real.sqrt (N+1:ℝ)-Real.sqrt N)]
    push_cast
    linarith

theorem exp_gap_lower {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    h/2 ≤ 1-Real.exp (-h) := by
  have he := Real.add_one_le_exp h
  have hp : 0 < Real.exp h := Real.exp_pos h
  have hp' : 0 < 1+h := by linarith
  have hinv : (Real.exp h)⁻¹ ≤ (1+h)⁻¹ := inv_anti₀ hp' (by simpa [add_comm] using he)
  rw [Real.exp_neg]
  have hi : (1+h)⁻¹*(1+h)=1 := inv_mul_cancel₀ (ne_of_gt hp')
  nlinarith [mul_nonneg hh.le (sub_nonneg.mpr h1)]

theorem sum_exp_decay {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (M : ℕ) :
    (∑ k ∈ Finset.range M, Real.exp (-h*(k:ℝ))) ≤ 2/h := by
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hf : (∑ k ∈ Finset.range M, (Real.exp (-h))^k) ≤ (1-Real.exp (-h))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1-Real.exp (-h)), geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg he M)
  have hi : (1-Real.exp (-h))⁻¹ ≤ 2/h := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0<1-Real.exp (-h))]
    have hb := exp_gap_lower hh h1
    have := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2/h by positivity)
    nlinarith [div_mul_cancel₀ (2:ℝ) hh.ne']
  calc
    _ = ∑ k ∈ Finset.range M, (Real.exp (-h))^k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := hf.trans hi

/-- The uniform lattice Laplace estimate used by the initial-pair construction, with an absolute constant. -/
theorem coarse_laplace_sum {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (M : ℕ) :
    (∑ k ∈ Finset.range M, (Real.sqrt (k+1:ℝ))⁻¹ *
      Real.exp (-h*(k+1:ℝ))) ≤ 6/Real.sqrt h := by
  let N := ⌈1/h⌉₊
  have hN : 1/h ≤ (N:ℝ) := Nat.le_ceil _
  have hNup : (N:ℝ) < 1/h+1 := Nat.ceil_lt_add_one (by positivity)
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hNsqrt : Real.sqrt N ≤ 2/Real.sqrt h := by
    have hn : (N:ℝ)*h ≤ 2 := by
      have hx := mul_le_mul_of_nonneg_right hNup.le hh.le
      have hc : (1/h)*h=1 := div_mul_cancel₀ _ hh.ne'
      nlinarith
    have hprod : Real.sqrt N * Real.sqrt h ≤ 2 := by
      have hsqh := Real.sq_sqrt hh.le
      have hsqN := Real.sq_sqrt (show 0≤(N:ℝ) by positivity)
      have hnon : 0≤Real.sqrt N*Real.sqrt h := by positivity
      nlinarith [sq_nonneg (Real.sqrt N*Real.sqrt h)]
    exact (le_div_iff₀ hs).2 hprod
  let low := (Finset.range M).filter (fun k => k<N)
  let high := (Finset.range M).filter (fun k => ¬k<N)
  have hlo : (∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) ≤
      2*Real.sqrt N := by
    calc
      _ ≤ ∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [show (0:ℝ)≤k by positivity]))
      _ ≤ ∑ k ∈ Finset.range N, (Real.sqrt (k+1:ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
        · intros; positivity
      _ ≤ _ := sum_inverse_sqrt N
  have hhi : (∑ k ∈ high, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) ≤
      Real.sqrt h * (2/h) := by
    calc
      _ ≤ ∑ k ∈ high, Real.sqrt h * Real.exp (-h*(k:ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : N ≤ k := Nat.le_of_not_gt (Finset.mem_filter.mp hk).2
        have hkR : 1/h ≤ (k+1:ℝ) := hN.trans (by exact_mod_cast (by omega : N≤k+1))
        have hinv : (Real.sqrt (k+1:ℝ))⁻¹ ≤ Real.sqrt h := by
          apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 (by positivity))).2
          have hmul : 1 ≤ h*(k+1:ℝ) := by simpa [mul_comm] using (div_le_iff₀ hh).mp hkR
          have hsqh := Real.sq_sqrt hh.le
          have hsqk := Real.sq_sqrt (show 0≤(k+1:ℝ) by positivity)
          nlinarith [mul_nonneg (Real.sqrt_nonneg h) (Real.sqrt_nonneg (k+1:ℝ))]
        apply mul_le_mul hinv _ (Real.exp_pos _).le (Real.sqrt_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ ∑ k ∈ Finset.range M, Real.sqrt h * Real.exp (-h*(k:ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intros; positivity
      _ = Real.sqrt h * ∑ k ∈ Finset.range M, Real.exp (-h*(k:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_exp_decay hh h1 M) (Real.sqrt_nonneg h)
  have hsum : (∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) +
      (∑ k ∈ high, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) =
      ∑ k ∈ Finset.range M, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hcancel : Real.sqrt h*(2/h)=2/Real.sqrt h := by
    have hsq := Real.sq_sqrt hh.le
    field_simp
    nlinarith
  rw [← hsum]
  rw [hcancel] at hhi
  have heq : 2*(2/Real.sqrt h)+2/Real.sqrt h=6/Real.sqrt h := by ring
  linarith


end TraceReconstruction


namespace TraceReconstruction

/-- The degree-series estimate in the common-mass argument, with no asymptotic notation. -/
theorem degree_series_bound (a : ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r)^2 ≤
      2 * Real.exp (2*a^2) := by
  let u (r : ℕ) : ℝ := (Real.sqrt ((1/2:ℝ)^r))
  let v (r : ℕ) : ℝ := (Real.sqrt ((2:ℝ)^r))*a^r/(Real.sqrt (r:ℝ))^r
  have huv (r : ℕ) : u r * v r = a^r/(Real.sqrt (r:ℝ))^r := by
    unfold u v
    have he : Real.sqrt ((1/2:ℝ)^r) * Real.sqrt ((2:ℝ)^r)=1 := by
      rw [← Real.sqrt_mul (by positivity), ← mul_pow]
      norm_num
    calc
      _ = (Real.sqrt ((1/2:ℝ)^r) * Real.sqrt ((2:ℝ)^r)) * (a^r/(Real.sqrt (r:ℝ))^r) := by ring
      _ = _ := by rw [he, one_mul]
  have hu : (∑ r ∈ Finset.range N, (u r)^2) ≤ 2 := by
    simp only [u, Real.sq_sqrt (by positivity : 0 ≤ (1/2:ℝ)^_)]
    have hg := geom_sum_mul_neg (1/2:ℝ) N
    have hp : 0≤(1/2:ℝ)^N := by positivity
    linarith
  have hv : (∑ r ∈ Finset.range N, (v r)^2) ≤ Real.exp (2*a^2) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by positivity) N)
    apply Finset.sum_le_sum
    intro r _
    have hr : 0 < ((r.factorial):ℝ) := by exact_mod_cast Nat.factorial_pos r
    have hrpow : 0 < (r:ℝ)^r := by
      cases r with
      | zero => norm_num
      | succ r => positivity
    have hfac : (r.factorial:ℝ) ≤ (r:ℝ)^r := by exact_mod_cast Nat.factorial_le_pow r
    have hveq : (v r)^2 = (2*a^2)^r / (r:ℝ)^r := by
      unfold v
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hd : ((Real.sqrt (r:ℝ))^r)^2=(r:ℝ)^r := by
        rw [← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt (by positivity)]
      rw [hd]
      rw [← pow_mul, mul_comm r 2, pow_mul]
      ring
    rw [hveq]
    exact div_le_div_of_nonneg_left (by positivity) hr hfac
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) u v
  simp only [huv] at hCS
  exact hCS.trans (mul_le_mul hu hv (by positivity) (by norm_num))

end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

theorem nat_add_one_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology

open Filter
open scoped Topology


end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

variable {α : Type*} [Fintype α]

theorem slotAtRank_strictMono {n l : ℕ} (S : FixedSubset (Fin n) l) :
    StrictMono (slotAtRank S) := by
  classical
  intro a b hab
  exact (S.val.orderIsoOfFin S.property).strictMono hab

theorem subsetRankKernel_nonneg {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (v : Fin r → Fin l) : 0 ≤ subsetRankKernel hl p v := by
  classical
  unfold subsetRankKernel
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact (uniformSubsetLaw l (by simpa using hl)).nonneg S
  · rfl

theorem card_gapEvent {r d : ℕ} (g z : Fin d → ℕ) :
    Fintype.card {S : Finset (GapUniverse r d g) // gapEvent z S} =
      ∏ i, (g i).choose (z i) := by
  classical
  rw [Fintype.card_congr gapEventEquiv, Fintype.card_pi]
  simp only [card_fixedSubset, Fintype.card_fin]


/-- The exact unconditioned tagged-gap probability; no asymptotic estimate is used. -/
theorem gapEvent_bernoulli_probability {r d : ℕ} (g z : Fin d → ℕ)
    (hz : ∀ i, z i≤g i) (p : ℝ) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      p^r * ∏ i, binomialMass (g i) p (z i) := by
  classical
  have hcount : (∑ S : Finset (GapUniverse r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i, ((g i).choose (z i):ℝ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype, card_gapEvent, Nat.cast_prod]
  have hnum : (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      (∏ i, ((g i).choose (z i):ℝ)) *
        (p^(r+∑ i, z i)*(1-p)^(r+∑ i, g i-(r+∑ i, z i))) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul, subsetWeight, card_of_gapEvent S hS,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    · exact (zero_mul _).symm
  have hsub : (∑ i, g i)-(∑ i, z i)=∑ i, (g i-z i) := by
    exact (Finset.sum_tsub_distrib Finset.univ (fun i _ => hz i)).symm
  rw [hnum, Nat.add_sub_add_left, hsub, pow_add]
  simp only [binomialMass, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Conditional Bernoulli representation of the source rank kernel in gap coordinates. -/
theorem gapEvent_conditional_formula {r d : ℕ} (g z : Fin d → ℕ)
    (hz : ∀ i, z i≤g i) (p : ℝ) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) /
      binomialMass (r+∑ i, g i) p (r+∑ i, z i) =
    p^r / binomialMass (r+∑ i, g i) p (r+∑ i, z i) *
      ∏ i, binomialMass (g i) p (z i) := by
  rw [gapEvent_bernoulli_probability g z hz]
  ring

end TraceReconstruction


namespace TraceReconstruction

theorem card_taggedRankEvent {n l r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (v : Fin r → Fin l) (hv : StrictMono v) :
    Fintype.card {S : FixedSubset (Fin n) l // taggedRankEvent p v S} =
      ∏ j, (tupleGap p j).choose (tupleGap v j) := by
  classical
  rw [Fintype.card_congr (rankGapEventEquiv p hp v hv), card_gapEvent]

/-- Exact counting formula, including impossible rank/gap profiles. -/
theorem subsetRankKernel_choose_formula {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v) :
    subsetRankKernel hl p v =
      (∏ j, ((tupleGap p j).choose (tupleGap v j) : ℝ)) / (n.choose l : ℝ) := by
  classical
  unfold subsetRankKernel
  simp only [uniformSubsetLaw, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    ← Fintype.card_subtype, card_taggedRankEvent p hp v hv, Nat.cast_prod]
  ring

theorem gapEvent_conditional_choose {r d : ℕ} (g z : Fin d → ℕ)
    (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) /
      binomialMass (r+∑ i, g i) p (r+∑ i, z i) =
    (∏ i, ((g i).choose (z i):ℝ)) /
      ((r+∑ i, g i).choose (r+∑ i, z i) : ℝ) := by
  classical
  have hcount : (∑ S : Finset (GapUniverse r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i, ((g i).choose (z i):ℝ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype, card_gapEvent, Nat.cast_prod]
  have hnum : (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      (∏ i, ((g i).choose (z i):ℝ)) *
        (p^(r+∑ i, z i)*(1-p)^(r+∑ i, g i-(r+∑ i, z i))) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul, subsetWeight, card_of_gapEvent S hS,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    · exact (zero_mul _).symm
  rw [hnum, binomialMass]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1-p ≠ 0 := by linarith [hp.2]
  rw [mul_assoc, mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hq0))]

/-- Conditional product formula for the kernel defined from actual retained
subsets, not an assumed auxiliary kernel. Source the initial-pair construction 50–62. -/
theorem subsetRankKernel_binomial_formula {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 1) :
    subsetRankKernel hl p v = θ^r / binomialMass n θ l *
      ∏ j, binomialMass (tupleGap p j) θ (tupleGap v j) := by
  classical
  by_cases hz : ∀ j, tupleGap v j ≤ tupleGap p j
  · have h1 := gapEvent_conditional_choose (r := r) (tupleGap p) (tupleGap v) θ hθ
    have h2 := gapEvent_conditional_formula (r := r) (tupleGap p) (tupleGap v) hz θ
    rw [tupleGap_total p hp, tupleGap_total v hv] at h1 h2
    rw [subsetRankKernel_choose_formula hl p hp v hv, ← h1, h2]
  · push Not at hz
    obtain ⟨j,hj⟩ := hz
    have hc : (tupleGap p j).choose (tupleGap v j) = 0 := Nat.choose_eq_zero_of_lt hj
    have hz1 : (∏ j, ((tupleGap p j).choose (tupleGap v j) : ℝ))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hc])
    have hz2 : (∏ j, binomialMass (tupleGap p j) θ (tupleGap v j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [binomialMass, hc])
    rw [subsetRankKernel_choose_formula hl p hp v hv, hz1, hz2]
    simp

end TraceReconstruction

namespace TraceReconstruction

theorem coarsePeriodGap_pos {u r : ℕ} (j : Fin r → Fin u) (i : Fin (r+1)) :
    1 ≤ coarsePeriodGap j i := by
  unfold coarsePeriodGap
  split_ifs <;> omega

theorem tupleGap_injective {n r : ℕ} {p q : Fin r → Fin n}
    (hp : StrictMono p) (hq : StrictMono q) (h : tupleGap p = tupleGap q) : p=q := by
  funext i
  apply Fin.ext
  have hp' := tupleGap_prefix p hp i
  have hq' := tupleGap_prefix q hq i
  rw [h] at hp'
  omega

theorem coarsePeriodGap_injective {u r : ℕ} {j k : Fin r → Fin u}
    (hj : StrictMono j) (hk : StrictMono k) (h : coarsePeriodGap j = coarsePeriodGap k) :
    j=k := by
  apply tupleGap_injective hj hk
  funext i
  have hi := congrFun h i
  unfold coarsePeriodGap at hi
  omega

theorem periodSlot_strictMono {u m : ℕ} (off : Fin u → Fin m) :
    StrictMono (periodSlot off) := by
  intro j k hjk
  change j.val*m + (off j).val < k.val*m + (off k).val
  have hjk' : j.val+1 ≤ k.val := hjk
  have ho := (off j).isLt
  have hm := Nat.mul_le_mul_right m hjk'
  nlinarith

theorem tupleGap_zero {n r : ℕ} (p : Fin (r+1) → Fin n) :
    tupleGap p 0 = (p 0).val := by
  have he : (0 : Fin (r+2)) = (0 : Fin (r+1)).castSucc := rfl
  unfold tupleGap
  rw [tupleLower_zero, Nat.sub_zero, he, tupleUpper_castSucc]

theorem tupleGap_last {n r : ℕ} (p : Fin (r+1) → Fin n) :
    tupleGap p (Fin.last (r+1)) = n - ((p (Fin.last r)).val+1) := by
  unfold tupleGap
  rw [tupleUpper_last, ← Fin.succ_last, tupleLower_succ]

theorem tupleGap_middle {n r : ℕ} (p : Fin (r+1) → Fin n) (i : Fin r) :
    tupleGap p i.castSucc.succ = (p i.succ).val - ((p i.castSucc).val+1) := by
  unfold tupleGap
  rw [tupleLower_succ, Fin.succ_castSucc, tupleUpper_castSucc]

theorem coarsePeriodGap_zero {u r : ℕ} (j : Fin (r+1) → Fin u) :
    coarsePeriodGap j 0 = 2*(j 0).val+1 := by
  simp only [coarsePeriodGap, tupleGap_zero, true_or, ↓reduceIte]

theorem coarsePeriodGap_last {u r : ℕ} (j : Fin (r+1) → Fin u) :
    coarsePeriodGap j (Fin.last (r+1)) = 2*(u-((j (Fin.last r)).val+1))+1 := by
  simp only [coarsePeriodGap, tupleGap_last, or_true, ↓reduceIte]

theorem coarsePeriodGap_middle {u r : ℕ} (j : Fin (r+1) → Fin u) (i : Fin r) :
    coarsePeriodGap j i.castSucc.succ = 2*((j i.succ).val-((j i.castSucc).val+1))+2 := by
  have hn : i.castSucc.succ ≠ Fin.last (r+1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp only [coarsePeriodGap, tupleGap_middle, Fin.succ_ne_zero, hn, or_self, ↓reduceIte]

/-- Actual bounded defect displacements give the O(1) gap errors of the initial-pair construction. -/
theorem period_gap_rounding {u m r : ℕ} (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j) (i : Fin (r+1)) :
    |(tupleGap (periodSlot off ∘ j) i:ℝ) - (m:ℝ)*coarsePeriodGap j i/2| ≤ 4 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hp := (periodSlot_strictMono off).comp hj
  induction i using Fin.cases with
  | zero =>
    rw [tupleGap_zero, coarsePeriodGap_zero]
    simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    have offset_bound := abs_le.mp (hoff (j 0))
    apply abs_le.mpr
    constructor <;> linarith
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, tupleGap_last, coarsePeriodGap_last]
      have hcut : (j (Fin.last d)).val+1 ≤ u := Nat.succ_le_of_lt (j _).isLt
      have hslot : ((periodSlot off ∘ j) (Fin.last d)).val+1 ≤ u*m :=
        Nat.succ_le_of_lt (((periodSlot off ∘ j) (Fin.last d))).isLt
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [Nat.cast_sub hslot, Nat.cast_sub hcut]
      simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have h := abs_le.mp (hoff (j (Fin.last d)))
      apply abs_le.mpr
      constructor <;> linarith
    | cast i =>
      rw [tupleGap_middle, coarsePeriodGap_middle]
      have hcut : (j i.castSucc).val+1 ≤ (j i.succ).val := hj (Fin.castSucc_lt_succ (i := i))
      have hslot : ((periodSlot off ∘ j) i.castSucc).val+1 ≤
          ((periodSlot off ∘ j) i.succ).val := hp (Fin.castSucc_lt_succ (i := i))
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [Nat.cast_sub hslot, Nat.cast_sub hcut]
      simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have h := abs_le.mp (hdiff (j i.succ) (j i.castSucc))
      apply abs_le.mpr
      constructor <;> linarith

end TraceReconstruction

namespace TraceReconstruction

theorem rankGapProfile_sum {n r : ℕ} (σ : Equiv.Perm (Fin (r+1)))
    (v : IncreasingTuple n r) : ∑ i, (rankGapProfile σ v i).val = n-r := by
  change (∑ i, tupleGap v.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  have ht := tupleGap_total v.val v.property
  omega

theorem rankGapProfile_injective {n r : ℕ} (σ : Equiv.Perm (Fin (r+1))) :
    Function.Injective (rankGapProfile (n := n) σ) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he : tupleGap v.val = tupleGap w.val := by
    funext j
    have hh := congrArg Fin.val (congrFun h (σ.symm j))
    simpa only [rankGapProfile, Equiv.apply_symm_apply] using hh
  have hv := tupleGap_prefix v.val v.property i
  have hw := tupleGap_prefix w.val w.property i
  rw [he] at hv
  omega

/-- Summing nonnegative kernels over actual profiles may drop any remaining constraints. -/
theorem sum_injective_profile_le {α β : Type*} [Fintype α] [Fintype β]
    (profile : α → β) (hinj : Function.Injective profile)
    (P : β → Prop) [DecidablePred P] (hp : ∀ a, P (profile a))
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (profile a)) ≤ ∑ b, if P b then f b else 0 := by
  classical
  let S := Finset.univ.image profile
  have hs : ∀ b ∈ S, P b := by
    intro b hb
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hb
    exact hp a
  calc
    _ = ∑ b ∈ S, f b := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => hinj h)
    _ = ∑ b ∈ S, if P b then f b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [ite_eq_left (hs b hb)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro b _ _
      split_ifs
      · exact hf b
      · rfl)

/-- The actual conditional rank kernel, summed over distinct observed ranks,
reduces to the constrained finite product estimate with any eliminated gap. -/
theorem subsetRankKernel_cross_le {n l r : ℕ} (hl : l ≤ n)
    (p q : Fin r → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 1) (e : Fin (r+1))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k : Fin (l-r+1),
      binomialMass (tupleGap p e) θ k * binomialMass (tupleGap q e) θ k ≤ M) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val) ≤
      (θ^r / binomialMass n θ l)^2 * M *
        ∏ i : Fin r, ∑ k : Fin (l-r+1),
          binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
          binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
  classical
  let σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 e
  let f : Fin (r+1) → Fin (l-r+1) → ℝ := fun i k => binomialMass (tupleGap p (σ i)) θ k
  let g : Fin (r+1) → Fin (l-r+1) → ℝ := fun i k => binomialMass (tupleGap q (σ i)) θ k
  have hf : ∀ i k, 0 ≤ f i k := by
    intro i k
    dsimp [f,binomialMass]
    positivity [hθ.1.le, sub_nonneg.mpr hθ.2.le]
  have hg : ∀ i k, 0 ≤ g i k := by
    intro i k
    dsimp [g,binomialMass]
    positivity [hθ.1.le, sub_nonneg.mpr hθ.2.le]
  let F (z : Fin (r+1) → Fin (l-r+1)) := (∏ i, f i (z i)) * (∏ i, g i (z i))
  have hF : ∀ z, 0 ≤ F z := by
    intro z
    exact mul_nonneg (Finset.prod_nonneg fun i _ => hf i _) (Finset.prod_nonneg fun i _ => hg i _)
  have hpoint (v : IncreasingTuple l r) :
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val =
        (θ^r / binomialMass n θ l)^2 * F (rankGapProfile σ v) := by
    rw [subsetRankKernel_binomial_formula hl p hp v.val v.property θ hθ,
      subsetRankKernel_binomial_formula hl q hq v.val v.property θ hθ]
    dsimp only [F,f,g,rankGapProfile]
    rw [Equiv.prod_comp σ (fun j => binomialMass (tupleGap p j) θ (tupleGap v.val j)),
      Equiv.prod_comp σ (fun j => binomialMass (tupleGap q j) θ (tupleGap v.val j))]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (θ^r / binomialMass n θ l)^2 *
        ∑ z : Fin (r+1) → Fin (l-r+1), if ∑ i, (z i).val = l-r then F z else 0 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_injective_profile_le (rankGapProfile σ) (rankGapProfile_injective σ)
        (fun z => ∑ i, (z i).val = l-r) (rankGapProfile_sum σ) F hF
    _ ≤ (θ^r / binomialMass n θ l)^2 * (M * ∏ i : Fin r, ∑ k, f i.succ k * g i.succ k) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact constrained_cross_kernel_le r (l-r) f g hf hg M hM (by
        intro k
        simpa only [f,g,σ,Equiv.swap_apply_left] using hbound k)
    _ = _ := by dsimp [f,g,σ]; ring

end TraceReconstruction

namespace TraceReconstruction

theorem finite_geometric_distance (S : Finset ℤ) (a : ℤ) {ρ : ℝ}
    (hρ : ρ∈Set.Ico 0 1) :
    (∑ z ∈ S, ρ^(z-a).natAbs) ≤ 2/(1-ρ) := by
  have hs : Summable (fun n:ℕ => ρ^n) := summable_geometric_of_lt_one hρ.1 hρ.2
  have hnat : Summable (fun n:ℕ => ρ^((n:ℤ).natAbs)) := by simpa using hs
  have hneg : Summable (fun n:ℕ => ρ^((-(n:ℤ)).natAbs)) := by simpa using hs
  have hz : Summable (fun z:ℤ => ρ^z.natAbs) := hnat.of_nat_of_neg hneg
  have ht : (∑' z:ℤ, ρ^z.natAbs)=2/(1-ρ)-1 := by
    rw [Summable.tsum_of_nat_of_neg (f := fun z : ℤ => ρ^z.natAbs) hnat hneg]
    simp only [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_zero, pow_zero]
    rw [tsum_geometric_of_lt_one hρ.1 hρ.2]
    ring
  have hshift : Summable (fun z:ℤ => ρ^(z-a).natAbs) :=
    hz.comp_injective (sub_left_injective)
  have hts : (∑' z:ℤ, ρ^(z-a).natAbs)=(∑' z:ℤ, ρ^z.natAbs) :=
    (Equiv.subRight a).tsum_eq (fun z:ℤ => ρ^z.natAbs)
  have hbound := hshift.sum_le_tsum S (fun z _ => pow_nonneg hρ.1 _)
  rw [hts,ht] at hbound
  linarith

end TraceReconstruction

namespace TraceReconstruction

theorem fin_geometric_distance (N : ℕ) (a : ℤ) {ρ : ℝ} (hρ : ρ∈Set.Ico 0 1) :
    (∑ z : Fin N, ρ^((z.val:ℤ)-a).natAbs) ≤ 2/(1-ρ) := by
  let e : ℕ ↪ ℤ := ⟨Int.ofNat, Nat.cast_injective⟩
  have h := finite_geometric_distance ((Finset.range N).map e) a hρ
  rw [Finset.sum_map] at h
  rw [Fin.sum_univ_eq_sum_range (fun z:ℕ => ρ^((z:ℤ)-a).natAbs) N]
  exact h

theorem coarse_laplace_sum_with_zero {h : ℝ} (hh : 0<h) (h1 : h≤1) (M : ℕ) :
    (∑ k : Fin (M+1), (Real.sqrt (k.val:ℝ))⁻¹ * Real.exp (-h*(k.val:ℝ))) ≤
      6/Real.sqrt h := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, zero_add]
  have hc := coarse_laplace_sum hh h1 M
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) M] at hc
  simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using hc

/-- The total constraint eliminates one coarse gap with no cost in its size.
The zero-extension of x^(-1/2) avoids any singular integral convention. -/
theorem coarse_constrained_inverse_sum (r U : ℕ) {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    (∑ γ : Fin (r+1) → Fin (U+1),
      if ∑ i, (γ i).val=U then ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ else 0) ≤
      Real.exp (h*U) * (6/Real.sqrt h)^r := by
  classical
  let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases
    (fun k => Real.exp (-h*(k.val:ℝ)))
    (fun _ k => (Real.sqrt (k.val:ℝ))⁻¹ * Real.exp (-h*(k.val:ℝ)))
  have hf : ∀ i k, 0≤f i k := by
    intro i k
    refine Fin.cases ?_ (fun _ => ?_) i <;> dsimp [f] <;> positivity
  have hf0 : ∀ k, f 0 k≤1 := by
    intro k
    change Real.exp (-h*(k.val:ℝ))≤1
    apply Real.exp_le_one_iff.mpr
    nlinarith [show (0:ℝ)≤k.val by positivity]
  have hid (γ : Fin (r+1) → Fin (U+1)) (hγ : ∑ i, (γ i).val=U) :
      ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ =
        Real.exp (h*U) * ∏ i, f i (γ i) := by
    have hγr : ((γ 0).val:ℝ) + ∑ i:Fin r, ((γ i.succ).val:ℝ)=(U:ℝ) := by
      exact_mod_cast (show (γ 0).val+∑ i:Fin r, (γ i.succ).val=U by
        simpa only [Fin.sum_univ_succ] using hγ)
    simp only [Fin.prod_univ_succ, f, Fin.cases_zero, Fin.cases_succ,
      Finset.prod_mul_distrib, ← Real.exp_sum]
    have he : Real.exp (h*U) * Real.exp (-h*((γ 0).val:ℝ)) *
        Real.exp (∑ i:Fin r, -h*((γ i.succ).val:ℝ))=1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Finset.mul_sum]
      rw [show h*(U:ℝ)+ -h*((γ 0).val:ℝ)+ -h*∑ i:Fin r, ((γ i.succ).val:ℝ)=0 by
        rw [← hγr]
        ring]
      exact Real.exp_zero
    calc
      _ = (Real.exp (h*U) * Real.exp (-h*((γ 0).val:ℝ)) *
        Real.exp (∑ i:Fin r, -h*((γ i.succ).val:ℝ))) *
          (∏ i:Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹) := by rw [he, one_mul]
      _ = _ := by ring
  have hrew : (∑ γ : Fin (r+1) → Fin (U+1),
      if ∑ i, (γ i).val=U then ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ else 0) =
      Real.exp (h*U) * ∑ γ : Fin (r+1) → Fin (U+1),
        if ∑ i, (γ i).val=U then ∏ i, f i (γ i) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    split_ifs with hγ
    · exact hid γ hγ
    · simp
  rw [hrew]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply (constrained_sum_product_le r U f hf 1 (by norm_num) hf0).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i : Fin r, (6/Real.sqrt h) := by
      apply Finset.prod_le_prod
      · intro i _; exact Finset.sum_nonneg (fun k _ => hf i.succ k)
      · intro i _; exact coarse_laplace_sum_with_zero hh h1 U
    _ = _ := by simp [div_pow]

/-- The squared norm of an aggregate equals the sum of the cross-kernels. -/
theorem sum_sq_sum_kernel {α β : Type*} [Fintype β] (S : Finset α) (K : α → β → ℝ) :
    (∑ z, (∑ a ∈ S, K a z)^2) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ z, K a z*K b z := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm


end TraceReconstruction

namespace TraceReconstruction

/-- Geometry of actual period gaps: the half-integer coarse gaps are
represented by positive integers a,b, with bounded slot-rounding errors. -/
theorem coarse_gap_geometry (m U a b g k : ℕ) (hm : 32 ≤ m) (hUm : U  ≤  2*m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (haU : a ≤ U) (hbU : b ≤ U)
    (hg : |(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk : |(k:ℝ)-(m:ℝ)*b/2| ≤ 4) :
    (m:ℝ)*a/4  ≤  (g:ℝ)+1 ∧ 0<(g:ℝ)+k ∧
      ((a:ℝ)-b)^2/1024  ≤  ((g:ℝ)-k)^2/(16*((g:ℝ)+k)) := by
  have hmR : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hUmR : (U:ℝ)  ≤  2*m := by exact_mod_cast hUm
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have haUR : (a:ℝ) ≤ U := by exact_mod_cast haU
  have hbUR : (b:ℝ) ≤ U := by exact_mod_cast hbU
  have hga := abs_le.mp hg
  have hkb := abs_le.mp hk
  have hma : (32:ℝ) ≤ (m:ℝ)*a := by nlinarith
  have hmb : (32:ℝ) ≤ (m:ℝ)*b := by nlinarith
  have hlo : (m:ℝ)*a/4 ≤ (g:ℝ)+1 := by nlinarith only [hga.1,hma]
  have hsum0 : 0<(g:ℝ)+k := by nlinarith only [hga.1,hkb.1,hma,hmb]
  refine ⟨hlo,hsum0,?_⟩
  by_cases hab : a=b
  · simp only [hab, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hd1 : 1 ≤ |(a:ℝ)-b| := by
    rcases lt_or_gt_of_ne hab with hab | hab
    · rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hab : (a:ℝ) < b))]
      have hx : (a:ℝ)+1 ≤ b := by exact_mod_cast hab
      linarith
    · rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hab : (b:ℝ) < a))]
      have hx : (b:ℝ)+1 ≤ a := by exact_mod_cast hab
      linarith
  have herr : |((g:ℝ)-k)-(m:ℝ)/2*((a:ℝ)-b)| ≤ 8 := by
    calc
      _ = |((g:ℝ)-(m:ℝ)*a/2)-((k:ℝ)-(m:ℝ)*b/2)| := by congr 1; ring
      _  ≤  |(g:ℝ)-(m:ℝ)*a/2|+|(k:ℝ)-(m:ℝ)*b/2| := abs_sub _ _
      _  ≤  _ := by linarith
  have hd : (m:ℝ)/4*|(a:ℝ)-b|  ≤  |(g:ℝ)-k| := by
    have ht := abs_sub_abs_le_abs_sub ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)
    rw [abs_sub_comm ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)] at ht
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)/2)] at ht
    have hmabs : (32:ℝ) ≤ (m:ℝ)*|(a:ℝ)-b| := by nlinarith only [hmR,hd1]
    nlinarith only [ht,herr,hmabs]
  have hsq : (m:ℝ)^2*((a:ℝ)-b)^2/16 ≤ ((g:ℝ)-k)^2 := by
    have hx := mul_self_le_mul_self (by positivity : 0 ≤ (m:ℝ)/4*|(a:ℝ)-b|) hd
    nlinarith only [hx, sq_abs ((a:ℝ)-b), sq_abs ((g:ℝ)-k)]
  have hsum : (g:ℝ)+k  ≤  4*(m:ℝ)^2 := by
    have hu1 : (1:ℝ) ≤ U := by linarith
    have hmu : (32:ℝ) ≤ (m:ℝ)*U := by nlinarith only [hmR,hu1]
    have hmaU := mul_le_mul_of_nonneg_left haUR (show (0:ℝ) ≤ m by positivity)
    have hmbU := mul_le_mul_of_nonneg_left hbUR (show (0:ℝ) ≤ m by positivity)
    have hUmM := mul_le_mul_of_nonneg_left hUmR (show (0:ℝ) ≤ m by positivity)
    nlinarith only [hga.2,hkb.2,hmaU,hmbU,hmu,hUmM]
  apply (le_div_iff₀ (by positivity : 0<16*((g:ℝ)+k))).mpr
  have hx := mul_le_mul_of_nonneg_right hsum (sq_nonneg ((a:ℝ)-b))
  nlinarith only [hx,hsq]

/-- From integer Gaussian decay to a summable geometric profile. -/
theorem exp_integer_square_le (a b : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-c * ((a:ℝ)-b)^2) ≤
      (Real.exp (-c)) ^ ((a:ℤ)-b).natAbs := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hd : (((a:ℤ)-b).natAbs : ℝ) = |(a:ℝ)-b| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub]
    simp only [Int.cast_natCast]
  have hsq : (((a:ℤ)-b).natAbs:ℝ) ≤ (((a:ℤ)-b).natAbs:ℝ)^2 := by
    exact_mod_cast (show ((a:ℤ)-b).natAbs ≤ ((a:ℤ)-b).natAbs^2 by
      simpa only [pow_two] using Nat.le_mul_self ((a:ℤ)-b).natAbs)
  rw [hd, sq_abs] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq hc
  rw [hd]
  nlinarith only [hmul]

theorem coarse_binomial_overlap (m U a b g k L : ℕ)
    (hm : 32 ≤ m) (hUm : U ≤ 2*m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (haU : a ≤ U) (hbU : b ≤ U)
    (hg : |(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk : |(k:ℝ)-(m:ℝ)*b/2| ≤ 4)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1) :
    (∑ z : Fin (L+1), binomialMass g θ z * binomialMass k θ z) ≤
      Real.sqrt (8 / ((m:ℝ)*θ*(1-θ))) * (Real.sqrt (a:ℝ))⁻¹ *
        (Real.exp (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs := by
  have geo := coarse_gap_geometry m U a b g k hm hUm ha hb haU hbU hg hk
  have hsum : 0 < g+k := by exact_mod_cast geo.2.1
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθ1 : 0 < 1-θ := sub_pos.mpr hθ.2
  have varpos : 0 < θ*(1-θ) := mul_pos hθ0 hθ1
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hpref : Real.sqrt (2 / (((g:ℝ)+1)*θ*(1-θ))) ≤
      Real.sqrt (8 / ((m:ℝ)*θ*(1-θ))) * (Real.sqrt (a:ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity : 0 ≤ 8/((m:ℝ)*θ*(1-θ)))]
    apply Real.sqrt_le_sqrt
    have hdg : 0 < ((g:ℝ)+1)*θ*(1-θ) := by nlinarith
    have hdm : 0 < (m:ℝ)*θ*(1-θ) := by nlinarith
    apply (div_le_iff₀ hdg).mpr
    have hdiv : 0 < (m:ℝ)*θ*(1-θ)*(a:ℝ) := by positivity
    have heq : (8 / ((m:ℝ)*θ*(1-θ)) * (a:ℝ)⁻¹) * (((g:ℝ)+1)*θ*(1-θ)) =
        (8*((g:ℝ)+1)) / ((m:ℝ)*a) := by
      field_simp [ne_of_gt hθ0, ne_of_gt hθ1, ne_of_gt hm0, ne_of_gt ha0]
    rw [heq]
    apply (le_div_iff₀ (mul_pos hm0 ha0)).mpr
    linarith [geo.1]
  have hexp : Real.exp (-((g:ℝ)-k)^2/(16*((g:ℝ)+k))) ≤
      (Real.exp (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs := by
    apply le_trans _ (exp_integer_square_le a b (by norm_num : (0:ℝ)≤1/1024))
    apply Real.exp_le_exp.mpr
    convert neg_le_neg geo.2.2 using 2 <;> first | rfl | ring
  exact (binomial_gaussian_overlap_general g k L hθ hsum).trans
    (mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity))

end TraceReconstruction


namespace TraceReconstruction

theorem int_natAbs_sub_comm (a b : ℤ) : (a-b).natAbs = (b-a).natAbs := by
  rw [← Int.natAbs_neg (a-b),neg_sub]

theorem subsetRankKernel_cross_normalized {n l r : ℕ} (hl : l  ≤  n)
    (p q : Fin r → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    {θ : ℝ} (hθ : θ  ∈  Set.Ico (1/2:ℝ) 1)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ)) (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val)  ≤ 
      (4608*n/((tupleGap p e:ℝ)+1))*
        ∏ i : Fin r, ∑ k : Fin (l-r+1),
          binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
          binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hqpos : 0 < 1-θ := sub_pos.mpr hθ.2
  have hc : (θ^r/binomialMass n θ l)^2  ≤  144*((n:ℝ)*θ*(1-θ)) := by
    rw [div_eq_mul_inv,mul_pow]
    apply (mul_le_mul_of_nonneg_right
      (show (θ^r)^2  ≤  (1:ℝ) by
        exact pow_le_one₀ (pow_nonneg hθ0.le _) (pow_le_one₀ hθ0.le hθ.2.le))
      (sq_nonneg _)).trans
    simpa only [one_mul] using binomialMass_mean_inverse_sq n l ⟨hθ0,hθ.2⟩ hl hmean hv
  have hprod : 0  ≤  ∏ i : Fin r, ∑ k : Fin (l-r+1),
      binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
      binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
    apply Finset.prod_nonneg
    intro i _
    exact Finset.sum_nonneg fun k _ => mul_nonneg
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (subsetRankKernel_cross_le hl p q hp hq θ ⟨hθ0,hθ.2⟩ e
    (32/(((tupleGap p e:ℝ)+1)*θ*(1-θ))) (by positivity)
    (fun k => binomial_product_sup _ _ k hθ)).trans
  calc
    _  ≤  (144*((n:ℝ)*θ*(1-θ)))*(32/(((tupleGap p e:ℝ)+1)*θ*(1-θ)))*_ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hprod
    _ = _ := by
      have hq0 : 1-θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ.2)
      field_simp
      ring

theorem periodProfile_sum {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1)))
    (j : IncreasingTuple u r) : ∑ i, (periodProfile hr σ j i).val = 2*u := by
  change (∑ i, coarsePeriodGap j.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  exact coarsePeriodGap_sum hr j.val j.property

theorem periodProfile_injective {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1))) :
    Function.Injective (periodProfile (u:=u) hr σ) := by
  intro j k h
  apply Subtype.ext
  apply coarsePeriodGap_injective j.property k.property
  funext i
  have he := congrArg Fin.val (congrFun h (σ.symm i))
  simpa only [periodProfile,Equiv.apply_symm_apply] using he

theorem period_kernel_cross {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j k : IncreasingTuple u r) (e : Fin (r+1))
    (he : 2*u  ≤  (r+1)*coarsePeriodGap j.val e) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl (periodSlot off ∘ j.val) v.val *
      subsetRankKernel hl (periodSlot off ∘ k.val) v.val)  ≤ 
      (9216*(r+1:ℕ) : ℝ)* (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        ∏ i : Fin r, (Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs := by
  classical
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hUm : 2*u ≤ 2*m := Nat.mul_le_mul_left 2 hum
  have hg (v : IncreasingTuple u r) (i : Fin (r+1)) :=
    period_gap_rounding hr off hoff hdiff v.val v.property i
  have hgeo := coarse_gap_geometry m (2*u) (coarsePeriodGap j.val e)
    (coarsePeriodGap k.val e) (tupleGap (periodSlot off ∘ j.val) e)
    (tupleGap (periodSlot off ∘ k.val) e) hm hUm
    (coarsePeriodGap_pos j.val e) (coarsePeriodGap_pos k.val e)
    (coarsePeriodGap_le hr j.val j.property e) (coarsePeriodGap_le hr k.val k.property e)
    (hg j e) (hg k e)
  have hlarge : (4608 * (u*m:ℕ) : ℝ)/((tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)  ≤ 
      9216*(r+1:ℕ) := by
    have heR : 2*(u:ℝ)  ≤  (r+1:ℕ)* (coarsePeriodGap j.val e:ℝ) := by exact_mod_cast he
    apply (div_le_iff₀ (by positivity : 0 < (tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)).mpr
    have hx := mul_le_mul_of_nonneg_right hgeo.1
      (show (0:ℝ) ≤ (r+1:ℕ) by positivity)
    have hy := mul_le_mul_of_nonneg_left heR hm0.le
    simp only [Nat.cast_mul]
    nlinarith only [hx,hy]
  have hover (i : Fin r) :
      (∑ z : Fin (l-r+1),
        binomialMass (tupleGap (periodSlot off ∘ j.val) (Equiv.swap 0 e i.succ)) θ z *
        binomialMass (tupleGap (periodSlot off ∘ k.val) (Equiv.swap 0 e i.succ)) θ z)  ≤ 
      Real.sqrt (8/((m:ℝ)*θ*(1-θ))) *
        ((Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs) := by
    have ho := coarse_binomial_overlap m (2*u) _ _ _ _ (l-r) hm hUm
      (coarsePeriodGap_pos j.val _) (coarsePeriodGap_pos k.val _)
      (coarsePeriodGap_le hr j.val j.property _) (coarsePeriodGap_le hr k.val k.property _)
      (hg j (Equiv.swap 0 e i.succ)) (hg k (Equiv.swap 0 e i.succ)) hθ
    rw [int_natAbs_sub_comm] at ho
    simpa only [periodProfile,mul_assoc] using ho
  have hn (i : Fin r) : 0 ≤  ∑ z : Fin (l-r+1),
      binomialMass (tupleGap (periodSlot off ∘ j.val) (Equiv.swap 0 e i.succ)) θ z *
      binomialMass (tupleGap (periodSlot off ∘ k.val) (Equiv.swap 0 e i.succ)) θ z := by
    exact Finset.sum_nonneg fun z _ => mul_nonneg
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩) (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (subsetRankKernel_cross_normalized hl _ _
    ((periodSlot_strictMono off).comp j.property) ((periodSlot_strictMono off).comp k.property)
    hθ hmean hv e).trans
  calc
    _  ≤  (9216*(r+1:ℕ) : ℝ)*
        ∏ i : Fin r, (Real.sqrt (8/((m:ℝ)*θ*(1-θ))) *
        ((Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs)) := by
      apply mul_le_mul hlarge (Finset.prod_le_prod (fun i _ => hn i) (fun i _ => hover i))
        (Finset.prod_nonneg (fun i _ => hn i)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; ring

end TraceReconstruction


namespace TraceReconstruction

theorem coarse_profile_geometric_sum {α : Type*} [Fintype α] (r U : ℕ)
    (profile : α → Fin (r+1) → Fin (U+1)) (hinj : Function.Injective profile)
    (htotal : ∀ a, ∑ i, (profile a i).val=U)
    (γ : Fin (r+1) → Fin (U+1)) {ρ : ℝ} (hρ : ρ∈Set.Ico 0 1) :
    (∑ a, ∏ i : Fin r, ρ^(((profile a i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
      (2/(1-ρ))^r := by
  classical
  let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases (fun _ => 1)
    (fun i k => ρ^((k.val:ℤ)-(γ i.succ).val).natAbs)
  have hf : ∀ i k, 0≤f i k := by
    intro i k
    refine Fin.cases ?_ (fun _ => ?_) i
    · norm_num [f]
    · exact pow_nonneg hρ.1 _
  have hid (δ : Fin (r+1) → Fin (U+1)) :
      (∏ i : Fin r, ρ^(((δ i.succ).val:ℤ)-(γ i.succ).val).natAbs) = ∏ i, f i (δ i) := by
    simp only [Fin.prod_univ_succ,f,Fin.cases_zero,Fin.cases_succ,one_mul]
  simp_rw [hid]
  apply (sum_injective_profile_le profile hinj (fun δ => ∑ i, (δ i).val=U)
    htotal (fun δ => ∏ i, f i (δ i)) (fun δ => Finset.prod_nonneg (fun i _ => hf i _))).trans
  apply (constrained_sum_product_le r U f hf 1 (by norm_num) (by intro k; rfl)).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i : Fin r, (2/(1-ρ)) := by
      apply Finset.prod_le_prod
      · exact fun i _ => Finset.sum_nonneg (fun k _ => hf i.succ k)
      · exact fun i _ => fin_geometric_distance (U+1) ((γ i.succ).val:ℤ) hρ
    _ = _ := by simp [div_pow]

theorem coarse_profile_inverse_sum {α : Type*} [Fintype α] (r U : ℕ)
    (profile : α → Fin (r+1) → Fin (U+1)) (hinj : Function.Injective profile)
    (htotal : ∀ a, ∑ i, (profile a i).val=U)
    {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    (∑ a, ∏ i : Fin r, (Real.sqrt ((profile a i.succ).val:ℝ))⁻¹) ≤
      Real.exp (h*U)*(6/Real.sqrt h)^r := by
  classical
  apply le_trans _ (coarse_constrained_inverse_sum r U hh h1)
  exact sum_injective_profile_le profile hinj (fun δ => ∑ i, (δ i).val=U)
    htotal (fun δ => ∏ i : Fin r, (Real.sqrt ((δ i.succ).val:ℝ))⁻¹) (fun δ => by positivity)

/-- Coarse Schur bound for actual injective profiles, with no extension of
kernels outside their geometric domain. -/
theorem coarse_profile_bilinear_sum {α β : Type*} [Fintype α] [Fintype β]
    (r U : ℕ) (p : α → Fin (r+1) → Fin (U+1)) (q : β → Fin (r+1) → Fin (U+1))
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpt : ∀ a, ∑ i, (p a i).val=U) (hqt : ∀ b, ∑ i, (q b i).val=U)
    (K : α → β → ℝ) {M ρ h : ℝ}
    (hM : 0≤M) (hρ : ρ∈Set.Ico 0 1) (hh : 0<h) (h1 : h≤1)
    (hcross : ∀ a b, K a b ≤ M * ∏ i : Fin r,
      (Real.sqrt ((p a i.succ).val:ℝ))⁻¹ *
        ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs) :
    (∑ a, ∑ b, K a b) ≤ M*(2/(1-ρ))^r * Real.exp (h*U)*(6/Real.sqrt h)^r := by
  classical
  let A (a : α) := ∏ i : Fin r, (Real.sqrt ((p a i.succ).val:ℝ))⁻¹
  have hA (a) : 0≤A a := by dsimp [A]; positivity
  have hinner (a) := coarse_profile_geometric_sum r U q hq hqt (p a) hρ
  have houter := coarse_profile_inverse_sum r U p hp hpt hh h1
  calc
    _ ≤ ∑ a, ∑ b, M * ∏ i : Fin r,
        (Real.sqrt ((p a i.succ).val:ℝ))⁻¹ *
          ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcross a b))
    _ = ∑ a, M*A a * ∑ b, ∏ i : Fin r, ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs := by
      simp only [Finset.prod_mul_distrib,A,Finset.mul_sum,mul_assoc]
    _ ≤ ∑ a, M*A a*(2/(1-ρ))^r :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hinner a) (mul_nonneg hM (hA a)))
    _ = M*(2/(1-ρ))^r * ∑ a, A a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ M*(2/(1-ρ))^r * (Real.exp (h*U)*(6/Real.sqrt h)^r) := by
      apply mul_le_mul_of_nonneg_left houter
      exact mul_nonneg hM (pow_nonneg (div_nonneg (by norm_num) (by linarith [hρ.2])) _)
    _ = _ := by ring

end TraceReconstruction

namespace TraceReconstruction

theorem exists_large_period_gap {u r : ℕ} (hr : 0 < r) (j : IncreasingTuple u r) :
    ∃ e : Fin (r+1), 2*u ≤ (r+1)*coarsePeriodGap j.val e := by
  obtain ⟨e,_,he⟩ := Finset.exists_max_image Finset.univ (coarsePeriodGap j.val)
    Finset.univ_nonempty
  refine ⟨e,?_⟩
  calc
    _ = ∑ i, coarsePeriodGap j.val i := (coarsePeriodGap_sum hr j.val j.property).symm
    _ ≤ ∑ _i : Fin (r+1), coarsePeriodGap j.val e := Finset.sum_le_sum (fun i hi => he i hi)
    _ = _ := by simp

/-- Unnormalized but explicit source rank-kernel square-sum estimate. The
only remaining factors are elementary scale simplifications. -/
theorem period_rank_square_sum_raw {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) {θ h : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : 0 < h) (h1 : h ≤ 1)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      9216*(r+1:ℕ)^2 * (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r := by
  classical
  let K (j : IncreasingTuple u r) (v : IncreasingTuple l r) :=
    subsetRankKernel hl (periodSlot off ∘ j.val) v.val
  let C (j k : IncreasingTuple u r) := ∑ v : IncreasingTuple l r, K j v*K k v
  have hC (j k) : 0 ≤ C j k := by
    exact Finset.sum_nonneg (fun v _ => mul_nonneg
      (subsetRankKernel_nonneg hl _ _) (subsetRankKernel_nonneg hl _ _))
  have hρ : Real.exp (-(1/1024:ℝ)) ∈ Set.Ico 0 1 := by
    refine ⟨(Real.exp_pos _).le,?_⟩
    rw [Real.exp_lt_one_iff]
    norm_num
  have hschur (e : Fin (r+1)) :
      (∑ j : LargePeriodTuple u r e, ∑ k : IncreasingTuple u r, C j.val k) ≤
        ((9216*(r+1:ℕ):ℝ)*(Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r := by
    apply coarse_profile_bilinear_sum r (2*u)
      (fun j : LargePeriodTuple u r e => periodProfile hr (Equiv.swap 0 e) j.val)
      (periodProfile hr (Equiv.swap 0 e))
      ((periodProfile_injective hr (Equiv.swap 0 e)).comp Subtype.val_injective)
      (periodProfile_injective hr (Equiv.swap 0 e))
      (fun j => periodProfile_sum hr _ j.val) (periodProfile_sum hr _)
      (fun j k => C j.val k) (by positivity) hρ hh h1
    intro j k
    exact period_kernel_cross hl hr hm hum hθ hmean hv off hoff hdiff j.val k e j.property
  have hcover (j : IncreasingTuple u r) :
      (∑ k : IncreasingTuple u r, C j k) ≤ ∑ e : Fin (r+1),
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0 := by
    obtain ⟨e,he⟩ := exists_large_period_gap hr j
    have hn : ∀ e' : Fin (r+1), 0 ≤
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e' then ∑ k : IncreasingTuple u r, C j k else 0 := by
      intro e'
      split_ifs
      · exact Finset.sum_nonneg (fun k _ => hC j k)
      · rfl
    simpa only [ite_eq_left he] using Finset.single_le_sum (fun e' _ => hn e') (Finset.mem_univ e)
  have heq (e : Fin (r+1)) :
      (∑ j : IncreasingTuple u r,
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0) =
      ∑ j : LargePeriodTuple u r e, ∑ k : IncreasingTuple u r, C j.val k := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro j; simp) _
  calc
    _ = ∑ j : IncreasingTuple u r, ∑ k : IncreasingTuple u r, C j k := by
      exact sum_sq_sum_kernel Finset.univ K
    _ ≤ ∑ j : IncreasingTuple u r, ∑ e : Fin (r+1),
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0 :=
      Finset.sum_le_sum (fun j _ => hcover j)
    _ = ∑ e : Fin (r+1), ∑ j : LargePeriodTuple u r e,
        ∑ k : IncreasingTuple u r, C j.val k := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun e _ => heq e)
    _ ≤ ∑ _e : Fin (r+1),
        ((9216*(r+1:ℕ):ℝ)*(Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r :=
      Finset.sum_le_sum (fun e _ => hschur e)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end TraceReconstruction

namespace TraceReconstruction

theorem rank_polynomial_factor {r : ℕ} (hr : 0 < r) :
    (9216:ℝ)*(r+1:ℕ)^2 ≤ (36864:ℝ)^r := by
  have h1 : (9216:ℝ) ≤ (9216:ℝ)^r := le_self_pow₀ (by norm_num) (Nat.ne_of_gt hr)
  have h2 : ((r+1:ℕ):ℝ) ≤ (2:ℝ)^r := by exact_mod_cast nat_add_one_le_two_pow r
  have h3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (r+1:ℕ)) h2 2
  have h4 : ((2:ℝ)^r)^2 = (4:ℝ)^r := by
    rw [← pow_mul,Nat.mul_comm r 2,pow_mul]
    norm_num
  calc
    _ ≤ (9216:ℝ)^r*((2:ℝ)^r)^2 := mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _ := by rw [h4,← mul_pow]; norm_num

theorem rankSchurConstant_pos : 0 < rankSchurConstant := by
  have hρ : Real.exp (-(1/1024:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  unfold rankSchurConstant
  positivity

/-- Rank-kernel square sum, with an explicit absolute constant, uniformly
in the defect types and admissible conditional count. -/
theorem period_rank_square_sum {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      (rankSchurConstant * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))))^r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hu0 : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hq0 : 0 < 1-θ := sub_pos.mpr hθ.2
  let h : ℝ := (r:ℝ)/(2*u)
  have hh : 0 < h := div_pos hr0 (by positivity)
  have h1 : h ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < 2*u)).mpr
    have hruR : (r:ℝ) ≤ u := by exact_mod_cast hru
    linarith
  have hx : h*(2*u:ℕ) = r := by
    dsimp [h]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  have he : Real.exp (h*(2*u:ℕ)) = (Real.exp 1)^r := by
    rw [hx,← Real.exp_nat_mul]
    simp
  have hρ : 0 ≤ 2/(1-Real.exp (-(1/1024:ℝ))) := by
    have hn : Real.exp (-(1/1024:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    positivity
  have hp : 0 ≤ (u:ℝ)/((m:ℝ)*r*θ*(1-θ)) := by positivity
  have hs : Real.sqrt (8/((m:ℝ)*θ*(1-θ))) * (6/Real.sqrt h) ≤
      24 * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) := by
    have hsq : (Real.sqrt (8/((m:ℝ)*θ*(1-θ))) * (6/Real.sqrt h))^2 =
        576 * ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) := by
      rw [mul_pow,div_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8/((m:ℝ)*θ*(1-θ))),
        Real.sq_sqrt hh.le]
      dsimp [h]
      field_simp
      ring
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))]
  apply (period_rank_square_sum_raw hl hr hm hum hθ hmean hv hh h1 off hoff hdiff).trans
  rw [he]
  calc
    _ ≤ (36864:ℝ)^r * (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Real.exp (-(1/1024:ℝ))))^r * (Real.exp 1)^r * (6/Real.sqrt h)^r := by
      gcongr
      exact rank_polynomial_factor hr
    _ = ((36864:ℝ)*(2/(1-Real.exp (-(1/1024:ℝ))))*Real.exp 1 *
        (Real.sqrt (8/((m:ℝ)*θ*(1-θ)))*(6/Real.sqrt h)))^r := by
      simp only [mul_pow]
      ring
    _ ≤ ((36864:ℝ)*(2/(1-Real.exp (-(1/1024:ℝ))))*Real.exp 1 *
        (24 * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))))^r := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by congr 1; unfold rankSchurConstant; ring

end TraceReconstruction

namespace TraceReconstruction

/-- The source's channel-uniform rank-kernel estimate (base-kernel),
with the absolute constant made explicit. -/
theorem period_rank_square_sum_delta {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      ((3*rankSchurConstant/δ) * Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  have hd0 : 0 < δ := hδ.1
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ.1
  have hd2b : δ^2 ≤ 1/4 := by nlinarith [hδ.1,hδ.2]
  have ht : θ ∈ Set.Ico (1/2:ℝ) 1 := by
    constructor <;> nlinarith [hθ.1,hθ.2]
  have ht0 : 0 < θ := by linarith [ht.1]
  have hq0 : 0 < 1-θ := sub_pos.mpr ht.2
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu0 : (0:ℝ) ≤ u := Nat.cast_nonneg u
  have hvar : δ^2/8 ≤ θ*(1-θ) := by
    have hq : δ^2/4 ≤ 1-θ := by linarith [hθ.2]
    nlinarith [mul_le_mul ht.1 hq (by positivity) ht0.le]
  have hdiv : (u:ℝ)/((m:ℝ)*r*θ*(1-θ)) ≤
      (3/δ)^2*((u:ℝ)/((m:ℝ)*r)) := by
    have hden : (0:ℝ) < (m:ℝ)*r*θ*(1-θ) := by positivity
    apply (div_le_iff₀ hden).mpr
    have he : (3/δ)^2 * ((u:ℝ)/((m:ℝ)*r)) * ((m:ℝ)*r*θ*(1-θ)) =
        ((u:ℝ)*9*θ*(1-θ))/δ^2 := by field_simp; ring
    rw [he]
    apply (le_div_iff₀ hd2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hvar (by positivity : (0:ℝ) ≤ 9*(u:ℝ))]
  have hs : Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) ≤
      (3/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)) := by
    calc
      _ ≤ Real.sqrt ((3/δ)^2*((u:ℝ)/((m:ℝ)*r))) := Real.sqrt_le_sqrt hdiv
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  apply (period_rank_square_sum hl hr hru hm hum ht hmean hv off hoff hdiff).trans
  apply pow_le_pow_left₀ (by positivity [rankSchurConstant_pos])
  calc
    _ ≤ rankSchurConstant*((3/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r))) :=
      mul_le_mul_of_nonneg_left hs rankSchurConstant_pos.le
    _ = _ := by ring

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section



noncomputable section


noncomputable section

open Filter
open scoped Topology

noncomputable section
noncomputable section
namespace TraceReconstruction

/-- An elementary centered MGF bound valid on both sides of the mean,
 with constants independent of the Bernoulli parameter. -/
theorem binomialMass_centered_mgf (n : ℕ) {p t : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : |t|≤1) :
    (∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*((k:ℝ)-n*p))) ≤
      Real.exp ((n:ℝ)*t^2) := by
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hn : 0≤(n:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp.1
  have hn' : (n:ℝ)*p≤n := mul_le_of_le_one_right (Nat.cast_nonneg _) hp.2
  calc
    _ = Real.exp (-t*(n:ℝ)*p)*
        ∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-t*(n:ℝ)*p)*Real.exp ((n:ℝ)*p*(Real.exp t-1)) :=
      mul_le_mul_of_nonneg_left (binomialMass_mgf_le n hp t) (Real.exp_nonneg _)
    _ ≤ Real.exp ((n:ℝ)*t^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have he' := mul_le_mul_of_nonneg_left he hn
      have hs := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      nlinarith only [he',hs]

/-- Either signed deviation has the same Chernoff estimate. -/
theorem binomialMass_signed_tail (n : ℕ) {p t a ε : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) (hε : ε=1 ∨ ε= -1) :
    (∑ k∈(Finset.range (n+1)).filter (fun k : ℕ => a≤ε*((k:ℝ)-n*p)), binomialMass n p k) ≤
      Real.exp (-t*a+(n:ℝ)*t^2) := by
  have heps : |t*ε|≤1 := by rcases hε with rfl | rfl <;> simpa [abs_of_nonneg ht.1] using ht.2
  have hm := finite_exp_markov (Finset.range (n+1)) (binomialMass n p)
    (fun k : ℕ => ε*((k:ℝ)-n*p)) (fun k _ => binomialMass_nonneg n k hp) a t ht.1
  calc
    _ ≤ Real.exp (-t*a)*∑ k∈Finset.range (n+1),
        binomialMass n p k*Real.exp ((t*ε)*((k:ℝ)-n*p)) := by
      simpa only [mul_assoc] using hm
    _ ≤ Real.exp (-t*a)*Real.exp ((n:ℝ)*(t*ε)^2) :=
      mul_le_mul_of_nonneg_left (binomialMass_centered_mgf n hp heps) (Real.exp_nonneg _)
    _ = _ := by rcases hε with rfl | rfl <;> simp [Real.exp_add]

/-- A uniform two-sided tail at any finite cutoff. Unlike a quoted
 concentration theorem, this follows here from the finite binomial MGF. -/
theorem binomialMass_abs_tail (n : ℕ) {p t a : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ k∈(Finset.range (n+1)).filter (fun k : ℕ => a≤|(k:ℝ)-n*p|), binomialMass n p k) ≤
      2*Real.exp (-t*a+(n:ℝ)*t^2) := by
  have hpoint (k : ℕ) : (if a≤|(k:ℝ)-n*p| then binomialMass n p k else 0) ≤
      (if a≤(k:ℝ)-n*p then binomialMass n p k else 0)+
      (if a≤-((k:ℝ)-n*p) then binomialMass n p k else 0) := by
    have hn := binomialMass_nonneg n k hp
    by_cases h : a≤|(k:ℝ)-n*p|
    · rw [ite_eq_left h]
      have hh := le_abs.mp h
      rcases hh with h1 | h2
      · rw [ite_eq_left h1]
        split_ifs <;> linarith
      · rw [ite_eq_left h2]
        split_ifs <;> linarith
    · rw [ite_eq_right h]
      split_ifs <;> linarith
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun k _ => hpoint k)
  rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter,← Finset.sum_filter] at hh
  have h1 := binomialMass_signed_tail n (a:=a) hp ht (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)= -1)
  have h2 := binomialMass_signed_tail n (a:=a) hp ht (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)= -1)
  simp only [one_mul,neg_one_mul] at h1 h2
  linarith

end TraceReconstruction
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialDensity

Defect monomials, orthogonality, normalized initial densities, and common mass.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open FiniteLaw

/-- A monotone tuple of defect slots is uniquely identified by the
retained ranks whenever all these ranks carry defects. -/
theorem exists_unique_defect_tuple {n l u r : ℕ}
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r)
    (S : FixedSubset (Fin n) l)
    (h : ∀ i, slotAtRank S (v.val i) ∈ Set.range d) :
    ∃! j : IncreasingTuple u r, taggedRankEvent (d ∘ j.val) v.val S := by
  classical
  choose j hj using h
  have hm : StrictMono j := by
    intro a b hab
    apply hd.lt_iff_lt.mp
    rw [hj a,hj b]
    exact slotAtRank_strictMono S (v.property hab)
  refine ⟨⟨j,hm⟩,?_,?_⟩
  · intro i
    exact (hj i).symm
  · intro k hk
    apply Subtype.ext
    funext i
    apply hd.injective
    exact (hk i).symm.trans (hj i).symm

/-- The degree coefficient is the sum over actual tagged defect tuples,
not a separately postulated kernel array. -/
theorem defect_tuple_indicator {n l u r : ℕ}
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r)
    (S : FixedSubset (Fin n) l) :
    (if ∀ i, slotAtRank S (v.val i) ∈ Set.range d then (1:ℝ) else 0) =
      ∑ j : IncreasingTuple u r, if taggedRankEvent (d ∘ j.val) v.val S then 1 else 0 := by
  classical
  by_cases h : ∀ i, slotAtRank S (v.val i) ∈ Set.range d
  · obtain ⟨j,hj,hu⟩ := exists_unique_defect_tuple d hd v S h
    rw [ite_eq_left h]
    symm
    rw [Finset.sum_eq_single j]
    · exact ite_eq_left hj
    · intro k _ hkj
      have hk : ¬taggedRankEvent (d ∘ k.val) v.val S := by
        intro hk
        exact hkj (hu k hk)
      exact ite_eq_right hk
    · simp
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    intro hj
    apply h
    intro i
    exact ⟨j.val i,(hj i).symm⟩

theorem rankDefectCoefficient_eq {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r) :
    rankDefectCoefficient hl d v =
      ∑ j : IncreasingTuple u r, subsetRankKernel hl (d ∘ j.val) v.val := by
  classical
  unfold rankDefectCoefficient FiniteLaw.expect subsetRankKernel
  simp_rw [defect_tuple_indicator d hd v, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

/-- Bool-mask form of the selected-rank coefficient, in the exact
multilinear density expansion. -/
theorem selected_defect_coefficient {n l : ℕ} (D : Finset (Fin n))
    (S : FixedSubset (Fin n) l) (σ : Fin l → Bool) :
    selectionCoefficient (defectAtRank D S) σ =
      if ∀ i, σ i = true → slotAtRank S i ∈ D then (1:ℝ) else 0 := by
  classical
  unfold selectionCoefficient defectAtRank
  by_cases h : ∀ i, σ i = true → slotAtRank S i ∈ D
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    cases hs : σ i
    · simp
    · simp [h i hs]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi,hni⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi,hni]

theorem averaged_rank_coefficient {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (v : IncreasingTuple l r) :
    averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
      (defectAtRank (Finset.univ.image d)) (rankMask v) =
      rankDefectCoefficient hl d v := by
  classical
  unfold averagedCoefficient rankDefectCoefficient FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  dsimp only
  rw [selected_defect_coefficient]
  congr 1
  simp only [rankMask,decide_eq_true_eq,Finset.mem_image,Finset.mem_univ,true_and,
    Set.mem_range]
  apply propext
  constructor
  · intro h i
    exact h (v.val i) ⟨i,rfl⟩
  · rintro h i ⟨j,rfl⟩
    exact h j

end TraceReconstruction

namespace TraceReconstruction
open FiniteLaw

theorem rankMask_tupleOfMask {l r : ℕ} (σ : Fin l → Bool) (hσ : monomialDegree σ = r) :
    rankMask (tupleOfMask σ hσ) = σ := by
  classical
  funext i
  have he : i ∈ Set.range (tupleOfMask σ hσ).val ↔ σ i = true := by
    constructor
    · rintro ⟨j,rfl⟩
      exact (Finset.mem_filter.mp (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ) j).property).2
    · intro hi
      let z : ↥(Finset.univ.filter (fun k => σ k = true)) := ⟨i,by simp [hi]⟩
      refine ⟨((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).symm z,?_⟩
      exact congrArg Subtype.val (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).apply_symm_apply z)
  simp only [rankMask,he]
  exact Bool.decide_eq_true

theorem tupleOfMask_injective {l r : ℕ} : Function.Injective
    (fun σ : {σ : Fin l → Bool // monomialDegree σ = r} => tupleOfMask σ.val σ.property) := by
  intro σ τ h
  apply Subtype.ext
  have he := congrArg rankMask h
  simpa only [rankMask_tupleOfMask] using he

/-- Changing from Boolean monomial labels to ordered rank tuples loses no
mass; an injection suffices for the upper bounds. -/
theorem sum_degree_coeff_sq_le {l r : ℕ} (A : (Fin l → Bool) → ℝ) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then A σ ^ 2 else 0) ≤
      ∑ v : IncreasingTuple l r, A (rankMask v)^2 := by
  classical
  rw [← Finset.sum_filter]
  have he : (∑ σ ∈ Finset.univ.filter (fun σ : Fin l → Bool => monomialDegree σ = r), A σ ^ 2) =
      ∑ σ : {σ : Fin l → Bool // monomialDegree σ = r}, A σ.val ^ 2 := by
    exact Finset.sum_subtype _ (by intro σ; simp) _
  rw [he]
  have h := sum_injective_profile_le
    (fun σ : {σ : Fin l → Bool // monomialDegree σ = r} => tupleOfMask σ.val σ.property)
    tupleOfMask_injective (fun _ => True) (fun _ => True.intro)
    (fun v => A (rankMask v)^2) (fun _ => sq_nonneg _)
  simpa only [rankMask_tupleOfMask,ite_true] using h

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open FiniteLaw

/-- Exact orthogonality of the multilinear expansion; this avoids any
loss in the channel power in consecutive-run overlap. -/
theorem multilinear_second_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (hcenter : P.expect Z = 0) (R : ℝ)
    (hvar : P.expect (fun a => Z a^2) = R^2) (n : ℕ)
    (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => multilinear A Z x ^ 2) =
      multilinearEnergy A R := by
  induction n with
  | zero => simp [FiniteLaw.expect,FiniteLaw.product,multilinear,multilinearEnergy]
  | succ n ih =>
    rw [product_succ_expect_tail]
    simp_rw [multilinear_cons]
    have he (x : Fin n → α) :
        P.expect (fun a => (multilinear (fun σ => A (Fin.cons false σ)) Z x +
            Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x)^2) =
          multilinear (fun σ => A (Fin.cons false σ)) Z x ^ 2 +
            R^2 * multilinear (fun σ => A (Fin.cons true σ)) Z x ^ 2 := by
      have hp (a : α) :
          P.mass a * (multilinear (fun σ => A (Fin.cons false σ)) Z x +
            Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x)^2 =
          P.mass a * (multilinear (fun σ => A (Fin.cons false σ)) Z x)^2 +
            2 * multilinear (fun σ => A (Fin.cons false σ)) Z x *
              multilinear (fun σ => A (Fin.cons true σ)) Z x * (P.mass a * Z a) +
            (multilinear (fun σ => A (Fin.cons true σ)) Z x)^2 * (P.mass a * Z a^2) := by ring
      unfold FiniteLaw.expect
      simp_rw [hp,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
      simp only [FiniteLaw.expect] at hcenter hvar
      rw [P.total,hcenter,hvar]
      ring
    simp_rw [he]
    rw [multilinearEnergy_cons]
    have hadd (f g : (Fin n → α) → ℝ) :
        (P.product n).expect (fun x => f x + R^2*g x) =
          (P.product n).expect f + R^2*(P.product n).expect g := by
      unfold FiniteLaw.expect
      simp_rw [mul_add,Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hadd,ih,ih]

/-- Association requires only a total preorder, allowing tied likelihoods. -/
theorem FiniteLaw.associated_totalPreorder {α : Type*} [Fintype α] [Preorder α]
    (P : FiniteLaw α) (htotal : ∀ a b : α, a ≤ b ∨ b ≤ a) : P.Associated := by
  intro f g hf hg
  have hn (a b : α) : 0 ≤ (f a - f b) * (g a - g b) := by
    rcases htotal a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hab))
        (sub_nonpos.mpr (hg hab))
    · exact mul_nonneg (sub_nonneg.mpr (hf hba)) (sub_nonneg.mpr (hg hba))
  have h := Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun b _ => mul_nonneg (mul_nonneg (P.nonneg a)
      (P.nonneg b)) (hn a b)))
  have hid : (∑ a, ∑ b, P.mass a * P.mass b * ((f a - f b) * (g a - g b))) =
      2 * (P.expect (fun a => f a * g a) - P.expect f * P.expect g) := by
    have hp (a b : α) : P.mass a * P.mass b * ((f a - f b) * (g a - g b)) =
        (P.mass a * (f a * g a)) * P.mass b + P.mass a * (P.mass b * (f b * g b)) -
        (P.mass a * f a) * (P.mass b * g b) - (P.mass a * g a) * (P.mass b * f b) := by ring
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, P.total, one_mul, mul_one]
    unfold FiniteLaw.expect
    ring
  rw [hid] at h
  linarith

theorem averagedDensity_mono {α Ω : Type*} [Preorder α] [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (Z : α → ℝ)
    (hZ : ∀ a, 0 ≤ 1+Z a) (hZm : Monotone Z) :
    Monotone (averagedDensity R θ Z) := by
  intro x y hxy
  apply R.expect_mono
  intro ω
  apply Finset.prod_le_prod
  · intro i _
    split_ifs
    · exact hZ _
    · norm_num
  · intro i _
    split_ifs
    · linarith [hZm (hxy i)]
    · rfl

end TraceReconstruction

namespace TraceReconstruction
open FiniteLaw

/-- Exact decomposition of the coefficient energy by its degree. -/
theorem multilinearEnergy_degrees {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R = ∑ r ∈ Finset.range (n+1),
      R^(2*r) * ∑ σ : Fin n → Bool, if monomialDegree σ = r then A σ^2 else 0 := by
  classical
  unfold multilinearEnergy
  simp_rw [monomial_weight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have hd : monomialDegree σ < n+1 := by
    have h := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => σ i = true)
    simpa [monomialDegree] using Nat.lt_succ_of_le h
  rw [Finset.sum_eq_single (monomialDegree σ)]
  · simp [mul_comm]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp [Finset.mem_range,hd]

/-- A zero-degree selection is precisely the empty selection. -/
theorem monomialDegree_eq_zero_iff {n : ℕ} (σ : Fin n → Bool) :
    monomialDegree σ = 0 ↔ σ = fun _ => false := by
  classical
  constructor
  · intro h
    have he : Finset.univ.filter (fun i => σ i = true) = ∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : σ i ≠ true := by
      intro hi
      have : i ∈ Finset.univ.filter (fun j => σ j = true) := by simp [hi]
      rw [he] at this
      exact Finset.notMem_empty i this
    exact Bool.eq_false_iff.mpr hn
  · rintro rfl
    simp [monomialDegree]

theorem averaged_degree_zero {Ω : Type*} [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) :
    (∑ σ : Fin n → Bool, if monomialDegree σ = 0 then averagedCoefficient R θ σ ^ 2 else 0) = 1 := by
  classical
  simp_rw [monomialDegree_eq_zero_iff]
  simp [averagedCoefficient_empty]

/-- There is no increasing selection with more entries than its ambient set. -/
theorem increasingTuple_isEmpty {n r : ℕ} (h : n < r) : IsEmpty (IncreasingTuple n r) := by
  refine ⟨fun v => ?_⟩
  have hc := Fintype.card_le_of_injective v.val v.property.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- The finite law of uniformly retained slots has no coefficients beyond
its number of actual defect slots. -/
theorem defect_degree_bound {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (hd : StrictMono d) (hru : u < r) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then
      averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image d)) σ ^ 2 else 0) = 0 := by
  classical
  apply le_antisymm
  · refine (sum_degree_coeff_sq_le (r:=r) (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image d)))).trans ?_
    simp_rw [averaged_rank_coefficient hl d,rankDefectCoefficient_eq hl d hd]
    have := increasingTuple_isEmpty hru
    simp
  · apply Finset.sum_nonneg
    intro σ _
    split_ifs <;> positivity

/-- Coefficient version of the conditional-rank square-sum estimate. -/
theorem period_degree_square_sum {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then
      averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) σ ^ 2 else 0) ≤
      ((3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  refine (sum_degree_coeff_sq_le (r:=r) (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
    (defectAtRank (Finset.univ.image (periodSlot off))))).trans ?_
  simp_rw [averaged_rank_coefficient hl (periodSlot off),
    rankDefectCoefficient_eq hl (periodSlot off) (periodSlot_strictMono off)]
  exact period_rank_square_sum_delta hl hr hru hm hum hδ hθ hmean hv off hoff hdiff

/-- The full coefficient energy is controlled by the subgaussian degree
series, uniformly in the number of retained coordinates. -/
theorem period_density_energy {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) (R : ℝ) :
    multilinearEnergy
      (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off)))) R ≤
      ∑ r ∈ Finset.range (l+1),
        (R^2*(3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/m))^r / (Real.sqrt (r:ℝ))^r := by
  rw [multilinearEnergy_degrees]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : r = 0
  · subst r
    rw [averaged_degree_zero]
    norm_num
  · by_cases hru : r ≤ u
    · have hr0 : 0 < r := Nat.pos_of_ne_zero hr
      have hb := period_degree_square_sum hl hr0 hru hm hum hδ hθ hmean hv off hoff hdiff
      calc
        _ ≤ R^(2*r)*((3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r :=
          mul_le_mul_of_nonneg_left hb (by rw [pow_mul]; positivity)
        _ = _ := by
          have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
          have hr0 : (0:ℝ) < r := by exact_mod_cast hr0
          rw [show (u:ℝ)/((m:ℝ)*r)=((u:ℝ)/m)/r by field_simp]
          rw [Real.sqrt_div (by positivity),pow_mul,← mul_pow,← div_pow]
          congr 1
          ring
    · rw [defect_degree_bound hl (periodSlot off) (periodSlot_strictMono off) (by omega),mul_zero]
      have := hδ.1
      positivity [rankSchurConstant_pos]

/-- A convenient exponential majorant for the full nonnegative degree series. -/
theorem degree_series_le_exp (a : ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r) ≤ 2*Real.exp (a^2) := by
  have hb := degree_series_bound a N
  have hp := Real.exp_pos (a^2)
  have he : Real.exp (2*a^2) = (Real.exp (a^2))^2 := by
    rw [show 2*a^2=a^2+a^2 by ring,Real.exp_add]
    ring
  rw [he] at hb
  nlinarith [sq_nonneg ((∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r)+2*Real.exp (a^2))]

/-- Actual conditional initial-oracle density, with its exact second moment. -/
theorem period_density_second_moment {α : Type*} [Fintype α]
    (P : FiniteLaw α) (Z : α → ℝ) (hZ : P.expect Z = 0)
    {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (P.product l).expect (fun x =>
      averagedDensity (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) Z x ^ 2) ≤
      2*Real.exp ((P.expect (fun a => Z a^2))^2 * (3*rankSchurConstant/δ)^2 * ((u:ℝ)/m)) := by
  have hv0 : 0 ≤ P.expect (fun a => Z a^2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  simp_rw [averagedDensity_expansion]
  rw [multilinear_second_moment P Z hZ (Real.sqrt (P.expect (fun a => Z a^2)))
    (Real.sq_sqrt hv0).symm]
  refine (period_density_energy hl hm hum hδ hθ hmean hv off hoff hdiff _).trans ?_
  apply (degree_series_le_exp _ (l+1)).trans
  rw [Real.sq_sqrt hv0]
  have he : (P.expect (fun a => Z a^2)*(3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/m))^2 =
      (P.expect (fun a => Z a^2))^2*(3*rankSchurConstant/δ)^2*((u:ℝ)/m) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  rw [he]

/-- The source association argument holds for any two conditional mixture
experiments using the same independent primitive marks, even when their
retained-subset sample spaces have different original sizes. -/
theorem averagedDensity_overlap {α Ω Ψ : Type*}
    [Fintype α] [Fintype Ω] [Fintype Ψ]
    (P : FiniteLaw α) (R : FiniteLaw Ω) (S : FiniteLaw Ψ)
    (Z : α → ℝ) (hZ : P.expect Z = 0) (hZpos : ∀ a, 0 ≤ 1+Z a)
    {l : ℕ} (f : Ω → Fin l → Bool) (g : Ψ → Fin l → Bool) :
    (1:ℝ)/32 ≤
      (P.product l).expect (fun x => min (averagedDensity R f Z x) (averagedDensity S g Z x)) *
      (P.product l).expect (fun x => averagedDensity R f Z x ^ 2) *
      (P.product l).expect (fun x => averagedDensity S g Z x ^ 2) := by
  let : Preorder α := Preorder.lift Z
  have htotal : ∀ a b : α, a ≤ b ∨ b ≤ a := fun a b => le_total (Z a) (Z b)
  have hm : Monotone Z := fun _ _ h => h
  exact increasing_density_overlap (P.product l)
    (associated_product P (P.associated_totalPreorder htotal) l)
    (averagedDensity R f Z) (averagedDensity S g Z)
    (averagedDensity_nonneg R f Z hZpos) (averagedDensity_nonneg S g Z hZpos)
    (averagedDensity_mono R f Z hZpos hm) (averagedDensity_mono S g Z hZpos hm)
    (averagedDensity_mean P R Z hZ f) (averagedDensity_mean P S Z hZ g)

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


namespace TraceReconstruction

theorem pureAtomRun_add (w : List Bool) (n m : ℕ) :
    pureAtomRun w (n+m)=pureAtomRun w n ++ pureAtomRun w m := by
  simp only [pureAtomRun,List.replicate_add,List.flatten_append]

/-- Splitting or regrouping a pure region into reported chunks changes no
 unmarked string. In particular arbitrary fixed chunk IDs are harmless. -/
theorem pureAtomRun_partition (w : List Bool) (ns : List ℕ) :
    (ns.map (pureAtomRun w)).flatten=pureAtomRun w ns.sum := by
  induction ns with
  | nil => simp [pureAtomRun]
  | cons n ns ih => simp [ih,pureAtomRun_add]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

/-- Pointwise Bayes factorization, valid even at zero probability reports. -/
theorem pairedFlag_bayes (P Q H : FiniteLaw α) (ω : ℝ)
    (z : Option Bool × (α × α)) (b : Bool) :
    (1/2 : ℝ)*pairedFlagMass P Q H ω b z =
      pairedReportMass P Q H ω z * (flagPosterior z.1).mass b := by
  rcases z with ⟨d,z⟩
  cases d with
  | none => simp [pairedReportMass,pairedFlagMass,flagPosterior]; ring
  | some c => cases b <;> cases c <;>
      simp [pairedReportMass,pairedFlagMass,flagPosterior]

/-- Conditioning solely on exact reports does not correlate mechanisms.
 This is the actual joint-mass factorization, not an independence hypothesis. -/
theorem pairedFlags_product_bayes {ι : Type*} [Fintype ι]
    (P Q H : ι → FiniteLaw α) (ω : ι → ℝ)
    (z : ι → Option Bool × (α × α)) (b : ι → Bool) :
    (∏ i, (1/2 : ℝ)*pairedFlagMass (P i) (Q i) (H i) (ω i) (b i) (z i)) =
      (∏ i, pairedReportMass (P i) (Q i) (H i) (ω i) (z i)) *
        ∏ i, (flagPosterior (z i).1).mass (b i) := by
  simp_rw [pairedFlag_bayes]
  exact Finset.prod_mul_distrib

end TraceReconstruction.FiniteLaw


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction

/-- Elementary chi-square upper bound on the Bernoulli relative entropy.
 No Stirling estimate is used in the subsequent count overlap. -/
theorem bernoulli_entropy_upper {t p : ℝ} (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    t*Real.log (t/p)+(1-t)*Real.log ((1-t)/(1-p)) ≤
      (t-p)^2/(p*(1-p)) := by
  have h1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht.1 hp.1)) ht.1.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hp.2)))
    (sub_nonneg.mpr ht.2.le)
  have hid : t*(t/p-1)+(1-t)*((1-t)/(1-p)-1)=(t-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
    ring
  linarith

/-- Exact likelihood change from the mean-matched Bernoulli law. -/
theorem binomialMass_likelihood (n l : ℕ) {t p : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p l = binomialMass n t l *
      Real.exp (-((l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))) := by
  have h1 : Real.exp (-((l:ℝ)*Real.log (t/p)))=(p/t)^l := by
    rw [show -((l:ℝ)*Real.log (t/p))=(l:ℝ)*Real.log (p/t) by
      rw [Real.log_div ht.1.ne' hp.1.ne',Real.log_div hp.1.ne' ht.1.ne']; ring,
      Real.exp_nat_mul,Real.exp_log (div_pos hp.1 ht.1)]
  have h2 : Real.exp (-(((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p))))=((1-p)/(1-t))^(n-l) := by
    rw [show -(((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))=
      ((n-l:ℕ):ℝ)*Real.log ((1-p)/(1-t)) by
      rw [Real.log_div (sub_pos.mpr ht.2).ne' (sub_pos.mpr hp.2).ne',
        Real.log_div (sub_pos.mpr hp.2).ne' (sub_pos.mpr ht.2).ne']; ring,
      Real.exp_nat_mul,Real.exp_log (div_pos (sub_pos.mpr hp.2) (sub_pos.mpr ht.2))]
  rw [neg_add,Real.exp_add,h1,h2]
  unfold binomialMass
  rw [div_pow,div_pow]
  field_simp [ht.1.ne', (sub_pos.mpr ht.2).ne']

/-- Pointwise lower mass at every interior integer, with mean-matched
 variance at least one. It applies uniformly even as deletion vanishes. -/
theorem binomialMass_near_mean_lower (n l : ℕ) {t p : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n:ℝ)*t=l) (hv : 1 ≤ (n:ℝ)*t*(1-t)) :
    Real.exp (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))) /
      (12*Real.sqrt ((n:ℝ)*t*(1-t))) ≤ binomialMass n p l := by
  have hn : (0:ℝ)<n := by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hnl : ((n-l:ℕ):ℝ)=(n:ℝ)-(l:ℝ) := by exact Nat.cast_sub hl
  have he : (l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)) ≤
      ((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p)) := by
    have H := mul_le_mul_of_nonneg_left (bernoulli_entropy_upper ht hp) hn.le
    calc
      _ = (n:ℝ)*(t*Real.log (t/p)+(1-t)*Real.log ((1-t)/(1-p))) := by
        rw [hnl,← hmean]; ring
      _ ≤ (n:ℝ)*((t-p)^2/(p*(1-p))) := H
      _ = _ := by
        rw [← hmean]
        field_simp [hn.ne', hp.1.ne', (sub_pos.mpr hp.2).ne']
  rw [binomialMass_likelihood n l ht hp]
  calc
    _ = (1/(12*Real.sqrt ((n:ℝ)*t*(1-t)))) *
      Real.exp (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))) := by ring
    _ ≤ (1/(12*Real.sqrt ((n:ℝ)*t*(1-t)))) *
      Real.exp (-((l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg he
    _ ≤ _ := mul_le_mul_of_nonneg_right (binomialMass_mean_lower n l ht hl hmean hv)
      (Real.exp_nonneg _)

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem translateSeries_L2Sq (c : ℤ) (f : IntSeries) :
    seriesL2Sq (translateSeries c f)=seriesL2Sq f := by
  unfold seriesL2Sq
  simp_rw [translateSeries_coeff]
  exact (Equiv.subRight c).tsum_eq (fun z => f.coeff z^2)

theorem mul_translateSeries (c : ℤ) (f g : IntSeries) :
    f*translateSeries c g=translateSeries c (f*g) := by
  unfold translateSeries
  ring

theorem translated_binomial_smoothing (g s : ℕ) (c : ℤ) :
    seriesL2Sq (prouhetSeries s*translateSeries c (fairSeries g)) ≤
      ((2:ℝ)^(s*s))^2*(((2*binomialBound (g/(s+1)))^s)^2*binomialBound (g/(s+1))) := by
  rw [mul_translateSeries,translateSeries_L2Sq]
  exact (signed_binomial_smoothing g s).2

end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitiveBlock_expectation (q : ℝ) (b : Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (primitiveBlock b) F =
      ∑z : PrimitiveMark, (if b then defectPrimitiveMass q z else ordinaryPrimitiveMass q z)*F (primitiveOutput z) := by
  cases b <;> simp [primitiveBlock,listDeletionExpectation,primitiveOutput,
    defectPrimitiveMass,ordinaryPrimitiveMass,Fin.sum_univ_succ]
  ring

theorem primitiveBlock_erasure_expectation {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (b : Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (primitiveBlock b) F =
      primitiveErasure q * F []+(1-primitiveErasure q)*
        (primitiveMarkLaw q hq b).expect (fun z => F (primitiveOutput z)) := by
  rw [primitiveBlock_expectation]
  simp_rw [← primitiveMark_simulation hq]
  simp only [add_mul,Finset.sum_add_distrib]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    primitiveOutput,Matrix.cons_val_zero]
  simp only [FiniteLaw.expect,primitiveMarkLaw,mul_assoc,← Finset.mul_sum]

/-- The common deterministic mark-joining simulator is exact for arbitrary
 concatenations of primitive blocks; block boundaries are not reported. -/
theorem primitive_run_simulation {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (bs : List Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q ((bs.map primitiveBlock).flatten) F =
      silentMarkExpectation q bs (fun ys => F (joinPrimitiveMarks ys)) := by
  induction bs generalizing F with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.flatten_cons]
    rw [listDeletionExpectation_append,primitiveBlock_erasure_expectation hq]
    simp only [List.nil_append,ih,FiniteLaw.expect,primitiveMarkLaw]
    simp only [silentMarkExpectation]
    rfl

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem emittedMarkExpectation_ofFn {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    emittedMarkExpectation q (List.ofFn θ) F=
      ∑x : Fin n → PrimitiveMark, (∏i, primitiveMarkMass q (θ i) (x i))*F (List.ofFn x) := by
  induction n generalizing F with
  | zero => simp [emittedMarkExpectation]
  | succ n ih =>
    rw [List.ofFn_succ,emittedMarkExpectation]
    simp_rw [ih,Finset.mul_sum]
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => PrimitiveMark)).sum_comp,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    simp [Fin.consEquiv,Fin.prod_univ_succ,List.ofFn_succ,mul_assoc]

/-- Conditioning the independent erasures on the return count chooses
 a uniformly random subset of the original block slots. -/
theorem silentMarkExpectation_mask_mixture {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑a : Mask n, maskWeight (primitiveErasure q) a*
        emittedMarkExpectation q (traceOfMask θ a) F := by
  induction n generalizing F with
  | zero => simp [silentMarkExpectation,emittedMarkExpectation,maskWeight,traceOfMask]
  | succ n ih =>
    rw [List.ofFn_succ,silentMarkExpectation]
    simp_rw [ih]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    change (∑b : Bool, ∑a : Mask n, maskWeight (primitiveErasure q) (Fin.cons b a)*
      emittedMarkExpectation q (traceOfMask θ (Fin.cons b a)) F)=_
    simp_rw [maskWeight_cons,traceOfMask_cons]
    simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false,emittedMarkExpectation]
    simp_rw [mul_assoc,Finset.mul_sum]
    rw [Finset.sum_comm,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem maskWeight_card {n : ℕ} (q : ℝ) (a : Mask n) :
    maskWeight q a = (1-q)^(maskSubset a).card*q^(n-(maskSubset a).card) := by
  unfold maskWeight maskSubset
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun i => a i)
  rw [Finset.card_univ,Fintype.card_fin] at h
  rw [show (Finset.univ.filter fun i : Fin n => ¬a i=true).card=
      n-(Finset.univ.filter fun i : Fin n => a i=true).card by omega]

theorem slotAtRank_ofFn {n l : ℕ} (S : FixedSubset (Fin n) l) :
    List.ofFn (slotAtRank S)=S.val.sort := by
  apply List.ext_getElem
  · simp [S.property]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    rfl

theorem filtered_finRange_eq_sort {n : ℕ} (S : Finset (Fin n)) :
    ((List.finRange n).filter fun i => decide (i∈S))=S.sort := by
  apply ((List.sortedLT_finRange n).pairwise.filter _).eq_of_mem_iff S.sortedLT_sort.pairwise
  intro a
  simp

theorem selected_types_ofFn {n l : ℕ} (θ : Fin n → Bool) (S : FixedSubset (Fin n) l) :
    traceOfMask θ (fun i => decide (i∈S.val))=List.ofFn (fun v => θ (slotAtRank S v)) := by
  rw [traceOfMask,filtered_finRange_eq_sort,← slotAtRank_ofFn S,List.map_ofFn]
  rfl

theorem silentMarkExpectation_subset_mixture {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑S : Finset (Fin n), subsetWeight (1-primitiveErasure q) S*
        emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S))) F := by
  rw [silentMarkExpectation_mask_mixture,← (maskSubsetEquiv n).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro S _
  rw [maskWeight_card]
  change (1-primitiveErasure q)^(maskSubsetEquiv n ((maskSubsetEquiv n).symm S)).card *
      (primitiveErasure q)^(n-(maskSubsetEquiv n ((maskSubsetEquiv n).symm S)).card)*
      emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S))) F=_
  rw [Equiv.apply_symm_apply]
  simp [subsetWeight]

theorem subsetWeight_count_factor {n l : ℕ} (hl : l ≤ n) (p : ℝ) (S : FixedSubset (Fin n) l) :
    subsetWeight p S.val=binomialMass n p l*(uniformSubsetLaw l (by simpa using hl)).mass S := by
  have hc : (n.choose l:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hl).ne'
  simp only [subsetWeight,binomialMass,uniformSubsetLaw,S.property,Fintype.card_fin]
  field_simp

theorem silentMarkExpectation_count_mixture {n : ℕ} (q : ℝ) (hq : q∈Set.Ioo 0 1)
    (θ : Fin n → Bool) (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑l : Fin (n+1), binomialMass n (1-primitiveErasure q) l.val*
        (conditionalPrimitiveLaw (Nat.le_of_lt_succ l.isLt) q hq θ).expect (fun x => F (List.ofFn x)) := by
  rw [silentMarkExpectation_subset_mixture,← (cardinalSubsetEquiv n).symm.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l _
  change (∑S : FixedSubset (Fin n) l.val, subsetWeight (1-primitiveErasure q) S.val*
      emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S.val))) F)=_
  calc
    _ = ∑S : FixedSubset (Fin n) l.val, binomialMass n (1-primitiveErasure q) l.val*
        (uniformSubsetLaw l.val (by simpa using Nat.le_of_lt_succ l.isLt)).mass S*
        (∑x : Fin l.val → PrimitiveMark, (∏v, primitiveMarkMass q (θ (slotAtRank S v)) (x v))*F (List.ofFn x)) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [subsetWeight_count_factor (Nat.le_of_lt_succ l.isLt),selected_types_ofFn θ S,emittedMarkExpectation_ofFn]
    _ = _ := by
      unfold conditionalPrimitiveLaw FiniteLaw.expect FiniteLaw.mixture FiniteLaw.coordinateProduct primitiveMarkLaw
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro S _
      ring

end TraceReconstruction



end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem SimulatesTrace.append {α β : Type*} [Fintype α] [Fintype β]
    {q : ℝ} {P : FiniteLaw α} {Q : FiniteLaw β} {f : α → List Bool} {g : β → List Bool}
    {x y : List Bool} (hP : SimulatesTrace q P f x) (hQ : SimulatesTrace q Q g y) :
    SimulatesTrace q (P.prod Q) (fun a => f a.1++g a.2) (x++y) := by
  intro F
  rw [FiniteLaw.expect_prod,listDeletionExpectation_append]
  change P.expect (fun a => Q.expect (fun b => F (f a++g b)))=_
  unfold SimulatesTrace at hP hQ
  calc
    _ = P.expect (fun a => listDeletionExpectation q y (fun t => F (f a++t))) :=
      congrArg P.expect (funext fun a => hQ (fun t => F (f a++t)))
    _ = _ := hP (fun t => listDeletionExpectation q y (fun u => F (t++u)))

end TraceReconstruction


noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]

theorem overlap_sigma_lower (P Q : FiniteLaw ι) (K L : ∀i,FiniteLaw (β i)) :
    (∑i,min (P.mass i) (Q.mass i)*overlap (K i) (L i))≤overlap (P.sigma K) (Q.sigma L) := by
  simp only [overlap,sigma,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro b _
  apply le_min
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (P.nonneg i)
  · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (Q.nonneg i)
end FiniteLaw

theorem countedPrimitiveLaw_expect {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) (F : List PrimitiveMark→ℝ) :
    (countedPrimitiveLaw hn hq θ).expect (fun a => F (List.ofFn a.2))=
      silentMarkExpectation q (List.ofFn θ) F := by
  rw [countedPrimitiveLaw,FiniteLaw.expect_sigma,silentMarkExpectation_count_mixture q hq θ F]
  change (∑l : Fin (N+1),binomialMass n (1-primitiveErasure q) l.val*
    (boundedConditionalPrimitiveLaw hq θ l).expect (fun x => F (List.ofFn x)))=_
  let f : ℕ→ℝ := fun l => if hl:l≤n then binomialMass n (1-primitiveErasure q) l*
    (conditionalPrimitiveLaw hl q hq θ).expect (fun x => F (List.ofFn x)) else 0
  have hleft : (∑l : Fin (N+1),binomialMass n (1-primitiveErasure q) l.val*
    (boundedConditionalPrimitiveLaw hq θ l).expect (fun x => F (List.ofFn x)))=
      ∑l : Fin (N+1),f l.val := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl:l.val≤n
    · simp only [boundedConditionalPrimitiveLaw,hl,dite_eq_left,f]
    · simp [boundedConditionalPrimitiveLaw,hl,f,binomialMass,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hl)]
  rw [hleft,Fin.sum_univ_eq_sum_range f (N+1)]
  have he : (∑l∈Finset.range (n+1),f l)=∑l∈Finset.range (N+1),f l := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l _ hl
    simp only [Finset.mem_range] at hl
    simp [f,show ¬l≤n by omega]
  rw [←he,←Fin.sum_univ_eq_sum_range f (n+1)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [f,dite_eq_left (Nat.le_of_lt_succ l.isLt)]

theorem countedPrimitiveLaw_simulates {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) :
    SimulatesTrace q (countedPrimitiveLaw hn hq θ) decodeBoundedMarks
      (((List.ofFn θ).map primitiveBlock).flatten) := by
  intro F
  rw [primitive_run_simulation hq]
  exact countedPrimitiveLaw_expect hn hq θ (fun a => F (joinPrimitiveMarks a))

end TraceReconstruction


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_comm (P : FiniteLaw α) (Q : FiniteLaw β) (F : α→β→ℝ) :
    P.expect (fun a => Q.expect (F a))=Q.expect (fun b => P.expect (fun a => F a b)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end FiniteLaw

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem coordinateProduct_simulates {α : Type*} [Fintype α]
    {n : ℕ} {q : ℝ} (P : Fin n→FiniteLaw α) (f : α→List Bool) (w : Fin n→List Bool)
    (h : ∀i,SimulatesTrace q (P i) f (w i)) :
    SimulatesTrace q (FiniteLaw.coordinateProduct P) (fun a => coordinateWord (fun i => f (a i)))
      (coordinateWord w) := by
  induction n with
  | zero =>
    intro F
    change (FiniteLaw.coordinateProduct P).expect (fun _ => F [])=F []
    exact FiniteLaw.expect_const _ _
  | succ n ih =>
    intro F
    rw [FiniteLaw.expect_coordinateProduct_succ,coordinateWord_succ,listDeletionExpectation_append]
    have hj (a : α) (x : Fin n→α) :
        coordinateWord (fun i => f ((Fin.cons a x : Fin (n+1)→α) i))=f a++coordinateWord (fun i => f (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [hj]
    have ht:=ih (fun i => P i.succ) (fun i => w i.succ) (fun i => h i.succ)
    calc
      _=(P 0).expect (fun a => listDeletionExpectation q (coordinateWord (fun i => w i.succ))
          (fun t => F (f a++t))) := by
        congr 1
        funext a
        exact ht (fun t => F (f a++t))
      _=_ := h 0 (fun t => listDeletionExpectation q (coordinateWord (fun i => w i.succ)) (fun u => F (t++u)))

theorem coordinateWord_pureAtomRun {n : ℕ} (w : List Bool) (k : Fin n→ℕ) :
    coordinateWord (fun i => pureAtomRun w (k i))=pureAtomRun w (∑i,k i) := by
  change (List.ofFn (pureAtomRun w ∘ k)).flatten=_
  rw [←List.map_ofFn,pureAtomRun_partition,List.sum_ofFn]

end TraceReconstruction
noncomputable section
universe u



/-!
Concrete objects for the scale inequalities, Definition 3 (the level invariant).
The observable channel remains the complete deletion trace of a literal word.
-/
noncomputable section



/-! The actual finite paired-flag experiment.  We separate its unconditional
orientation-first generation (used for trace simulation) from its exact
metadata-first Bayes factorization (used for the density estimates).
Neither construction conditions on successful window layout. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_joint (P : FiniteLaw α) (K : α → FiniteLaw β) (F : α × β → ℝ) :
    (P.joint K).expect F = P.expect (fun a => (K a).expect (fun b => F (a,b))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_mixture (P : FiniteLaw α) (K : α → FiniteLaw β) (F : β → ℝ) :
    (P.mixture K).expect F = P.expect (fun a => (K a).expect F) := by
  simp only [expect, mixture, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Independent maps commute with the literal finite product law. -/
theorem coordinateProduct_map {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → β) :
    (coordinateProduct P).map (fun a i => f i (a i)) =
      coordinateProduct (fun i => (P i).map (f i)) := by
  apply FiniteLaw.ext
  funext b
  rw [map_mass]
  change (∑ a : Fin n → α, if (fun i => f i (a i)) = b then ∏ i, (P i).mass (a i) else 0) =
    ∏ i, ((P i).map (f i)).mass (b i)
  simp_rw [map_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : (fun i => f i (a i)) = b
  · rw [ite_eq_left hab]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun hab i)]
  · rw [ite_eq_right hab]
    symm
    have hi : ∃ i, f i (a i) ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Forgetting the report recovers the two independent side emissions. -/
theorem pairedFlagLaw_map (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a)
    (b : Bool) :
    (pairedFlagLaw P Q H hω hP hQ b).map Prod.snd = orientedProd P Q b := by
  apply FiniteLaw.ext
  funext z
  rw [map_mass, Fintype.sum_prod_type]
  simp only [pairedFlagLaw]
  simp_rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact pairedFlag_simulation P Q H ω b z

end FiniteLaw

variable {Side Leaf : Type*} [Fintype Side] [Fintype Leaf] {m n : ℕ}

namespace PairedMechanisms
variable (M : PairedMechanisms Side m)

/-- Conditional on every orientation, forgetting flags gives independent side
emissions. This is the unconditional simulation side of the construction. -/
theorem reportsGiven_forget (b : Fin m → Bool) :
    (M.reportsGiven b).map (fun z i => (z i).2) =
      FiniteLaw.coordinateProduct (fun i => FiniteLaw.orientedProd (M.first i) (M.second i) (b i)) := by
  rw [reportsGiven, FiniteLaw.coordinateProduct_map]
  congr 1
  funext i
  exact FiniteLaw.pairedFlagLaw_map _ _ _ _ _ _ _

end PairedMechanisms
end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitive_one_add_score_nonneg {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (a : PrimitiveMark) : 0 ≤ 1 + primitiveScore q a := by
  have hq1 : 1 ≤ 1/q := (le_div_iff₀ hq.1).mpr (by simpa using hq.2.le)
  have hq0 := hq.1
  fin_cases a <;> norm_num [primitiveScore] <;> linarith [show 2/q=2*(1/q) by ring]

/-- Exact conditional law of the genuine periodic primitive observation. -/
theorem conditionalPeriodLaw_density {u m l : ℕ} (hl : l ≤ u*m)
    {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (off : Fin u → Fin m) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot off))).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        averagedDensity (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image (periodSlot off))) (primitiveScore q) x := by
  rw [conditionalPrimitiveLaw_density]
  congr 2
  funext S
  exact defectTypes_atRank (periodSlot off) S

theorem primitivePeriodConstant_nonneg : 0 ≤ primitivePeriodConstant := by
  unfold primitivePeriodConstant
  positivity

theorem conditionalPeriod_second_moment {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {q θ : ℝ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    ((primitiveMarkLaw q ⟨hq.1, by linarith [hq.2]⟩ false).product l).expect (fun x =>
      averagedDensity (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) (primitiveScore q) x ^ 2) ≤
      2*Real.exp (primitivePeriodConstant/q^4 * ((u:ℝ)/m)) := by
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1, by linarith [hq.2]⟩
  let P := primitiveMarkLaw q hqi false
  have hZ : P.expect (primitiveScore q) = 0 := primitive_score_centered hqi
  have h := period_density_second_moment P (primitiveScore q) hZ hl hm hum hq hθ hmean hv off hoff hdiff
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hv0 : 0 ≤ P.expect (fun a => primitiveScore q a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hv1 : P.expect (fun a => primitiveScore q a ^ 2) ≤ 2/q :=
    primitive_score_variance_le hqi
  have hsq : (P.expect (fun a => primitiveScore q a ^ 2))^2 ≤ (2/q)^2 :=
    pow_le_pow_left₀ hv0 hv1 2
  calc
    _ ≤ (2/q)^2*(3*rankSchurConstant/q)^2*((u:ℝ)/m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity)
    _ = _ := by unfold primitivePeriodConstant; field_simp; ring

/-- Association converts the two actual conditional period-laws into common
mass. The two original block totals may differ; only the retained count agrees. -/
theorem conditionalPeriod_overlap {u v m l : ℕ}
    (hl : l ≤ u*m) (hl' : l ≤ v*m) (hm : 32 ≤ m) (hum : u ≤ m) (hvm : v ≤ m)
    {q θ θ' : ℝ} (hq : q ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hθ' : θ' ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hmean' : ((v*m:ℕ):ℝ)*θ'=l)
    (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (hv' : 1 ≤ ((v*m:ℕ):ℝ)*θ'*(1-θ'))
    (off : Fin u → Fin m) (off' : Fin v → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hoff' : ∀ j, |((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hdiff' : ∀ j k, |((off' j).val:ℝ)-(off' k).val| ≤ 2) :
    Real.exp (-(primitivePeriodConstant/q^4*((u:ℝ)/m+(v:ℝ)/m)))/128 ≤
      FiniteLaw.overlap
        (conditionalPrimitiveLaw hl q ⟨hq.1, by linarith [hq.2]⟩ (defectTypes (periodSlot off)))
        (conditionalPrimitiveLaw hl' q ⟨hq.1, by linarith [hq.2]⟩ (defectTypes (periodSlot off'))) := by
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1, by linarith [hq.2]⟩
  let P := primitiveMarkLaw q hqi false
  let R := uniformSubsetLaw l (show l≤Fintype.card (Fin (u*m)) by simpa using hl)
  let S := uniformSubsetLaw l (show l≤Fintype.card (Fin (v*m)) by simpa using hl')
  let f := defectAtRank (l:=l) (Finset.univ.image (periodSlot off))
  let g := defectAtRank (l:=l) (Finset.univ.image (periodSlot off'))
  let G := averagedDensity R f (primitiveScore q)
  let H := averagedDensity S g (primitiveScore q)
  let A := primitivePeriodConstant/q^4*((u:ℝ)/m)
  let B := primitivePeriodConstant/q^4*((v:ℝ)/m)
  have h1 := conditionalPeriod_second_moment hl hm hum hq hθ hmean hv off hoff hdiff
  have h2 := conditionalPeriod_second_moment hl' hm hvm hq hθ' hmean' hv' off' hoff' hdiff'
  change (P.product l).expect (fun x => G x^2) ≤ 2*Real.exp A at h1
  change (P.product l).expect (fun x => H x^2) ≤ 2*Real.exp B at h2
  have ha := averagedDensity_overlap P R S (primitiveScore q)
    (primitive_score_centered hqi) (primitive_one_add_score_nonneg hqi) f g
  change 1/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) *
    (P.product l).expect (fun x => G x^2) * (P.product l).expect (fun x => H x^2) at ha
  have hG : ∀x, 0 ≤ G x := averagedDensity_nonneg R f _ (primitive_one_add_score_nonneg hqi)
  have hH : ∀x, 0 ≤ H x := averagedDensity_nonneg S g _ (primitive_one_add_score_nonneg hqi)
  have ho : 0 ≤ (P.product l).expect (fun x => min (G x) (H x)) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product l).nonneg _) (le_min (hG x) (hH x)))
  have hm2 : 0 ≤ (P.product l).expect (fun x => H x^2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product l).nonneg _) (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ho) hm2
  have hc := mul_le_mul_of_nonneg_left h2 (mul_nonneg ho (by positivity : 0≤2*Real.exp A))
  have he : (P.product l).expect (fun x => min (G x) (H x)) =
      FiniteLaw.overlap
        (conditionalPrimitiveLaw hl q hqi (defectTypes (periodSlot off)))
        (conditionalPrimitiveLaw hl' q hqi (defectTypes (periodSlot off'))) := by
    unfold FiniteLaw.expect FiniteLaw.overlap
    apply Finset.sum_congr rfl
    intro x _
    rw [conditionalPeriodLaw_density,conditionalPeriodLaw_density]
    exact mul_min_of_nonneg _ _ ((P.product l).nonneg x)
  rw [← he]
  have hd : Real.exp (-(A+B))/128 ≤ (P.product l).expect (fun x => min (G x) (H x)) := by
    have hx : (1:ℝ)/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) * (4*Real.exp (A+B)) := by
      calc
        _ ≤ _ := ha.trans (hb.trans hc)
        _ = _ := by rw [Real.exp_add]; ring
    have hp : 0 < 4*Real.exp (A+B) := by positivity
    calc
      _ = ((1:ℝ)/32)/(4*Real.exp (A+B)) := by rw [Real.exp_neg]; ring
      _ ≤ _ := (div_le_iff₀ hp).2 hx
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  dsimp [A,B]
  ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The common count window is admissible for every genuine period count in
the base case. All hypotheses are elementary size/location inequalities. -/
theorem primitive_count_window {q θ : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hmean : (n:ℝ)*θ=l)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    θ ∈ Set.Icc (1-q^2) (1-q^2/4) ∧
    1 ≤ (n:ℝ)*θ*(1-θ) ∧
    Real.sqrt ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ) ∧
    ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 / ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq0 := hq.1
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.2]
  have hq2p : 0 < q^2 := sq_pos_of_pos hq0
  have hq3 : 0 < q^3 := pow_pos hq0 3
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by have hq0 := hq.1; positivity) hnlo
  have hsize : 8*(m:ℝ) ≤ (n:ℝ)*q^2 := by
    have ha := mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb := mul_le_mul_of_nonneg_right hscale hm0.le
    nlinarith
  have hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4) := by
    have hl := (abs_le.mp hdev).1
    have hr := (abs_le.mp hdev).2
    rw [←hmean] at hl hr
    constructor
    · nlinarith
    · nlinarith
  have ht0 : 0 < θ := by nlinarith [hθ.1]
  have ht1 : θ < 1 := by nlinarith [hθ.2]
  have hvlo : (n:ℝ)*q^2/8 ≤ (n:ℝ)*θ*(1-θ) := by
    have hlow : (1:ℝ)/2 ≤ θ := by linarith [hθ.1]
    have hhigh : q^2/4 ≤ 1-θ := by linarith [hθ.2]
    have hp := mul_le_mul hlow hhigh (by positivity : (0:ℝ)≤q^2/4) ht0.le
    have hp' := mul_le_mul_of_nonneg_left hp hn0.le
    nlinarith
  have hv : 1 ≤ (n:ℝ)*θ*(1-θ) := by
    have hm32 : (32:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hvhi : (n:ℝ)*θ*(1-θ) ≤ (m:ℝ)^2 := by
    have hprod : θ*(1-θ) ≤ 1 := by nlinarith [sq_nonneg θ]
    have hh := mul_le_mul_of_nonneg_left hprod hn0.le
    nlinarith
  have hsqrt : Real.sqrt ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ) := by
    exact (Real.sqrt_le_iff).mpr ⟨hm0.le,hvhi⟩
  have hp0 : 0 < 1-q^2/2 := by linarith
  have hden0 : 0 < (n:ℝ)*(1-q^2/2)*(q^2/2) := by positivity
  have hden : q^3*(m:ℝ)^2/8 ≤ (n:ℝ)*(1-q^2/2)*(q^2/2) := by
    have ha := mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb := mul_le_mul_of_nonneg_right (show (1:ℝ)/2≤1-q^2/2 by linarith)
      (mul_nonneg hn0.le (by positivity : (0:ℝ)≤q^2/2))
    nlinarith
  have hdev2 : ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 ≤ 4*(m:ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hdev 2
    rw [sq_abs] at h
    nlinarith
  have hquot : ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3 := by
    apply (div_le_div_iff₀ hden0 hq3).mpr
    have hh := mul_le_mul_of_nonneg_right hdev2 hq3.le
    nlinarith
  exact ⟨hθ,hv,hsqrt,hquot⟩

/-- Genuine binomial count mass in the window, uniformly in the vanishing
working deletion rate, with an absolute explicit exponential cost. -/
theorem primitive_count_mass_lower {q : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    Real.exp (-32/q^3)/(12*(m:ℝ)) ≤ binomialMass n (1-primitiveErasure q) l := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by have hq0 := hq.1; positivity) hnlo
  let θ : ℝ := (l:ℝ)/n
  have hmean : (n:ℝ)*θ=l := by dsimp [θ]; field_simp
  obtain ⟨ht,hv,hsqrt,hquot⟩ := primitive_count_window hq hm hscale hnlo hnhi hmean hdev
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.1,hq.2]
  have hq2p : 0 < q^2 := sq_pos_of_pos hq.1
  have ht' : θ ∈ Set.Ioo 0 1 := ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hp : 1-q^2/2 ∈ Set.Ioo 0 1 := ⟨by linarith, by linarith⟩
  have hl : l ≤ n := by
    have h := mul_le_mul_of_nonneg_left ht'.2.le hn0.le
    rw [hmean,mul_one] at h
    exact_mod_cast h
  have hmass := binomialMass_near_mean_lower n l ht' hp hl hmean hv
  have hden : 0 < 12*Real.sqrt ((n:ℝ)*θ*(1-θ)) := by positivity
  have hexp : Real.exp (-32/q^3) ≤ Real.exp (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))) := by
    apply Real.exp_le_exp.mpr
    have he : 1-(1-q^2/2)=q^2/2 := by ring
    rw [he]
    simpa only [neg_div] using neg_le_neg hquot
  calc
    _ ≤ Real.exp (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
        ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))) / (12*Real.sqrt ((n:ℝ)*θ*(1-θ))) := by
      exact div_le_div₀ (Real.exp_nonneg _) hexp hden (by nlinarith)
    _ ≤ _ := by simpa only [primitiveErasure] using hmass


theorem initialSideCount_bounds {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) :
    q*(m:ℝ)/2 ≤ (initialSideCount q m:ℝ) ∧
    (initialSideCount q m:ℝ) ≤ q*(m:ℝ) ∧ initialSideCount q m+1 ≤ m := by
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hm32 : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hq0 := hq.1
  have hq2 : q^2 ≤ 1 := by nlinarith [hq.2]
  have hqm : 2 ≤ q*(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hq2 (mul_nonneg hq0.le hm0)
    nlinarith
  have hlow := Nat.lt_floor_add_one (q*(m:ℝ))
  have hhigh := Nat.floor_le (mul_nonneg hq0.le hm0)
  change q*(m:ℝ) < (initialSideCount q m:ℝ)+1 at hlow
  change (initialSideCount q m:ℝ) ≤ q*(m:ℝ) at hhigh
  refine ⟨by linarith,hhigh,?_⟩
  have hh := mul_le_mul_of_nonneg_right hq.2 hm0
  have : (initialSideCount q m:ℝ)+1 ≤ (m:ℝ) := by linarith
  exact_mod_cast this

theorem commonCountIndex_injective {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    Function.Injective (commonCountIndex (m:=m) k p hp) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [commonCountIndex,Nat.add_left_cancel_iff] at hv
  exact Fin.ext hv

theorem commonCountIndex_deviation {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (j : Fin m) :
    |((commonCountIndex k p hp j).val:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧
    |((commonCountIndex k p hp j).val:ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt j.isLt))
  have hj : (j.val:ℝ) < m := by exact_mod_cast j.isLt
  have hj0 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha := Nat.floor_le (mul_nonneg hp.1 (Nat.cast_nonneg (k*m)))
  have hb := Nat.lt_floor_add_one (p*((k*m:ℕ):ℝ))
  have hp0 := hp.1
  have hp1 := hp.2
  have hmp : 0 ≤ (m:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hmp' : (m:ℝ)*p ≤ m := mul_le_of_le_one_right (Nat.cast_nonneg _) hp1
  change |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-((k*m:ℕ):ℝ)*p| ≤ _ ∧
    |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ _
  have hn : (((k+1)*m:ℕ):ℝ)=((k*m:ℕ):ℝ)+(m:ℝ) := by push_cast; ring
  rw [hn]
  push_cast
  constructor <;> apply abs_le.mpr <;> constructor <;> push_cast at ha hb <;> nlinarith

end TraceReconstruction



namespace TraceReconstruction
open scoped Classical

theorem ordinaryRun_replicate (n : ℕ) :
    (List.replicate n [false,true]).flatten = ordinaryRun n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ordinaryRun,ih]

/-- Unique primitive parsing identifies the rank model with the literal
period words in the manuscript, not just a law on unlabeled locations. -/
theorem primitive_period_word {m : ℕ} (off : Fin m) :
    (List.ofFn (fun j : Fin m => primitiveBlock (decide (j=off)))).flatten =
      initialPeriod m off.val := by
  induction m with
  | zero => exact Fin.elim0 off
  | succ m ih =>
    refine Fin.cases ?_ (fun d => ?_) off
    · simp [List.ofFn_succ,primitiveBlock,initialPeriod,ordinaryRun,ordinaryRun_replicate]
    · rw [List.ofFn_succ,List.flatten_cons]
      have hf : primitiveBlock (decide ((0:Fin (m+1))=d.succ))=[false,true] := by
        simp [primitiveBlock,Ne.symm (Fin.succ_ne_zero d)]
      rw [hf]
      simp only [Fin.succ_inj]
      rw [ih d]
      simp [initialPeriod,ordinaryRun,Nat.sub_sub,Nat.add_comm]

/-- Membership in the true periodic defect set is exactly the within-period
slot test, uniformly for all deterministic period types. -/
theorem periodSlot_range_iff {u m : ℕ} (off : Fin u → Fin m) (i : Fin u) (j : Fin m) :
    (⟨i.val*m+j.val,by
      have hi := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      have hj := j.isLt
      nlinarith⟩ : Fin (u*m)) ∈ Set.range (periodSlot off) ↔ j=off i := by
  constructor
  · rintro ⟨a,ha⟩
    have hval := congrArg Fin.val ha
    change a.val*m+(off a).val=i.val*m+j.val at hval
    have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
    have hdiv := congrArg (fun k : ℕ => k/m) hval
    simp only [Nat.mul_comm _ m, Nat.mul_add_div hm, Nat.div_eq_of_lt (off a).isLt,
      Nat.div_eq_of_lt j.isLt,add_zero] at hdiv
    have hai : a=i := Fin.ext hdiv
    subst a
    apply Fin.ext
    omega
  · intro h
    refine ⟨i,?_⟩
    apply Fin.ext
    simp only [periodSlot]
    exact congrArg (fun k:Fin m => i.val*m+k.val) h.symm

/-- The simulator's actual primitive list is the unpadded source gadget. -/
theorem periodic_primitive_word {u m : ℕ} (off : Fin u → Fin m) :
    (((List.ofFn (defectTypes (periodSlot off))).map primitiveBlock).flatten) =
      periodString m u off := by
  rw [List.map_ofFn,List.ofFn_mul]
  rw [List.flatten_flatten,List.map_ofFn]
  unfold periodString
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  have he : (fun j:Fin m => primitiveBlock (defectTypes (periodSlot off)
      ⟨i.val*m+j.val,by
        have hi := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
        have hj := j.isLt
        nlinarith⟩)) = fun j:Fin m => primitiveBlock (decide (j=off i)) := by
    funext j
    simp only [defectTypes,periodSlot_range_iff]
  rw [he]
  exact primitive_period_word (off i)

theorem periodString_constant {u m : ℕ} (off : Fin m) :
    periodString m u (fun _ => off) = pureAtomRun (initialPeriod m off.val) u := by
  simp only [periodString,List.ofFn_const,pureAtomRun]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitive_count_admissible {q : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    ∃ θ : ℝ, l ≤ n ∧ θ ∈ Set.Icc (1-q^2) (1-q^2/4) ∧
      (n:ℝ)*θ=l ∧ 1 ≤ (n:ℝ)*θ*(1-θ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq0 := hq.1
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hnlo
  let θ : ℝ := (l:ℝ)/n
  have hmean : (n:ℝ)*θ=l := by dsimp [θ]; field_simp
  obtain ⟨ht,hv,_,_⟩ := primitive_count_window hq hm hscale hnlo hnhi hmean hdev
  have hl : l ≤ n := by
    have ht1 : θ ≤ 1 := by nlinarith [ht.2,sq_nonneg q]
    have hh := mul_le_mul_of_nonneg_left ht1 hn0.le
    rw [hmean,mul_one] at hh
    exact_mod_cast hh
  exact ⟨θ,hl,ht,hmean,hv⟩

theorem initialOverlapLower_pos (q : ℝ) : 0 < initialOverlapLower q := by
  unfold initialOverlapLower
  positivity

theorem initialOverlapLower_lt_eighth {q : ℝ} (hq : 0 < q) :
    initialOverlapLower q < 1/8 := by
  have hx : -(32+3*primitivePeriodConstant)/q^3 ≤ 0 := by
    have hc := primitivePeriodConstant_nonneg
    apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pow_pos hq 3]
  have he : Real.exp (-(32+3*primitivePeriodConstant)/q^3) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hx
  unfold initialOverlapLower
  linarith

/-- Unconditioned common mass of the two genuine count-and-mark simulators.
This includes all retained counts, not a conditioned or changed channel. -/
theorem initial_counted_overlap {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) (off : Fin m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k := initialSideCount q m
    initialOverlapLower q ≤ FiniteLaw.overlap
      (countedPrimitiveLaw (N:=(k+1)*m) (Nat.mul_le_mul_right m (Nat.le_succ k))
        ⟨hq.1,by linarith [hq.2]⟩ (defectTypes (periodSlot (u:=k) (fun _ => off))))
      (countedPrimitiveLaw (N:=(k+1)*m) le_rfl
        ⟨hq.1,by linarith [hq.2]⟩ (defectTypes (periodSlot (u:=k+1) (fun _ => off)))) := by
  let k := initialSideCount q m
  let N := (k+1)*m
  have hq0 := hq.1
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.2]
  let p := 1-primitiveErasure q
  have hp : p ∈ Set.Icc 0 1 := primitiveRetention_mem hqi
  have hp' : p=1-q^2/2 := rfl
  obtain ⟨hklo,hkhi,hk1⟩ := initialSideCount_bounds hq hm hscale
  change q*(m:ℝ)/2 ≤ (k:ℝ) at hklo
  change (k:ℝ) ≤ q*(m:ℝ) at hkhi
  change k+1 ≤ m at hk1
  have hk : k ≤ m := by omega
  have hnlo : q*(m:ℝ)^2/2 ≤ ((k*m:ℕ):ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hklo hm0.le
    push_cast
    nlinarith
  have hnhi : ((k*m:ℕ):ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show k*m ≤ m^2 by simpa [pow_two] using Nat.mul_le_mul_right m hk)
  have hNlo : q*(m:ℝ)^2/2 ≤ (N:ℝ) := by
    exact hnlo.trans (by exact_mod_cast Nat.mul_le_mul_right m (Nat.le_succ k))
  have hNhi : (N:ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show N ≤ m^2 by simpa [N,pow_two] using Nat.mul_le_mul_right m hk1)
  have hqm : 1 ≤ q*(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show q^2≤1 by linarith) (mul_nonneg hq0.le hm0.le)
    nlinarith
  have hrate : (k:ℝ)/(m:ℝ)+((k+1:ℕ):ℝ)/(m:ℝ) ≤ 3*q := by
    rw [←add_div]
    apply (div_le_iff₀ hm0).mpr
    push_cast
    nlinarith
  have harg : primitivePeriodConstant/q^4*((k:ℝ)/m+((k+1:ℕ):ℝ)/m) ≤
      3*primitivePeriodConstant/q^3 := by
    calc
      _ ≤ primitivePeriodConstant/q^4*(3*q) :=
        mul_le_mul_of_nonneg_left hrate (div_nonneg primitivePeriodConstant_nonneg (by positivity))
      _ = _ := by field_simp
  let C₁ := boundedCountLaw (N:=N) (Nat.mul_le_mul_right m (Nat.le_succ k)) p hp
  let C₂ := boundedCountLaw (N:=N) le_rfl p hp
  let K := boundedConditionalPrimitiveLaw hqi (defectTypes (periodSlot (u:=k) (fun _ => off))) (N:=N)
  let L := boundedConditionalPrimitiveLaw hqi (defectTypes (periodSlot (u:=k+1) (fun _ => off))) (N:=N)
  let f : Fin (N+1) → ℝ := fun l => min (C₁.mass l) (C₂.mass l) * FiniteLaw.overlap (K l) (L l)
  let a : ℝ := Real.exp (-32/q^3)/(12*(m:ℝ))
  let b : ℝ := Real.exp (-(3*primitivePeriodConstant)/q^3)/128
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hf0 : ∀l, 0 ≤ f l := fun l =>
    mul_nonneg (le_min (C₁.nonneg l) (C₂.nonneg l)) (FiniteLaw.overlap_nonneg _ _)
  let ix : Fin m → Fin (N+1) := commonCountIndex k p hp
  have hterm : ∀j : Fin m, a*b ≤ f (ix j) := by
    intro j
    let l := (ix j).val
    have hd := commonCountIndex_deviation k p hp j
    change |(l:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧ |(l:ℝ)-(N:ℝ)*p| ≤ 2*(m:ℝ) at hd
    rw [hp'] at hd
    obtain ⟨θ,hl,hθ,hmean,hv⟩ := primitive_count_admissible hq hm hscale hnlo hnhi hd.1
    obtain ⟨θ',hl',hθ',hmean',hv'⟩ := primitive_count_admissible hq hm hscale hNlo hNhi hd.2
    have hm1 := primitive_count_mass_lower hq hm hscale hnlo hnhi hd.1
    have hm2 := primitive_count_mass_lower hq hm hscale hNlo hNhi hd.2
    have hmin : a ≤ min (C₁.mass (ix j)) (C₂.mass (ix j)) := le_min hm1 hm2
    have hc := conditionalPeriod_overlap hl hl' hm hk hk1 hq hθ hθ' hmean hmean' hv hv'
      (fun _ => off) (fun _ => off) (fun _ => hoff) (fun _ => hoff)
      (fun _ _ => by simp) (fun _ _ => by simp)
    have hb : b ≤ FiniteLaw.overlap (K (ix j)) (L (ix j)) := by
      dsimp only [K,L,boundedConditionalPrimitiveLaw]
      rw [dite_eq_left hl,dite_eq_left hl']
      refine le_trans ?_ hc
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤128)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg harg
    exact mul_le_mul hmin hb hb0 (le_min (C₁.nonneg _) (C₂.nonneg _))
  have hsub : (∑j : Fin m, f (ix j)) ≤ ∑l : Fin (N+1), f l := by
    have hi := commonCountIndex_injective (m:=m) k p hp
    calc
      _ = ∑l ∈ Finset.univ.image ix, f l := by
        rw [Finset.sum_image]
        exact fun a _ b _ hab => hi hab
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => hf0 l)
  have hsum : (m:ℝ)*(a*b) ≤ ∑l : Fin (N+1), f l := by
    calc
      _ = ∑_j : Fin m, a*b := by simp
      _ ≤ ∑j : Fin m, f (ix j) := Finset.sum_le_sum (fun j _ => hterm j)
      _ ≤ _ := hsub
  have he : (m:ℝ)*(a*b)=initialOverlapLower q := by
    dsimp [a,b,initialOverlapLower]
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : -32/q^3 + -(3*primitivePeriodConstant)/q^3 = -(32+3*primitivePeriodConstant)/q^3 := by ring
    rw [hx]
    field_simp
    ring
  rw [he] at hsum
  exact hsum.trans (FiniteLaw.overlap_sigma_lower C₁ C₂ K L)

/-- Data processing for common exact simulators, stated as a common-mass
inequality and allowing unequal original lengths. -/
theorem simulations_overlap_le {α : Type*} [Fintype α] {q : ℝ}
    (hq : q ∈ Set.Icc 0 1) (P Q : FiniteLaw α) (decode : α → List Bool)
    (x y : List Bool) (hP : SimulatesTrace q P decode x)
    (hQ : SimulatesTrace q Q decode y) :
    P.overlap Q ≤ listTraceOverlap q hq x y := by
  have h := approximations_trace_tv hq P Q decode x y 0 0
    (max x.length y.length) (le_max_left _ _) (le_max_right _ _)
    hP.approximate hQ.approximate
  simp only [add_zero] at h
  unfold listTraceOverlap
  rw [FiniteLaw.overlap_eq_one_sub_tv, FiniteLaw.overlap_eq_one_sub_tv]
  linarith

/-- The initial hidden-bit overlap for ordinary complete deletion traces of
consecutive pure runs. This is the unconditioned original channel. -/
theorem initial_pure_trace_overlap {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) (off : Fin m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k := initialSideCount q m
    initialOverlapLower q ≤ listTraceOverlap q ⟨hq.1.le, by linarith [hq.2]⟩
      (pureAtomRun (initialPeriod m off.val) k)
      (pureAtomRun (initialPeriod m off.val) (k+1)) := by
  let k := initialSideCount q m
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hca := countedPrimitiveLaw_simulates (N:=(k+1)*m)
    (Nat.mul_le_mul_right m (Nat.le_succ k)) hqi
    (defectTypes (periodSlot (u:=k) (fun _ => off)))
  have hcb := countedPrimitiveLaw_simulates (N:=(k+1)*m) le_rfl hqi
    (defectTypes (periodSlot (u:=k+1) (fun _ => off)))
  rw [periodic_primitive_word,periodString_constant] at hca hcb
  exact (initial_counted_overlap hq hm hscale off hoff).trans
    (simulations_overlap_le ⟨hq.1.le,by linarith [hq.2]⟩ _ _ _ _ _ hca hcb)

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LeafOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_const_mul (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f := by
  unfold expect
  simp only [mul_left_comm (P.mass _) c,Finset.mul_sum]

theorem coordinateProduct_expect_product {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i,f i (x i)) = ∏i,(P i).expect (f i) := by
  unfold expect coordinateProduct
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : α) => (P i).mass a*f i a)).symm

end FiniteLaw

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Metadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem pairedReportMass_none (P Q H : FiniteLaw α) (ω : ℝ) (z : α × α) :
    pairedReportMass P Q H ω (none,z)=pairedHiddenMass H ω z := by
  simp only [pairedReportMass,Fintype.sum_bool,pairedFlagMass]
  ring

theorem pairedReport_hidden_expect (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a) (F : ℕ → ℝ) :
    (pairedReport P Q H hω hP hQ).expect (fun z => F (hiddenTrial z.1))=
      ω^2*F 1+(1-ω^2)*F 0 := by
  let R := pairedReport P Q H hω hP hQ
  have hp : R.expect (fun z => if z.1=none then (1:ℝ) else 0)=ω^2 := by
    simp only [expect,R,pairedReport,Fintype.sum_prod_type,Fintype.sum_option]
    simp only [reduceCtorEq,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
    simpa only [pairedReportMass_none,Fintype.sum_prod_type,ite_true,mul_one] using sum_pairedHiddenMass H ω
  have he (z : Option Bool × (α × α)) : F (hiddenTrial z.1)=
      F 0+(F 1-F 0)*(if z.1=none then 1 else 0) := by
    rcases z with ⟨d,z⟩; cases d <;> simp [hiddenTrial]
  simp_rw [he]
  have hadd : R.expect (fun z => F 0+(F 1-F 0)*(if z.1=none then 1 else 0))=
      R.expect (fun _ => F 0)+R.expect (fun z => (F 1-F 0)*(if z.1=none then 1 else 0)) := by
    simp only [expect,mul_add,Finset.sum_add_distrib]
  rw [hadd,expect_const,expect_const_mul,hp]
  ring

/-- Centered hidden-flag MGF, derived from the literal paired experiment. -/
theorem pairedReport_hidden_mgf (P Q H : FiniteLaw α) {ω t : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    (pairedReport P Q H hω hP hQ).expect (fun z =>
      Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2)))≤Real.exp (t^2) := by
  rw [pairedReport_hidden_expect P Q H hω hP hQ (fun k => Real.exp (t*((k:ℝ)-ω^2)))]
  have H := binomialMass_centered_mgf 1 hp ht
  norm_num [Finset.sum_range_succ,binomialMass] at H ⊢
  convert H using 1 <;> first | rfl | ring

end FiniteLaw

namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

/-- No independence of displacements is presumed: only the flags of the
 distinct literal paired mechanisms are independent. -/
theorem hiddenCount_mgf {ω t : ℝ} (hw : ∀i,M.hiddenWeight i=ω)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    M.reports.expect (fun z => Real.exp (t*((hiddenCount z:ℕ)-(m:ℝ)*ω^2)))≤
      Real.exp ((m:ℝ)*t^2) := by
  have he (z : Reports Side m) :
      Real.exp (t*((hiddenCount z:ℕ)-(m:ℝ)*ω^2))=
        ∏i : Fin m,Real.exp (t*((hiddenTrial (z i).1:ℕ)-ω^2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,hiddenCount,Nat.cast_sum]
    ring
  simp_rw [he]
  rw [reports,FiniteLaw.coordinateProduct_expect_product _
    (fun (_ : Fin m) (z : Option Bool × (Side × Side)) => Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2))) ]
  calc
    _ ≤ ∏i : Fin m,Real.exp (t^2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun z _ => mul_nonneg
          ((FiniteLaw.pairedReport (M.first i) (M.second i) (M.common i) (M.weight_nonneg i)
            (M.common_first i) (M.common_second i)).nonneg z) (Real.exp_nonneg _))
      · intro i _
        have h := FiniteLaw.pairedReport_hidden_mgf (M.first i) (M.second i) (M.common i)
          (M.weight_nonneg i) (M.common_first i) (M.common_second i) (by simpa [hw i] using hp) ht
        simpa only [hw i] using h
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Real.exp_nat_mul]

/-- A quantitative unconditional bound for failure of a source hidden-count
 condition. The exponent ω⁴m is sufficient for the uniform scale margins. -/
theorem hiddenCount_small {ω : ℝ} (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      Real.exp (-(m:ℝ)*ω^4/16) := by
  have ht : 0≤ω^2/4 := by positivity
  have ht' : |-(ω^2/4)|≤1 := by rw [abs_neg,abs_of_nonneg ht]; linarith [hp.2]
  have H := finite_exp_markov Finset.univ M.reports.mass
    (fun z => -((hiddenCount z:ℕ)-(m:ℝ)*ω^2)) (fun z _ => M.reports.nonneg z)
    ((m:ℝ)*ω^2/2) (ω^2/4) ht
  have hm := M.hiddenCount_mgf hw hp ht'
  have hsub : M.reports.expect (fun z => if (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      ∑z∈Finset.univ.filter (fun z => (m:ℝ)*ω^2/2≤-((hiddenCount z:ℕ)-(m:ℝ)*ω^2)),M.reports.mass z := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    dsimp only
    by_cases hz : (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2
    · rw [ite_eq_left hz,ite_eq_left (by linarith : (m:ℝ)*ω^2/2≤-((hiddenCount z:ℕ)-(m:ℝ)*ω^2)),mul_one]
    · rw [ite_eq_right hz,mul_zero]; split_ifs <;> positivity [M.reports.nonneg z]
  calc
    _ ≤ _ := hsub.trans H
    _ ≤ Real.exp (-(ω^2/4)*((m:ℝ)*ω^2/2))*Real.exp ((m:ℝ)*(-(ω^2/4))^2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [FiniteLaw.expect,neg_mul,mul_neg,neg_neg] using hm
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end PairedMechanisms
end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem expect_add (P : FiniteLaw α) (f g : α → ℝ) :
    P.expect (fun a => f a+g a)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

end FiniteLaw

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hidden_binomial_bound (m G : ℕ) (ω : ℝ)
    (h : (m:ℝ)*ω^2/2≤G) : binomialBound G≤hiddenBinomialCap m ω := by
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<G+1)
    (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  nlinarith

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem ApproximatesTrace.of_tv {α : Type*} [Fintype α]
    {q E e : ℝ} {P Q : FiniteLaw α} {f : α → List Bool} {w : List Bool}
    (hP : ApproximatesTrace q P f w E) (htv : Q.tv P ≤ e) :
    ApproximatesTrace q Q f w (e+E) := by
  intro F hF
  exact (abs_sub_le (Q.expect (fun a => F (f a))) (P.expect (fun a => F (f a)))
    (listDeletionExpectation q w F)).trans (add_le_add
      ((FiniteLaw.abs_expect_sub_le_tv Q P _ (fun a => hF _)).trans htv) (hP F hF))

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOracle

Actual initial scores and anchors, count partitions and typicality, clipped metadata, common decoding, sharp hidden-count energy, tails, and budget caps.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace PairedMechanisms
variable {Side α : Type*} [Fintype Side] [Fintype α] {J : ℕ}

/-- Bayes factorization is valid for arbitrary conditional finite emissions,
 including the dependent-length initial primitive-mark list. -/
theorem emission_factorization (M : PairedMechanisms Side J) (K : (Fin J → Bool) → FiniteLaw α) :
    (fairOrientations J).mixture (fun b => (M.reportsGiven b).prod (K b))=M.emissionOracle K := by
  apply FiniteLaw.ext
  funext zx
  rcases zx with ⟨z,x⟩
  change (∑b,(∏i : Fin J,(1/2:ℝ))*
    ((∏i,FiniteLaw.pairedFlagMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (b i) (z i))*(K b).mass x))=
    (∏i,FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (z i))*(∑b,(∏i,(flagPosterior (z i).1).mass (b i))*(K b).mass x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [←mul_assoc,←Finset.prod_mul_distrib,FiniteLaw.pairedFlags_product_bayes,mul_assoc]

end PairedMechanisms

theorem conditionalMotifLaw_posterior {u m l J : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (d : Fin J → Option Bool) (s : ℕ) (τ : ℝ) :
    (FiniteLaw.coordinateProduct (fun i => flagPosterior (d i))).mixture
      (fun b => conditionalPrimitiveLaw hl q hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    conditionalMotifLaw hl off hsafe hq (posteriorAnchorSeries c d)
      (posteriorAnchorSeries_nonneg c d) (posteriorAnchorSeries_total c d) s τ := by
  apply FiniteLaw.ext
  funext x
  change (∑b : Fin J → Bool,(∏i : Fin J,(flagPosterior (d i)).mass (b i))*
    (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s
      (c-∑i,(bitIndex (b i):ℤ)) τ))).mass x)=_
  classical
  have H := posterior_anchor_average c d (fun X =>
    (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X τ))).mass x)
  calc
    _ = ∑X∈(posteriorAnchorSeries c d).coeff.support,
        (posteriorAnchorSeries c d).coeff X*
          (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X τ))).mass x := by
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext b
      simp
    _ = _ := (Finset.sum_coe_sort _ _).symm


theorem countedMotifLaw_posterior {u m J : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (d : Fin J → Option Bool) (s : ℕ) (τ : ℝ) :
    (FiniteLaw.coordinateProduct (fun i => flagPosterior (d i))).mixture
      (fun b => countedPrimitiveLaw (le_refl (u*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    countedMotifLaw off hsafe hq (posteriorAnchorSeries c d)
      (posteriorAnchorSeries_nonneg c d) (posteriorAnchorSeries_total c d) s τ := by
  apply FiniteLaw.ext
  funext x
  rcases x with ⟨l,x⟩
  have hl : l.val ≤ u*m := by omega
  have H := congrArg (fun P : FiniteLaw (Fin l.val → PrimitiveMark) => P.mass x)
    (conditionalMotifLaw_posterior hl off hsafe hq c d s τ)
  change (∑b, _ * ((boundedCountLaw _ _ _).mass l *
    (boundedConditionalPrimitiveLaw hq _ l).mass x))=_
  simp only [boundedConditionalPrimitiveLaw,dite_eq_left hl]
  change _ = (boundedCountLaw _ _ _).mass l * _
  rw [←H]
  simp only [FiniteLaw.mixture,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring


end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem signedPeriodDefects_periodSlot {u m : ℕ} (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    signedPeriodDefects off hsafe s X τ =
      periodSlot (fun j => motifOffset off hi s X τ j.val) := by
  funext j
  apply Fin.ext
  simp only [signedPeriodDefects,shiftedTag,periodSlot,motifOffset]
  omega

theorem signed_primitive_word {u m : ℕ} (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    (((List.ofFn (defectTypes (signedPeriodDefects off hsafe s X τ))).map primitiveBlock).flatten)=
    motifPeriodWord off hi u s X τ := by
  rw [signedPeriodDefects_periodSlot off hi,periodic_primitive_word]
  rfl

theorem motifOffset_outside {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : ℤ) (hj : j<X ∨ X+(2^s:ℕ) ≤ j) :
    motifOffset off hi s X τ j=off := by
  apply Fin.ext
  have h : ¬(0 ≤ j-X ∧ j-X<(2^s:ℕ)) := by omega
  simp only [motifOffset,motifIndicator,ite_eq_right h,motifShift,ite_true]
  norm_num

theorem motifOffset_translate {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X t : ℤ) (τ : ℝ) (j : ℤ) :
    motifOffset off hi s X τ (t+j)=motifOffset off hi s (X-t) τ j := by
  have h : t+j-X=j-(X-t) := by ring
  simp only [motifOffset,h]

theorem periodString_three {m : ℕ} (n k z : ℕ) (off : Fin (n+k+z) → Fin m) :
    periodString m (n+k+z) off =
      periodString m n (fun i => off ⟨i.val,by omega⟩) ++
      periodString m k (fun i => off ⟨n+i.val,by omega⟩) ++
      periodString m z (fun i => off ⟨n+k+i.val,by omega⟩) := by
  simp only [periodString,List.ofFn_add,List.flatten_append]
  rfl

/-- Every randomized initial partition is a partition of the same literal
period string, with no fit conditioning or change of channel. -/
theorem motifPeriodWord_window {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (t K z s : ℕ) (a : ℤ) (τ : ℝ) (hleft : (t:ℤ) ≤ a) (hright : a+(2^s:ℕ) ≤ t+K) :
    motifPeriodWord off hi (t+K+z) s a τ =
      pureAtomRun (initialPeriod m off.val) t ++ motifPeriodWord off hi K s (a-t) τ ++
      pureAtomRun (initialPeriod m off.val) z := by
  unfold motifPeriodWord
  rw [periodString_three]
  congr 2
  · rw [←periodString_constant off]
    congr 1
    funext i
    exact motifOffset_outside off hi s a τ i.val (Or.inl (by have H:=i.isLt; omega))
  · congr 1
    funext i
    rw [Nat.cast_add,motifOffset_translate]
  · rw [←periodString_constant off]
    congr 1
    funext i
    exact motifOffset_outside off hi s a τ (t+K+i.val) (Or.inr (by
      have H : (0:ℤ) ≤ i.val := by positivity
      omega))

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem coordinateProduct_expect_pairs {n : ℕ} (P : Fin n → FiniteLaw α)
    (Q : Fin n → FiniteLaw β) (F : (Fin n → α×β) → ℝ) :
    (coordinateProduct (fun i => (P i).prod (Q i))).expect F=
      (coordinateProduct P).expect (fun a =>
        (coordinateProduct Q).expect (fun b => F (fun i => (a i,b i)))) := by
  induction n with
  | zero =>
    have H (a : Fin 0 → α×β) : a = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    have hF : F=fun _ => F (fun i => Fin.elim0 i) := by
      funext a
      exact congrArg F (H a)
    rw [hF]
    simp only [expect_const]
  | succ n ih =>
    rw [expect_coordinateProduct_succ,expect_prod,expect_coordinateProduct_succ]
    congr 1
    funext a
    simp_rw [ih,expect_coordinateProduct_succ Q]
    rw [expect_comm]
    congr 1
    funext x
    congr 1
    funext b
    congr 1
    funext y
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

end FiniteLaw

namespace PairedMechanisms
variable {Side α : Type*} [Fintype Side] [Fintype α] {J : ℕ}

theorem reportsGiven_paired_simulates (M : PairedMechanisms Side J) (b : Fin J → Bool)
    {q : ℝ} (side : Side → List Bool) (central : α → List Bool) (K : FiniteLaw α)
    (U V : Fin J → List Bool) (w : List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (U i))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (V i))
    (hK : SimulatesTrace q K central w) :
    SimulatesTrace q ((M.reportsGiven b).prod K) (decodePairedEmission side central)
      (coordinateWord (fun i => if b i then V i else U i) ++ w ++
        coordinateWord (fun i => if b i then U i else V i)) := by
  let P : Fin J → FiniteLaw Side := fun i => if b i then M.second i else M.first i
  let Q : Fin J → FiniteLaw Side := fun i => if b i then M.first i else M.second i
  have HP : ∀i,SimulatesTrace q (P i) side (if b i then V i else U i) := by
    intro i
    dsimp [P]
    cases h:b i
    · exact hfirst i
    · exact hsecond i
  have HQ : ∀i,SimulatesTrace q (Q i) side (if b i then U i else V i) := by
    intro i
    dsimp [Q]
    cases h:b i
    · exact hsecond i
    · exact hfirst i
  have H := ((coordinateProduct_simulates P side _ HP).append hK).append
    (coordinateProduct_simulates Q side _ HQ)
  intro F
  rw [←H F,FiniteLaw.expect_prod,FiniteLaw.expect_prod]
  change (M.reportsGiven b).expect (fun z => K.expect (fun x =>
    F (coordinateWord (fun i => side (z i).2.1) ++ central x ++
      coordinateWord (fun i => side (z i).2.2))))=_
  have hf := congrArg (fun L : FiniteLaw (Fin J → Side×Side) => L.expect (fun z =>
    K.expect (fun x => F (coordinateWord (fun i => side (z i).1) ++ central x ++
      coordinateWord (fun i => side (z i).2))))) (M.reportsGiven_forget b)
  rw [FiniteLaw.expect_map] at hf
  simp only [Function.comp_def] at hf
  rw [hf]
  have he : (fun i => FiniteLaw.orientedProd (M.first i) (M.second i) (b i))=
      fun i => (P i).prod (Q i) := by
    funext i
    cases h:b i <;> simp [FiniteLaw.orientedProd,P,Q,h]
  rw [he,FiniteLaw.coordinateProduct_expect_pairs]
  simp only [FiniteLaw.expect_prod]
  congr 1
  funext a
  rw [FiniteLaw.expect_comm]

end PairedMechanisms
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initialPrefixPeriods_eval {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    initialPrefixPeriods k b=J*k+∑i,bitIndex (b i) := by
  simp [initialPrefixPeriods,Finset.sum_add_distrib]

theorem initialPairPeriods_total {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    initialPrefixPeriods k b+initialSuffixPeriods k b=J*(2*k+1) := by
  unfold initialPrefixPeriods initialSuffixPeriods
  rw [←Finset.sum_add_distrib]
  have H (i : Fin J) : (k+bitIndex (b i))+(k+(1-bitIndex (b i)))=2*k+1 := by
    cases h:b i <;> simp [bitIndex] <;> omega
  simp only [H,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem initialPrefixPeriods_bounds {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    J*k ≤ initialPrefixPeriods k b ∧ initialPrefixPeriods k b ≤ J*k+J := by
  rw [initialPrefixPeriods_eval]
  have H : (∑i,bitIndex (b i)) ≤ J := by
    calc
      _ ≤ ∑_i : Fin J,1 := Finset.sum_le_sum (fun i _ => by cases b i <;> simp [bitIndex])
      _ = _ := by simp
  omega

theorem initial_paired_oracle_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k s : ℕ) (a : ℤ) (τ : ℝ)
    (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1)))
    (ha : (J*k+J:ℕ) ≤ a) (ha' : a+(2^s:ℕ) ≤ (J*k+K:ℕ)) :
    SimulatesTrace q
      (M.emissionOracle (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))))
      (decodePairedEmission side decodeBoundedMarks)
      (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) := by
  rw [←M.emission_factorization]
  intro F
  rw [FiniteLaw.expect_mixture]
  have H (b : Fin J → Bool) :
      ((M.reportsGiven b).prod (countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ)))).expect
        (fun z => F (decodePairedEmission side decodeBoundedMarks z))=
      listDeletionExpectation q (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) F := by
    let t := initialPrefixPeriods k b
    let z := initialSuffixPeriods k b
    have ht := initialPrefixPeriods_bounds k b
    have htot : t+K+z=J*(2*k+1)+K := by
      have H:=initialPairPeriods_total k b
      dsimp [t,z]
      omega
    have hanchor : a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)=a-t := by
      dsimp [t]
      rw [initialPrefixPeriods_eval]
      push_cast
      ring
    have hleft : (t:ℤ) ≤ a := by
      have H : (t:ℤ) ≤ (J*k+J:ℕ) := by exact_mod_cast ht.2
      omega
    have hright : a+(2^s:ℕ) ≤ (t:ℤ)+K := by
      have H : ((J*k:ℕ):ℤ) ≤ t := by exact_mod_cast ht.1
      simp only [Nat.cast_add] at ha'
      omega
    have hp : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) (k+1) else pureAtomRun (initialPeriod m off.val) k)=
        pureAtomRun (initialPeriod m off.val) t := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) (k+1) else
          pureAtomRun (initialPeriod m off.val) k)=pureAtomRun (initialPeriod m off.val) (k+bitIndex (b i)) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hz : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) k else pureAtomRun (initialPeriod m off.val) (k+1))=
        pureAtomRun (initialPeriod m off.val) z := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=pureAtomRun (initialPeriod m off.val) (k+(1-bitIndex (b i))) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hc := countedPrimitiveLaw_simulates (le_refl (K*m)) hq
      (defectTypes (signedPeriodDefects off hsafe s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))
    rw [signed_primitive_word off hi] at hc
    have hs := M.reportsGiven_paired_simulates b side decodeBoundedMarks _
      (fun _ => pureAtomRun (initialPeriod m off.val) k)
      (fun _ => pureAtomRun (initialPeriod m off.val) (k+1)) _ hfirst hsecond hc
    have hword : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) (k+1) else pureAtomRun (initialPeriod m off.val) k) ++
        motifPeriodWord off hi K s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ ++
        coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=
        motifPeriodWord off hi (J*(2*k+1)+K) s a τ := by
      rw [hp,hz,hanchor,←motifPeriodWord_window off hi t K z s a τ hleft hright,htot]
    rw [hword] at hs
    exact hs F
  simp only [H,FiniteLaw.expect_const]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initialSigmaLaw_expect {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ)
    (F : Reports Side J × BoundedMarks (K*m) → ℝ) :
    (initialSigmaLaw M off hsafe hq c s τ).expect (fun z => F (z.1.1,⟨z.1.2,z.2⟩))=
    (M.emissionOracle (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
      (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))).expect F := by
  unfold PairedMechanisms.emissionOracle
  rw [FiniteLaw.expect_joint]
  have H (z : Reports Side J) : (PairedMechanisms.orientationsGiven z).mixture
      (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
      countedMotifLaw off hsafe hq (posteriorAnchorSeries c (fun i => (z i).1))
        (posteriorAnchorSeries_nonneg c _) (posteriorAnchorSeries_total c _) s τ :=
    countedMotifLaw_posterior off hsafe hq c (fun i => (z i).1) s τ
  simp_rw [H]
  simp only [initialSigmaLaw,initialMetadataLaw,FiniteLaw.expect_sigma,FiniteLaw.expect_prod,
    countedMotifLaw,initialConditionalLaw]

theorem initial_sigma_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k s : ℕ) (a : ℤ) (τ : ℝ)
    (off : Fin m) (hi : 1  ≤  off.val ∧ off.val+1  <  m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1)))
    (ha : (J*k+J:ℕ)  ≤  a) (ha' : a+(2^s:ℕ)  ≤  (J*k+K:ℕ)) :
    SimulatesTrace q (initialSigmaLaw M off hsafe hq (a-(J*k:ℕ)) s τ)
      (decodeInitialObservation side) (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) := by
  intro F
  unfold decodeInitialObservation
  rw [initialSigmaLaw_expect M off hsafe hq (a-(J*k:ℕ)) s τ (fun z => F (decodePairedEmission side decodeBoundedMarks z))]
  exact initial_paired_oracle_simulates M k s a τ off hi hsafe hq side hfirst hsecond ha ha' F

end TraceReconstruction



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A common finite decoder transfers normalized clipping to actual complete
 traces. Neither interface is permitted to assume the main lower bound. -/
theorem ClippedOracle.tracePair {α : Type} [Fintype α] {P Q : FiniteLaw α}
    {q e V : ℝ} {x y : List Bool} {k : ℕ} (f : α → List Bool)
    (C : ClippedOracle P Q k e V) (hP : SimulatesTrace q P f x)
    (hQ : SimulatesTrace q Q f y) : Nonempty (OracleTracePair q x y k e V) := by
  refine ⟨{
    Outcome := α
    finiteOutcome := inferInstance
    first := C.first
    second := C.second
    decode := f
    score := C.score
    density := C.density
    likelihood_nonneg := C.likelihood_nonneg
    centered := C.centered
    moment := C.moment
    first_simulation := ?_
    second_simulation := ?_
  }⟩
  · simpa using hP.approximate.of_tv C.first_tv
  · simpa using hQ.approximate.of_tv C.second_tv

theorem initialPureSigmaLaw_expect {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (F : Reports Side J × BoundedMarks (K*m) → ℝ) :
    (initialPureSigmaLaw M off hq).expect (fun z => F (z.1.1,⟨z.1.2,z.2⟩))=
    (M.emissionOracle (fun _ => countedPrimitiveLaw (le_refl (K*m)) hq
      (defectTypes (periodSlot (u:=K) (fun _ => off))))).expect F := by
  simp only [initialPureSigmaLaw,initialMetadataLaw,FiniteLaw.expect_sigma,
    FiniteLaw.expect_prod,PairedMechanisms.emissionOracle,FiniteLaw.expect_joint,
    FiniteLaw.expect_mixture,FiniteLaw.expect_const,initialPureConditionalLaw,
    countedPrimitiveLaw,FiniteLaw.expect_sigma]
  have hl (l : Fin (K*m+1)) : l.val ≤ K*m := Nat.le_of_lt_succ l.isLt
  simp only [boundedConditionalPrimitiveLaw,hl,dite_eq_left]

theorem initial_pure_sigma_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k : ℕ) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1))) :
    SimulatesTrace q (initialPureSigmaLaw (K:=K) M off hq) (decodeInitialObservation side)
      (pureAtomRun (initialPeriod m off.val) (J*(2*k+1)+K)) := by
  intro F
  unfold decodeInitialObservation
  rw [initialPureSigmaLaw_expect M off hq (fun z => F (decodePairedEmission side decodeBoundedMarks z)),
    ←M.emission_factorization,FiniteLaw.expect_mixture]
  have H (b : Fin J → Bool) :
      ((M.reportsGiven b).prod (countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (periodSlot (u:=K) (fun _ => off))))).expect
        (fun z => F (decodePairedEmission side decodeBoundedMarks z))=
      listDeletionExpectation q (pureAtomRun (initialPeriod m off.val) (J*(2*k+1)+K)) F := by
    have hc := countedPrimitiveLaw_simulates (le_refl (K*m)) hq (defectTypes (periodSlot (u:=K) (fun _ => off)))
    rw [periodic_primitive_word,periodString_constant] at hc
    have hs := M.reportsGiven_paired_simulates b side decodeBoundedMarks _
      (fun _ => pureAtomRun (initialPeriod m off.val) k)
      (fun _ => pureAtomRun (initialPeriod m off.val) (k+1)) _ hfirst hsecond hc
    have hp : coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) (k+1)
        else pureAtomRun (initialPeriod m off.val) k)=
        pureAtomRun (initialPeriod m off.val) (initialPrefixPeriods k b) := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) (k+1) else
          pureAtomRun (initialPeriod m off.val) k)=pureAtomRun (initialPeriod m off.val) (k+bitIndex (b i)) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hz : coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) k
        else pureAtomRun (initialPeriod m off.val) (k+1))=
        pureAtomRun (initialPeriod m off.val) (initialSuffixPeriods k b) := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=pureAtomRun (initialPeriod m off.val) (k+(1-bitIndex (b i))) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    rw [hp,hz,←pureAtomRun_add,←pureAtomRun_add] at hs
    have ht : initialPrefixPeriods k b+K+initialSuffixPeriods k b=J*(2*k+1)+K := by
      have ht:=initialPairPeriods_total k b
      omega
    rw [ht] at hs
    exact hs F
  simp only [H,FiniteLaw.expect_const]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hidden_quotient_bound (J G s : ℕ) (ω : ℝ) (h : (J:ℝ)*ω^2/2≤G) :
    binomialBound (G/(s+1))≤Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)) := by
  apply (binomialBound_quotient_le G s).trans
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(G:ℝ)+1)
    (by positivity : (0:ℝ)<(J:ℝ)*ω^2+2)).mpr
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤4*((s:ℝ)+1))
  nlinarith

theorem posteriorAnchorSeries_signed_L2 {J : ℕ} (d : Fin J→Option Bool) (c : ℤ) (s : ℕ) (ω : ℝ)
    (h : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    seriesL2Sq (prouhetSeries s*posteriorAnchorSeries c d)≤hiddenSignedL2Bound J s ω := by
  have hn : (J:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  have hb := hidden_quotient_bound J (∑i,hiddenTrial (d i)) s ω hn
  apply (translated_binomial_smoothing (∑i,hiddenTrial (d i)) s _).trans
  unfold hiddenSignedL2Bound
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul
  · apply pow_le_pow_left₀ (by unfold binomialBound; positivity)
    exact pow_le_pow_left₀ (by unfold binomialBound; positivity) (mul_le_mul_of_nonneg_left hb (by norm_num)) _
  · exact hb
  · exact Real.sqrt_nonneg _
  · positivity

theorem posteriorAnchorSeries_unsigned_L2 {J : ℕ} (d : Fin J→Option Bool) (c : ℤ) (s : ℕ) (ω : ℝ)
    (h : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    seriesL2Sq (geomSeries (2^s)*posteriorAnchorSeries c d)≤hiddenUnsignedL2Bound J s ω := by
  have hn : (J:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  calc
    _ ≤ seriesL1 (geomSeries (2^s))^2*seriesL2Sq (posteriorAnchorSeries c d) := seriesL2Sq_mul_le _ _
    _ ≤ ((2:ℝ)^s)^2*hiddenBinomialCap J ω := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (seriesL1_nonneg _) (by exact_mod_cast geomSeries_L1_le (2^s)) _
      · rw [posteriorAnchorSeries,translateSeries_L2Sq]
        exact (fairSeries_L2Sq_bound _).trans (hidden_binomial_bound J _ ω hn)
      · exact seriesL2Sq_nonneg _
      · positivity

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initial_theta_variance {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    θ∈Set.Ioo 0 1 ∧ 1/2≤θ ∧ q^2/8≤θ*(1-θ) := by
  have hq2 : q^2≤1/4 := by nlinarith [hq.1,hq.2]
  have hs : 0<q^2 := sq_pos_of_pos hq.1
  have hh : 1/2≤θ := by linarith [hθ.1]
  refine ⟨⟨by linarith,by linarith [hθ.2]⟩,hh,?_⟩
  have H := mul_le_mul hh (show q^2/4≤1-θ by linarith [hθ.2])
    (by positivity : (0:ℝ)≤q^2/4) (by linarith : 0≤θ)
  nlinarith

theorem initialDifferenceCap_bound (d : ℕ) {q θ : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    lengthDifferenceConstant d θ≤ initialDifferenceCap d q := by
  have ht := initial_theta_variance hq hθ
  unfold lengthDifferenceConstant initialDifferenceCap
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (mul_pos ht.1.1 (sub_pos.mpr ht.1.2)) (sq_pos_of_pos hq.1)).mpr
  have H := mul_le_mul_of_nonneg_left ht.2.2 (by positivity : (0:ℝ)≤8*((d:ℝ)+1))
  nlinarith

theorem initialPrefactorCap_nonneg (u m r d : ℕ) (q : ℝ) : 0≤ initialPrefactorCap u m r d q := by
  unfold initialPrefactorCap initialDifferenceCap
  positivity

theorem initial_prefactor_bound (u m r d : ℕ) {q θ : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    periodDifferencePrefactor u m r d θ≤ initialPrefactorCap u m r d q := by
  unfold periodDifferencePrefactor initialPrefactorCap
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by unfold lengthDifferenceConstant; positivity) (initialDifferenceCap_bound d hq hθ) _

theorem binomial_mean_inverse_le_sqrt {n l : ℕ} {θ : ℝ}
    (hθ : θ∈Set.Ioo 0 1) (hl : l≤n) (hmean : (n:ℝ)*θ=l)
    (hv : 1≤(n:ℝ)*θ*(1-θ)) :
    (binomialMass n θ l)⁻¹≤12*Real.sqrt (n:ℝ) := by
  have h0 : 0≤(binomialMass n θ l)⁻¹ := inv_nonneg.mpr (binomialMass_nonneg n l ⟨hθ.1.le,hθ.2.le⟩)
  have hi := binomialMass_mean_inverse_sq n l hθ hl hmean hv
  have hv' : (n:ℝ)*θ*(1-θ)≤n := by
    have h := mul_le_mul_of_nonneg_left (show θ*(1-θ)≤1 by nlinarith [sq_nonneg θ]) (Nat.cast_nonneg (α:=ℝ) n)
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith [Real.sqrt_nonneg (n:ℝ)]

theorem initial_rank_tail_bound {u m l : ℕ} (r : ℕ) {θ : ℝ}
    (hθ : θ∈Set.Ioo 0 1) (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l)
    (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ)) :
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l*(2*Real.exp (-(m:ℝ)/(1024*u))))))^2 ≤
    initialRankTailCap u m r := by
  have hp : θ^r≤1 := pow_le_one₀ hθ.1.le hθ.2.le
  have hi := binomial_mean_inverse_le_sqrt hθ hl hmean hv
  have hn : 0≤(binomialMass (u*m) θ l)⁻¹ := inv_nonneg.mpr (binomialMass_nonneg _ _ ⟨hθ.1.le,hθ.2.le⟩)
  unfold initialRankTailCap
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hb := binomialMass_nonneg (u*m) l ⟨hθ.1.le,hθ.2.le⟩
  apply pow_le_pow_left₀ (by
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hθ.1.le _)) hb)
        (by positivity))))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have H := mul_le_mul hp hi hn (by norm_num : (0:ℝ)≤1)
  have HH := mul_le_mul_of_nonneg_left H (by positivity : (0:ℝ)≤4*((r+1:ℕ):ℝ)*Real.exp (-(m:ℝ)/(1024*u)))
  simp only [div_eq_mul_inv,one_mul] at *
  nlinarith only [HH]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The central binomial typical interval also guarantees the rank-kernel
 variance condition, rather than imposing it by conditioning. -/
theorem initialCountAdmissible_of_near {N : ℕ} {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2) (l : Fin (N+1))
    (hnear : |(l.val:ℝ)-(N:ℝ)*(1-q^2/2)|<(N:ℝ)*q^2/4) :
    initialCountAdmissible N q l := by
  have hN : (0:ℝ)<N := by
    have h0 : (0:ℝ)≤N := Nat.cast_nonneg N
    by_contra H
    have hn : (N:ℝ)=0 := le_antisymm (le_of_not_gt H) h0
    rw [hn,zero_mul] at hscale
    norm_num at hscale
  have hq2 : q^2≤1/4 := by nlinarith [hq.1,hq.2]
  let θ : ℝ := (l.val:ℝ)/(N:ℝ)
  have he : (N:ℝ)*θ=l.val := mul_div_cancel₀ _ hN.ne'
  have hθ : θ∈Set.Icc (1-q^2) (1-q^2/4) := by
    have hn := abs_lt.mp hnear
    constructor
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith [sq_nonneg q]
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith
  have hhalf : 3/4≤θ := by linarith [hθ.1]
  have hlow : q^2/4≤1-θ := by linarith [hθ.2]
  have hp := mul_le_mul ((mul_le_mul_iff_right₀ hN).mpr hhalf) hlow
    (by positivity : (0:ℝ)≤q^2/4) (mul_nonneg hN.le (by linarith : 0≤θ))
  refine ⟨hθ,?_⟩
  change 1≤(N:ℝ)*θ*(1-θ)
  nlinarith

/-- An explicit unconditional tail for the actual count law. Its q⁴ exponent
 is more than enough under the source's q⁻¹=N^{o(1)} standing regime. -/
theorem initial_count_bad_mass {N : ℕ} {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2) :
    (boundedCountLaw (le_refl N) (1-primitiveErasure q)
      (primitiveRetention_mem ⟨hq.1,by linarith [hq.2]⟩)).expect
      (fun l => if initialCountAdmissible N q l then 0 else 1) ≤
    2*Real.exp (-(N:ℝ)*q^4/64) := by
  let p := 1-primitiveErasure q
  have hp : p∈Set.Icc 0 1 := primitiveRetention_mem ⟨hq.1,by linarith [hq.2]⟩
  have ht : q^2/8∈Set.Icc (0:ℝ) 1 := ⟨by positivity,by nlinarith [hq.1,hq.2]⟩
  have H := binomialMass_abs_tail N (a:=(N:ℝ)*q^2/4) hp ht
  have he : -(q^2/8)*((N:ℝ)*q^2/4)+(N:ℝ)*(q^2/8)^2= -(N:ℝ)*q^4/64 := by ring
  rw [he] at H
  apply le_trans _ H
  rw [Finset.sum_filter,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro l _
  change binomialMass N p l.val*(if initialCountAdmissible N q l then 0 else 1)≤_
  have hn := binomialMass_nonneg N l.val hp
  by_cases hl : initialCountAdmissible N q l
  · rw [ite_eq_left hl,mul_zero]
    split_ifs <;> positivity
  · rw [ite_eq_right hl,mul_one,ite_eq_left]
    exact le_of_not_gt (fun h => hl (initialCountAdmissible_of_near hq hscale l (by simpa [p,primitiveErasure] using h)))

/-- The true bad metadata mass is charged without changing any conditional
 law or requiring an unproved concentration conclusion. -/
theorem initial_metadata_bad_mass {Side : Type*} [Fintype Side] {J N : ℕ}
    (M : PairedMechanisms Side J) {q ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2)
    (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    (initialMetadataLaw M N ⟨hq.1,by linarith [hq.2]⟩).expect
      (fun z => if initialMetadataGood q ω z then 0 else 1) ≤
    2*Real.exp (-(N:ℝ)*q^4/64)+Real.exp (-(J:ℝ)*ω^4/16) := by
  calc
    _ ≤ (initialMetadataLaw M N ⟨hq.1,by linarith [hq.2]⟩).expect
        (fun z => (if initialCountAdmissible N q z.2 then 0 else 1)+
          (if (PairedMechanisms.hiddenCount z.1:ℝ)<(J:ℝ)*ω^2/2 then 1 else 0)) := by
      apply FiniteLaw.expect_mono
      intro z
      have he : (PairedMechanisms.hiddenCount z.1:ℝ)=∑i,(hiddenTrial (z.1 i).1:ℝ) := by
        simp only [PairedMechanisms.hiddenCount,Nat.cast_sum]
      unfold initialMetadataGood
      rw [←he]
      split_ifs <;> simp_all
    _ ≤ _ := by
      simp only [FiniteLaw.expect_add,initialMetadataLaw,FiniteLaw.expect_prod]
      apply add_le_add
      · exact (M.reports.expect_mono (fun _ => initial_count_bad_mass hq hscale)).trans (by rw [FiniteLaw.expect_const])
      · convert M.hiddenCount_small hw hp using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext a
        split_ifs <;> simp [FiniteLaw.expect,FiniteLaw.total]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initial_signed_pattern_cap {J : ℕ} (d : Fin J → Option Bool) (c : ℤ)
    (u m r s : ℕ) (k : Fin r → GapDifference) {q θ ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    signedPatternBound u m r s (posteriorAnchorSeries c d) θ k ≤
      initialSignedPatternCap J u m r s q ω k := by
  unfold signedPatternBound initialSignedPatternCap
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r 1 hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_signed_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r _ hq hθ)
        (by unfold periodBoundedSumConstant; positivity)
    · exact posteriorAnchorSeries_unsigned_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodBoundedSumConstant; positivity)

theorem initial_pure_pattern_cap {J : ℕ} (d : Fin J → Option Bool) (c : ℤ)
    (u m r s : ℕ) (k : Fin r → GapDifference) {q θ ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    purePatternBound u m r s (posteriorAnchorSeries c d) θ k ≤
      initialPurePatternCap J u m r s q ω k := by
  unfold purePatternBound initialPurePatternCap
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r 1 hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_signed_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r _ hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_unsigned_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)

theorem initial_signed_degree_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (r s : ℕ)
    {q θ ω : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    signedInitialDegreeBound u m r s (posteriorAnchorSeries c d) θ l ≤
      initialSignedDegreeCap J u m r s q ω := by
  unfold signedInitialDegreeBound initialSignedDegreeCap
  split_ifs
  · exact le_rfl
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact initial_signed_pattern_cap d c u m r s k hq hθ hh
      · exact le_rfl
    · exact initial_rank_tail_bound r (initial_theta_variance hq hθ).1 hl hmean hv

theorem initial_pure_degree_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (r s : ℕ)
    {q θ ω : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialPureDegreeBound u m r s (posteriorAnchorSeries c d) θ l ≤
      initialPureDegreeCap J u m r s q ω := by
  unfold initialPureDegreeBound initialPureDegreeCap
  split_ifs
  · exact le_rfl
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact initial_pure_pattern_cap d c u m r s k hq hθ hh
    · exact initial_rank_tail_bound r (initial_theta_variance hq hθ).1 hl hmean hv

theorem initial_signed_budget_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (R s : ℕ)
    {q θ ω w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialSignedBudget u m l R s (posteriorAnchorSeries c d) θ q w ≤
      initialSignedCap J u m R s q ω w := by
  unfold initialSignedBudget initialSignedCap
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (initial_signed_degree_cap d c r s hq hθ hl hmean hv hh)
    (by rw [pow_mul]; positivity)

theorem initial_pure_budget_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (R s : ℕ)
    {q θ ω w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialPureBudget u m l R s (posteriorAnchorSeries c d) θ q w ≤
      initialPureCap J u m R s q ω w := by
  unfold initialPureBudget initialPureCap
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (initial_pure_degree_cap d c r s hq hθ hl hmean hv hh)
    (by rw [pow_mul]; positivity)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Both required initial comparisons are genuine approximate complete-trace
 oracles. The metadata budgets have been eliminated: only explicit finite
 scalar bounds and literal period geometry remain to be instantiated. -/
theorem actual_initial_oracles_oai {J K m R : ℕ}
    (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m) (hR : 0 < R)
    (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (a : ℤ) (s k : ℕ) (hk : 1 ≤ k) {q w V W : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hseed : 16 ≤ q^3*(m:ℝ)) (hcount : 8 ≤ ((K*m:ℕ):ℝ)*q^2)
    (ha : (J*initialSideCount q m+J:ℕ) ≤ a)
    (ha' : a+(2^s:ℕ) ≤ (J*initialSideCount q m+K:ℕ))
    (hleft : (K:ℝ)/3 ≤ 2*((a-(J*initialSideCount q m:ℕ):ℤ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((a-(J*initialSideCount q m:ℕ):ℤ)+(2:ℝ)^s)+1))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hSV : 64*initialSignedCap J K m R s q (initialOverlapLower q) w ≤ V)
    (hPW : 64*initialPureCap J K m R s q (initialOverlapLower q) w ≤ W) :
    Nonempty (OracleTracePair q
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a (-1))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) V) ∧
    Nonempty (OracleTracePair q
      (pureAtomRun (initialPeriod m off.val) (J*(2*initialSideCount q m+1)+K))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) W) := by
  let t := initialSideCount q m
  let ω := initialOverlapLower q
  let c : ℤ := a-(J*t:ℕ)
  have hω : 0 < ω := initialOverlapLower_pos q
  have hω1 : ω < 1/8 := initialOverlapLower_lt_eighth hq.1
  have hqi : q∈Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hqc : q∈Set.Icc 0 1 := ⟨hq.1.le,hqi.2.le⟩
  let u := pureAtomRun (initialPeriod m off.val) t
  let v := pureAtomRun (initialPeriod m off.val) (t+1)
  let N := max u.length v.length
  have hu : u.length ≤ N := le_max_left _ _
  have hv : v.length ≤ N := le_max_right _ _
  have hov : ω ≤ listTraceOverlap q hqc u v := initial_pure_trace_overlap hq (by omega)
    hseed off (by linarith)
  let M : PairedMechanisms (BoundedTrace N) J := tracePairedMechanisms hqc hω
    (fun _ => u) (fun _ => v) N (fun _ => hu) (fun _ => hv) (fun _ => hov)
  have hfirst (i : Fin J) : SimulatesTrace q (M.first i) Subtype.val u :=
    listTraceLaw_simulates q hqc u N hu
  have hsecond (i : Fin J) : SimulatesTrace q (M.second i) Subtype.val v :=
    listTraceLaw_simulates q hqc v N hv
  have htail := initial_metadata_bad_mass M hq hcount (fun _ => rfl)
    (show ω^2∈Set.Icc (0:ℝ) 1 from ⟨sq_nonneg _,by nlinarith⟩)
  have hsigned (z : InitialMetadata (BoundedTrace N) J (K*m))
      (hz : initialMetadataGood q ω z) :
      64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V := by
    apply le_trans _ hSV
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact initial_signed_budget_cap _ c R s hq hz.1.1 (by have H:=z.2.isLt; omega)
      (mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0))))
      hz.1.2 hz.2
  have hpure (z : InitialMetadata (BoundedTrace N) J (K*m))
      (hz : initialMetadataGood q ω z) :
      64*initialPureBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ W := by
    apply le_trans _ hPW
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact initial_pure_budget_cap _ c R s hq hz.1.1 (by have H:=z.2.isLt; omega)
      (mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0))))
      hz.1.2 hz.2
  have hsim (τ : ℝ) := initial_sigma_simulates M t s a τ off hi hsafe hqi
    Subtype.val hfirst hsecond ha ha'
  have hp := initial_pure_sigma_simulates (K:=K) M t off hqi Subtype.val hfirst hsecond
  obtain ⟨S⟩ := initial_sigma_clipped_exists M hK hm hKm hR off hi hoff hsafe c s k hk
    hleft hright hq hM hw hscale hclip hV hsigned
  obtain ⟨P⟩ := initial_pure_sigma_clipped_exists M hK hm hKm hR off hi hoff hsafe c s k hk
    hleft hright hq hw hscale hclip hW hpure
  constructor
  · obtain ⟨O⟩ := S.tracePair (decodeInitialObservation Subtype.val) (hsim (-1)) (hsim 1)
    exact ⟨O.weaken (add_le_add le_rfl htail) le_rfl⟩
  · obtain ⟨O⟩ := P.tracePair (decodeInitialObservation Subtype.val) hp (hsim 1)
    exact ⟨O.weaken (add_le_add le_rfl htail) le_rfl⟩

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.actual_initial_oracles_oai := @OAI.TraceReconstruction.actual_initial_oracles_oai
