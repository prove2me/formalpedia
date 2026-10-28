-- Prove2me | solution 1 for OAI.TraceReconstruction.initial_sigma_clipped_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:54:40.918216+00:00
-- url     : https://prove2.me/submissions/4fe07784-1223-47ee-8605-9707436835cb

import Mathlib
import Definitions.Def_OAIQ9Tr002

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

theorem seriesL2Sq_eq_sum (f : IntSeries) :
    seriesL2Sq f = ∑ z ∈ f.coeff.support, f.coeff z ^ 2 := by
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

theorem prouhetSeries_succ_coeff (s : ℕ) (z : ℤ) :
    (prouhetSeries (s + 1)).coeff z =
    (prouhetSeries s).coeff z - (prouhetSeries s).coeff (z - (2 ^ s : ℕ)) := by
  rw [prouhetSeries, Finset.prod_range_succ, mul_sub, mul_one]
  change (prouhetSeries s - prouhetSeries s *
    (AddMonoidAlgebra.single 1 1 : IntSeries) ^ (2 ^ s)).coeff z = _
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one,
    AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

/-- The exact generating polynomial from the manuscript has unit signed
    coefficients at every index 0,...,2^s-1, and no other coefficients. -/
theorem prouhetSeries_coeff_spec (s : ℕ) :
    (∀ z : ℤ, (z < 0 ∨ (2 ^ s : ℕ) ≤ z) → (prouhetSeries s).coeff z = 0) ∧
    (∀ z : ℤ, 0 ≤ z → z < (2 ^ s : ℕ) → |(prouhetSeries s).coeff z| = 1) := by
  induction s with
  | zero =>
    have hcoeff (z : ℤ) : (prouhetSeries 0).coeff z = if 0 = z then 1 else 0 := by
      change (AddMonoidAlgebra.single 0 (1 : ℝ)).coeff z = _
      exact Finsupp.single_apply
    constructor
    · intro z hz
      rw [hcoeff, ite_eq_right]
      norm_num only [pow_zero, Nat.cast_one] at hz
      omega
    · intro z h0 h1
      have hz : z = 0 := by norm_num only [pow_zero, Nat.cast_one] at h1; omega
      subst hz
      rw [hcoeff, ite_eq_left rfl, abs_one]
  | succ s ih =>
    have hp : (0 : ℤ) < (2 ^ s : ℕ) := by positivity
    have hd : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 * (2 ^ s : ℕ) := by push_cast; ring
    constructor
    · intro z hz
      rw [prouhetSeries_succ_coeff]
      rcases hz with hz | hz
      · rw [ih.1 z (Or.inl hz), ih.1 _ (Or.inl (by omega)), sub_zero]
      · rw [hd] at hz
        rw [ih.1 z (Or.inr (by omega)), ih.1 _ (Or.inr (by omega)), sub_zero]
    · intro z h0 h1
      rw [hd] at h1
      rw [prouhetSeries_succ_coeff]
      by_cases hz : z < (2 ^ s : ℕ)
      · rw [ih.1 (z - (2 ^ s : ℕ)) (Or.inl (by omega)), sub_zero]
        exact ih.2 z h0 hz
      · rw [ih.1 z (Or.inr (by omega)), zero_sub, abs_neg]
        exact ih.2 _ (by omega) (by omega)


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

theorem seriesL1_smul (a : ℝ) (f : IntSeries) :
    seriesL1 (a • f) = |a| * seriesL1 f := by
  unfold seriesL1
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  exact tsum_mul_left

theorem mixedFairSeries_difference_L1_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioc 0 1) :
    seriesL1 (firstDifference * mixedFairSeries n p) ≤
      2 * Real.sqrt (2 / (((n : ℝ) + 1) * p)) := by
  rw [mixedFairSeries_expansion, Finset.mul_sum]
  simp_rw [mul_smul_comm]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        seriesL1 (binomialMass n p k • (firstDifference * fairSeries k)) := seriesL1_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (2 * binomialBound k) := by
      apply Finset.sum_le_sum
      intro k _
      have hw := binomialMass_nonneg n k ⟨hp.1.le, hp.2⟩
      rw [seriesL1_smul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (fairSeries_difference_L1_bound k) hw
    _ = 2 * ∑ k ∈ Finset.range (n + 1), binomialMass n p k * binomialBound k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_binomialBound_le n hp) (by norm_num)

theorem biasedSeries_difference_L1_bound_low (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioc 0 (1 / 2)) :
    seriesL1 (firstDifference * biasedSeries n p) ≤
      2 * Real.sqrt (1 / (((n : ℝ) + 1) * p)) := by
  have h := mixedFairSeries_difference_L1_bound n
    (show 2 * p ∈ Set.Ioc 0 1 from ⟨by linarith [hp.1], by linarith [hp.2]⟩)
  rw [mixedFairSeries_eq_biased] at h
  have hp2 : 2 * p / 2 = p := by ring
  have heq : 2 / (((n : ℝ) + 1) * (2 * p)) = 1 / (((n : ℝ) + 1) * p) := by
    have hp0 : p ≠ 0 := ne_of_gt hp.1
    have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rwa [hp2, heq] at h

theorem biasedSeries_difference_reflect (n : ℕ) (p : ℝ) (z : ℤ) :
    (firstDifference * biasedSeries n (1 - p)).coeff z =
      -(firstDifference * biasedSeries n p).coeff ((n : ℤ) + 1 - z) := by
  rw [firstDifference_coeff, firstDifference_coeff]
  have h1 := biasedSeries_coeff_reflect n p ((n : ℤ) - z)
  have h2 := biasedSeries_coeff_reflect n p ((n : ℤ) - (z - 1))
  have hz1 : (n : ℤ) - ((n : ℤ) - z) = z := by ring
  have hz2 : (n : ℤ) - ((n : ℤ) - (z - 1)) = z - 1 := by ring
  rw [hz1] at h1
  rw [hz2] at h2
  rw [h1, h2]
  have he1 : (n : ℤ) - (z - 1) = n + 1 - z := by ring
  have he2 : (n : ℤ) + 1 - z - 1 = n - z := by ring
  rw [he1, he2]
  ring

theorem biasedSeries_difference_L1_reflect (n : ℕ) (p : ℝ) :
    seriesL1 (firstDifference * biasedSeries n (1 - p)) =
      seriesL1 (firstDifference * biasedSeries n p) := by
  unfold seriesL1
  simp_rw [biasedSeries_difference_reflect, abs_neg]
  exact (Equiv.subLeft ((n : ℤ) + 1)).tsum_eq
    (fun z : ℤ => |(firstDifference * biasedSeries n p).coeff z|)

theorem biasedSeries_difference_L1_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL1 (firstDifference * biasedSeries n p) ≤
      2 * Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p))) := by
  by_cases hlow : p ≤ 1 / 2
  · apply (biasedSeries_difference_L1_bound_low n ⟨hp.1, hlow⟩).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p)]
  · have hq : 1 - p ∈ Set.Ioc 0 (1 / 2) := ⟨by linarith [hp.2], by linarith⟩
    rw [← biasedSeries_difference_L1_reflect n p]
    apply (biasedSeries_difference_L1_bound_low n hq).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]


theorem biasedSeries_L1 (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    seriesL1 (biasedSeries n p) = 1 := by
  rw [seriesL1_eq_sum_range _ n (biasedSeries_coeff_neg n p)]
  · simp_rw [biasedSeries_coeff_nat, abs_of_nonneg (binomialMass_nonneg _ _ hp)]
    exact sum_binomialMass n p
  · intro k hk
    exact biasedSeries_coeff_high n p k (by exact_mod_cast hk)

theorem biasedSeries_L2Sq_bound (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (biasedSeries n p) ≤ biasedBinomialBound n p := by
  have := seriesL2Sq_le_L1_mul_bound (biasedSeries n p) _ (biasedSeries_coeff_bound n hp)
  simpa only [biasedSeries_L1 n ⟨hp.1.le, hp.2.le⟩, one_mul, biasedBinomialBound] using this

theorem biasedSeries_add (m n : ℕ) (p : ℝ) :
    biasedSeries (m + n) p = biasedSeries m p * biasedSeries n p := by
  exact pow_add _ _ _

theorem biasedSeries_mul_power (n s : ℕ) (p : ℝ) :
    firstDifference ^ s * biasedSeries ((s + 1) * n) p =
      (firstDifference * biasedSeries n p) ^ s * biasedSeries n p := by
  simp only [biasedSeries, add_mul, one_mul, pow_add, pow_mul, mul_pow]
  ring

theorem biased_difference_coeff_bound (n s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(firstDifference ^ s * biasedSeries ((s + 1) * n) p).coeff z| ≤
      (2 * biasedBinomialBound n p) ^ s * biasedBinomialBound n p := by
  rw [biasedSeries_mul_power]
  apply (series_coeff_mul_bound _ _ _ (biasedSeries_coeff_bound n hp) z).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (seriesL1_pow_le _ _).trans
    (pow_le_pow_left₀ (seriesL1_nonneg _) (biasedSeries_difference_L1_bound n hp) s)

theorem biased_difference_L2Sq_bound (n s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n) p) ≤
      ((2 * biasedBinomialBound n p) ^ s) ^ 2 * biasedBinomialBound n p := by
  rw [biasedSeries_mul_power]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (seriesL1_nonneg _)
    exact (seriesL1_pow_le _ _).trans
      (pow_le_pow_left₀ (seriesL1_nonneg _) (biasedSeries_difference_L1_bound n hp) s)
  · exact biasedSeries_L2Sq_bound n hp
  · exact seriesL2Sq_nonneg _
  · exact sq_nonneg _

theorem biased_difference_coeff_bound_remainder (n s r : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (z : ℤ) :
    |(firstDifference ^ s * biasedSeries ((s + 1) * n + r) p).coeff z| ≤
      (2 * biasedBinomialBound n p) ^ s * biasedBinomialBound n p := by
  rw [biasedSeries_add, ← mul_assoc, mul_comm (firstDifference ^ s * _)]
  simpa only [biasedSeries_L1 r ⟨hp.1.le, hp.2.le⟩, one_mul] using
    series_coeff_mul_bound (biasedSeries r p) (firstDifference ^ s * biasedSeries ((s + 1) * n) p)
      _ (biased_difference_coeff_bound n s hp) z

theorem biased_difference_L2Sq_bound_remainder (n s r : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo 0 1) :
    seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n + r) p) ≤
      ((2 * biasedBinomialBound n p) ^ s) ^ 2 * biasedBinomialBound n p := by
  rw [biasedSeries_add, ← mul_assoc, mul_comm (firstDifference ^ s * _)]
  calc
    _ ≤ seriesL1 (biasedSeries r p) ^ 2 *
        seriesL2Sq (firstDifference ^ s * biasedSeries ((s + 1) * n) p) := seriesL2Sq_mul_le _ _
    _ ≤ _ := by simpa only [biasedSeries_L1 r ⟨hp.1.le, hp.2.le⟩, one_pow, one_mul] using
        biased_difference_L2Sq_bound n s hp

/-- All fixed-order nonfair binomial differences, at the exact variance scale.
This is the analytic estimate needed for the initial conditional rank kernels. -/
theorem biased_difference_smoothing (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, |(firstDifference ^ s * biasedSeries g p).coeff z| ≤
      (2 * biasedBinomialBound (g / (s + 1)) p) ^ s *
        biasedBinomialBound (g / (s + 1)) p) ∧
    (seriesL2Sq (firstDifference ^ s * biasedSeries g p) ≤
      ((2 * biasedBinomialBound (g / (s + 1)) p) ^ s) ^ 2 *
        biasedBinomialBound (g / (s + 1)) p) := by
  have hg : (s + 1) * (g / (s + 1)) + g % (s + 1) = g := Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using biased_difference_coeff_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) hp z
  · simpa only [hg] using biased_difference_L2Sq_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) hp

theorem biasedBinomialBound_quotient_le (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    biasedBinomialBound (g / (s + 1)) p ≤
      Real.sqrt (((s : ℝ) + 1) / (((g : ℝ) + 1) * p * (1 - p))) := by
  unfold biasedBinomialBound
  apply Real.sqrt_le_sqrt
  have hpq : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hnat : g + 1 ≤ (s + 1) * (g / (s + 1) + 1) := by
    have hdiv := Nat.div_add_mod g (s + 1)
    have hmod : g % (s + 1) < s + 1 := Nat.mod_lt g (by omega)
    calc
      g + 1 = (s + 1) * (g / (s + 1)) + g % (s + 1) + 1 := by omega
      _ ≤ (s + 1) * (g / (s + 1)) + (s + 1) := by omega
      _ = _ := by ring
  have hreal : (g : ℝ) + 1 ≤ ((s : ℝ) + 1) * ((g / (s + 1) : ℕ) + 1 : ℝ) := by
    exact_mod_cast hnat
  have hp0 := hp.1
  have hq0 := sub_pos.mpr hp.2
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hreal hpq.le]

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

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
theorem small_geometric_sum (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 2)) :
    (∑ j ∈ Finset.range n, x ^ j) ≤ 2 := by
  have he := geom_sum_mul x n
  have hn : 0 ≤ ∑ j ∈ Finset.range n, x ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hx.1 j)
  have hp := pow_nonneg hx.1 n
  nlinarith [mul_le_mul_of_nonneg_left hx.2 hn]

/-- Elementary tail of a binomial polynomial after cancelling orders zero and one. -/
theorem small_binomial_tail (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (∑ j ∈ Finset.range (n - 1), (n.choose (j + 2) : ℝ) * x ^ (j + 2)) ≤
      2 * ((n : ℝ) * x) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ 2 * ((n : ℝ) * x) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hc : (n.choose (j + 2) : ℝ) ≤ (n : ℝ) ^ (j + 2) := by
        exact_mod_cast Nat.choose_le_pow n (j + 2)
      calc
        _ ≤ (n : ℝ) ^ (j + 2) * x ^ (j + 2) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
        _ = _ := by rw [← mul_pow, pow_add]; ring
    _ = ((n : ℝ) * x) ^ 2 * ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ j := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := small_geometric_sum (n - 1) ⟨mul_nonneg (Nat.cast_nonneg n) hx, hsmall⟩
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ) * x))]

theorem expect_pow_expansion (P : FiniteLaw α) (Z : α → ℝ) (u : ℝ) (t : ℕ) :
    P.expect (fun a => (1 + u * Z a) ^ t) =
      ∑ j ∈ Finset.range (t + 1), (t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j) := by
  unfold expect
  simp_rw [add_comm (1 : ℝ), add_pow, one_pow, mul_one, mul_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_small_affine_pow (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ) (ht : 2 ≤ t)
    (hcenter : P.expect Z = 0)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2)
    {u : ℝ} (hu : (t : ℝ) * |u| ≤ 1 / 2) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 1 + 4 * ((t : ℝ) * u) ^ 2 := by
  rw [expect_pow_expansion]
  have ht' : t + 1 = 2 + (t - 1) := by omega
  rw [ht', Finset.sum_range_add]
  have hz : P.expect (fun _ : α => (1 : ℝ)) = 1 := by simp [expect, P.total]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
    Nat.choose_one_right, pow_one]
  rw [hz, hcenter]
  simp only [mul_zero, add_zero]
  have hb : (∑ j ∈ Finset.range (t - 1), (t.choose (2 + j) : ℝ) * u ^ (2 + j) *
      P.expect (fun a => Z a ^ (2 + j))) ≤
      2 * ∑ j ∈ Finset.range (t - 1), (t.choose (j + 2) : ℝ) * |u| ^ (j + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjt : 2 + j ≤ t := by have := Finset.mem_range.mp hj; omega
    have hm := hmom (2 + j) hjt
    calc
      _ ≤ |(t.choose (2 + j) : ℝ) * u ^ (2 + j) * P.expect (fun a => Z a ^ (2 + j))| :=
        le_abs_self _
      _ ≤ (t.choose (2 + j) : ℝ) * |u| ^ (2 + j) * 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by rw [Nat.add_comm 2 j]; ring
  have htail := small_binomial_tail t (abs_nonneg u) hu
  have he : ((t : ℝ) * |u|) ^ 2 = ((t : ℝ) * u) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  rw [he] at htail
  linarith

/-- Only the centered first moment must vanish; lower absolute moments
are obtained from the one available source moment, without boundedness. -/
theorem expect_lower_moment_le_two (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (ht : P.expect (fun a => |Z a| ^ t) ≤ 1) (j : ℕ) (hj : j ≤ t) :
    |P.expect (fun a => Z a ^ j)| ≤ 2 := by
  have hpoint (a : α) : |Z a| ^ j ≤ 1 + |Z a| ^ t := by
    by_cases hx : |Z a| ≤ 1
    · have h := pow_le_one₀ (n := j) (abs_nonneg _) hx
      nlinarith [pow_nonneg (abs_nonneg (Z a)) t]
    · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hj
      linarith
  calc
    _ ≤ ∑ a, |P.mass a * Z a ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.mass a * |Z a| ^ j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (P.nonneg a), abs_pow]
    _ ≤ ∑ a, P.mass a * (1 + |Z a| ^ t) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a)
    _ = 1 + P.expect (fun a => |Z a| ^ t) := by
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib, P.total]
      rfl
    _ ≤ 2 := by linarith

theorem expect_affine_pow_le (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 2 * (1 + |u|) ^ t := by
  rw [expect_pow_expansion, add_comm (1 : ℝ), add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := hmom j (by have := Finset.mem_range.mp hj; omega)
  calc
    _ ≤ |(t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j)| := le_abs_self _
    _ ≤ (t.choose j : ℝ) * |u| ^ j * 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by simp only [one_pow, mul_one]; ring

/-- Scalar two-smoothness at even moment order; its constant is linear
in that order after taking the square root, as required for tensorization. -/
theorem scalar_even_moment_unit (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ (2 * k)) ≤
      (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
  have hmom := expect_lower_moment_le_two P Z (2 * k) ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htR : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
  have hbase : 1 ≤ 1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (6 * ((2 * k : ℕ) : ℝ))) (sq_nonneg u)]
  by_cases hu : ((2 * k : ℕ) : ℝ) * |u| ≤ 1 / 2
  · have hs := expect_small_affine_pow P Z (2 * k) (by omega) hcenter hmom hu
    have hb : 1 + 4 * (((2 * k : ℕ) : ℝ) * u) ^ 2 ≤
        1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [sq_nonneg (((2 * k : ℕ) : ℝ) * u)]
    exact hs.trans (hb.trans (le_self_pow₀ hbase (by omega)))
  · have hu' : 1 / 2 ≤ ((2 * k : ℕ) : ℝ) * |u| := le_of_lt (lt_of_not_ge hu)
    have hsum : 1 + |u| ≤ 3 * ((2 * k : ℕ) : ℝ) * |u| := by
      have hh := mul_le_mul_of_nonneg_right htR (abs_nonneg u)
      nlinarith
    have hc : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := le_self_pow₀ (by norm_num) (by omega)
    calc
      _ ≤ 2 * (1 + |u|) ^ (2 * k) := expect_affine_pow_le P Z (2 * k) hmom u
      _ ≤ 2 * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by gcongr
      _ ≤ 2 ^ (2 * k) * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
        rw [← mul_pow, pow_mul]
        congr 1
        simp only [mul_pow, sq_abs]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) k

/-- Homogeneous version of the scalar even-moment inequality. -/
theorem scalar_even_moment (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (b v : ℝ) :
    P.expect (fun a => (b + v * Z a) ^ (2 * k)) ≤
      (b ^ 2 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * v ^ 2) ^ k := by
  have heven (a : α) : |Z a| ^ (2 * k) = Z a ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have hmoment : P.expect (fun a => Z a ^ (2 * k)) ≤ 1 := by
    simpa only [heven] using ht
  have hc : 1 ≤ (6 * (2 * k : ℕ) : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
    nlinarith
  by_cases hb : b = 0
  · subst b
    simp only [zero_add, zero_pow (by omega : 2 ≠ 0)]
    have he : P.expect (fun a => (v * Z a) ^ (2 * k)) =
        v ^ (2 * k) * P.expect (fun a => Z a ^ (2 * k)) := by
      simp only [expect, mul_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he]
    calc
      _ ≤ v ^ (2 * k) := by
        have hv : 0 ≤ v ^ (2 * k) := by rw [pow_mul]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hmoment hv]
      _ = (v ^ 2) ^ k := pow_mul v 2 k
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg v) (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg v)]) k
  · have hs := scalar_even_moment_unit P Z k hk hcenter ht (v / b)
    have hbpow : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; positivity
    have he : P.expect (fun a => (b + v * Z a) ^ (2 * k)) =
        b ^ (2 * k) * P.expect (fun a => (1 + v / b * Z a) ^ (2 * k)) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have h : b + v * Z a = b * (1 + v / b * Z a) := by field_simp [hb]
      dsimp only
      rw [h, mul_pow]
      ring
    rw [he]
    calc
      _ ≤ b ^ (2 * k) * (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * (v / b) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left hs hbpow
      _ = _ := by
        rw [pow_mul, ← mul_pow]
        congr 1
        field_simp [hb]

theorem weighted_minkowski_bound (P : FiniteLaw α) (k : ℕ) (hk : 1 ≤ k)
    (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : P.expect (fun a => f a ^ k) ≤ A ^ k)
    (hgb : P.expect (fun a => g a ^ k) ≤ B ^ k) :
    P.expect (fun a => (f a + g a) ^ k) ≤ (A + B) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  let w : α → ℝ := fun a => P.mass a ^ (1 / (k : ℝ))
  have hw (a : α) : 0 ≤ w a := Real.rpow_nonneg (P.nonneg a) _
  have hwk (a : α) : w a ^ k = P.mass a := by
    dsimp [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (P.nonneg a), one_div_mul_cancel hk0, Real.rpow_one]
  have hsingle (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) :
      (∑ a, |w a * F a| ^ (k : ℝ)) = P.expect (fun a => F a ^ k) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_of_nonneg (mul_nonneg (hw a) (hF a)), Real.rpow_natCast, mul_pow, hwk]
  have hsum : (∑ a, |w a * f a + w a * g a| ^ (k : ℝ)) =
      P.expect (fun a => (f a + g a) ^ k) := by
    simp_rw [← mul_add]
    exact hsingle _ (fun a => add_nonneg (hf a) (hg a))
  have hm := Real.Lp_add_le Finset.univ (fun a => w a * f a) (fun a => w a * g a) hkR
  rw [hsum, hsingle f hf, hsingle g hg] at hm
  have hroots (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) (C : ℝ) (hC : 0 ≤ C)
      (hFC : P.expect (fun a => F a ^ k) ≤ C ^ k) :
      (P.expect (fun a => F a ^ k)) ^ (1 / (k : ℝ)) ≤ C := by
    calc
      _ ≤ (C ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (hF a) k))) hFC (by positivity)
      _ = C := by
        rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv hC hk0]
  have hroot : (P.expect (fun a => (f a + g a) ^ k)) ^ (1 / (k : ℝ)) ≤ A + B :=
    hm.trans (add_le_add (hroots f hf A hA hfa) (hroots g hg B hB hgb))
  have hexp : 0 ≤ P.expect (fun a => (f a + g a) ^ k) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (add_nonneg (hf a) (hg a)) k))
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hexp _) hroot k
  rw [← Real.rpow_natCast, ← Real.rpow_mul hexp, one_div_mul_cancel hk0, Real.rpow_one] at hp
  exact hp
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

theorem multilinearEnergy_nonneg {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    0 ≤ multilinearEnergy A R := by
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro j _
  split <;> positivity

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

/-- The finite-product moment inequality used for every score expansion.
The order-cost is linear per degree, and no boundedness assumption is needed. -/
theorem multilinear_even_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z = 0)
    (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => multilinear A Z x ^ (2 * k)) ≤
      (multilinearEnergy A (6 * (2 * k : ℕ))) ^ k := by
  induction n with
  | zero =>
    simp only [FiniteLaw.expect, FiniteLaw.product, multilinear, multilinearEnergy,
      Fintype.prod_empty, mul_one, one_mul]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact le_of_eq (pow_mul _ 2 k)
  | succ n ih =>
    let A0 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons false σ)
    let A1 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons true σ)
    let R : ℝ := 6 * (2 * k : ℕ)
    let F0 : (Fin n → α) → ℝ := fun x => multilinear A0 Z x
    let F1 : (Fin n → α) → ℝ := fun x => multilinear A1 Z x
    have h0 := ih A0
    have h1 := ih A1
    have hA0 := multilinearEnergy_nonneg A0 R
    have hA1 := multilinearEnergy_nonneg A1 R
    rw [FiniteLaw.product_succ_expect_tail, multilinearEnergy_cons]
    calc
      _ ≤ (P.product n).expect (fun x => (F0 x ^ 2 + R ^ 2 * F1 x ^ 2) ^ k) := by
        apply FiniteLaw.expect_mono
        intro x
        simp_rw [multilinear_cons]
        have hs := FiniteLaw.scalar_even_moment P Z k hk hcenter ht (F0 x) (F1 x)
        simpa only [F0, F1, A0, A1, R, mul_comm] using hs
      _ ≤ (multilinearEnergy A0 R + R ^ 2 * multilinearEnergy A1 R) ^ k := by
        apply FiniteLaw.weighted_minkowski_bound (P.product n) k hk
          (fun x => F0 x ^ 2) (fun x => R ^ 2 * F1 x ^ 2)
          (fun x => sq_nonneg _) (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (multilinearEnergy A0 R) (R ^ 2 * multilinearEnergy A1 R) hA0
          (mul_nonneg (sq_nonneg _) hA1)
        · simpa only [← pow_mul] using h0
        · have he : (P.product n).expect (fun x => (R ^ 2 * F1 x ^ 2) ^ k) =
              (R ^ 2) ^ k * (P.product n).expect (fun x => F1 x ^ (2 * k)) := by
            unfold FiniteLaw.expect
            simp only [mul_pow, ← pow_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [he, mul_pow (R ^ 2) (multilinearEnergy A1 R)]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (sq_nonneg R) k)
      _ = _ := rfl

theorem monomial_weight {n : ℕ} (σ : Fin n → Bool) (R : ℝ) :
    (∏ j, if σ j then R ^ 2 else 1) = R ^ (2 * monomialDegree σ) := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, ← pow_mul, monomialDegree]

end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]

theorem eventMass_nonneg (P : FiniteLaw α) (A : Finset α) : 0 ≤ P.eventMass A :=
  Finset.sum_nonneg (fun a _ => P.nonneg a)

theorem eventMass_le_one (P : FiniteLaw α) (A : Finset α) : P.eventMass A ≤ 1 := by
  rw [← P.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => P.nonneg a)

theorem overlap_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    overlap P (condition P A hA) = P.eventMass A := by
  classical
  have he (a : α) : min (P.mass a) ((condition P A hA).mass a) =
      if a ∈ A then P.mass a else 0 := by
    by_cases ha : a ∈ A
    · simp only [condition, ha, ↓reduceIte]
      apply min_eq_left
      apply (le_div_iff₀ hA).mpr
      have h := mul_le_mul_of_nonneg_left (P.eventMass_le_one A) (P.nonneg a)
      simpa only [mul_one] using h
    · simp only [condition, ha, ↓reduceIte, min_eq_right (P.nonneg a)]
  unfold overlap
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, eventMass]

theorem tv_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    tv P (condition P A hA) = 1 - P.eventMass A := by
  have he := P.overlap_condition A hA
  rw [overlap_eq_one_sub_tv] at he
  linarith

theorem density_bad_mass_sq (P : FiniteLaw α) (f : α → ℝ) (A : Finset α) :
    (∑ a ∈ A, P.mass a * f a) ^ 2 ≤
      (P.eventMass A) * P.expect (fun a => f a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun a => Real.sqrt (P.mass a))
    (fun a => Real.sqrt (P.mass a) * f a)
  simp only [mul_pow, Real.sq_sqrt (P.nonneg _)] at h
  have he : (∑ a ∈ A, Real.sqrt (P.mass a) * (Real.sqrt (P.mass a) * f a)) =
      ∑ a ∈ A, P.mass a * f a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (P.nonneg a)]
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (P.eventMass_nonneg A)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
    mul_nonneg (P.nonneg a) (sq_nonneg _))

/-- Loss from the small-reference-density event by the exact available moment. -/
theorem low_density_reference_mass (P : FiniteLaw α) (f : α → ℝ) (t : ℕ)
    (A : Finset α) (hA : ∀ a ∈ A, f a < 1 / 2) :
    P.eventMass A ≤ (2 : ℝ) ^ t * P.expect (fun a => |f a - 1| ^ t) := by
  have hlocal (a : α) (ha : a ∈ A) : 1 ≤ (2 : ℝ) ^ t * |f a - 1| ^ t := by
    rw [← mul_pow]
    apply one_le_pow₀
    have hh := neg_le_abs (f a - 1)
    linarith [hA a ha]
  calc
    _ ≤ ∑ a ∈ A, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      apply Finset.sum_le_sum
      intro a ha
      nlinarith [mul_le_mul_of_nonneg_left (hlocal a ha) (P.nonneg a)]
    _ ≤ ∑ a, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => by positivity [P.nonneg a])
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Exact common-event likelihood ratio: no lower bound is imposed off the event. -/
theorem conditioned_density_identity (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (hfm : R.expect f = 1) (hgm : R.expect g = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 0 < f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A)
    (hQ : 0 < (R.withDensity g hg hgm).eventMass A) (a : α) :
    (condition (R.withDensity g hg hgm) A hQ).mass a =
      (condition (R.withDensity f hf hfm) A hP).mass a *
      ((R.withDensity f hf hfm).eventMass A /
        (R.withDensity g hg hgm).eventMass A * (g a / f a)) := by
  classical
  by_cases ha : a ∈ A
  · simp only [condition, ha, ↓reduceIte]
    change R.mass a * g a / (R.withDensity g hg hgm).eventMass A =
      R.mass a * f a / (R.withDensity f hf hfm).eventMass A *
        ((R.withDensity f hf hfm).eventMass A /
          (R.withDensity g hg hgm).eventMass A * (g a / f a))
    field_simp [ne_of_gt hP, ne_of_gt hQ, ne_of_gt (hAf a ha)]
  · simp only [condition, ha, ↓reduceIte, zero_mul]

/-- The raw likelihood score on a common clipping event, at every integer moment. -/
theorem clipped_raw_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hfm : R.expect f = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 1 / 2 ≤ f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect
        (fun a => |g a / f a - 1| ^ (k + 1)) ≤
      (2 : ℝ) ^ k / (R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |g a - f a| ^ (k + 1)) := by
  classical
  have hpoint (a : α) (ha : a ∈ A) :
      f a * |g a / f a - 1| ^ (k + 1) ≤
        (2 : ℝ) ^ k * |g a - f a| ^ (k + 1) := by
    have hp : 0 < f a := lt_of_lt_of_le (by norm_num) (hAf a ha)
    rw [div_sub_one (ne_of_gt hp), abs_div, abs_of_pos hp]
    have hi : 0 ≤ 1 / f a := by positivity
    have hi2 : 1 / f a ≤ 2 := (div_le_iff₀ hp).mpr (by linarith [hAf a ha])
    calc
      _ = |g a - f a| ^ (k + 1) * (1 / f a) ^ k := by
        rw [div_pow, div_pow, one_pow, pow_succ (f a)]
        field_simp [ne_of_gt hp]
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hi hi2 k) (show 0 ≤ |g a - f a| ^ (k + 1) by positivity)
  unfold expect
  calc
    _ = ∑ a ∈ A, (R.mass a * (f a * |g a / f a - 1| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      simp only [condition, withDensity]
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ A, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum
      intro a ha
      apply div_le_div_of_nonneg_right _ hP.le
      nlinarith [mul_le_mul_of_nonneg_left (hpoint a ha) (R.nonneg a)]
    _ ≤ ∑ a, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro a _ _
      positivity [R.nonneg a]
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; ring

/-- Normalizing the second conditioned law costs only its scalar normalization error. -/
theorem score_rescaling_moment (P : FiniteLaw α) (u : α → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    P.expect (fun a => |c * u a - 1| ^ (k + 1)) ≤
      2 ^ k * (c ^ (k + 1) * P.expect (fun a => |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1)) := by
  have hb (a : α) : |c * u a - 1| ^ (k + 1) ≤
      2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) + |c - 1| ^ (k + 1)) := by
    have he : c * u a - 1 = c * (u a - 1) + (c - 1) := by ring
    rw [he]
    calc
      _ ≤ (|c * (u a - 1)| + |c - 1|) ^ (k + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
      _ ≤ _ := by
        have h := add_pow_le (abs_nonneg (c * (u a - 1))) (abs_nonneg (c - 1)) (k + 1)
        simpa only [Nat.add_sub_cancel, abs_mul, abs_of_nonneg hc, mul_pow] using h
  unfold expect
  calc
    _ ≤ ∑ a, P.mass a * (2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) +
        |c - 1| ^ (k + 1))) := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (hb a) (P.nonneg a))
    _ = 2 ^ k * (c ^ (k + 1) * (∑ a, P.mass a * |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1) * ∑ a, P.mass a) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ = _ := by rw [P.total, mul_one]
end TraceReconstruction.FiniteLaw

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

theorem primitive_score_centered {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    ∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z = 0 := by
  have hi := primitiveMarkMass_sum hq true
  simp_rw [primitive_score_identity hq, mul_add, mul_one, Finset.sum_add_distrib,
    primitiveMarkMass_sum hq false] at hi
  linarith

theorem primitive_score_bound {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (z : PrimitiveMark) :
    |primitiveScore q z| ≤ 2 / q := by
  have hi : 1 ≤ 1 / q := (le_div_iff₀ hq.1).mpr (by linarith [hq.2])
  simp only [one_div] at hi
  have he : 2 / q = 2 * (1 / q) := by ring
  fin_cases z <;> simp [primitiveScore, abs_le, he] <;> (try constructor) <;> linarith

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parity

Parity-tree roles, forced leaves, coefficient shapes, and exact unsigned/signed motif expansions.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
attribute [local instance] Classical.propDecidable

theorem sign_pow_parity {τ : ℝ} (ht : IsTypeSign τ) (n : ℕ) :
    τ^n = if Odd n then τ else 1 := by
  rcases ht with rfl | rfl
  · simp
  · split_ifs with hn
    · exact hn.neg_one_pow
    · exact (Nat.not_odd_iff_even.mp hn).neg_one_pow

end TraceReconstruction


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

namespace TraceReconstruction

theorem biasedSeries_step_sub_one (p : ℝ) :
    biasedSeries 1 p - 1 = (-p) • firstDifference := by
  unfold biasedSeries firstDifference
  rw [pow_one,smul_sub,AddMonoidAlgebra.smul_single,AddMonoidAlgebra.smul_single]
  simp only [smul_eq_mul,mul_one]
  have h1 : (1 : IntSeries) = AddMonoidAlgebra.single 0 1 := rfl
  rw [h1]
  simp only [AddMonoidAlgebra.single_sub]
  ext z
  simp only [AddMonoidAlgebra.coeff_sub,AddMonoidAlgebra.coeff_add,
    Finsupp.sub_apply,Finsupp.add_apply,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> ring

theorem binomialLengthDifference_eq (g s : ℕ) (p : ℝ) :
    binomialLengthDifference g s p =
      (-p)^s • (firstDifference^s * biasedSeries g p) := by
  unfold binomialLengthDifference
  rw [biasedSeries_step_sub_one,smul_pow,smul_mul_assoc]

theorem seriesL2Sq_smul (c : ℝ) (f : IntSeries) :
    seriesL2Sq (c • f) = c^2 * seriesL2Sq f := by
  unfold seriesL2Sq
  simp only [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,mul_pow]
  exact tsum_mul_left

/-- Pointwise and square-sum bounds for every forward length difference.
The quotient form keeps every order and every channel factor explicit. -/
theorem binomialLengthDifference_bounds (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, |(binomialLengthDifference g s p).coeff z| ≤
      (2*biasedBinomialBound (g/(s+1)) p)^s * biasedBinomialBound (g/(s+1)) p) ∧
    (seriesL2Sq (binomialLengthDifference g s p) ≤
      ((2*biasedBinomialBound (g/(s+1)) p)^s)^2 * biasedBinomialBound (g/(s+1)) p) := by
  have hpow : |(-p)^s| ≤ 1 := by
    rw [abs_pow,abs_neg,abs_of_pos hp.1]
    exact pow_le_one₀ hp.1.le hp.2.le
  have hs := biased_difference_smoothing g s hp
  rw [binomialLengthDifference_eq]
  constructor
  · intro z
    simp only [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans (by simpa using hs.1 z)
  · rw [seriesL2Sq_smul]
    have h : ((-p)^s) ^ 2 ≤ 1 := by nlinarith [sq_abs ((-p)^s),abs_nonneg ((-p)^s)]
    exact (mul_le_mul_of_nonneg_right h (seriesL2Sq_nonneg _)).trans (by simpa using hs.2)

theorem lengthDifferenceConstant_pos (s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    0 < lengthDifferenceConstant s p := by
  unfold lengthDifferenceConstant
  positivity [hp.1,sub_pos.mpr hp.2]

theorem biasedBinomialBound_length_le (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    2*biasedBinomialBound (g/(s+1)) p ≤
      lengthDifferenceConstant s p / Real.sqrt ((g:ℝ)+1) := by
  calc
    _ ≤ 2*Real.sqrt (((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p))) :=
      mul_le_mul_of_nonneg_left (biasedBinomialBound_quotient_le g s hp) (by norm_num)
    _ = _ := by
      unfold lengthDifferenceConstant
      rw [show ((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p)) =
        (((s:ℝ)+1)/(p*(1-p)))/((g:ℝ)+1) by field_simp]
      rw [Real.sqrt_div (by positivity [hp.1,sub_pos.mpr hp.2])]
      ring

/-- Squared supremum and squared L2 smoothing estimates in a form suitable
for exact constrained rank profiles. -/
theorem binomialLengthDifference_numeric (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, (binomialLengthDifference g s p).coeff z ^ 2 ≤
      (lengthDifferenceConstant s p)^(2*s+2) / ((g:ℝ)+1)^(s+1)) ∧
    (seriesL2Sq (binomialLengthDifference g s p) ≤
      (lengthDifferenceConstant s p)^(2*s+1) /
        (((g:ℝ)+1)^s * Real.sqrt ((g:ℝ)+1))) := by
  have hb := binomialLengthDifference_bounds g s hp
  have hc := biasedBinomialBound_length_le g s hp
  have hB : 0 ≤ biasedBinomialBound (g/(s+1)) p := Real.sqrt_nonneg _
  have hC : 0 < lengthDifferenceConstant s p := lengthDifferenceConstant_pos s hp
  have hg : 0 < Real.sqrt ((g:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hB' : biasedBinomialBound (g/(s+1)) p ≤
      lengthDifferenceConstant s p / Real.sqrt ((g:ℝ)+1) := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*biasedBinomialBound (g/(s+1)) p) hc s
  constructor
  · intro z
    have h := (hb.1 z).trans (mul_le_mul hs hB' hB (by positivity))
    rw [← pow_succ] at h
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hsq
    refine hsq.trans_eq ?_
    rw [← pow_mul,div_pow]
    have he : (s+1)*2=2*s+2 := by omega
    rw [he]
    congr 1
    rw [show 2*s+2=2*(s+1) by omega,pow_mul,Real.sq_sqrt (by positivity)]
  · have hsq := pow_le_pow_left₀ (by positivity :
        0 ≤ (2*biasedBinomialBound (g/(s+1)) p)^s) hs 2
    refine hb.2.trans ((mul_le_mul hsq hB' hB (by positivity)).trans_eq ?_)
    rw [← pow_mul,← pow_succ,div_pow]
    congr 1
    · congr 1; omega
    · rw [pow_succ,show s*2=2*s by omega,pow_mul,Real.sq_sqrt (by positivity)]

end TraceReconstruction

namespace TraceReconstruction

theorem series_finite_sum_sq_le {α : Type*} [Fintype α]
    (f : IntSeries) (z : α → ℤ) (hz : Function.Injective z) :
    (∑ a, f.coeff (z a)^2) ≤ seriesL2Sq f := by
  simpa only [tsum_fintype,seriesL2Sq] using
    Summable.tsum_le_tsum_of_inj z hz (fun _ _ => sq_nonneg _)
      (fun _ => le_rfl) (hasSum_fintype _).summable (series_summable f (fun x => x^2) (by simp))

/-- Largest-gap elimination also holds for signed finite-difference series.
The fixed sum of the observed gaps supplies the missing square-root factor;
translations are unrestricted and the estimate contains no omitted ranks. -/
theorem signedRankProduct_square_sum_le {l r : ℕ}
    (f : Fin (r+1) → IntSeries) (shift : Fin (r+1) → ℤ)
    (e : Fin (r+1)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℤ, (f e).coeff z ^ 2 ≤ M) :
    (∑ v : IncreasingTuple l r, signedRankProduct f shift v ^ 2) ≤
      M * ∏ i : Fin r, seriesL2Sq (f (Equiv.swap 0 e i.succ)) := by
  classical
  let σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 e
  let F : Fin (r+1) → Fin (l-r+1) → ℝ :=
    fun i k => (f (σ i)).coeff ((k.val:ℤ)-shift (σ i)) ^ 2
  have hF : ∀ i k, 0 ≤ F i k := fun _ _ => sq_nonneg _
  have hpoint (v : IncreasingTuple l r) :
      signedRankProduct f shift v ^ 2 = ∏ i, F i (rankGapProfile σ v i) := by
    unfold signedRankProduct
    rw [← Finset.prod_pow]
    dsimp [F,rankGapProfile]
    exact (Equiv.prod_comp σ _).symm
  simp_rw [hpoint]
  calc
    _ ≤ ∑ z : Fin (r+1) → Fin (l-r+1),
        if ∑ i, (z i).val = l-r then ∏ i, F i (z i) else 0 := by
      exact sum_injective_profile_le (rankGapProfile σ) (rankGapProfile_injective σ)
        (fun z => ∑ i, (z i).val = l-r) (rankGapProfile_sum σ)
        (fun z => ∏ i, F i (z i)) (fun _ => Finset.prod_nonneg (fun _ _ => hF _ _))
    _ ≤ M * ∏ i : Fin r, ∑ k : Fin (l-r+1), F i.succ k :=
      constrained_sum_product_le r (l-r) F hF M hM (by
        intro k
        simpa only [F,σ,Equiv.swap_apply_left] using hbound ((k.val:ℤ)-shift e))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => hF _ _))
      intro i _
      dsimp only [F]
      apply series_finite_sum_sq_le
      intro a b h
      exact Fin.ext (Int.ofNat_inj.mp (sub_left_injective h))

/-- Finite mixtures of signed rank products can be estimated termwise.
This is the exact Cauchy--Schwarz form used when expanding positional
finite-difference operators into gap derivatives. -/
theorem rank_mixture_square_sum_le {α V : Type*} [Fintype α] [Fintype V]
    (c : α → ℝ) (F : α → V → ℝ) (B : α → ℝ)
    (hB : ∀ a, (∑ v, F a v ^ 2) ≤ B a) :
    (∑ v, (∑ a, c a * F a v)^2) ≤ (∑ a, |c a|) * ∑ a, |c a| * B a := by
  have hp (v : V) : (∑ a, c a*F a v)^2 ≤
      (∑ a, |c a|) * ∑ a, |c a| * F a v^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun _ _ => abs_nonneg _) (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro a _
    rw [mul_pow,← mul_assoc,← sq, sq_abs]
  calc
    _ ≤ ∑ v, (∑ a, |c a|) * ∑ a, |c a| * F a v^2 :=
      Finset.sum_le_sum (fun v _ => hp v)
    _ = (∑ a, |c a|) * ∑ a, |c a| * ∑ v, F a v^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hB a) (abs_nonneg _)

end TraceReconstruction

namespace TraceReconstruction

theorem tensorSeries_coeff {ι : Type*} [Fintype ι] (f : ι → IntSeries) (z : ι → ℤ) :
    (tensorSeries f).coeff z = ∏ i, (f i).coeff (z i) := rfl

theorem tensorSeries_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → IntSeries) :
    (tensorSeries f).coeff.support = Fintype.piFinset (fun i => (f i).coeff.support) := by
  classical
  ext z
  simp [tensorSeries_coeff,Finset.prod_ne_zero_iff]

/-- Literal tensor multiplication is coordinatewise convolution. -/
theorem tensorSeries_mul {ι : Type*} [Fintype ι] (f g : ι → IntSeries) :
    tensorSeries (fun i => f i*g i) = tensorSeries f * tensorSeries g := by
  classical
  ext z
  rw [tensorSeries_coeff,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum,tensorSeries_support]
  simp_rw [tensorSeries_coeff,← Finset.prod_mul_distrib]
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [← Finset.prod_univ_sum (fun i => (f i).coeff.support)
    (fun i j => (f i).coeff j * (g i).coeff (-j + z i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]

theorem tensorSeries_one {ι : Type*} [Fintype ι] :
    tensorSeries (fun _ : ι => (1 : IntSeries)) = 1 := by
  classical
  ext z
  rw [tensorSeries_coeff]
  change (∏ i, Finsupp.single 0 (1:ℝ) (z i)) = Finsupp.single 0 (1:ℝ) z
  simp only [Finsupp.single_apply]
  by_cases hz : z = 0
  · subst z; simp
  · have he : ∃ i, z i ≠ 0 := by simpa [funext_iff] using hz
    obtain ⟨i,hi⟩ := he
    rw [ite_eq_right (Ne.symm hz)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])


theorem coordinateExponent_injective {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Injective (coordinateExponent i) := by
  intro a b h
  simpa only [coordinateExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.single_eq_same]
    using congrFun h i

theorem tensorSeries_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : IntSeries) :
    tensorSeries (fun j => if j=i then f else 1) = coordinateSeriesHom i f := by
  classical
  ext z
  rw [tensorSeries_coeff]
  change (∏ j, (if j=i then f else (1:IntSeries)).coeff (z j)) =
    (Finsupp.mapDomain (coordinateExponent i) f.coeff) z
  by_cases hz : ∀ j, j ≠ i → z j = 0
  · have he : coordinateExponent i (z i) = z := by
      funext j
      by_cases hj : j=i
      · subst j; simp [coordinateExponent]
      · simp [coordinateExponent,Pi.single_eq_of_ne hj,hz j hj]
    rw [← he,Finsupp.mapDomain_apply (coordinateExponent_injective i)]
    rw [Finset.prod_eq_single i]
    · simp [coordinateExponent]
    · intro j _ hj
      simp [hj,coordinateExponent]
    · simp
  · push Not at hz
    obtain ⟨j,hji,hj⟩ := hz
    have hn : z ∉ Set.range (coordinateExponent i) := by
      rintro ⟨a,ha⟩
      have h := congrFun ha j
      simp [coordinateExponent,Pi.single_eq_of_ne hji] at h
      exact hj h.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [ite_eq_right hji]
    change Finsupp.single 0 (1:ℝ) (z j) = 0
    simp [Ne.symm hj]

theorem tensorSeries_prod {ι α : Type*} [Fintype ι]
    (s : Finset α) (f : α → ι → IntSeries) :
    tensorSeries (fun i => ∏ a ∈ s, f a i) = ∏ a ∈ s, tensorSeries (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorSeries_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [tensorSeries_mul,ih]

end TraceReconstruction

namespace TraceReconstruction

/-- Increasing an order increases only its explicit smoothing constant. -/
theorem lengthDifferenceConstant_mono {s t : ℕ} (hst : s ≤ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    lengthDifferenceConstant s p ≤ lengthDifferenceConstant t p := by
  unfold lengthDifferenceConstant
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hst)
    (mul_pos hp.1 (sub_pos.mpr hp.2)).le

end TraceReconstruction

namespace TraceReconstruction

theorem tensorSeries_two_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (f g : IntSeries) :
    tensorSeries (fun i => f^(if i=a then 1 else 0) * g^(if i=b then 1 else 0)) =
      coordinateSeriesHom a f * coordinateSeriesHom b g := by
  rw [tensorSeries_mul]
  have h (c : ι) (u : IntSeries) :
      (fun i => u^(if i=c then 1 else 0)) = (fun i => if i=c then u else 1) := by
    funext i
    split <;> simp
  rw [h,h,tensorSeries_coordinate,tensorSeries_coordinate]

theorem gapLocalTerm_factor {r : ℕ} (h : Fin r) (k : GapDifference)
    (a : Bool × Bool) (p : ℝ) :
    tensorSeries (fun i => (biasedSeries 1 p-1)^gapTermOrder h k a i *
      (biasedSeries 1 p)^gapTermExtra h k a i) =
      match k with
      | .unchanged => coordinateSeriesHom h.castSucc (biasedSeries 1 p) *
          coordinateSeriesHom h.succ (biasedSeries 1 p)
      | .first => (coordinateSeriesHom (adjacentGap h a.1) (biasedSeries 1 p)-1) *
          coordinateSeriesHom (adjacentGap h a.2) (biasedSeries 1 p)
      | .second => (coordinateSeriesHom (adjacentGap h a.1) (biasedSeries 1 p)-1) *
          (coordinateSeriesHom (adjacentGap h a.2) (biasedSeries 1 p)-1) := by
  cases k <;> simp only [gapTermOrder,gapTermExtra,pow_zero,pow_add,one_mul,mul_one]
  all_goals rw [tensorSeries_two_coordinates]
  all_goals simp only [map_sub,map_one]

/-- Exact four-term assignment of positional differences to the adjacent
binomial gap lengths, including all signs and all bounded shifts. -/
theorem gapOperator_expansion {r : ℕ} (h : Fin r) (k : GapDifference) (p : ℝ) :
    gapOperator h k p = ∑ a : Bool × Bool, gapTermWeight k a •
      tensorSeries (fun i => (biasedSeries 1 p-1)^gapTermOrder h k a i *
        (biasedSeries 1 p)^gapTermExtra h k a i) := by
  simp_rw [gapLocalTerm_factor]
  cases k <;> simp only [gapOperator,gapTermWeight,Fintype.sum_prod_type,
    Fintype.sum_bool,adjacentGap,Bool.false_eq_true,ite_false,ite_true]
  · module
  all_goals simp only [Algebra.smul_def]
  all_goals norm_num
  all_goals ring

theorem gapTermWeight_l1 (k : GapDifference) :
    (∑ a : Bool × Bool, |gapTermWeight k a|) ≤ 2 := by
  cases k <;> norm_num [gapTermWeight,Fintype.sum_prod_type,Fintype.sum_bool]

theorem gapTermOrder_total {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool) :
    (∑ i, gapTermOrder h k a i) = k.order := by
  cases k <;> simp [gapTermOrder,GapDifference.order,Finset.sum_add_distrib]

/-- Exact global expansion inside the unconstrained vector of gap counts. -/
theorem gapOperators_expansion {r : ℕ} (g : Fin (r+1) → ℕ)
    (k : Fin r → GapDifference) (p : ℝ) :
    tensorSeries (fun i => biasedSeries (g i) p) * (∏ h, gapOperator h (k h) p) =
      ∑ a : Fin r → Bool × Bool, (∏ h, gapTermWeight (k h) (a h)) •
        tensorSeries (fun i => binomialLengthDifference
          (g i + ∑ h, gapTermExtra h (k h) (a h) i)
          (∑ h, gapTermOrder h (k h) (a h) i) p) := by
  classical
  simp_rw [gapOperator_expansion]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_smul, mul_smul_comm, ← tensorSeries_prod, ← tensorSeries_mul]
  congr 2
  funext i
  simp only [binomialLengthDifference,biasedSeries,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

theorem gapOperators_weight_l1 {r : ℕ} (k : Fin r → GapDifference) :
    (∑ a : Fin r → Bool × Bool, |∏ h, gapTermWeight (k h) (a h)|) ≤ (2:ℝ)^r := by
  simp_rw [Finset.abs_prod]
  rw [← Fintype.prod_sum (fun h a => |gapTermWeight (k h) a|)]
  calc
    _ ≤ ∏ _h : Fin r, (2:ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      intro h _
      exact gapTermWeight_l1 (k h)
    _ = _ := by simp

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem prod_eliminate_fin {α : Type*} [CommMonoid α] {r : ℕ}
    (f : Fin (r+1) → α) (e : Fin (r+1)) :
    f e * (∏ i : Fin r, f (Equiv.swap 0 e i.succ)) = ∏ i, f i := by
  calc
    _ = ∏ i : Fin (r+1), f (Equiv.swap 0 e i) := by
      rw [Fin.prod_univ_succ,Equiv.swap_apply_left]
    _ = _ := Equiv.prod_comp (Equiv.swap 0 e) f

/-- Uniform smoothing with the individual gap scale retained, and a common
lower gap scale reserved for every derivative order. -/
theorem lengthDifference_uniform (g b s : ℕ) {p C G : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hC : lengthDifferenceConstant s p ≤ C)
    (hG : 0 < G) (hb : b ≤ g) (hGg : G ≤ (g:ℝ)+1) :
    (∀ z : ℤ, (binomialLengthDifference g s p).coeff z^2 ≤
      (C/Real.sqrt ((b:ℝ)+1)) * (C^(2*s+1)/(G^s*Real.sqrt ((b:ℝ)+1)))) ∧
    seriesL2Sq (binomialLengthDifference g s p) ≤
      C^(2*s+1)/(G^s*Real.sqrt ((b:ℝ)+1)) := by
  have hC0 : 0 < C := (lengthDifferenceConstant_pos s hp).trans_le hC
  have hb0 : 0 < (b:ℝ)+1 := by positivity
  have hg0 : 0 < (g:ℝ)+1 := by positivity
  have hb' : (b:ℝ)+1 ≤ (g:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hb 1
  have hpow : G^s ≤ ((g:ℝ)+1)^s := pow_le_pow_left₀ hG.le hGg s
  have hx := binomialLengthDifference_numeric g s hp
  constructor
  · intro z
    refine (hx.1 z).trans ?_
    have hc := pow_le_pow_left₀ (lengthDifferenceConstant_pos s hp).le hC (2*s+2)
    have hd : G^s*((b:ℝ)+1) ≤ ((g:ℝ)+1)^(s+1) := by
      rw [pow_succ]
      exact mul_le_mul hpow hb' hb0.le (by positivity)
    calc
      _ ≤ C^(2*s+2)/(G^s*((b:ℝ)+1)) := by
        apply div_le_div₀ (by positivity) hc (by positivity) hd
      _ = _ := by
        have hsq := Real.sq_sqrt hb0.le
        have hs : Real.sqrt ((b:ℝ)+1) ≠ 0 := (Real.sqrt_pos.mpr hb0).ne'
        rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ]
        field_simp
        nlinarith only [hsq]
  · refine hx.2.trans ?_
    apply div_le_div₀ (by positivity)
      (pow_le_pow_left₀ (lengthDifferenceConstant_pos s hp).le hC (2*s+1))
      (by positivity)
    exact mul_le_mul hpow (Real.sqrt_le_sqrt hb') (Real.sqrt_nonneg _) (by positivity)

/-- A single translated signed rank product, with every smoothing scale
and the largest-gap constraint exposed. -/
theorem rank_derivatives_uniform {l r : ℕ}
    (g b s : Fin (r+1) → ℕ) (shift : Fin (r+1) → ℤ)
    {p C G : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hC : ∀ i, lengthDifferenceConstant (s i) p ≤ C) (hG : 0 < G)
    (hb : ∀ i, b i ≤ g i) (hGg : ∀ i, G ≤ (g i:ℝ)+1) (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r,
      signedRankProduct (fun i => binomialLengthDifference (g i) (s i) p) shift v ^ 2) ≤
      C^(2*(∑ i, s i)+r+2) /
        (G^(∑ i, s i) * Real.sqrt ((b e:ℝ)+1) * ∏ i, Real.sqrt ((b i:ℝ)+1)) := by
  let F (i : Fin (r+1)) : ℝ := C^(2*s i+1)/(G^(s i)*Real.sqrt ((b i:ℝ)+1))
  have hC0 : 0 < C := (lengthDifferenceConstant_pos (s e) hp).trans_le (hC e)
  have hF : ∀ i, 0 ≤ F i := fun i => by dsimp [F]; positivity
  have hbound (i : Fin (r+1)) := lengthDifference_uniform (g i) (b i) (s i) hp (hC i) hG (hb i) (hGg i)
  calc
    _ ≤ (C/Real.sqrt ((b e:ℝ)+1)*F e) *
        ∏ i : Fin r, seriesL2Sq (binomialLengthDifference (g (Equiv.swap 0 e i.succ))
          (s (Equiv.swap 0 e i.succ)) p) := by
      apply signedRankProduct_square_sum_le _ shift e _ (by positivity [hF e])
      exact (hbound e).1
    _ ≤ (C/Real.sqrt ((b e:ℝ)+1)*F e) * ∏ i : Fin r, F (Equiv.swap 0 e i.succ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [hF e])
      apply Finset.prod_le_prod (fun _ _ => seriesL2Sq_nonneg _)
      intro i _
      exact (hbound _).2
    _ = (C/Real.sqrt ((b e:ℝ)+1))*∏ i, F i := by
      rw [mul_assoc,prod_eliminate_fin]
    _ = _ := by
      simp only [F,Finset.prod_div_distrib,Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib,← Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
      rw [show 2*(∑ i, s i)+r+2=(2*(∑ i, s i)+(r+1))+1 by omega,pow_succ]
      ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem shiftedTag_strictMono {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) : StrictMono (shiftedTag p hp a) := by
  intro i j hij
  change (p i).val+(a i).val-1 < (p j).val+(a j).val-1
  have h := hp.2 i j hij
  have hi := hp.1 i
  have hj := hp.1 j
  have hai := (a i).isLt
  omega

theorem sum_castSucc_indicator {r : ℕ} (f : Fin r → ℕ) (i : Fin (r+1)) :
    (∑ h, if i=h.castSucc then f h else 0) = Fin.snoc (α := fun _ => ℕ) f 0 i := by
  induction i using Fin.lastCases with
  | last => simp [eq_comm]
  | cast h => simp

theorem sum_succ_indicator {r : ℕ} (f : Fin r → ℕ) (i : Fin (r+1)) :
    (∑ h, if i=h.succ then f h else 0) = Fin.cons (α := fun _ => ℕ) 0 f i := by
  induction i using Fin.cases with
  | zero => simp [eq_comm]
  | succ h => simp

theorem shiftGapExtra_eq_sum {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) :
    shiftGapExtra a i = ∑ h, localShiftExtra h (a h) i := by
  simp only [localShiftExtra,Finset.sum_add_distrib,sum_castSucc_indicator,
    sum_succ_indicator,shiftGapExtra]
  omega

theorem gapIncidence_le {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (i : Fin (r+1)) : gapIncidence r i ≤ tupleGap p i := by
  cases r with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    simp [gapIncidence,Fin.snoc_zero]
  | succ r =>
    induction i using Fin.cases with
    | zero => simpa only [gapIncidence,Fin.cons_zero,zero_add,Fin.snoc_apply_zero,
        tupleGap_zero] using (hp.1 0).1
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [gapIncidence,Fin.succ_last,Fin.cons_last,Fin.snoc_last,add_zero,
          tupleGap_last]
        have h := (hp.1 (Fin.last r)).2
        omega
      | cast i =>
        simp only [gapIncidence,Fin.cons_succ]
        rw [Fin.succ_castSucc,Fin.snoc_castSucc]
        rw [← Fin.succ_castSucc,tupleGap_middle]
        have h := hp.2 i.castSucc i.succ (by simp)
        omega

/-- The exact geometric identity relating translated tag positions to
nonnegative binomial-gap lengths. -/
theorem tupleGap_shifted {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) (i : Fin (r+1)) :
    tupleGap (shiftedTag p hp a) i =
      tupleGap p i - gapIncidence r i + shiftGapExtra a i := by
  cases r with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    simp [tupleGap,tupleLower,tupleUpper,gapIncidence,shiftGapExtra,Fin.snoc_zero]
  | succ r =>
    induction i using Fin.cases with
    | zero =>
      simp only [tupleGap_zero,gapIncidence,shiftGapExtra,Fin.cons_zero,zero_add,
        Fin.snoc_apply_zero,shiftedTag]
      have h := (hp.1 0).1
      omega
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [gapIncidence,shiftGapExtra,Fin.succ_last,Fin.cons_last,
          Fin.snoc_last,add_zero,tupleGap_last,shiftedTag]
        have h := hp.1 (Fin.last r)
        have ha := (a (Fin.last r)).isLt
        omega
      | cast i =>
        simp only [gapIncidence,shiftGapExtra,Fin.cons_succ]
        rw [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_castSucc]
        rw [← Fin.succ_castSucc,tupleGap_middle,tupleGap_middle]
        change (p i.succ).val+(a i.succ).val-1-((p i.castSucc).val+(a i.castSucc).val-1+1) = _
        have hi := hp.1 i.castSucc
        have hj := hp.1 i.succ
        have hij := hp.2 i.castSucc i.succ (by simp)
        have hai := (a i.castSucc).isLt
        have haj := (a i.succ).isLt
        omega


theorem localShift_factor {r : ℕ} (h : Fin r) (a : Fin 3) (p : ℝ) :
    tensorSeries (fun i => (biasedSeries 1 p)^localShiftExtra h a i) =
      coordinateSeriesHom h.castSucc (biasedSeries 1 p)^a.val *
        coordinateSeriesHom h.succ (biasedSeries 1 p)^(2-a.val) := by
  have hpow (u : IntSeries) (t : ℕ) (c i : Fin (r+1)) :
      u^(if i=c then t else 0) = (u^t)^(if i=c then 1 else 0) := by
    split <;> simp
  have he : (fun i => (biasedSeries 1 p)^localShiftExtra h a i) =
      (fun i => ((biasedSeries 1 p)^a.val)^(if i=h.castSucc then 1 else 0) *
        ((biasedSeries 1 p)^(2-a.val))^(if i=h.succ then 1 else 0)) := by
    funext i
    rw [localShiftExtra,pow_add,hpow _ _ h.castSucc i,hpow _ _ h.succ i]
  rw [he,tensorSeries_two_coordinates,map_pow,map_pow]

theorem gapOperator_positional_expansion {r : ℕ} (h : Fin r) (k : GapDifference)
    (p : ℝ) :
    gapOperator h k p = ∑ a : Fin 3, positionalWeight k a •
      tensorSeries (fun i => (biasedSeries 1 p)^localShiftExtra h a i) := by
  simp_rw [localShift_factor]
  rw [Fin.sum_univ_three]
  cases k <;> norm_num [positionalWeight,gapOperator,Fin.ext_iff]
  all_goals try simp only [two_mul,add_mul]
  all_goals module

/-- Literal centered differences of all rank kernels are coefficients of
the adjacent-gap operator product, with no formal negative trial lengths. -/
theorem shifted_gap_series_expansion {n r : ℕ} (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (k : Fin r → GapDifference) (θ : ℝ) :
    (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) •
      tensorSeries (fun i => biasedSeries (tupleGap (shiftedTag p hp a) i) θ)) =
    tensorSeries (fun i => biasedSeries (tupleGap p i-gapIncidence r i) θ) *
      ∏ h, gapOperator h (k h) θ := by
  classical
  simp_rw [gapOperator_positional_expansion]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_smul,mul_smul_comm,← tensorSeries_prod,← tensorSeries_mul]
  congr 2
  funext i
  rw [tupleGap_shifted,shiftGapExtra_eq_sum]
  simp only [biasedSeries,pow_one,Finset.prod_pow_eq_pow_sum,pow_add]


theorem positionalRankDifference_expansion {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (v : IncreasingTuple l r) :
    positionalRankDifference hl p hp k v = θ^r / binomialMass n θ l *
      ∑ a : Fin r → Bool × Bool, (∏ h, gapTermWeight (k h) (a h)) *
        signedRankProduct (fun i => binomialLengthDifference
          (tupleGap p i-gapIncidence r i + ∑ h, gapTermExtra h (k h) (a h) i)
          (∑ h, gapTermOrder h (k h) (a h) i) θ) (fun _ => 0) v := by
  have h := shifted_gap_series_expansion p hp k θ
  rw [gapOperators_expansion] at h
  have hh := congrArg (fun f : AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) =>
    f.coeff (fun i => (tupleGap v.val i:ℤ))) h
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,tensorSeries_coeff,
    biasedSeries_coeff_nat] at hh
  unfold positionalRankDifference
  simp_rw [subsetRankKernel_binomial_formula hl _ (shiftedTag_strictMono p hp _) _ v.property θ hθ]
  calc
    _ = θ^r / binomialMass n θ l *
        ∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) *
          ∏ i, binomialMass (tupleGap (shiftedTag p hp a) i) θ (tupleGap v.val i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      exact congrArg (fun t => θ^r / binomialMass n θ l * t) (by
        simpa only [signedRankProduct,sub_zero] using hh)

/-- The total derivative order is the source value |D|+2|V|. -/
theorem gap_global_order {r : ℕ} (k : Fin r → GapDifference) (a : Fin r → Bool × Bool) :
    (∑ i : Fin (r+1), ∑ h, gapTermOrder h (k h) (a h) i) = ∑ h, (k h).order := by
  rw [Finset.sum_comm]
  simp_rw [gapTermOrder_total]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem gapTermOrder_sum_le_global {r : ℕ} (k : Fin r → GapDifference)
    (a : Fin r → Bool × Bool) (i : Fin (r+1)) :
    (∑ h, gapTermOrder h (k h) (a h) i) ≤ ∑ h, (k h).order := by
  rw [← gap_global_order k a]
  exact Finset.single_le_sum (f := fun j : Fin (r+1) => ∑ h, gapTermOrder h (k h) (a h) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Literal mixed centered positional differences of a conditional rank
kernel, with a single explicit constant depending only on the total order
and the Bernoulli parameter. Every gap scale remains available for summing
over the period tuples in the signed initial construction. -/
theorem positionalRankDifference_square_sum_le {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ G : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (hG : 0 < G)
    (hgap : ∀ i, G ≤ (tupleGap p i-gapIncidence r i : ℕ)+1)
    (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r, positionalRankDifference hl p hp k v ^ 2) ≤
      (θ^r / binomialMass n θ l)^2 * (2:ℝ)^(2*r) *
        (lengthDifferenceConstant (∑ h, (k h).order) θ)^(2*(∑ h, (k h).order)+r+2) /
      (G^(∑ h, (k h).order) * Real.sqrt ((tupleGap p e-gapIncidence r e:ℕ)+1) *
        ∏ i, Real.sqrt ((tupleGap p i-gapIncidence r i:ℕ)+1)) := by
  let d := ∑ h, (k h).order
  let C := lengthDifferenceConstant d θ
  let b (i : Fin (r+1)) := tupleGap p i-gapIncidence r i
  let B := C^(2*d+r+2) / (G^d*Real.sqrt ((b e:ℝ)+1)*∏ i,Real.sqrt ((b i:ℝ)+1))
  let c (a : Fin r → Bool × Bool) := ∏ h, gapTermWeight (k h) (a h)
  let F (a : Fin r → Bool × Bool) (v : IncreasingTuple l r) :=
    signedRankProduct (fun i => binomialLengthDifference
      (b i+∑ h, gapTermExtra h (k h) (a h) i)
      (∑ h, gapTermOrder h (k h) (a h) i) θ) (fun _ => 0) v
  have hC : 0 < C := lengthDifferenceConstant_pos d hθ
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB (a : Fin r → Bool × Bool) : (∑ v, F a v^2) ≤ B := by
    have hd (i : Fin (r+1)) : lengthDifferenceConstant (∑ h, gapTermOrder h (k h) (a h) i) θ ≤ C :=
      lengthDifferenceConstant_mono (gapTermOrder_sum_le_global k a i) hθ
    have h := rank_derivatives_uniform (l := l)
      (fun i => b i+∑ h, gapTermExtra h (k h) (a h) i) b
      (fun i => ∑ h, gapTermOrder h (k h) (a h) i) (fun _ => 0)
      hθ hd hG (fun _ => Nat.le_add_right _ _) (by
        intro i
        exact (hgap i).trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right (b i) _) 1)) e
    simpa only [F,B,d,gap_global_order] using h
  have hmix := rank_mixture_square_sum_le c F (fun _ => B) hB
  have hM : (∑ a, |c a|) ≤ (2:ℝ)^r := gapOperators_weight_l1 k
  have hM0 : 0 ≤ ∑ a, |c a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmix' : (∑ v, (∑ a, c a*F a v)^2) ≤ (2:ℝ)^(2*r)*B := by
    refine hmix.trans ?_
    rw [← Finset.sum_mul,← mul_assoc]
    have hs : (∑ a, |c a|)^2 ≤ ((2:ℝ)^r)^2 := (sq_le_sq₀ hM0 (by positivity)).mpr hM
    calc
      _ = (∑ a, |c a|)^2*B := by ring
      _ ≤ ((2:ℝ)^r)^2*B := mul_le_mul_of_nonneg_right hs hB0
      _ = _ := by rw [← pow_mul,Nat.mul_comm r 2]
  simp_rw [positionalRankDifference_expansion hl p hp k hθ,mul_pow]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (θ^r / binomialMass n θ l)^2 * ((2:ℝ)^(2*r)*B) :=
      mul_le_mul_of_nonneg_left hmix' (sq_nonneg _)
    _ = _ := by dsimp [B,C,d,b]; ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem gapIncidence_le_two (r : ℕ) (i : Fin (r+1)) : gapIncidence r i ≤ 2 := by
  have h₁ : Fin.cons (α := fun _ => ℕ) 0 (fun _ : Fin r => 1) i ≤ 1 := by
    induction i using Fin.cases <;> simp
  have h₂ : Fin.snoc (α := fun _ => ℕ) (fun _ : Fin r => 1) 0 i ≤ 1 := by
    induction i using Fin.lastCases <;> simp
  exact Nat.add_le_add h₁ h₂

/-- Removing both incident displacement units still leaves a fixed
fraction of each actual coarse gap. Doubled coarse gaps are used to keep
all combinatorial labels integer-valued. -/
theorem period_derivative_base_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (i : Fin (r+1)) :
    (m:ℝ)*coarsePeriodGap j i/4 ≤
      ((tupleGap (periodSlot off ∘ j) i-gapIncidence r i:ℕ):ℝ)+1 := by
  have he := abs_le.mp (period_gap_rounding hr off hoff hdiff j hj i)
  have hs := gapIncidence_le (periodSlot off ∘ j) hsafe i
  have hs₂ : (gapIncidence r i:ℝ) ≤ 2 := by exact_mod_cast gapIncidence_le_two r i
  have hc : 1 ≤ (coarsePeriodGap j i:ℝ) := by exact_mod_cast coarsePeriodGap_pos j i
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.cast_sub hs]
  nlinarith

theorem period_derivative_common_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (i : Fin (r+1)) :
    (m:ℝ)/4 ≤ ((tupleGap (periodSlot off ∘ j) i-gapIncidence r i:ℕ):ℝ)+1 := by
  refine le_trans ?_ (period_derivative_base_lower hm hr off hoff hdiff j hj hsafe i)
  have hc : 1 ≤ (coarsePeriodGap j i:ℝ) := by exact_mod_cast coarsePeriodGap_pos j i
  nlinarith [show (0:ℝ) ≤ m by positivity]

/-- A largest coarse gap supplies the additional square-root improvement
coming from the fixed sum of the observed ranks. -/
theorem period_derivative_largest_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (e : Fin (r+1))
    (he : 2*u ≤ (r+1)*coarsePeriodGap j e) :
    (u:ℝ)*m/(2*(r+1:ℝ)) ≤
      ((tupleGap (periodSlot off ∘ j) e-gapIncidence r e:ℕ):ℝ)+1 := by
  refine le_trans ?_ (period_derivative_base_lower hm hr off hoff hdiff j hj hsafe e)
  have he' : 2*(u:ℝ) ≤ (r+1:ℝ)*coarsePeriodGap j e := by exact_mod_cast he
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right he' (show (0:ℝ) ≤ m by positivity)
  nlinarith only [hh]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

theorem binomial_rank_normalization {n l r : ℕ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hl : l ≤ n)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ)) :
    (θ^r/binomialMass n θ l)^2 ≤ 144*(n:ℝ) := by
  have hpow : (θ^r)^2 ≤ 1 := pow_le_one₀ (pow_nonneg hθ.1.le r) (pow_le_one₀ hθ.1.le hθ.2.le) 
  calc
    _ = (θ^r)^2*(binomialMass n θ l)⁻¹^2 := by rw [div_eq_mul_inv,mul_pow]
    _ ≤ (binomialMass n θ l)⁻¹^2 := mul_le_of_le_one_left (sq_nonneg _) hpow
    _ ≤ 144*((n:ℝ)*θ*(1-θ)) := binomialMass_mean_inverse_sq n l hθ hl hmean hv
    _ ≤ _ := by
      have h : θ*(1-θ) ≤ 1 := by nlinarith [sq_nonneg θ]
      have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (n:ℝ) by positivity)
      nlinarith only [hh]

/-- The exact mean-count version, with arbitrary proven positive lower
scales for all gaps; no asymptotic or analytic estimate is assumed. -/
theorem positionalRankDifference_scale_bound {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ G H : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (hG : 0 < G) (hH : 0 < H)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ))
    (B : Fin (r+1) → ℝ) (hB : ∀ i, 0 < B i)
    (hgap : ∀ i, G ≤ (tupleGap p i-gapIncidence r i:ℕ)+1)
    (hscale : ∀ i, B i ≤ (tupleGap p i-gapIncidence r i:ℕ)+1)
    (e : Fin (r+1)) (hlarge : H ≤ Real.sqrt ((tupleGap p e-gapIncidence r e:ℕ)+1)) :
    (∑ v : IncreasingTuple l r, positionalRankDifference hl p hp k v ^ 2) ≤
      144*(n:ℝ)*(2:ℝ)^(2*r)*
        (lengthDifferenceConstant (∑ h, (k h).order) θ)^(2*(∑ h, (k h).order)+r+2) /
      (G^(∑ h, (k h).order)*H*∏ i, Real.sqrt (B i)) := by
  refine (positionalRankDifference_square_sum_le hl p hp k hθ hG hgap e).trans ?_
  have hC := (lengthDifferenceConstant_pos (∑ h, (k h).order) hθ).le
  apply div_le_div₀ (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (binomial_rank_normalization hθ hl hmean hv) (by positivity))
      (pow_nonneg hC _)
  · exact mul_pos (mul_pos (pow_pos hG _) hH)
      (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hB i)))
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hlarge (by positivity)
    · exact Finset.prod_le_prod (fun i _ => (Real.sqrt_nonneg (B i)))
        (fun i _ => Real.sqrt_le_sqrt (hscale i))
    · exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
    · positivity

/-- The finite-difference estimate for actual translated tagged slots in
periodic words. The tuple dependence is exactly the product of inverse
square roots of its doubled coarse gaps. -/
theorem period_positionalRankDifference_bound {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑ v : IncreasingTuple l r,
      positionalRankDifference hl (periodSlot off ∘ j.val) hsafe k v ^ 2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le (j.val ⟨0,hr⟩).val) (j.val ⟨0,hr⟩).isLt
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu0 : (0:ℝ) < u := by exact_mod_cast hu
  obtain ⟨e,he⟩ := exists_large_period_gap hr j
  have hb (i : Fin (r+1)) := period_derivative_base_lower hm hr off hoff hdiff j.val j.property hsafe i
  have hg (i : Fin (r+1)) := period_derivative_common_lower hm hr off hoff hdiff j.val j.property hsafe i
  have hc (i : Fin (r+1)) : (0:ℝ) < coarsePeriodGap j.val i := by exact_mod_cast coarsePeriodGap_pos j.val i
  have h := positionalRankDifference_scale_bound hl (periodSlot off ∘ j.val) hsafe k hθ
    (G := (m:ℝ)/4) (H := Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))) (by positivity) (by positivity)
    hmean hv (fun i => (m:ℝ)*coarsePeriodGap j.val i/4) (fun i => by positivity [hc i]) hg hb e
    (Real.sqrt_le_sqrt (period_derivative_largest_lower hm hr off hoff hdiff j.val j.property hsafe e he))
  refine h.trans_eq ?_
  have hs (i : Fin (r+1)) : Real.sqrt ((m:ℝ)*coarsePeriodGap j.val i/4) =
      Real.sqrt ((m:ℝ)/4)*Real.sqrt (coarsePeriodGap j.val i) := by
    rw [show (m:ℝ)*coarsePeriodGap j.val i/4=((m:ℝ)/4)*coarsePeriodGap j.val i by ring,
      Real.sqrt_mul (by positivity)]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [periodDifferencePrefactor,Finset.prod_inv_distrib]
  ring

end TraceReconstruction

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction

/-- Two independent exact sum constraints determine a missing coordinate on
 each side of a fixed cut. This is the second-gap elimination needed when
 a period label has been fixed. -/
theorem two_sums_determine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (x y : ι → ℕ) (hA : ∑ i∈A, x i = ∑ i∈A, y i)
    (ht : ∑ i, x i = ∑ i, y i)
    (hxy : ∀ i, i≠e → i≠d → x i=y i) : x=y := by
  have hs : (∑ i∈A.erase e, x i) = ∑ i∈A.erase e, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    apply hxy i hi'.1
    intro hid
    exact hd (hid ▸ hi'.2)
  have hxe : x e=y e := by
    have hx := Finset.sum_erase_add A x he
    have hy := Finset.sum_erase_add A y he
    omega
  have hs' : (∑ i∈Finset.univ.erase d, x i) = ∑ i∈Finset.univ.erase d, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hie : i=e
    · simpa only [hie] using hxe
    · exact hxy i hie (Finset.mem_erase.mp hi).1
  have hxd : x d=y d := by
    have hx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ d)
    have hy := Finset.sum_erase_add Finset.univ y (Finset.mem_univ d)
    omega
  funext i
  by_cases hie : i=e
  · simpa only [hie] using hxe
  by_cases hid : i=d
  · simpa only [hid] using hxd
  exact hxy i hie hid

/-- Restricting an injective gap profile to all but the two eliminated
 coordinates is still injective on two fixed-sum fibers. -/
theorem two_sums_restrict_injective {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V) :
    Function.Injective (fun a => fun i : RemainingCoordinates e d => p a i.val) := by
  intro a b hab
  apply hp
  have hv : (fun i => (p a i).val) = (fun i => (p b i).val) := by
    apply two_sums_determine A he hd
    · rw [hA,hA]
    · rw [ht,ht]
    · intro i hie hid
      exact congrArg Fin.val (congrFun hab ⟨i,hie,hid⟩)
  funext i
  exact Fin.ext (congrFun hv i)

/-- Once the two coordinates are eliminated all remaining gap weights sum
 independently; any additional constraints may be dropped. -/
theorem two_sums_product_bound {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    (w : ι → Fin (U+1) → ℝ) (hw : ∀ i k, 0≤w i k) :
    (∑ a, ∏ i : RemainingCoordinates e d, w i.val (p a i.val)) ≤
      ∏ i : RemainingCoordinates e d, ∑ k, w i.val k := by
  classical
  have hh := sum_injective_profile_le
    (fun a => fun i : RemainingCoordinates e d => p a i.val)
    (two_sums_restrict_injective A he hd p hp hA ht)
    (fun _ => True) (fun _ => trivial)
    (fun δ => ∏ i : RemainingCoordinates e d, w i.val (δ i))
    (fun δ => Finset.prod_nonneg (fun i _ => hw i.val (δ i)))
  simp only [ite_true] at hh
  exact hh.trans_eq (by rw [Finset.prod_univ_sum]; simp only [Fintype.piFinset_univ])

/-- The sum of doubled coarse gaps to a specified period label is exact,
 including the half endpoint cells in the source convention. -/
theorem coarsePeriodGap_prefix {u r : ℕ} (j : Fin r → Fin u) (hj : StrictMono j)
    (i : Fin r) : (∑ g∈Finset.Iic i.castSucc, coarsePeriodGap j g) = 2*(j i).val+1 := by
  classical
  have hg := tupleGap_prefix j hj i
  have hz : (0 : Fin (r+1)) ∈ Finset.Iic i.castSucc := by simp
  have hl : ∀ g∈Finset.Iic i.castSucc, g≠Fin.last r := by
    intro g hg he
    have hle := Finset.mem_Iic.mp hg
    have hval : g.val ≤ i.val := hle
    have he' := congrArg Fin.val he
    simp only [Fin.val_last] at he'
    omega
  have hc : (∑ g∈Finset.Iic i.castSucc,
      if g=0 ∨ g=Fin.last r then 1 else 2) = 2*i.val+1 := by
    have hsub : (∑ g∈(Finset.Iic i.castSucc).erase 0,
        if g=0 ∨ g=Fin.last r then 1 else 2) = 2*i.val := by
      have hc : ((Finset.Iic i.castSucc).erase 0).card = i.val := by
        rw [Finset.card_erase_of_mem hz,Fin.card_Iic]
        simp
      calc
        _ = ∑ _g∈(Finset.Iic i.castSucc).erase 0, 2 := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [ite_eq_right (not_or.mpr ⟨(Finset.mem_erase.mp hg).1,
            hl g (Finset.mem_erase.mp hg).2⟩)]
        _ = _ := by simp [hc,Nat.mul_comm]
    have hsum := Finset.sum_erase_add (Finset.Iic i.castSucc)
      (fun g => if g=0 ∨ g=Fin.last r then 1 else 2) hz
    rw [hsub] at hsum
    simpa using hsum.symm
  simp only [coarsePeriodGap,Finset.sum_add_distrib,← Finset.mul_sum]
  omega

/-- The full inverse-square-root sum, including the zero cell (whose
 value is zero), has the same elementary integral bound. -/
theorem fin_sum_inverse_sqrt (U : ℕ) :
    (∑ k : Fin (U+1), (Real.sqrt (k.val:ℝ))⁻¹) ≤ 2*Real.sqrt U := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, Real.sqrt_zero, inv_zero,zero_add,Fin.val_succ]
  have h := sum_inverse_sqrt U
  rw [Finset.sum_range] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

theorem prod_two_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e d : ι} (hed : e≠d) (f : ι → ℝ) :
    (∏ i, f i) = f e*f d*∏ i : RemainingCoordinates e d, f i.val := by
  have hd : d∈Finset.univ.erase e := by simp [hed.symm]
  have h1 := Finset.prod_erase_mul Finset.univ f (Finset.mem_univ e)
  have h2 := Finset.prod_erase_mul (Finset.univ.erase e) f hd
  have hrem : (∏ i∈(Finset.univ.erase e).erase d, f i) =
      ∏ i : RemainingCoordinates e d, f i.val :=
    Finset.prod_subtype _ (by intro i; simp [and_comm]) f
  rw [← h1,← h2,hrem]
  ring

theorem inverse_sqrt_pair {x y R : ℝ} (hR : 0<R) (hx : R≤x) (hy : R≤y) :
    (Real.sqrt x)⁻¹*(Real.sqrt y)⁻¹ ≤ R⁻¹ := by
  have hs : 0<Real.sqrt R := Real.sqrt_pos.mpr hR
  have hix := (inv_le_inv₀ (hs.trans_le (Real.sqrt_le_sqrt hx)) hs).mpr (Real.sqrt_le_sqrt hx)
  have hiy := (inv_le_inv₀ (hs.trans_le (Real.sqrt_le_sqrt hy)) hs).mpr (Real.sqrt_le_sqrt hy)
  calc
    _ ≤ (Real.sqrt R)⁻¹*(Real.sqrt R)⁻¹ := mul_le_mul hix hiy (by positivity) (by positivity)
    _ = _ := by rw [← mul_inv,Real.mul_self_sqrt hR.le]

/-- Explicit two-gap summation on a fixed-sum fiber. Both large gaps
 contribute R^(-1), rather than losing a free label factor. -/
theorem two_large_gaps_inverse_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (heR : ∀ a, R≤(p a e).val) (hdR : ∀ a, R≤(p a d).val) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(2*Real.sqrt U)^Fintype.card (RemainingCoordinates e d) := by
  classical
  have hed : e≠d := by intro h; exact hd (h ▸ he)
  have hpoint (a) := inverse_sqrt_pair hR (heR a) (hdR a)
  calc
    _ ≤ ∑ a, R⁻¹*∏ i : RemainingCoordinates e d, (Real.sqrt ((p a i.val).val:ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro a _
      rw [prod_two_coordinates hed]
      exact mul_le_mul_of_nonneg_right (hpoint a) (by positivity)
    _ = R⁻¹*∑ a, ∏ i : RemainingCoordinates e d, (Real.sqrt ((p a i.val).val:ℝ))⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ R⁻¹*∏ _i : RemainingCoordinates e d, ∑ k : Fin (U+1), (Real.sqrt (k.val:ℝ))⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact two_sums_product_bound A he hd p hp hA ht
        (fun _ k => (Real.sqrt (k.val:ℝ))⁻¹) (fun _ _ => by positivity)
    _ ≤ R⁻¹*∏ _i : RemainingCoordinates e d, (2*Real.sqrt U) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Finset.prod_le_prod (fun _ _ => by positivity) (fun _ _ => fin_sum_inverse_sqrt U)
    _ = _ := by simp

theorem fixedPeriodProfile_injective {u r : ℕ} (a : Fin r) (h : Fin u) :
    Function.Injective (fixedPeriodProfile a h) := by
  intro j k hjk
  apply Subtype.ext
  apply Subtype.ext
  apply coarsePeriodGap_injective j.val.property k.val.property
  funext i
  exact congrArg Fin.val (congrFun hjk i)

theorem fixedPeriodProfile_prefix {u r : ℕ} (a : Fin r) (h : Fin u)
    (j : FixedPeriodTuple u r a h) :
    (∑ i∈Finset.Iic a.castSucc, (fixedPeriodProfile a h j i).val)=2*h.val+1 := by
  change (∑ i∈Finset.Iic a.castSucc, coarsePeriodGap j.val.val i)=_
  rw [coarsePeriodGap_prefix _ j.val.property,j.property]

theorem fixedPeriodProfile_total {u r : ℕ} (a : Fin r) (h : Fin u)
    (j : FixedPeriodTuple u r a h) :
    (∑ i, (fixedPeriodProfile a h j i).val)=2*u :=
  coarsePeriodGap_sum (Nat.zero_lt_of_lt a.isLt) j.val.val j.val.property

end TraceReconstruction
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
noncomputable section
namespace TraceReconstruction

/-- Cardinality bookkeeping for the two eliminated gap coordinates. -/
theorem remainingCoordinates_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e d : ι} (hed : e≠d) :
    Fintype.card (RemainingCoordinates e d)=Fintype.card ι-2 := by
  classical
  have hset : (Finset.univ.filter (fun i : ι => i≠e ∧ i≠d)) = (Finset.univ.erase e).erase d := by
    ext i
    simp [and_comm]
  rw [Fintype.card_subtype, hset]
  rw [Finset.card_erase_of_mem (by simp [hed.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ e)]
  simp only [Finset.card_univ]
  omega

/-- A finite sum's largest entry on a nonempty set controls its average,
 with the full number of coordinates in place of the subset cardinality. -/
theorem exists_large_in_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (hA : A.Nonempty) (x : ι → ℝ) (hx : ∀ i, 0≤x i)
    {R : ℝ} (hR : R*Fintype.card ι ≤ ∑ i∈A, x i) :
    ∃ e∈A, R≤x e := by
  obtain ⟨e,he,hm⟩ := A.exists_max_image x hA
  refine ⟨e,he,?_⟩
  have hc : (A.card:ℝ)≤Fintype.card ι := by exact_mod_cast Finset.card_le_univ A
  have hcard : (0:ℝ)<Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨e⟩
  have hs : (∑ i∈A, x i) ≤ (Fintype.card ι:ℝ)*x e := by
    calc
      _ ≤ ∑ _i∈A, x e := Finset.sum_le_sum (fun i hi => hm i hi)
      _ = (A.card:ℝ)*x e := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (hx e)
  nlinarith

/-- Covering the fixed-sum profile by its selected largest coordinates
 costs only the square of its (fixed) dimension. -/
theorem two_sided_large_gaps_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R)
    (hleft : ∀ a, ∃ e∈A, R≤(p a e).val)
    (hright : ∀ a, ∃ d∉A, R≤(p a d).val) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      (Fintype.card ι:ℝ)^2*R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) := by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a : α) := (e a,d a)
  let W (a : α) := ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹
  have hfiber (z : ι × ι) :
      (∑ a : {a // f a=z}, W a.val) ≤ R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) := by
    by_cases hne : Nonempty {a // f a=z}
    · obtain ⟨a⟩ := hne
      have ha := congrArg Prod.fst a.property
      have ha' := congrArg Prod.snd a.property
      have hz1 : z.1∈A := by simpa only [f] using ha ▸ he a.val
      have hz2 : z.2∉A := by simpa only [f] using ha' ▸ hd a.val
      have hzd : z.1≠z.2 := by intro h; exact hz2 (h ▸ hz1)
      have hh := two_large_gaps_inverse_sum A hz1 hz2
        (fun a : {a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h := congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h := congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
      simpa only [W,remainingCoordinates_card hzd] using hh
    · have : IsEmpty {a // f a=z} := not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z : ι × ι, ∑ a : {a // f a=z}, W a.val := by
      exact (Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z : ι × ι, R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) :=
      Finset.sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp [pow_two,mul_assoc]

/-- The fixed central label leaves a macroscopic sum on both sides. -/
theorem fixedPeriodProfile_central_sum {u r : ℕ} (a : Fin r) (h : Fin u)
    (hleft : (u:ℝ)/3≤2*h.val+1)
    (hright : (u:ℝ)/3≤2*u-(2*h.val+1)) :
    (∑ j : FixedPeriodTuple u r a h,
      ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹) ≤
      ((r+1:ℕ):ℝ)^2 * ((u:ℝ)/(3*(r+1:ℝ)))⁻¹ *
        (2*Real.sqrt (2*u:ℕ))^(r-1) := by
  classical
  have hu : (0:ℝ)<u := by exact_mod_cast (Nat.zero_lt_of_lt h.isLt)
  let A := Finset.Iic a.castSucc
  let p := fixedPeriodProfile a h
  have hR : 0<(u:ℝ)/(3*(r+1:ℝ)) := by positivity
  have hL (j : FixedPeriodTuple u r a h) :
      ∃ e∈A, (u:ℝ)/(3*(r+1:ℝ))≤(p j e).val := by
    apply exists_large_in_subset A ⟨0, by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Nat.cast_nonneg _)
    have hs := fixedPeriodProfile_prefix a h j
    have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
    rw [hs']
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    convert hleft using 1; field_simp
  have hD (j : FixedPeriodTuple u r a h) :
      ∃ d∉A, (u:ℝ)/(3*(r+1:ℝ))≤(p j d).val := by
    have ha : a.val < r := a.isLt
    have hlast : Fin.last r∈Aᶜ := by simp [A]
    obtain ⟨d,hd,hdR⟩ := exists_large_in_subset Aᶜ ⟨Fin.last r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Nat.cast_nonneg _) (R := (u:ℝ)/(3*(r+1:ℝ))) (by
        have hs := fixedPeriodProfile_prefix a h j
        have ht := fixedPeriodProfile_total a h j
        have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
        have ht' : (∑ i, ((p j i).val:ℝ))=2*u := by exact_mod_cast ht
        have hc := Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum : (∑ i∈Aᶜ, ((p j i).val:ℝ))=2*u-(2*h.val+1) := by linarith
        rw [hsum]
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  have hh := two_sided_large_gaps_sum A p (fixedPeriodProfile_injective a h)
    (fixedPeriodProfile_prefix a h) (fixedPeriodProfile_total a h) hR hL hD
  simpa only [p,fixedPeriodProfile,Fin.val_mk,Fintype.card_fin,show r+1-2=r-1 by omega] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

/-- Any finite cutoff only removes nonnegative mass from the full binomial
 support, even if the cutoff extends beyond that support. -/
theorem binomialMass_cutoff_filter_le (n U : ℕ) {p : ℝ} (hp : p∈Set.Icc 0 1)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ k : Fin (U+1), if P k.val then binomialMass n p k.val else 0) ≤
      ∑ k∈(Finset.range (n+1)).filter P, binomialMass n p k := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if P k then binomialMass n p k else 0) (U+1),Finset.sum_filter]
  by_cases hU : U≤n
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    split_ifs
    · exact binomialMass_nonneg n k hp
    · rfl
  · apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hnk : n<k := by simp only [Finset.mem_range] at hk; omega
    simp [binomialMass,Nat.choose_eq_zero_of_lt hnk]

/-- A single-coordinate event for any injective family of profiles is
 bounded by the corresponding full product marginal. -/
theorem profile_coordinate_event_le {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p : α → ι → κ) (hp : Function.Injective p)
    (w : ι → κ → ℝ) (hw : ∀ i k, 0≤w i k)
    (hs : ∀ i, ∑ k, w i k≤1) (e : ι) (P : κ → Prop) [DecidablePred P]
    {T : ℝ} (_hT : 0≤T) (ht : (∑ k, if P k then w e k else 0)≤T) :
    (∑ a, if P (p a e) then ∏ i, w i (p a i) else 0) ≤ T := by
  classical
  let w' (i : ι) (k : κ) := if i=e then (if P k then w i k else 0) else w i k
  have hw' (i k) : 0≤w' i k := by
    dsimp [w']
    split_ifs
    · exact hw i k
    · exact le_rfl
    · exact hw i k
  have hprod (δ : ι → κ) : (∏ i, w' i (δ i)) =
      if P (δ e) then ∏ i, w i (δ i) else 0 := by
    by_cases h : P (δ e)
    · rw [ite_eq_left h]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i=e
      · subst i; simp [w',h]
      · simp [w',hi]
    · rw [ite_eq_right h]
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [w',h])
  have hsum (i) : (∑ k, w' i k)≤ if i=e then T else 1 := by
    by_cases hi : i=e
    · subst i; simpa only [w',ite_true] using ht
    · simpa only [w',ite_eq_right hi] using hs i
  calc
    _ = ∑ a, ∏ i, w' i (p a i) := by simp_rw [hprod]
    _ ≤ ∑ δ : ι → κ, ∏ i, w' i (δ i) := by
      have hh := sum_injective_profile_le p hp (fun _ => True) (fun _ => trivial)
        (fun δ => ∏ i, w' i (δ i)) (fun δ => Finset.prod_nonneg (fun i _ => hw' i (δ i)))
      simpa only [ite_true] using hh
    _ = ∏ i, ∑ k, w' i k := (Fintype.prod_sum _).symm
    _ ≤ ∏ i : ι, if i=e then T else 1 :=
      Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun k _ => hw' i k)) (fun i _ => hsum i)
    _ = T := by simp

/-- Exponentially small clipping loss for a single gap of the actual
 conditional retained-subset rank kernel. -/
theorem subsetRankKernel_gap_tail {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (hp : StrictMono p) (e : Fin (r+1))
    {θ t a : ℝ} (hθ : θ∈Set.Ioo 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ v : IncreasingTuple l r,
      if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(tupleGap p e:ℝ)*t^2)) := by
  classical
  have hθ' : θ∈Set.Icc 0 1 := ⟨hθ.1.le,hθ.2.le⟩
  let prof := rankGapProfile (n := l) (r := r) (Equiv.refl _)
  let w (i : Fin (r+1)) (k : Fin (l-r+1)) := binomialMass (tupleGap p i) θ k.val
  have hw (i k) : 0≤w i k := binomialMass_nonneg _ _ hθ'
  have hs (i) : (∑ k, w i k)≤1 := by
    have hh := binomialMass_cutoff_filter_le (tupleGap p i) (l-r) hθ' (fun _ => True)
    simpa only [ite_true,Finset.filter_true,sum_binomialMass] using hh
  have ht' : (∑ k : Fin (l-r+1),
      if a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ| then w e k else 0) ≤
      2*Real.exp (-t*a+(tupleGap p e:ℝ)*t^2) := by
    exact (binomialMass_cutoff_filter_le (tupleGap p e) (l-r) hθ'
      (fun k : ℕ => a≤|(k:ℝ)-(tupleGap p e:ℝ)*θ|)).trans
        (binomialMass_abs_tail _ hθ' ht)
  have hh := profile_coordinate_event_le prof (rankGapProfile_injective _) w hw hs e
    (fun k => a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ|) (by positivity) ht'
  have hfac : 0≤θ^r / binomialMass n θ l :=
    div_nonneg (pow_nonneg hθ.1.le _) (binomialMass_nonneg _ _ hθ')
  calc
    _ = θ^r / binomialMass n θ l *
        ∑ v : IncreasingTuple l r,
          if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
          then ∏ i, binomialMass (tupleGap p i) θ (tupleGap v.val i) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs
      · exact subsetRankKernel_binomial_formula hl p hp v.val v.property θ hθ
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [prof,rankGapProfile,Equiv.refl_apply,w] using hh) hfac

/-- A coordinatewise rank region has a union-bound clipping estimate. -/
theorem subsetRankKernel_outside_region {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (hp : StrictMono p)
    {θ t a : ℝ} (hθ : θ∈Set.Ioo 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ v : IncreasingTuple l r,
      if ∃ i, a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      ((r+1:ℕ):ℝ)*θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(n:ℝ)*t^2)) := by
  classical
  have hθ' : θ∈Set.Icc 0 1 := ⟨hθ.1.le,hθ.2.le⟩
  have hpoint (v : IncreasingTuple l r) :
      (if ∃ i, a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      ∑ i, if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := by
    have hn (i) : 0≤(if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0) := by
      split_ifs
      · exact subsetRankKernel_nonneg hl p v.val
      · rfl
    split_ifs with h
    · obtain ⟨e,he⟩ := h
      have hh := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ e)
      simpa only [ite_eq_left he] using hh
    · exact Finset.sum_nonneg (fun i _ => hn i)
  calc
    _ ≤ ∑ v : IncreasingTuple l r, ∑ i,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = ∑ i, ∑ v : IncreasingTuple l r,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := Finset.sum_comm
    _ ≤ ∑ _i : Fin (r+1), θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(n:ℝ)*t^2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply (subsetRankKernel_gap_tail hl p hp i hθ ht).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg hθ.1.le _) (binomialMass_nonneg _ _ hθ'))
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hgap : tupleGap p i≤n := (tupleGap_le_remainder ⟨p,hp⟩ i).trans (Nat.sub_le _ _)
      have hg : (tupleGap p i:ℝ)≤n := by exact_mod_cast hgap
      have hh := mul_le_mul_of_nonneg_right hg (sq_nonneg t)
      linarith
    _ = _ := by simp; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

/-- An inverse square root at an integer, extended by zero at zero,
 never exceeds one. -/
theorem inverse_sqrt_nat_le_one (k : ℕ) : (Real.sqrt (k:ℝ))⁻¹≤1 := by
  by_cases hk : k=0
  · simp [hk]
  have hk' : (1:ℝ)≤k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have hs : 1≤Real.sqrt (k:ℝ) := by simpa using Real.sqrt_le_sqrt hk'
  exact (inv_le_one₀ (by positivity : 0<Real.sqrt (k:ℝ))).mpr hs

/-- A bounded gap costs a constant depending only on that bound, rather
 than an additional square root of the ambient period count. -/
theorem fin_bounded_inverse_sqrt (U M : ℕ) :
    (∑ k : Fin (U+1), if k.val≤M then (Real.sqrt (k.val:ℝ))⁻¹ else 0) ≤ M+1 := by
  classical
  calc
    _ ≤ ∑ k : Fin (U+1), if k.val≤M then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact inverse_sqrt_nat_le_one k.val
      · rfl
    _ = ((Finset.univ.filter (fun k : Fin (U+1) => k.val≤M)).card:ℝ) := by simp
    _ ≤ M+1 := by
      have hh : (Finset.univ.filter (fun k : Fin (U+1) => k.val≤M)).card≤M+1 := by
        rw [← Finset.card_range (M+1)]
        apply Finset.card_le_card_of_injOn Fin.val
          (fun k hk => by
            have hh := (Finset.mem_filter.mp hk).2
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hh))
        intro k _ j _ hkj; exact Fin.ext hkj
      exact_mod_cast hh

theorem prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι) (A B : ℝ) :
    (∏ i : ι, if i=e then A else B)=A*B^(Fintype.card ι-1) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => if i=e then A else B) (Finset.mem_univ e)]
  simp only [ite_true]
  have hh : (∏ i∈Finset.univ.erase e, if i=e then A else B)=
      ∏ _i∈Finset.univ.erase e, B := by
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_right (Finset.mem_erase.mp hi).1
  rw [hh]
  simp

/-- Refined two-gap elimination when a third gap has bounded size. -/
theorem two_large_bounded_gap_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M : ℕ} (A : Finset ι) {e d c : ι} (he : e∈A) (hd : d∉A)
    (hce : c≠e) (hcd : c≠d)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (heR : ∀ a, R≤(p a e).val) (hdR : ∀ a, R≤(p a d).val)
    (hcM : ∀ a, (p a c).val≤M) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
  classical
  have hed : e≠d := by intro h; exact hd (h ▸ he)
  let c' : RemainingCoordinates e d := ⟨c,hce,hcd⟩
  let w (i : ι) (k : Fin (U+1)) :=
    if i=c then (if k.val≤M then (Real.sqrt (k.val:ℝ))⁻¹ else 0)
    else (Real.sqrt (k.val:ℝ))⁻¹
  have hw (i k) : 0≤w i k := by dsimp [w]; split_ifs <;> positivity
  have hwP (a i) : w i (p a i)=(Real.sqrt ((p a i).val:ℝ))⁻¹ := by
    by_cases hi : i=c
    · subst i; simp only [w,ite_true,ite_eq_left (hcM a)]
    · simp only [w,ite_eq_right hi]
  have hwS (i : RemainingCoordinates e d) : (∑ k, w i.val k)≤
      if i=c' then (M+1:ℝ) else 2*Real.sqrt U := by
    by_cases hi : i=c'
    · subst i
      simpa only [c',w,ite_true] using fin_bounded_inverse_sqrt U M
    · have hic : i.val≠c := by intro h; apply hi; exact Subtype.ext h
      simpa only [w,ite_eq_right hi,ite_eq_right hic] using fin_sum_inverse_sqrt U
  calc
    _ ≤ ∑ a, R⁻¹*∏ i : RemainingCoordinates e d, w i.val (p a i.val) := by
      apply Finset.sum_le_sum
      intro a _
      simp_rw [hwP]
      rw [prod_two_coordinates hed]
      exact mul_le_mul_of_nonneg_right (inverse_sqrt_pair hR (heR a) (hdR a)) (by positivity)
    _ = R⁻¹*∑ a, ∏ i : RemainingCoordinates e d, w i.val (p a i.val) := by rw [Finset.mul_sum]
    _ ≤ R⁻¹*∏ i : RemainingCoordinates e d, ∑ k, w i.val k :=
      mul_le_mul_of_nonneg_left (two_sums_product_bound A he hd p hp hA ht w hw) (inv_nonneg.mpr hR.le)
    _ ≤ R⁻¹*∏ i : RemainingCoordinates e d, if i=c' then (M+1:ℝ) else 2*Real.sqrt U := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun k _ => hw i.val k)) (fun i _ => hwS i)
    _ = _ := by
      rw [prod_one_special,remainingCoordinates_card hed]
      simp only [Nat.sub_sub]
      ring

/-- A small internal gap cannot be either selected macroscopic gap.
 The bound retains the extra factor u^(-1/2) needed for nonlinear terms. -/
theorem two_sided_bounded_gaps_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M : ℕ} (A : Finset ι) (c : ι)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (hMR : (M:ℝ)<R)
    (hleft : ∀ a, ∃ e∈A, R≤(p a e).val)
    (hright : ∀ a, ∃ d∉A, R≤(p a d).val)
    (hcM : ∀ a, (p a c).val≤M) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      (Fintype.card ι:ℝ)^2*R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a : α) := (e a,d a)
  let W (a : α) := ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹
  have hfiber (z : ι × ι) :
      (∑ a : {a // f a=z}, W a.val) ≤ R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
    by_cases hne : Nonempty {a // f a=z}
    · obtain ⟨a⟩ := hne
      have ha := congrArg Prod.fst a.property
      have ha' := congrArg Prod.snd a.property
      have hz1 : z.1∈A := by simpa only [f] using ha ▸ he a.val
      have hz2 : z.2∉A := by simpa only [f] using ha' ▸ hd a.val
      have hzR : R≤(p a.val z.1).val := by simpa only [f] using ha ▸ heR a.val
      have hzR' : R≤(p a.val z.2).val := by simpa only [f] using ha' ▸ hdR a.val
      have hc : ((p a.val c).val:ℝ)≤M := by exact_mod_cast hcM a.val
      have hce : c≠z.1 := by intro h; rw [h] at hc; linarith
      have hcd : c≠z.2 := by intro h; rw [h] at hc; linarith
      exact two_large_bounded_gap_sum A hz1 hz2 hce hcd
        (fun a : {a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h := congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h := congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
        (fun a => hcM a.val)
    · have : IsEmpty {a // f a=z} := not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z : ι × ι, ∑ a : {a // f a=z}, W a.val := (Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z : ι × ι, R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) :=
      Finset.sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp [pow_two,mul_assoc]

end TraceReconstruction


noncomputable section
open scoped Classical
namespace TraceReconstruction

/-- Enough accuracy to distinguish two integer gap lengths. -/
theorem nearby_gap_centers_equal {x y : ℕ} {z θ m : ℝ}
    (hθ : 1 / 2 ≤ θ) (hm : 0 < m)
    (hx : |z - θ * m * x / 2| < m / 8) (hy : |z - θ * m * y / 2| < m / 8) : x = y := by
  have hx' := abs_lt.mp hx
  have hy' := abs_lt.mp hy
  have hscale : m / 4 ≤ θ * m / 2 := by nlinarith
  by_contra hxy
  obtain h | h := lt_or_gt_of_ne hxy
  · have h' : (x:ℝ)+1≤y := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ θ * m / 2)
    nlinarith
  · have h' : (y:ℝ)+1≤x := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ θ * m / 2)
    nlinarith

/-- Regions for distinct tagged period tuples are genuinely disjoint,
 before any coefficient or orientation averaging. -/
theorem periodRankRegion_unique {u l r m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    {j k : IncreasingTuple u r} {v : IncreasingTuple l r}
    (hj : PeriodRankRegion m θ j v) (hk : PeriodRankRegion m θ k v) : j=k := by
  apply Subtype.ext
  by_cases hr : r=0
  · subst r; exact Subsingleton.elim _ _
  have hg (i : Fin r) : coarsePeriodGap j.val i.castSucc=coarsePeriodGap k.val i.castSucc :=
    nearby_gap_centers_equal hθ (by exact_mod_cast hm) (hj i) (hk i)
  have hsum := coarsePeriodGap_sum (Nat.pos_of_ne_zero hr) j.val j.property
  have hsum' := coarsePeriodGap_sum (Nat.pos_of_ne_zero hr) k.val k.property
  have hgSum : (∑ i : Fin r, coarsePeriodGap j.val i.castSucc)=
      ∑ i : Fin r, coarsePeriodGap k.val i.castSucc := Finset.sum_congr rfl (fun i _ => hg i)
  rw [Fin.sum_univ_castSucc] at hsum hsum'
  have hlast : coarsePeriodGap j.val (Fin.last r)=coarsePeriodGap k.val (Fin.last r) := by omega
  apply coarsePeriodGap_injective j.property k.property
  funext i
  refine Fin.lastCases hlast (fun i => hg i) i

/-- Orthogonality of a finite family with pointwise disjoint supports. -/
theorem disjoint_support_sum_sq {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) (hf : ∀ a b, a≠b → ∀ v, f a v*f b v=0) :
    (∑ v, (∑ a, f a v)^2) = ∑ a, ∑ v, f a v^2 := by
  classical
  have hp (v) : (∑ a, f a v)^2=∑ a, f a v^2 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single a]
    · ring
    · intro b _ hba
      exact hf a b hba.symm v
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  simp_rw [hp]
  exact Finset.sum_comm

/-- Squared norm of the clipped sum is at most the sum of the original
 squared norms, with arbitrary signed multipliers on each tuple. -/
theorem period_clipped_square_sum {u l r m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (W : IncreasingTuple u r → IncreasingTuple l r → ℝ)
    (a : IncreasingTuple u r → ℝ) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then a j*W j v else 0)^2) ≤
      ∑ j, a j^2*∑ v, W j v^2 := by
  classical
  rw [disjoint_support_sum_sq _ (by
    intro j k hjk v
    by_cases hj : PeriodRankRegion m θ j v
    · have hk : ¬PeriodRankRegion m θ k v := fun hk => hjk (periodRankRegion_unique hm hθ hj hk)
      simp only [ite_eq_left hj,ite_eq_right hk,mul_zero]
    · simp only [ite_eq_right hj,zero_mul])]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  split_ifs
  · exact le_of_eq (mul_pow _ _ _)
  · simp only [zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sum_gapDifference (f : GapDifference → ℝ) :
    (∑ k, f k)=f .unchanged+f .first+f .second := by
  change (∑ k ∈ ({.unchanged,.first,.second} : Finset GapDifference), f k)=_
  simp [Finset.sum_insert]; ring

/-- The centered operator expansion is an exact displacement, not an
 approximation of the trace kernel. -/
theorem motif_positional_identity {χ β τ : ℝ} (hβ : IsMotifValue χ β)
    (hτ : IsTypeSign τ) (a : Fin 3) :
    (∑ k, motifDifferenceWeight χ β τ k * positionalWeight k a)=
      if a=motifShift χ β τ then 1 else 0 := by
  rw [sum_gapDifference]
  rcases hβ with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;>
  rcases hτ with rfl | rfl <;> fin_cases a <;>
    norm_num [motifDifferenceWeight,motifShift,positionalWeight,Fin.ext_iff]

theorem product_function_delta {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a b : ι → κ) :
    (∏ i, if a i=b i then (1:ℝ) else 0)=if a=b then 1 else 0 := by
  classical
  by_cases h : a=b
  · subst a; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Tensorization of the exact local shift identity, with an arbitrary
 array W (in particular any literal retained-subset rank kernel). -/
theorem motif_shift_expansion {r : ℕ} (χ β : Fin r → ℝ) (τ : ℝ)
    (hβ : ∀ h, IsMotifValue (χ h) (β h)) (hτ : IsTypeSign τ)
    (W : (Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) τ)=
      ∑ k : Fin r → GapDifference,
        (∏ h, motifDifferenceWeight (χ h) (β h) τ (k h))*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  classical
  symm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (∑ k : Fin r → GapDifference,
        ∏ h, motifDifferenceWeight (χ h) (β h) τ (k h)*positionalWeight (k h) (a h))*W a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ a, (∏ h, if a h=motifShift (χ h) (β h) τ then (1:ℝ) else 0)*W a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Fintype.prod_sum (fun h k => motifDifferenceWeight (χ h) (β h) τ k * positionalWeight k (a h))]
      simp_rw [motif_positional_identity (hβ _) hτ]
    _ = _ := by simp_rw [product_function_delta]; simp

/-- Every factor of the hypothesis sign comes precisely from a D operator. -/
theorem motifDifferenceWeight_product {r : ℕ} (χ β : Fin r → ℝ) (τ : ℝ)
    (k : Fin r → GapDifference) :
    (∏ h, motifDifferenceWeight (χ h) (β h) τ (k h))=
      τ^firstDifferenceCount k *∏ h, motifDifferenceWeight (χ h) (β h) 1 (k h) := by
  classical
  have hw (h) : motifDifferenceWeight (χ h) (β h) τ (k h)=
      (if k h=.first then τ else 1)*motifDifferenceWeight (χ h) (β h) 1 (k h) := by
    cases k h <;> simp [motifDifferenceWeight]
  simp_rw [hw]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter]
  simp [firstDifferenceCount]

/-- The signed difference retains exactly the patterns having an odd
 number of centered first differences, with the source's factor two. -/
theorem motif_signed_shift_expansion {r : ℕ} (χ β : Fin r → ℝ)
    (hβ : ∀ h, IsMotifValue (χ h) (β h)) (W : (Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) 1)-
      W (fun h => motifShift (χ h) (β h) (-1))=
      ∑ k : Fin r → GapDifference,
        (if Odd (firstDifferenceCount k) then
          2*∏ h, motifDifferenceWeight (χ h) (β h) 1 (k h) else 0)*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  rw [motif_shift_expansion χ β 1 hβ (Or.inl rfl) W,
    motif_shift_expansion χ β (-1) hβ (Or.inr rfl) W,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [motifDifferenceWeight_product χ β 1 k,motifDifferenceWeight_product χ β (-1) k]
  rw [sign_pow_parity (Or.inr rfl : IsTypeSign (-1))]
  simp only [one_pow,one_mul]
  split_ifs <;> ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem shiftGapExtra_le {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) :
    shiftGapExtra a i  ≤  2*gapIncidence r i := by
  have hl : Fin.cons (α := fun _ =>  ℕ) 0 (fun h =>  2-(a h).val) i  ≤ 
      2*Fin.cons (α := fun _ =>  ℕ) 0 (fun _ : Fin r =>  1) i := by
    induction i using Fin.cases with
    | zero =>  simp
    | succ i =>  simp
  have hr : Fin.snoc (α := fun _ =>  ℕ) (fun h =>  (a h).val) 0 i  ≤ 
      2*Fin.snoc (α := fun _ =>  ℕ) (fun _ : Fin r =>  1) 0 i := by
    induction i using Fin.lastCases with
    | last =>  simp
    | cast i =>  simpa using Nat.le_of_lt_succ (a i).isLt
  dsimp [shiftGapExtra,gapIncidence]
  omega

/-- A unit positional shift changes each actual rank gap by at most two. -/
theorem tupleGap_shifted_close {n r : ℕ} (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (a : Fin r → Fin 3) (i : Fin (r+1)) :
    |(tupleGap (shiftedTag p hp a) i:ℝ)-(tupleGap p i:ℝ)| ≤ 2 := by
  rw [tupleGap_shifted,Nat.cast_add,Nat.cast_sub (gapIncidence_le p hp i)]
  have hi : (gapIncidence r i:ℝ) ≤ 2 := by exact_mod_cast gapIncidence_le_two r i
  have he : (shiftGapExtra a i:ℝ) ≤ 2*(gapIncidence r i:ℝ) := by exact_mod_cast shiftGapExtra_le a i
  have h0 : (0:ℝ) ≤ shiftGapExtra a i := by positivity
  apply abs_le.mpr
  constructor  <;>  linarith

theorem period_shifted_gap_rounding {u m r : ℕ} (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (a : Fin r → Fin 3) (i : Fin (r+1)) :
    |(tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)-
      (m:ℝ)*coarsePeriodGap j.val i/2| ≤ 6 := by
  have ht := abs_sub_le (tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)
    (tupleGap (periodSlot off ∘ j.val) i:ℝ) ((m:ℝ)*coarsePeriodGap j.val i/2)
  have h1 := tupleGap_shifted_close (periodSlot off ∘ j.val) hsafe a i
  have h2 := period_gap_rounding hr off hoff hdiff j.val j.property i
  linarith

theorem coarse_outside_implies_gap_tail {z g c θ m : ℝ}
    (hθ : θ ∈ Set.Icc 0 1) (hm : 128 ≤ m) (hg : |g-m*c/2| ≤ 6)
    (hz : m/8 ≤ |z-θ*m*c/2|) : m/16 ≤ |z-g*θ| := by
  have he : |g*θ-θ*m*c/2| ≤ 6 := by
    have h := mul_le_mul_of_nonneg_right hg hθ.1
    rw [show g*θ-θ*m*c/2=(g-m*c/2)*θ by ring,abs_mul,abs_of_nonneg hθ.1]
    exact h.trans (by nlinarith [hθ.2])
  have ht := abs_sub_le z (g*θ) (θ*m*c/2)
  linarith

/-- The manuscript's rank rectangles lose exponentially little mass for
 every bounded shift of a tagged tuple. -/
theorem period_shifted_outside_region {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (a : Fin r → Fin 3) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    (∑ v : IncreasingTuple l r,
      if PeriodRankRegion m θ j v then 0 else
        subsetRankKernel hl (shiftedTag (periodSlot off ∘ j.val) hsafe a) v.val)  ≤ 
      ((r+1:ℕ):ℝ)*θ^r /binomialMass (u*m) θ l *
        (2*Real.exp (-(m:ℝ)/(1024*u))) := by
  let p := shiftedTag (periodSlot off ∘ j.val) hsafe a
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have ht : (1/(32*(u:ℝ))) ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have : (1:ℝ) ≤ u := by exact_mod_cast hu
      linarith
  have hx : -(1/(32*(u:ℝ)))*((m:ℝ)/16)+((u*m:ℕ):ℝ)*(1/(32*(u:ℝ)))^2 =
      -(m:ℝ)/(1024*u) := by push_cast; field_simp; ring
  calc
    _  ≤  ∑ v : IncreasingTuple l r,
      if ∃ i, (m:ℝ)/16 ≤ |(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : PeriodRankRegion m θ j v
      · simp only [ite_eq_left hv]
        split_ifs
        · exact subsetRankKernel_nonneg hl p v.val
        · rfl
      · simp only [PeriodRankRegion,not_forall,not_lt] at hv
        obtain ⟨i,hi⟩ := hv
        have he : ∃ i', (m:ℝ)/16 ≤ |(tupleGap v.val i':ℝ)-(tupleGap p i':ℝ)*θ| :=
          ⟨i.castSucc,coarse_outside_implies_gap_tail ⟨hθ.1.le,hθ.2.le⟩
            (by exact_mod_cast hm) (period_shifted_gap_rounding hr off hoff hdiff j hsafe a i.castSucc) hi⟩
        rw [ite_eq_left he]
        split_ifs
        · exact subsetRankKernel_nonneg hl p v.val
        · rfl
    _  ≤  _ := by
      have hh := subsetRankKernel_outside_region hl p (shiftedTag_strictMono _ hsafe a) hθ ht (a := (m:ℝ)/16)
      simpa only [hx] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem prouhet_motif_value (s : ℕ) (z : ℤ) :
    IsMotifValue (motifIndicator s z) ((prouhetSeries s).coeff z) := by
  by_cases hz : 0 ≤ z ∧ z < (2^s : ℕ)
  · right
    refine ⟨by simp only [motifIndicator,ite_eq_left hz], ?_⟩
    have hv := (prouhetSeries_coeff_spec s).2 z hz.1 hz.2
    exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv
  · left
    refine ⟨by simp only [motifIndicator,ite_eq_right hz], ?_⟩
    apply (prouhetSeries_coeff_spec s).1 z
    omega

theorem motif_weight_abs_le (χ β : ℝ) (h : IsMotifValue χ β) (k : GapDifference) :
    |motifDifferenceWeight χ β 1 k| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [motifDifferenceWeight]

theorem motif_weight_abs_le_indicator (χ β : ℝ) (h : IsMotifValue χ β)
    (k : GapDifference) (hk : k ≠ .unchanged) :
    |motifDifferenceWeight χ β 1 k| ≤ χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [motifDifferenceWeight] at *

theorem motif_linear_multiplier {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (h : Fin r) :
    motifPatternMultiplier π s j (linearPattern h)=
      (prouhetSeries s * π).coeff (j h) := by
  classical
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro X _
  congr 1
  have hw (a : Fin r) : motifDifferenceWeight (motifIndicator s (j a-X))
      ((prouhetSeries s).coeff (j a-X)) 1 (linearPattern h a)=
      if a=h then (prouhetSeries s).coeff (j h-X) else 1 := by
    by_cases ha : a=h <;> simp [linearPattern,ha,motifDifferenceWeight]
  simp_rw [hw]
  simp [sub_eq_neg_add]

theorem motifPatternMultiplier_abs_le {r : ℕ} (π : IntSeries)
    (hπ : ∀ X, 0 ≤ π.coeff X) (s : ℕ) (j : Fin r → ℤ)
    (k : Fin r → GapDifference) (h : Fin r) (hk : k h ≠ .unchanged) :
    |motifPatternMultiplier π s j k| ≤
      ∑ X ∈ π.coeff.support, π.coeff X*motifIndicator s (j h-X) := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro X _
  rw [abs_mul,abs_of_nonneg (hπ X),Finset.abs_prod]
  apply mul_le_mul_of_nonneg_left _ (hπ X)
  have hi (a) := motif_weight_abs_le _ _ (prouhet_motif_value s (j a-X)) (k a)
  have hh := motif_weight_abs_le_indicator _ _ (prouhet_motif_value s (j h-X)) (k h) hk
  calc
    _ ≤ ∏ a : Fin r, if a=h then motifIndicator s (j h-X) else 1 := by
      apply Finset.prod_le_prod
      · intro a _; positivity
      · intro a _
        by_cases ha : a=h
        · subst a; simpa using hh
        · simpa [ha] using hi a
    _ = _ := by simp

/-- A nonzero averaged pattern requires every involved tagged position to
 lie in one common translate of the motif; correlations are retained. -/
theorem motif_multiplier_nonzero_support {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference)
    (hm : motifPatternMultiplier π s j k ≠ 0) :
    ∃ X ∈ π.coeff.support, ∀ h, k h ≠ .unchanged →
      0 ≤ j h-X ∧ j h-X < (2^s : ℕ) := by
  classical
  obtain ⟨X,hX,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨X,hX,?_⟩
  intro h hk
  by_contra hh
  apply hv
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ h)
  have hi : motifIndicator s (j h-X)=0 := by simp only [motifIndicator,ite_eq_right hh]
  have hw := motif_weight_abs_le_indicator _ _ (prouhet_motif_value s (j h-X)) (k h) hk
  exact abs_nonpos_iff.mp (hw.trans_eq hi)

theorem motif_multiplier_bounded_separation {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference)
    (hm : motifPatternMultiplier π s j k ≠ 0)
    (a b : Fin r) (ha : k a ≠ .unchanged) (hb : k b ≠ .unchanged) :
    |j a-j b| < (2^s : ℕ) := by
  obtain ⟨X,_,hX⟩ := motif_multiplier_nonzero_support π s j k hm
  have h1 := hX a ha
  have h2 := hX b hb
  exact abs_lt.mpr ⟨by omega,by omega⟩

/-- Mixing commutes with the exact signed positional expansion. -/
theorem mixed_signed_shift_expansion {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (W : (Fin r → Fin 3) → ℝ) :
    (∑ X ∈ π.coeff.support, π.coeff X *
      (W (fun h => motifShift (motifIndicator s (j h-X)) ((prouhetSeries s).coeff (j h-X)) 1)-
       W (fun h => motifShift (motifIndicator s (j h-X)) ((prouhetSeries s).coeff (j h-X)) (-1))))=
      ∑ k : Fin r → GapDifference,
        (if Odd (firstDifferenceCount k) then 2*motifPatternMultiplier π s j k else 0)*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  calc
    _ = ∑ X ∈ π.coeff.support, ∑ k : Fin r → GapDifference,
        π.coeff X*((if Odd (firstDifferenceCount k) then
          2*∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
            ((prouhetSeries s).coeff (j h-X)) 1 (k h) else 0)*
          (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a)) := by
      apply Finset.sum_congr rfl
      intro X _
      rw [motif_signed_shift_expansion _ _ (fun h => prouhet_motif_value s (j h-X)) W,
        Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : Odd (firstDifferenceCount k)
      · simp only [ite_eq_left hk,motifPatternMultiplier]
        calc
          _ = (∑ X ∈ π.coeff.support, 2*(π.coeff X *
                ∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
                  ((prouhetSeries s).coeff (j h-X)) 1 (k h))) *
              (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro X _; ring
          _ = _ := by rw [← Finset.mul_sum]
      · simp only [ite_eq_right hk,zero_mul,mul_zero,Finset.sum_const_zero]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A general weighted fiber sum, including multipliers which vanish on
 inadmissible anchor labels. -/
theorem weighted_fiber_sum_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (a : α → ℝ) (w : β → ℝ) (P : α → ℝ) (C : ℝ)
    (hP : ∀ x, 0 ≤ P x) (ha : ∀ x, a x^2 ≤ w (f x)^2)
    (hC : ∀ y, w y ≠ 0 → (∑ x : {x // f x=y}, P x.val) ≤ C) :
    (∑ x, a x^2*P x) ≤ C*∑ y, w y^2 := by
  classical
  calc
    _ ≤ ∑ x, w (f x)^2*P x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (ha x) (hP x)
    _ = ∑ y, w y^2*∑ x : {x // f x=y}, P x.val := by
      rw [← Fintype.sum_fiberwise f (fun x => w (f x)^2*P x)]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [x.property]
    _ ≤ ∑ y, w y^2*C := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : w y=0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (hC y hy) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem weighted_period_gap_sum {u r : ℕ} (a : Fin r)
    (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ j : IncreasingTuple u r, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) ≤
      periodCentralSumConstant u r *∑ h, w h^2 := by
  apply weighted_fiber_sum_le (fun j : IncreasingTuple u r => j.val a) A w
    (fun j => ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹)
    (periodCentralSumConstant u r) (fun _ => by positivity) hA
  intro h hh
  calc
    _ = ∑ j : FixedPeriodTuple u r a h,
        ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ :=
      by
        congr 1
        exact congrArg (fun i : Fintype (FixedPeriodTuple u r a h) => @Finset.univ _ i)
          (Subsingleton.elim _ _)
    _ ≤ _ := fixedPeriodProfile_central_sum a h (hw h hh).1 (hw h hh).2

/-- The two largest gaps exist even after arbitrary restrictions on the
 tuple, provided its anchor label is central. -/
theorem fixedPeriodProfile_large_sides {u r : ℕ} (a : Fin r) (h : Fin u)
    (hleft : (u:ℝ)/3 ≤ 2*h.val+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (j : FixedPeriodTuple u r a h) :
    (∃ e ∈ Finset.Iic a.castSucc, (u:ℝ)/(3*(r+1:ℝ)) ≤ (fixedPeriodProfile a h j e).val) ∧
    (∃ d ∉ Finset.Iic a.castSucc, (u:ℝ)/(3*(r+1:ℝ)) ≤ (fixedPeriodProfile a h j d).val) := by
  classical
  let A := Finset.Iic a.castSucc
  let p := fixedPeriodProfile a h
  have hL : ∃ e∈A, (u:ℝ)/(3*(r+1:ℝ)) ≤ (p j e).val := by
    apply exists_large_in_subset A ⟨0, by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Nat.cast_nonneg _)
    have hs := fixedPeriodProfile_prefix a h j
    have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
    rw [hs']
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    convert hleft using 1; field_simp
  have hD : ∃ d∉A, (u:ℝ)/(3*(r+1:ℝ)) ≤ (p j d).val := by
    have ha : a.val < r := a.isLt
    have hlast : Fin.last r∈Aᶜ := by simp [A]
    obtain ⟨d,hd,hdR⟩ := exists_large_in_subset Aᶜ ⟨Fin.last r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Nat.cast_nonneg _) (R := (u:ℝ)/(3*(r+1:ℝ))) (by
        have hs := fixedPeriodProfile_prefix a h j
        have ht := fixedPeriodProfile_total a h j
        have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
        have ht' : (∑ i, ((p j i).val:ℝ))=2*u := by exact_mod_cast ht
        have hc := Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum : (∑ i∈Aᶜ, ((p j i).val:ℝ))=2*u-(2*h.val+1) := by linarith
        rw [hsum]
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  exact ⟨hL,hD⟩

/-- Source's bounded gap refinement at a prescribed central label. -/
theorem fixedPeriodProfile_bounded_central_sum {u r M : ℕ} (a : Fin r) (h : Fin u)
    (c : Fin (r+1)) (hleft : (u:ℝ)/3 ≤ 2*h.val+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j : FixedPeriodTuple u r a h,
      if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0) ≤
      ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Real.sqrt (2*u:ℕ))^(r-2) := by
  classical
  let α := {j : FixedPeriodTuple u r a h // coarsePeriodGap j.val.val c ≤ M}
  let p (j : α) := fixedPeriodProfile a h j.val
  have hu : (0:ℝ) < u := by exact_mod_cast (Nat.zero_lt_of_lt h.isLt)
  have hR : 0 < (u:ℝ)/(3*(r+1:ℝ)) := by positivity
  have hs := two_sided_bounded_gaps_sum (Finset.Iic a.castSucc) c p
    ((fixedPeriodProfile_injective a h).comp Subtype.val_injective)
    (fun j => fixedPeriodProfile_prefix a h j.val)
    (fun j => fixedPeriodProfile_total a h j.val) hR hM
    (fun j => (fixedPeriodProfile_large_sides a h hleft hright j.val).1)
    (fun j => (fixedPeriodProfile_large_sides a h hleft hright j.val).2)
    (fun j => j.property)
  have he : (∑ j : FixedPeriodTuple u r a h,
      if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0)=
      ∑ j : α, ∏ i, (Real.sqrt (coarsePeriodGap j.val.val.val i))⁻¹ := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro j; simp) _
  rw [he]
  simpa only [α,p,fixedPeriodProfile,Fin.val_mk,Fintype.card_fin,
    show r+1-3=r-2 by omega] using hs

theorem weighted_period_bounded_gap_sum {u r M : ℕ} (a : Fin r) (c : Fin (r+1))
    (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hsupport : ∀ j, A j ≠ 0 → coarsePeriodGap j.val c ≤ M)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j : IncreasingTuple u r, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) ≤
      periodBoundedSumConstant u r M *∑ h, w h^2 := by
  have hp (j : IncreasingTuple u r) :
      A j^2*(∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹)=
      A j^2*(if coarsePeriodGap j.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ else 0) := by
    by_cases hj : A j=0
    · simp [hj]
    · rw [ite_eq_left (hsupport j hj)]
  simp_rw [hp]
  apply weighted_fiber_sum_le (fun j : IncreasingTuple u r => j.val a) A w
    (fun j => if coarsePeriodGap j.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ else 0)
    (periodBoundedSumConstant u r M) (fun _ => by split_ifs <;> positivity) hA
  intro h hh
  calc
    _ = ∑ j : FixedPeriodTuple u r a h,
        if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0 :=
      by
        congr 1
        exact congrArg (fun i : Fintype (FixedPeriodTuple u r a h) => @Finset.univ _ i)
          (Subsingleton.elim _ _)
    _ ≤ _ := fixedPeriodProfile_bounded_central_sum a h c (hw h hh).1 (hw h hh).2 hM

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
open scoped Classical

theorem seriesL2Sq_partial {α : Type*} [Fintype α] (f : IntSeries)
    (j : α → ℤ) (hj : Function.Injective j) :
    (∑ a, f.coeff (j a)^2) ≤ seriesL2Sq f := by
  classical
  let A := Finset.univ.image j
  have he : (∑ a, f.coeff (j a)^2)=∑ z∈A, f.coeff z^2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hj h
  rw [he]
  calc
    _ ≤ ∑ z∈f.coeff.support ∪ A, f.coeff z^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      rw [seriesL2Sq_eq_sum]
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro z _ hz
      simp [Finsupp.notMem_support_iff.mp hz]

/-- The cancellation estimate after disjoint rank clipping, retaining the
 actual fixed-period kernels and all anchor correlations. -/
theorem period_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe : ∀ j : IncreasingTuple u r, SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hhalf : 1/2 ≤ θ) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a : Fin r) (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then
      A j*positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        periodCentralSumConstant u r * ∑ h, w h^2 := by
  have hC : 0 ≤ periodDifferencePrefactor u m r (∑ h, (k h).order) θ := by
    unfold periodDifferencePrefactor lengthDifferenceConstant
    positivity
  calc
    _ ≤ ∑ j, A j^2*∑ v, positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      period_clipped_square_sum (by omega) hhalf _ A
    _ ≤ ∑ j, A j^2*(periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (period_positionalRankDifference_bound hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∑ j, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (weighted_period_gap_sum a A w hA hw) hC

theorem period_pattern_bounded_norm {u m l r M : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe : ∀ j : IncreasingTuple u r, SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hhalf : 1/2 ≤ θ) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a : Fin r) (c : Fin (r+1)) (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hsupport : ∀ j, A j ≠ 0 → coarsePeriodGap j.val c ≤ M)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then
      A j*positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        periodBoundedSumConstant u r M * ∑ h, w h^2 := by
  have hC : 0 ≤ periodDifferencePrefactor u m r (∑ h, (k h).order) θ := by
    unfold periodDifferencePrefactor lengthDifferenceConstant
    positivity
  calc
    _ ≤ ∑ j, A j^2*∑ v, positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      period_clipped_square_sum (by omega) hhalf _ A
    _ ≤ ∑ j, A j^2*(periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (period_positionalRankDifference_bound hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∑ j, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (weighted_period_bounded_gap_sum a c A w hA hsupport hw hM) hC

/-- Two involved motif positions force a short *fixed* internal coarse gap.
 The chosen gap is independent of the actual labels and of the offset law. -/
theorem motif_pattern_bounded_gap {u r : ℕ} (π : IntSeries) (s : ℕ)
    (j : IncreasingTuple u (r+1)) (k : Fin (r+1) → GapDifference)
    (i : Fin r) (b : Fin (r+1)) (hib : i.castSucc < b)
    (hi : k i.castSucc ≠ .unchanged) (hb : k b ≠ .unchanged)
    (hA : motifPatternMultiplier π s (fun a => (j.val a).val) k ≠ 0) :
    coarsePeriodGap j.val i.castSucc.succ ≤ 2*(2^s) := by
  have hs := motif_multiplier_bounded_separation π s (fun a => (j.val a).val) k hA i.castSucc b hi hb
  have hj1 := j.property (show i.castSucc < i.succ by exact Fin.castSucc_lt_succ)
  have hj2 := j.property.monotone (show i.succ ≤ b by simpa only [Fin.le_iff_val_le_val,Fin.lt_def,
    Fin.val_succ,Fin.val_castSucc] using (Nat.succ_le_of_lt hib))
  have h1 : (j.val i.castSucc).val < (j.val i.succ).val := hj1
  have h2 : (j.val i.succ).val ≤ (j.val b).val := hj2
  have hh := (abs_lt.mp hs).1
  rw [coarsePeriodGap_middle]
  omega

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem geomSeries_coeff (k : ℕ) (z : ℤ) :
    (geomSeries k).coeff z = if 0 ≤ z ∧ z < k then 1 else 0 := by
  unfold geomSeries
  simp only [AddMonoidAlgebra.single_pow,one_pow,nsmul_eq_mul,mul_one,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases hz : 0 ≤ z ∧ z < k
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
    rw [ite_eq_left hz,Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      exact ite_eq_right (by exact_mod_cast hb)
    · intro ha
      have ha' : a < k := by exact_mod_cast hz.2
      exact (ha (Finset.mem_range.mpr ha')).elim
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    intro haz
    subst z
    exact hz ⟨by positivity,by exact_mod_cast Finset.mem_range.mp ha⟩

theorem motif_unsigned_convolution (π : IntSeries) (s : ℕ) (z : ℤ) :
    (∑ X ∈ π.coeff.support, π.coeff X*motifIndicator s (z-X)) =
      (geomSeries (2^s)*π).coeff z := by
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [geomSeries_coeff]
  simp only [motifIndicator,sub_eq_neg_add]

theorem motifPatternMultiplier_sq_le {r : ℕ} (π : IntSeries)
    (hπ : ∀ X, 0 ≤ π.coeff X) (s : ℕ) (j : Fin r → ℤ)
    (k : Fin r → GapDifference) (h : Fin r) (hk : k h ≠ .unchanged) :
    (motifPatternMultiplier π s j k)^2 ≤ ((geomSeries (2^s)*π).coeff (j h))^2 := by
  have ha := motifPatternMultiplier_abs_le π hπ s j k h hk
  rw [motif_unsigned_convolution] at ha
  have hh := pow_le_pow_left₀ (abs_nonneg (motifPatternMultiplier π s j k)) ha 2
  simpa only [sq_abs] using hh

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem signedPeriodDefects_strictMono {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) : StrictMono (signedPeriodDefects off hsafe s X τ) :=
  shiftedTag_strictMono _ _ _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem fairSeries_support (g : ℕ) (z : ℤ) (hz : (fairSeries g).coeff z ≠ 0) :
    0≤z ∧ z≤g := by
  have h0 : 0≤z := by
    by_contra h
    exact hz (fairSeries_coeff_neg g z (by omega))
  obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le h0
  refine ⟨by positivity,?_⟩
  by_contra hk
  rw [fairSeries_coeff_nat,fairBinomial,Nat.choose_eq_zero_of_lt (by omega)] at hz
  simp at hz

theorem translated_binomial_support (g : ℕ) (c z : ℤ)
    (hz : (translateSeries c (fairSeries g)).coeff z ≠ 0) :
    c≤z ∧ z ≤ c+g := by
  rw [translateSeries_coeff] at hz
  have h := fairSeries_support g (z-c) hz
  omega

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem linearPattern_order {r : ℕ} (a : Fin r) :
    (∑ h, ((linearPattern a) h).order)=1 := by
  classical
  have he (h : Fin r) : ((linearPattern a) h).order=if h=a then 1 else 0 := by
    by_cases hh : h=a <;> simp [linearPattern,hh,GapDifference.order]
  simp_rw [he]
  simp

theorem odd_pattern_pair {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    ∃ a b : Fin r, a<b ∧ k a≠.unchanged ∧ k b≠.unchanged := by
  classical
  have hp : 0<firstDifferenceCount k := hk.pos
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  have ha' : k a=.first := (Finset.mem_filter.mp ha).2
  by_contra hh
  push Not at hh
  apply hnl
  refine ⟨a,funext fun b => ?_⟩
  by_cases hb : b=a
  · subst b; simp [linearPattern,ha']
  · have hba : k b=.unchanged := by
      rcases lt_or_gt_of_ne hb with hba|hab
      · by_contra hb'
        exact (show k a≠.unchanged by simp [ha']) (hh b a hba hb')
      · exact hh a b hab (by simp [ha'])
    simp [linearPattern,hb,hba]

/-- An actual convolution witness, retaining the common motif offset. -/
theorem motif_convolution_support (f π : IntSeries) (L : ℕ)
    (hf : ∀z, f.coeff z≠0 → 0≤z ∧ z<L) (z : ℤ) (hz : (f*π).coeff z≠0) :
    ∃X∈π.coeff.support, X≤z ∧ z<X+L := by
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum] at hz
  obtain ⟨X,hX,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hh := hf (-X+z) (mul_ne_zero_iff.mp hv).2
  exact ⟨X,hX,by omega,by omega⟩

theorem motif_convolution_central {u s : ℕ} (π f : IntSeries)
    (hπ : CentralMotifSupport u s π)
    (hf : ∀z, f.coeff z≠0 → 0≤z ∧ z<(2^s:ℕ))
    (h : Fin u) (hh : (f*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  obtain ⟨X,hX,hL,hR⟩ := motif_convolution_support f π (2^s) hf h.val hh
  have hL' : (X:ℝ)≤h.val := by exact_mod_cast hL
  have hR' : (h.val:ℝ)<(X:ℝ)+(2:ℝ)^s := by exact_mod_cast hR
  have hs := hπ X hX
  constructor <;> linarith

theorem prouhet_convolution_central {u s : ℕ} (π : IntSeries)
    (hπ : CentralMotifSupport u s π) (h : Fin u)
    (hh : (prouhetSeries s*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  apply motif_convolution_central π _ hπ _ h hh
  intro z hz
  constructor
  · by_contra h; exact hz ((prouhetSeries_coeff_spec s).1 z (Or.inl (by omega)))
  · by_contra h; exact hz ((prouhetSeries_coeff_spec s).1 z (Or.inr (by omega)))

theorem unsigned_convolution_central {u s : ℕ} (π : IntSeries)
    (hπ : CentralMotifSupport u s π) (h : Fin u)
    (hh : (geomSeries (2^s)*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  apply motif_convolution_central π _ hπ _ h hh
  intro z hz
  by_contra hs
  rw [geomSeries_coeff,ite_eq_right hs] at hz
  exact hz rfl

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
namespace TraceReconstruction
open scoped Classical

theorem signedPeriodDefects_comp {u m r : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : IncreasingTuple u r) :
    signedPeriodDefects off hsafe s X τ ∘ j.val =
      shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property)
        (fun i => motifShift (motifIndicator s ((j.val i).val-X))
          ((prouhetSeries s).coeff ((j.val i).val-X)) τ) := by
  funext i; apply Fin.ext; rfl

theorem signedRankCoefficient_tuple_sum {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (v : IncreasingTuple l r) :
    signedRankCoefficient hl off hsafe π s v=∑j, signedTupleKernel hl off hsafe π s j v := by
  unfold signedRankCoefficient signedTupleKernel
  simp_rw [rankDefectCoefficient_eq _ _ (signedPeriodDefects_strictMono _ _ _ _ _),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_comm

theorem signedTupleKernel_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (j : IncreasingTuple u r) (v : IncreasingTuple l r) :
    signedTupleKernel hl off hsafe π s j v = ∑k : Fin r → GapDifference,
      if Odd (firstDifferenceCount k) then
        2*motifPatternMultiplier π s (fun i => (j.val i).val) k *
          positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
            (hsafe.comp j.val j.property) k v else 0 := by
  unfold signedTupleKernel
  simp_rw [signedPeriodDefects_comp]
  have H := mixed_signed_shift_expansion π s (fun i => (j.val i).val)
    (fun a => subsetRankKernel hl
      (shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property) a) v.val)
  simpa only [ite_mul,zero_mul,positionalRankDifference] using H

theorem clippedSignedRankCoefficient_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) :
    clippedSignedRankCoefficient hl off hsafe π s θ v =
      2*∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        clippedPatternCoefficient hl off hsafe π s θ k v else 0 := by
  unfold clippedSignedRankCoefficient clippedPatternCoefficient
  have he (j : IncreasingTuple u r) :
      (if PeriodRankRegion m θ j v then signedTupleKernel hl off hsafe π s j v else 0) =
      ∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        (if PeriodRankRegion m θ j v then
          2*motifPatternMultiplier π s (fun i => (j.val i).val) k *
            positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0) else 0 := by
    by_cases hv : PeriodRankRegion m θ j v
    · simp only [ite_eq_left hv, signedTupleKernel_expansion]
    · simp [hv]
  simp_rw [he]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : Odd (firstDifferenceCount k)
  · simp only [ite_eq_left hk,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  · simp [hk]

/-- Removing coarse rank rectangles loses an explicitly exponentially
 small amount in the actual coefficient, before any finite differences. -/
theorem signedTupleKernel_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2|≤3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0≤π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (j : IncreasingTuple u r) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else
      |signedTupleKernel hl off hsafe π s j v|) ≤
      2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) := by
  let K (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) :=
    subsetRankKernel hl (signedPeriodDefects off hsafe s X τ ∘ j.val) v.val
  let B := ((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))
  have hK (X : ℤ) (τ : ℝ) : (∑v : IncreasingTuple l r,
      if PeriodRankRegion m θ j v then 0 else K X τ v)≤B := by
    simp_rw [K,signedPeriodDefects_comp]
    exact period_shifted_outside_region hu hm hr hl (fun _ => off) (fun _ => hoff)
      (by intro _ _; simp) j (hsafe.comp j.val j.property) _ hθ
  have hnon (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) : 0≤K X τ v :=
    subsetRankKernel_nonneg _ _ _
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑X∈π.coeff.support, π.coeff X*
        (if PeriodRankRegion m θ j v then 0 else K X 1 v+K X (-1) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : PeriodRankRegion m θ j v
      · simp [hv]
      · simp only [ite_eq_right hv]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro X _
        rw [abs_mul,abs_of_nonneg (hπ X)]
        apply mul_le_mul_of_nonneg_left _ (hπ X)
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hnon X 1 v),abs_of_nonneg (hnon X (-1) v)])
    _ = ∑X∈π.coeff.support, π.coeff X*((∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else K X 1 v)+
        (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else K X (-1) v)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      rw [← Finset.mul_sum,← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl
      intro v _; split_ifs <;> ring
    _ ≤ ∑X∈π.coeff.support, π.coeff X*(B+B) := by
      apply Finset.sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_left (add_le_add (hK X 1) (hK X (-1))) (hπ X)
    _ = _ := by rw [← Finset.sum_mul,hπsum]; dsimp [B]; ring

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem motif_pattern_common_short_gap {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    ∃ a : Fin r, k a≠.unchanged ∧ ∃c : Fin (r+1), ∀ {u s : ℕ} (π : IntSeries)
      (j : IncreasingTuple u r),
      motifPatternMultiplier π s (fun h => (j.val h).val) k≠0 →
        coarsePeriodGap j.val c ≤ 2*(2^s) := by
  obtain ⟨a,b,hab,ha,hb⟩ := odd_pattern_pair k hk hnl
  cases r with
  | zero => exact Fin.elim0 a
  | succ r =>
    have har : a.val < r := by have := b.isLt; exact lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)
    let i : Fin r := ⟨a.val,har⟩
    have hi : i.castSucc=a := by ext; rfl
    refine ⟨a,ha,i.castSucc.succ,?_⟩
    intro u s π j hj
    apply motif_pattern_bounded_gap π s j k i b
    · simpa only [hi] using hab
    · simpa only [hi] using ha
    · exact hb
    · exact hj

theorem clipped_linear_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (a : Fin r) :
    (∑v, (clippedPatternCoefficient hl off hsafe π s θ (linearPattern a) v)^2)  ≤ 
      periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r *
        seriesL2Sq (prouhetSeries s*π) := by
  have hb := period_pattern_norm hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) (linearPattern a)
    hθ hhalf hmean hv a
    (fun j => motifPatternMultiplier π s (fun i => (j.val i).val) (linearPattern a))
    (fun h => (prouhetSeries s*π).coeff h.val)
    (by intro j; rw [motif_linear_multiplier])
    (prouhet_convolution_central π hcentral)
  rw [linearPattern_order] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (seriesL2Sq_partial _ (fun h : Fin u => (h.val:ℤ)) (by intro a b h; apply Fin.ext; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold periodDifferencePrefactor lengthDifferenceConstant periodCentralSumConstant
  positivity

theorem clipped_nonlinear_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (k : Fin r → GapDifference) (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a)
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v, (clippedPatternCoefficient hl off hsafe π s θ k v)^2)  ≤ 
      periodDifferencePrefactor u m r (∑h, (k h).order) θ *
        periodBoundedSumConstant u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π) := by
  obtain ⟨a,ha,c,hc⟩ := motif_pattern_common_short_gap k hk hnl
  have hb := period_pattern_bounded_norm hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) k
    hθ hhalf hmean hv a c
    (fun j => motifPatternMultiplier π s (fun i => (j.val i).val) k)
    (fun h => (geomSeries (2^s)*π).coeff h.val)
    (fun j => motifPatternMultiplier_sq_le π hπ s _ k a ha)
    (fun j hj => hc π j hj) (unsigned_convolution_central π hcentral) hM
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (seriesL2Sq_partial _ (fun h : Fin u => (h.val:ℤ)) (by intro a b h; apply Fin.ext; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold periodDifferencePrefactor lengthDifferenceConstant periodBoundedSumConstant
  positivity

theorem sum_square_card_bound {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    (∑ b, (∑a, f a b)^2)  ≤  (Fintype.card α:ℝ)*∑a, ∑b, f a b^2 := by
  calc
    _  ≤  ∑b, (Fintype.card α:ℝ)*∑a, f a b^2 := by
      apply Finset.sum_le_sum
      intro b _
      have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun a => f a b) (f := fun _ => (1:ℝ)) (g := fun a => f a b^2)
        (by intro _ _; norm_num) (by intro _ _; positivity) (by intro _ _; simp)
      simpa using h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem clipped_signed_initial_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v : IncreasingTuple l r, (clippedSignedRankCoefficient hl off hsafe π s θ v)^2)  ≤ 
      4*(Fintype.card (Fin r → GapDifference):ℝ)*
        ∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0 := by
  simp_rw [clippedSignedRankCoefficient_expansion,mul_pow,show (2:ℝ)^2=4 by norm_num]
  rw [← Finset.mul_sum]
  calc
    _  ≤  4*((Fintype.card (Fin r → GapDifference):ℝ)*∑k : Fin r → GapDifference, ∑v : IncreasingTuple l r,
        (if Odd (firstDifferenceCount k) then clippedPatternCoefficient hl off hsafe π s θ k v else 0)^2) := by
      exact mul_le_mul_of_nonneg_left (sum_square_card_bound (fun (k : Fin r → GapDifference) (v : IncreasingTuple l r) =>
        if Odd (firstDifferenceCount k) then clippedPatternCoefficient hl off hsafe π s θ k v else 0)) (by norm_num)
    _  ≤  _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : Odd (firstDifferenceCount k)
      · simp only [ite_eq_left hk]
        unfold signedPatternBound
        split_ifs with hlin
        · obtain ⟨a,rfl⟩ := hlin
          exact clipped_linear_pattern_norm hm hr hl off hoff hsafe π s hcentral hθ hhalf hmean hv a
        · exact clipped_nonlinear_pattern_norm hm hr hl off hoff hsafe π hπ s hcentral
            hθ hhalf hmean hv k hk hlin hM
      · simp [hk]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem signedRankCoefficient_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, |signedRankCoefficient hl off hsafe π s v-
        clippedSignedRankCoefficient hl off hsafe π s θ v|) ≤
      (Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))) := by
  simp_rw [signedRankCoefficient_tuple_sum,clippedSignedRankCoefficient,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑j : IncreasingTuple u r,
        if PeriodRankRegion m θ j v then 0 else |signedTupleKernel hl off hsafe π s j v| := by
      apply Finset.sum_le_sum
      intro v _
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = ∑j : IncreasingTuple u r, ∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else |signedTupleKernel hl off hsafe π s j v| := Finset.sum_comm
    _ ≤ _ := by
      calc
        _ ≤ ∑j : IncreasingTuple u r,
            2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) :=
          Finset.sum_le_sum (fun j _ => signedTupleKernel_tail hu hm hr hl off hoff hsafe π hπ hπsum s j hθ)
        _ = _ := by simp

/-- A globally discarded l1 tail is also negligible in coefficient energy.
 This does not assume pointwise cancellation on the discarded ranks. -/
theorem finite_sum_sq_le_abs_sum_sq {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑a, f a^2) ≤ (∑a, |f a|)^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun a => |f a|)
    (by intro a _; exact abs_nonneg _)
  simpa only [sq_abs] using h

theorem initial_signed_energy {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v : IncreasingTuple l r, (signedRankCoefficient hl off hsafe π s v)^2) ≤
      8*(Fintype.card (Fin r → GapDifference):ℝ)*
        (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0) +
      2*((Fintype.card (IncreasingTuple u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2 := by
  let A : IncreasingTuple l r → ℝ := signedRankCoefficient hl off hsafe π s
  let C : IncreasingTuple l r → ℝ := clippedSignedRankCoefficient hl off hsafe π s θ
  have hn := clipped_signed_initial_norm (by omega) hr hl off hoff hsafe π hπ s hcentral hθ hhalf hmean hv hM
  have ht := signedRankCoefficient_tail hu hm hr hl off hoff hsafe π hπ hπsum s hθ
  have hE := (finite_sum_sq_le_abs_sum_sq (fun v : IncreasingTuple l r => A v-C v)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => abs_nonneg (A v-C v))) ht 2)
  have hsum : (∑v : IncreasingTuple l r, A v^2) ≤
      2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    nlinarith [sq_nonneg (A v-2*C v)]
  calc
    _ ≤ 2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := hsum
    _ ≤ _ := by dsimp [C] at *; linarith

end TraceReconstruction


noncomputable section
noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem mixedMotifCoefficient_rank_difference {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) :
    mixedMotifCoefficient hl off hsafe π s 1 (rankMask v)-
      mixedMotifCoefficient hl off hsafe π s (-1) (rankMask v)=
        signedRankCoefficient hl off hsafe π s v := by
  unfold mixedMotifCoefficient signedRankCoefficient
  simp_rw [averaged_rank_coefficient hl _ v]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro X _
  ring

end TraceReconstruction



noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem multilinear_scale {α : Type*} {n : ℕ} (A : (Fin n → Bool) → ℝ)
    (Z : α → ℝ) {L : ℝ} (hL : L≠0) (x : Fin n → α) :
    multilinear (scaleCoefficient A L) (fun a => Z a/L) x=multilinear A Z x := by
  unfold multilinear scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  exact mul_div_cancel₀ _ hL

theorem multilinearEnergy_scale {n : ℕ} (A : (Fin n → Bool) → ℝ) (L R : ℝ) :
    multilinearEnergy (scaleCoefficient A L) R=multilinearEnergy A (R*L) := by
  unfold multilinearEnergy scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_pow,← Finset.prod_pow,mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  ring

/-- The exact norm-of-input factor in the conditional leaf expansion. -/
theorem multilinear_moment_scaled {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => |multilinear A Z x|^(2*k)) ≤
      (multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L))^k := by
  have hcenter' : P.expect (fun a => Z a/L)=0 := by
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    change P.expect Z / L = 0
    rw [hcenter,zero_div]
  have hmoment' : P.expect (fun a => |Z a/L|^(2*k))≤1 := by
    simp_rw [abs_div,abs_of_pos hL,div_pow]
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    apply (div_le_one (by positivity)).mpr hMoment
  have H := multilinear_even_moment P (fun a => Z a/L) k hk hcenter' hmoment' n (scaleCoefficient A L)
  simp_rw [multilinear_scale A Z hL.ne',multilinearEnergy_scale] at H
  simpa only [pow_mul,sq_abs] using H

theorem multilinear_moment_sq_scaled {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).evenMomentSq (multilinear A Z) k ≤
      multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L) := by
  have H := multilinear_moment_scaled P Z k hk hcenter hL hMoment n A
  have hn : 0≤(P.product n).expect (fun x => |multilinear A Z x|^(2*k)) := by
    exact Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product n).nonneg x) (by positivity))
  unfold FiniteLaw.evenMomentSq
  calc
    _ ≤ (multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L)^k)^(1/(k:ℝ)) :=
      Real.rpow_le_rpow hn H (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,one_div,Real.rpow_rpow_inv (multilinearEnergy_nonneg _ _) (by positivity)]

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



noncomputable section



noncomputable section



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem oneStepOffset_add_one {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) :
    (oneStepOffset off hi a).val+1=off.val+a.val := by
  dsimp [oneStepOffset]
  omega

theorem oneStepOffset_distance {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) :
    |((oneStepOffset off hi a).val:ℝ)-(off.val:ℝ)|  ≤  1 := by
  have he := oneStepOffset_add_one off hi a
  have ha : (a.val:ℝ)  ≤  2 := by exact_mod_cast (show a.val ≤ 2 by omega)
  have ha0 : (0:ℝ)  ≤  a.val := Nat.cast_nonneg _
  have he' : ((oneStepOffset off hi a).val:ℝ)+1=(off.val:ℝ)+a.val := by exact_mod_cast he
  rw [abs_le]
  constructor <;> linarith

theorem shifted_constantPeriod {u m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (a : Fin u → Fin 3) :
    shiftedTag (periodSlot (fun _ => off)) hsafe a =
      periodSlot (fun i => oneStepOffset off hi (a i)) := by
  funext i
  apply Fin.ext
  change i.val*m+off.val+(a i).val-1=i.val*m+(off.val+(a i).val-1)
  omega

/-- Arbitrary deterministic motif orientations remain genuine one-defect
periods with the exact geometry used in the high-degree rank bound. -/
theorem signedPeriod_geometry {u m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    ∃ off' : Fin u → Fin m,
      signedPeriodDefects off hsafe s X τ = periodSlot off' ∧
      (∀j, |((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3) ∧
      (∀j k, |((off' j).val:ℝ)-(off' k).val| ≤ 2) := by
  let a : Fin u → Fin 3 := fun j =>
    motifShift (motifIndicator s ((j.val:ℤ)-X)) ((prouhetSeries s).coeff ((j.val:ℤ)-X)) τ
  refine ⟨fun j => oneStepOffset off hi (a j),shifted_constantPeriod off hi hsafe a,?_,?_⟩
  · intro j
    have h := oneStepOffset_distance off hi (a j)
    have ht := abs_add_le (((oneStepOffset off hi (a j)).val:ℝ)-(off.val:ℝ))
      ((off.val:ℝ)-(m:ℝ)/2)
    rw [sub_add_sub_cancel] at ht
    linarith
  · intro j k
    have hj := oneStepOffset_distance off hi (a j)
    have hk := oneStepOffset_distance off hi (a k)
    rw [abs_le] at hj hk ⊢
    constructor <;> linarith


/-- Every moment of the actual primitive score has the source uniform
bound. -/
theorem primitive_score_evenMoment {q : ℝ} (hq : q∈Set.Ioo 0 1) (k : ℕ) :
    (primitiveMarkLaw q hq false).expect (fun z => |primitiveScore q z|^(2*k))  ≤ 
      (2/q)^(2*k) := by
  calc
    _  ≤  (primitiveMarkLaw q hq false).expect (fun _ => (2/q)^(2*k)) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (primitive_score_bound hq z) _) ((primitiveMarkLaw q hq false).nonneg z)
    _ = _ := (primitiveMarkLaw q hq false).expect_const _


/-- Jensen's inequality on each homogeneous degree. -/
theorem degree_square_mixture_le {Ω : Type*} [Fintype Ω] {n : ℕ}
    (P : FiniteLaw Ω) (A : Ω → (Fin n → Bool) → ℝ) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then
      (P.expect (fun ω => A ω σ))^2 else 0)  ≤ 
    P.expect (fun ω => ∑σ : Fin n → Bool,
      if monomialDegree σ=r then (A ω σ)^2 else 0) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro σ _
  by_cases h : monomialDegree σ=r
  · simp only [ite_eq_left h]
    have H := weighted_sum_sq_le Finset.univ P.mass (fun ω => A ω σ) (fun ω => P.nonneg ω)
    simpa only [P.total,one_mul] using H
  · simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero,le_refl]

theorem degree_square_sub_le {n : ℕ} (A B : (Fin n → Bool) → ℝ) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then (A σ-B σ)^2 else 0)  ≤ 
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0)+
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then B σ^2 else 0) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs <;> nlinarith [sq_nonneg (A σ+B σ)]

theorem mixedMotifCoefficient_expect {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) (σ : Fin l → Bool) :
    mixedMotifCoefficient hl off hsafe π s τ σ =
      (seriesProbabilityLaw π hπ hπsum).expect (fun X =>
        averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X.val τ))) σ) := by
  unfold mixedMotifCoefficient FiniteLaw.expect seriesProbabilityLaw
  exact (Finset.sum_coe_sort _ _).symm

theorem mixedMotifCoefficient_empty {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) (τ : ℝ) :
    mixedMotifCoefficient hl off hsafe π s τ (fun _ => false)=1 := by
  simp only [mixedMotifCoefficient,averagedCoefficient_empty,mul_one,hπsum]

/-- Uniform high-degree estimate after the real hidden-anchor mixture. -/
theorem mixedMotif_degree_le {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s τ σ)^2 else 0)  ≤ 
      ((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  simp_rw [mixedMotifCoefficient_expect hl off hsafe π hπ hπsum]
  refine (degree_square_mixture_le _ _ r).trans ?_
  calc
    _  ≤  (seriesProbabilityLaw π hπ hπsum).expect (fun _ =>
        ((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r) := by
      apply FiniteLaw.expect_mono
      intro X
      obtain ⟨d,hd,hnear,hclose⟩ := signedPeriod_geometry off hi hoff hsafe s X.val τ
      rw [hd]
      exact period_degree_square_sum hl hr hru hm hum hq hθ hmean hv d hnear hclose
    _ = _ := FiniteLaw.expect_const _ _

/-- There are never more selected ranks than actual defect periods, even
in the hidden-anchor mixture. -/
theorem mixedMotif_degree_vanish {u m l r : ℕ} (hl : l ≤ u*m) (hru : u < r) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s τ σ)^2 else 0)=0 := by
  apply le_antisymm
  · simp_rw [mixedMotifCoefficient_expect hl off hsafe π hπ hπsum]
    refine (degree_square_mixture_le _ _ r).trans ?_
    simp_rw [defect_degree_bound hl _ (signedPeriodDefects_strictMono off hsafe s _ τ) hru]
    rw [FiniteLaw.expect_const]
  · exact Finset.sum_nonneg (fun σ _ => by split_ifs <;> positivity)

/-- The signed difference has no constant term. -/
theorem signedMotif_degree_zero {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=0 then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)=0 := by
  simp_rw [monomialDegree_eq_zero_iff]
  simp [mixedMotifCoefficient_empty hl off hsafe π hπsum]

/-- Low-degree cancellation is for exactly the coefficients of the
conditional motif densities, without a rank surrogate at the boundary. -/
theorem signedMotif_degree_cancellation {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ)<(u:ℝ)/(3*(r+1:ℝ))) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)  ≤ 
      8*(Fintype.card (Fin r → GapDifference):ℝ)*
        (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0) +
      2*((Fintype.card (IncreasingTuple u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2 := by
  refine (sum_degree_coeff_sq_le _).trans ?_
  simp_rw [mixedMotifCoefficient_rank_difference]
  exact initial_signed_energy hu hm hr hl off hoff hsafe π hπ hπsum s hcentral
    hθ hhalf hmean hv hM

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A finite tail is no larger than the full geometric tail. -/
theorem finite_geometric_tail_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (N R : ℕ) :
    (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) ≤ a^R/(1-a) := by
  have ht : HasSum (fun n : ℕ => a^(n+R)) (a^R/(1-a)) := by
    simpa only [pow_add, mul_comm, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one ha ha1).mul_left (a^R)
  have hsum : (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) =
      ∑r ∈ (Finset.range N).filter (R ≤ ·), a^r := by
    rw [Finset.sum_filter]
  rw [hsum]
  calc
    _ = ∑r ∈ ((Finset.range N).filter (R ≤ ·)).image (fun r => r-R), a^(r+R) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [Nat.sub_add_cancel (Finset.mem_filter.mp hr).2]
      · intro r hr s hs h
        dsimp only at h
        have hrR := (Finset.mem_filter.mp hr).2
        have hsR := (Finset.mem_filter.mp hs).2
        omega
    _ ≤ _ := by
      rw [←ht.tsum_eq]
      exact ht.summable.sum_le_tsum _ (fun _ _ => by positivity)

/-- Splitting the exact homogeneous expansion, not a surrogate polynomial. -/
theorem multilinearEnergy_low_high {n R : ℕ} (A : (Fin n → Bool) → ℝ)
    (w a K : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (ha1 : a < 1) (hK : 0 ≤ K)
    (L : ℕ → ℝ)
    (hlow : ∀r < R, (∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0) ≤ L r)
    (hhigh : ∀r, R ≤ r → w^(2*r)*(∑σ : Fin n → Bool,
      if monomialDegree σ=r then A σ^2 else 0) ≤ K*a^r)
    (hL : ∀r, 0 ≤ L r) :
    multilinearEnergy A w ≤ (∑r ∈ Finset.range R, w^(2*r)*L r)+K*a^R/(1-a) := by
  rw [multilinearEnergy_degrees]
  calc
    _ ≤ ∑r ∈ Finset.range (n+1),
        ((if r < R then w^(2*r)*L r else 0)+(if R ≤ r then K*a^r else 0)) := by
      apply Finset.sum_le_sum
      intro r _
      by_cases h : r < R
      · simp only [ite_eq_left h,ite_eq_right (show ¬R ≤ r by omega),add_zero]
        exact mul_le_mul_of_nonneg_left (hlow r h) (by positivity)
      · simp only [ite_eq_right h,ite_eq_left (show R ≤ r by omega),zero_add]
        exact hhigh r (by omega)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      apply add_le_add
      · rw [←Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2)
          (fun r _ _ => mul_nonneg (by positivity) (hL r))
      · have he : (∑r ∈ Finset.range (n+1), if R ≤ r then K*a^r else 0)=
            K*∑r ∈ Finset.range (n+1), if R ≤ r then a^r else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          split_ifs <;> ring
        rw [he,mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (finite_geometric_tail_le ha ha1 _ _) hK

/-- The signed high-degree bound includes the true anchor mixture. -/
theorem signedMotif_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0) ≤
      4*(w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by
  have hw0 : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp : 0 ≤ 3*rankSchurConstant/q := by positivity [rankSchurConstant_pos,hq.1]
  have hb := degree_square_sub_le (mixedMotifCoefficient hl off hsafe π s 1)
    (mixedMotifCoefficient hl off hsafe π s (-1)) r
  by_cases hru : r ≤ u
  · have hplus := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s 1 hq hθ hmean hv
    have hminus := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s (-1) hq hθ hmean hv
    have hsqrt : Real.sqrt ((u:ℝ)/((m:ℝ)*r)) ≤ Real.sqrt ((u:ℝ)/m) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*(4*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [pow_mul]; positivity)
      _ ≤ w^(2*r)*(4*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r) := by
        gcongr
      _ = _ := by rw [pow_mul, mul_pow, mul_pow]; ring
  · rw [mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s 1,
      mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s (-1)] at hb
    have hz : (∑σ : Fin l → Bool, if monomialDegree σ=r then
        (mixedMotifCoefficient hl off hsafe π s 1 σ-
          mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)=0 := by
      apply le_antisymm (by linarith)
      exact Finset.sum_nonneg (fun σ _ => by split_ifs <;> positivity)
    rw [hz,mul_zero]
    positivity

theorem signedInitialDegreeBound_nonneg (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) :
    0 ≤ signedInitialDegreeBound u m r s π θ l := by
  unfold signedInitialDegreeBound
  split_ifs
  · exact le_rfl
  · apply add_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · unfold signedPatternBound
      split_ifs <;> apply mul_nonneg _ (seriesL2Sq_nonneg _)
      all_goals dsimp only [periodDifferencePrefactor, lengthDifferenceConstant, periodCentralSumConstant, periodBoundedSumConstant]
      all_goals positivity
    · exact le_rfl

/-- A fully finite norm estimate for the actual low and high degree pieces.
Only numerical admissible-count and geometric conditions remain to be chosen. -/
theorem signed_initial_full_energy {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : 0 ≤ w) (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    multilinearEnergy (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ) w ≤
      (∑r ∈ Finset.range R, w^(2*r)*signedInitialDegreeBound u m r s π θ l)+
        4*(w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^R /
          (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have hq2 : q^2 ≤ (1/4:ℝ) := by
    calc q^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hq.1.le hq.2 2
         _ = _ := by norm_num
  have hθ0 : θ∈Set.Ioo 0 1 := by constructor <;> nlinarith [hq.1,hθ.1,hθ.2]
  have hhalf : 1/2 ≤ θ := by nlinarith [hθ.1]
  apply multilinearEnergy_low_high _ w _ 4 hw (by positivity [rankSchurConstant_pos,hq.1]) ha
    (by norm_num) (signedInitialDegreeBound u m · s π θ l) _ _
    (fun r => signedInitialDegreeBound_nonneg _ _ _ _ _ _ _)
  · intro r hr
    by_cases hr0 : r=0
    · subst r
      rw [signedMotif_degree_zero hl off hsafe π hπsum s]
      exact signedInitialDegreeBound_nonneg _ _ _ _ _ _ _
    · have hMr : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ)) := by
        apply hM.trans_le
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show r+1 ≤ R+1 by omega)) (by norm_num)
      simpa only [signedInitialDegreeBound,ite_eq_right hr0] using
        signedMotif_degree_cancellation hu hm (Nat.pos_of_ne_zero hr0) hl off
          (hoff.trans (by norm_num)) hsafe π hπ hπsum s hcentral hθ0 hhalf hmean hv hMr
  · intro r hr
    exact signedMotif_degree_geometric hl (by omega) (by omega) hum off hi hoff hsafe π hπ
      hπsum s hq hθ hmean hv w

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem initialMotifLaw_withDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ =
      ((primitiveMarkLaw q hq false).product l).withDensity
        (initialMotifDensity hl off hsafe π s τ q)
        (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s τ hq)
        (initialMotifDensity_mean hl off hsafe π hπ hπsum s τ hq) := by
  apply FiniteLaw.ext
  funext x
  exact conditionalMotifLaw_density hl off hsafe hq π hπ hπsum s τ x

theorem multilinear_sub {α : Type*} {l : ℕ} (A B : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (fun σ => A σ-B σ) Z x = multilinear A Z x-multilinear B Z x := by
  simp only [multilinear,sub_mul,Finset.sum_sub_distrib]

theorem nonconstant_multilinear {α : Type*} {l : ℕ} (A : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (nonconstantCoefficient A) Z x=multilinear A Z x-A (fun _ => false) := by
  have he : ∀σ, nonconstantCoefficient A σ=A σ-(if σ=(fun _ => false) then A σ else 0) := by
    intro σ
    by_cases h : σ=(fun _ => false) <;> simp [nonconstantCoefficient,h]
  rw [show nonconstantCoefficient A = (fun σ => A σ-(if σ=(fun _ => false) then A σ else 0)) from funext he, multilinear_sub]
  congr 1
  simp [multilinear,ite_mul]

theorem nonconstant_degree_zero {l : ℕ} (A : (Fin l → Bool) → ℝ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=0 then (nonconstantCoefficient A σ)^2 else 0)=0 := by
  simp [monomialDegree_eq_zero_iff,nonconstantCoefficient]

theorem nonconstant_degree_pos {l r : ℕ} (A : (Fin l → Bool) → ℝ) (hr : 0 < r) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then (nonconstantCoefficient A σ)^2 else 0)=
      ∑σ : Fin l → Bool, if monomialDegree σ=r then (A σ)^2 else 0 := by
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ=(fun _ => false)
  · subst σ
    simp [monomialDegree,Ne.symm (Nat.ne_of_gt hr)]
  · simp [nonconstantCoefficient,h]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem mixedMotif_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool, if monomialDegree σ=r then
      mixedMotifCoefficient hl off hsafe π s τ σ^2 else 0) ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by
  have hw : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp : 0 ≤ 3*rankSchurConstant/q := by positivity [rankSchurConstant_pos,hq.1]
  by_cases hru : r ≤ u
  · have hb := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s τ hq hθ hmean hv
    have hsqrt : Real.sqrt ((u:ℝ)/((m:ℝ)*r)) ≤ Real.sqrt ((u:ℝ)/m) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r :=
        mul_le_mul_of_nonneg_left hb hw
      _ ≤ w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by gcongr
      _ = _ := by rw [pow_mul,mul_pow,mul_pow]; ring
  · rw [mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s τ,mul_zero]
    positivity

/-- Clipping input: the actual conditional density is close to one. -/
theorem initial_centered_energy {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : 0 ≤ w) (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    multilinearEnergy (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ)) w ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) /
        (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have H := multilinearEnergy_low_high (R:=1)
    (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ)) w _ 1 hw
    (by positivity [rankSchurConstant_pos,hq.1]) ha (by norm_num) (fun _ => 0)
    (fun r hr => by
      have he : r=0 := by omega
      subst r
      rw [nonconstant_degree_zero])
    (fun r hr => by
      rw [nonconstant_degree_pos _ (by omega)]
      simpa only [one_mul] using mixedMotif_degree_geometric hl (by omega) hm hum off
        hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv w)
    (fun _ => le_rfl)
  simpa using H

theorem initial_centered_moment {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hk : 1 ≤ k) (τ : ℝ) {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => initialMotifDensity hl off hsafe π s τ q x-1) k ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) /
        (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => initialMotifDensity hl off hsafe π s τ q x-1) =
      multilinear (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ))
        (primitiveScore q) := by
    funext x
    rw [nonconstant_multilinear,mixedMotifCoefficient_empty hl off hsafe π hπsum]
    rfl
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk (primitive_score_centered hq')
    (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  apply initial_centered_energy hl hm hum off hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv _ ha
  rw [hw]; positivity [hq.1]

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


noncomputable section


noncomputable section


noncomputable section

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem density_score_centered (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀a,Q.mass a=P.mass a*(1+Z a)) : P.expect Z=0 := by
  have h := Q.total
  simp_rw [hZ,mul_add,mul_one,Finset.sum_add_distrib,P.total] at h
  change _+P.expect Z=1 at h
  linarith

/-- Common-event mass difference is controlled by the restricted density
 difference at every moment, by finite Jensen rather than a pointwise bound. -/
theorem clipping_mass_difference (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (t : ℕ) :
    |(R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A|^t ≤
      R.expect (fun a => |if a∈A then g a-f a else 0|^t) := by
  have he : (R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A=
      -(R.expect (fun a => if a∈A then g a-f a else 0)) := by
    simp only [expect,mul_ite,mul_zero,←Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass,withDensity,mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [he,abs_neg]
  exact R.abs_expect_pow_le _ t

theorem clipped_raw_moment_restricted (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hfm : R.expect f=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hP : 0<(R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1)) ≤
      2^k/(R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |if a∈A then g a-f a else 0|^(k+1)) := by
  let g' : α → ℝ := fun a => if a∈A then g a else f a
  have H := clipped_raw_moment R f g' hf hfm A hAf hP k
  have he : (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1))=
      (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g' a/f a-1|^(k+1)) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈A <;> simp [condition,g',ha]
  rw [he]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext a
  by_cases ha : a∈A <;> simp [g',ha]

/-- Explicit normalized clipping, at half of any positive even moment. This
 constructs the actual conditioned score; no bounded-score hypothesis. -/
theorem clipped_score_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hp : 1/2 ≤ (R.withDensity f hf hfm).eventMass A)
    (hq : 1/2 ≤ (R.withDensity g hg hgm).eventMass A)
    (k : ℕ) (hk : 1 ≤ k) (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k) :
    let p := (R.withDensity f hf hfm).eventMass A
    let q := (R.withDensity g hg hgm).eventMass A
    let hP : 0 < p := lt_of_lt_of_le (by norm_num) hp
    (condition (R.withDensity f hf hfm) A hP).evenMomentSq (fun a => p/q*(g a/f a)-1) k ≤64*V := by
  dsimp only
  let p := (R.withDensity f hf hfm).eventMass A
  let q := (R.withDensity g hg hgm).eventMass A
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hp1 : p ≤ 1 := eventMass_le_one _ _
  have hratio : p/q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith)
  have hden : (1:ℝ)/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have ht : 2*k-1+1=2*k := by omega
  have hraw := clipped_raw_moment_restricted R f g hf hfm A hAf hp0 (2*k-1)
  rw [ht] at hraw
  have hraw' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |g a/f a-1|^(2*k)) ≤
      2^(2*k)*V^k := by
    apply hraw.trans
    calc
      _ ≤ (2^(2*k-1)/p)*V^k := mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ (2^(2*k-1)*2)*V^k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hV _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (2:ℝ)^(2*k-1))
      _ = _ := by rw [←pow_succ,ht]
  have hnorm : |p/q-1|^(2*k) ≤ 2^(2*k)*V^k := by
    rw [div_sub_one hq0.ne',abs_div,abs_of_pos hq0,div_pow]
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    have hd := (clipping_mass_difference R f g hf hg hfm hgm A (2*k)).trans hM
    have hqpow : 1 ≤ (2*q)^(2*k) := one_le_pow₀ (by linarith)
    calc
      _ ≤ V^k := hd
      _ ≤ (2*q)^(2*k)*V^k := by nlinarith [pow_nonneg hV k]
      _ = _ := by rw [mul_pow]; ring
  have hs := score_rescaling_moment (condition (R.withDensity f hf hfm) A hp0)
    (fun a => g a/f a) (p/q) (div_nonneg hp0.le hq0.le) (2*k-1)
  rw [ht] at hs
  have hpower : (p/q)^(2*k) ≤ (2:ℝ)^(2*k) :=
    pow_le_pow_left₀ (div_nonneg hp0.le hq0.le) hratio _
  have hs' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |p/q*(g a/f a)-1|^(2*k)) ≤
      (64*V)^k := by
    apply hs.trans
    calc
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*V^k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul hpower hraw' (by
          apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) (by positivity)) hnorm
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*(2^(2*k)*V^k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        have htwo : (1:ℝ) ≤ 2^(2*k) := one_le_pow₀ (by norm_num)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo
          (by positivity : 0 ≤ (2:ℝ)^(2*k)*V^k)
      _ = (64*V)^k := by
        have hm : 2^(2*k-1)*2= (2:ℝ)^(2*k) := by rw [←pow_succ,ht]
        calc
          _ = (2^(2*k-1)*2)*(2:ℝ)^(2*k)*(2:ℝ)^(2*k)*V^k := by ring
          _ = _ := by rw [hm,←pow_add,←pow_add,mul_pow]; congr 1; rw [show 2*k+2*k+2*k=6*k by omega,pow_mul]; norm_num
  unfold evenMomentSq
  calc
    _ ≤ ((64*V)^k)^(1/(k:ℝ)) := Real.rpow_le_rpow
      (by apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) hs' (by positivity)
    _ = _ := by rw [←Real.rpow_natCast,one_div,Real.rpow_rpow_inv (by positivity) (by positivity)]

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eventMass_indicator (P : FiniteLaw α) (A : Finset α) :
    P.eventMass A=P.expect (fun a => if a∈A then 1 else 0) := by
  simp only [expect,mul_ite,mul_one,mul_zero,←Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass]

theorem eventMass_compl (P : FiniteLaw α) (A : Finset α) :
    P.eventMass Aᶜ=1-P.eventMass A := by
  rw [eventMass_indicator,eventMass_indicator]
  have he : P.expect (fun a => (if a∈Aᶜ then (1:ℝ) else 0)+(if a∈A then 1 else 0))=1 := by
    convert P.expect_const 1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext a
    by_cases ha : a∈A <;> simp [ha]
  rw [expect_add] at he
  linarith

theorem density_second_moment_le_six (R : FiniteLaw α) (f : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hM : R.expect (fun a => |f a-1|^(2*k)) ≤ 1) :
    R.expect (fun a => f a^2) ≤ 6 := by
  have h := R.expect_lower_moment_le_two (fun a => f a-1) (2*k) hM 2 (by omega)
  calc
    _ ≤ R.expect (fun a => 2*(f a-1)^2+2) := R.expect_mono (fun a => by nlinarith [sq_nonneg (f a-2)])
    _ = 2*R.expect (fun a => (f a-1)^2)+2 := by rw [expect_add,expect_const_mul,expect_const]
    _ ≤ _ := by linarith [le_abs_self (R.expect (fun a => (f a-1)^2))]

/-- Cauchy--Schwarz loss on the actual low-reference-density event, for
 either density. The same clipping event is used for both hypotheses. -/
theorem density_low_event_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hg : ∀a,0 ≤ g a) (hgm : R.expect g=1) (k : ℕ) (hk : 1 ≤ k) (U : ℝ)
    (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    (R.withDensity g hg hgm).eventMass (Finset.univ.filter (fun a => f a<1/2)) ≤
      Real.sqrt (6*(4*U)^k) := by
  let A := Finset.univ.filter (fun a => f a<1/2)
  have hR : R.eventMass A ≤ (4*U)^k := by
    calc
      _ ≤ 2^(2*k)*R.expect (fun a => |f a-1|^(2*k)) :=
        R.low_density_reference_mass f (2*k) A (fun a ha => (Finset.mem_filter.mp ha).2)
      _ ≤ 2^(2*k)*U^k := mul_le_mul_of_nonneg_left hfM (by positivity)
      _ = _ := by rw [pow_mul,mul_pow]; norm_num
  have hsecond := R.density_second_moment_le_six g k hk (hgM.trans (pow_le_one₀ hU hU1))
  have hsq : ((R.withDensity g hg hgm).eventMass A)^2 ≤ 6*(4*U)^k := by
    apply (R.density_bad_mass_sq g A).trans
    calc
      _ ≤ R.eventMass A*6 := mul_le_mul_of_nonneg_left hsecond (R.eventMass_nonneg A)
      _ ≤ _ := by nlinarith
  exact (Real.le_sqrt ((R.withDensity g hg hgm).eventMass_nonneg A) (by positivity)).mpr hsq

theorem commonClipEvent_loss (P : FiniteLaw α) (B : Finset α) (f : α → ℝ) :
    1-P.eventMass (commonClipEvent B f) ≤
      P.eventMass Bᶜ+P.eventMass (Finset.univ.filter (fun a => f a<1/2)) := by
  rw [←eventMass_compl,eventMass_indicator,eventMass_indicator,eventMass_indicator,←expect_add]
  apply P.expect_mono
  intro a
  simp only [commonClipEvent,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all


/-- Quantitative common clipping on any genuine good event. Both bad-event
 costs below are measured under the actual normalized laws, not reference mass. -/
theorem commonClipEvent_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    1-(R.withDensity f hf hfm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) ∧
    1-(R.withDensity g hg hgm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) := by
  constructor
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hfB
      (density_low_event_mass R f f hf hfm k hk U hU hU1 hfM hfM))
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hgB
      (density_low_event_mass R f g hg hgm k hk U hU hU1 hfM hgM))

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem exists_clippedOracle (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k)
    (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈B then g a-f a else 0|^(2*k)) ≤ V^k)
    (hsmall : e+Real.sqrt (6*(4*U)^k) ≤ 1/2) :
    Nonempty (ClippedOracle (R.withDensity f hf hfm) (R.withDensity g hg hgm)
      k (e+Real.sqrt (6*(4*U)^k)) (64*V)) := by
  let A := commonClipEvent B f
  let P := R.withDensity f hf hfm
  let Q := R.withDensity g hg hgm
  have hA (a : α) (ha : a∈A) : 1/2 ≤ f a := (Finset.mem_filter.mp ha).2
  have hloss := commonClipEvent_mass R f g hf hg hfm hgm B e hfB hgB k hk U hU hU1 hfM hgM
  have hp : 1/2 ≤ P.eventMass A := by linarith [hloss.1]
  have hq : 1/2 ≤ Q.eventMass A := by linarith [hloss.2]
  have hp0 : 0<P.eventMass A := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<Q.eventMass A := lt_of_lt_of_le (by norm_num) hq
  let Z : α → ℝ := fun a => P.eventMass A/Q.eventMass A*(g a/f a)-1
  have hden (a : α) : (Q.condition A hq0).mass a=(P.condition A hp0).mass a*(1+Z a) := by
    dsimp only [Z]
    rw [show 1+(P.eventMass A/Q.eventMass A*(g a/f a)-1)=P.eventMass A/Q.eventMass A*(g a/f a) by ring]
    exact conditioned_density_identity R f g hf hg hfm hgm A
      (fun a ha => lt_of_lt_of_le (by norm_num) (hA a ha)) hp0 hq0 a
  have hAM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k := by
    apply le_trans (R.expect_mono _) hM
    intro a
    by_cases ha : a∈A
    · have hb := (Finset.mem_filter.mp ha).1
      simp only [ite_eq_left ha,ite_eq_left hb,le_refl]
    · rw [ite_eq_right ha]
      simp only [abs_zero,zero_pow (by omega : 2*k≠0)]
      exact pow_nonneg (abs_nonneg _) _
  exact ⟨{
    first := P.condition A hp0
    second := Q.condition A hq0
    score := Z
    density := hden
    likelihood_nonneg := fun a => by
      dsimp only [Z]
      have hh := mul_nonneg (div_nonneg hp0.le hq0.le) (div_nonneg (hg a) (hf a))
      linarith
    centered := density_score_centered _ _ Z hden
    moment := clipped_score_moment R f g hf hg hfm hgm A hA hp hq k hk V hV hAM
    first_tv := by rw [tv_symm,tv_condition]; exact hloss.1
    second_tv := by rw [tv_symm,tv_condition]; exact hloss.2
  }⟩

end FiniteLaw
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
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem initialSignedBudget_nonneg (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ)
    (hq : 0 ≤ q) (ha : initialMomentRatio u m q w < 1) :
    0 ≤ initialSignedBudget u m l R s π θ q w := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun r _ => mul_nonneg (by rw [pow_mul]; positivity)
      (signedInitialDegreeBound_nonneg _ _ _ _ _ _ _))
  · apply div_nonneg _ (sub_nonneg.mpr ha.le)
    exact mul_nonneg (by norm_num) (pow_nonneg (by unfold initialMomentRatio; positivity [rankSchurConstant_pos]) _)

/-- The signed score numerator in the *actual conditional mark-list laws*,
 with the entire finite cancellation energy and geometric tail retained. -/
theorem initial_signed_moment {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (ha : initialMomentRatio u m q w < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => initialMotifDensity hl off hsafe π s 1 q x-initialMotifDensity hl off hsafe π s (-1) q x) k  ≤ 
        initialSignedBudget u m l R s π θ q w := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => initialMotifDensity hl off hsafe π s 1 q x-initialMotifDensity hl off hsafe π s (-1) q x)=
      multilinear (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-mixedMotifCoefficient hl off hsafe π s (-1) σ)
        (primitiveScore q) := by funext x; exact (multilinear_sub _ _ _ _).symm
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk
    (primitive_score_centered hq') (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  exact signed_initial_full_energy hu hm hum hR hl off hi hoff hsafe π hπ hπsum s hcentral hq hθ hmean hv hM
    (by rw [hw]; positivity [hq.1]) ha

/-- Quantitative normalized common clipping of the level-zero conditional
 pair. This theorem has only the literal count/geometric inequalities of the
 initial construction, not a signed-density or oracle conclusion premise. -/
theorem initial_conditional_clipped_exists {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (hscale : initialMomentRatio u m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k) ≤ 1/2) :
    Nonempty (ClippedOracle
      (conditionalMotifLaw hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s (-1))
      (conditionalMotifLaw hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k))
      (64*initialSignedBudget u m l R s π θ q w)) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  let A := (primitiveMarkLaw q hq' false).product l
  let f := initialMotifDensity hl off hsafe π s (-1) q
  let g := initialMotifDensity hl off hsafe π s 1 q
  let U := initialMomentRatio u m q w/(1-initialMomentRatio u m q w)
  have ha : initialMomentRatio u m q w < 1 := by linarith
  have hz : 0 ≤ initialMomentRatio u m q w := by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]
  have hU : 0 ≤ U := div_nonneg hz (sub_nonneg.mpr ha.le)
  have hU1 : U ≤ 1 := (div_le_iff₀ (sub_pos.mpr ha)).mpr (by linarith)
  have hmom (τ : ℝ) : A.expect (fun x => |initialMotifDensity hl off hsafe π s τ q x-1|^(2*k)) ≤ U^k :=
    A.expect_even_pow_le_of_moment _ k hk (initial_centered_moment hl (by omega) hum off hi hoff hsafe π hπ hπsum s k hk τ hq hθ hmean hv hw ha)
  have hV := initialSignedBudget_nonneg u m l R s π θ q w hq.1.le ha
  have hsig := A.expect_even_pow_le_of_moment _ k hk
    (initial_signed_moment hu hm hum hR hl off hi hoff hsafe π hπ hπsum s k hcentral hk hq hθ hmean hv hM hw ha)
  rw [initialMotifLaw_withDensity hl off hsafe π hπ hπsum s (-1) hq',
    initialMotifLaw_withDensity hl off hsafe π hπ hπsum s 1 hq']
  have H := A.exists_clippedOracle f g
    (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s (-1) hq')
    (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s 1 hq')
    (initialMotifDensity_mean hl off hsafe π hπ hπsum s (-1) hq')
    (initialMotifDensity_mean hl off hsafe π hπ hπsum s 1 hq')
    Finset.univ 0 (by simp [eventMass]) (by simp [eventMass]) k hk U hU hU1 (hmom (-1)) (hmom 1)
    (initialSignedBudget u m l R s π θ q w) hV (by simpa only [Finset.mem_univ,ite_true] using hsig)
    (by simpa only [zero_add] using hclip)
  simpa only [zero_add] using H

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace ClippedOracle
variable {α : Type*} [Fintype α] {P Q : FiniteLaw α} {k : ℕ} {e V E W : ℝ}

/-- Replace bad conditional observations by a common law rather than making
 the original metadata law conditional on typicality. The exact cost is
 the true metadata failure mass plus the good conditional clipping cost. -/
theorem assemble_good {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) (Good : ι → Prop)
    (k : ℕ) (hk : 1≤k) (e V : ℝ) (he : 0≤e) (hV : 0≤V)
    (C : ∀i,Good i → Nonempty (ClippedOracle (P i) (Q i) k e V)) :
    Nonempty (ClippedOracle (M.sigma P) (M.sigma Q) k
      (e+M.expect (fun i => if Good i then 0 else 1)) V) := by
  let err := fun i => if Good i then e else 1
  have hi (i) : Nonempty (ClippedOracle (P i) (Q i) k (err i) V) := by
    by_cases h : Good i
    · simpa only [err,ite_eq_left h] using C i h
    · exact ⟨(trivial (P i) (Q i) k hk).weaken (by simp [err,h]) hV⟩
  let D := sigma M P Q err k hk V hV (fun i => Classical.choice (hi i))
  refine ⟨D.weaken ?_ le_rfl⟩
  calc
    M.expect err ≤ M.expect (fun i => e+(if Good i then 0 else 1)) := M.expect_mono (fun i => by
      dsimp only [err]; split_ifs <;> linarith)
    _ = _ := by rw [M.expect_add,M.expect_const]

end ClippedOracle
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem posteriorAnchorSeries_support {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (X : ℤ) (hX : X∈(posteriorAnchorSeries c d).coeff.support) :
    c-Fintype.card ι ≤ X ∧ X ≤ c := by
  have H := translated_binomial_support (∑i,hiddenTrial (d i))
    (c-(∑i,(visibleOnes (d i):ℤ))-(∑i,hiddenTrial (d i))) X
    (Finsupp.mem_support_iff.mp hX)
  have hz : 0 ≤ ∑i,(visibleOnes (d i):ℤ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hh : (∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i)) ≤ Fintype.card ι := by
    rw [Nat.cast_sum,←Finset.sum_add_distrib]
    calc
      _ ≤ ∑_i : ι,(1:ℤ) := Finset.sum_le_sum (fun i _ => by
        cases h:d i with
        | none => simp [visibleOnes,hiddenTrial]
        | some b => cases b <;> simp [visibleOnes,hiddenTrial])
      _ = _ := by simp
  omega

theorem posteriorAnchorSeries_central {ι : Type*} [Fintype ι]
    (u s : ℕ) (c : ℤ) (d : ι → Option Bool)
    (hleft : (u:ℝ)/3 ≤ 2*((c:ℝ)-Fintype.card ι)+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*((c:ℝ)+(2:ℝ)^s)+1)) :
    CentralMotifSupport u s (posteriorAnchorSeries c d) := by
  intro X hX
  have H := posteriorAnchorSeries_support c d X hX
  have H₁ : (c:ℝ)-Fintype.card ι ≤ X := by exact_mod_cast H.1
  have H₂ : (X:ℝ) ≤ c := by exact_mod_cast H.2
  constructor <;> linarith


end TraceReconstruction
noncomputable section
noncomputable section
noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The genuine initial metadata oracle is clipped by conditioning each
 admissible fiber only. Every bad report/count keeps its original mass and
 is replaced by a common law, so all discarded mass is charged. -/
theorem initial_sigma_clipped_exists_oai {Side : Type*} [Fintype Side] {J K m R : ℕ}
    (M : PairedMechanisms Side J) (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m)
    (hR : 0 < R) (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (c : ℤ) (s k : ℕ) (hk : 1 ≤ k)
    (hleft : (K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
    {q ω w V : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V)
    (hbudget : ∀z : InitialMetadata Side J (K*m),initialMetadataGood q ω z →
      64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
    Nonempty (ClippedOracle
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s (-1))
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
        (initialMetadataLaw M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
          (fun z => if initialMetadataGood q ω z then 0 else 1)) V) := by
  apply ClippedOracle.assemble_good _ _ _ (initialMetadataGood q ω) k hk _ V (Real.sqrt_nonneg _) hV
  intro z hz
  have hmean : ((K*m:ℕ):ℝ)*((z.2.val:ℝ)/(K*m:ℕ))=z.2.val := by
    exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0)))
  have H := initial_conditional_clipped_exists hK hm hKm hR (by have H:=z.2.isLt; omega) off hi hoff hsafe
    (posteriorAnchorSeries c (fun i => (z.1 i).1)) (posteriorAnchorSeries_nonneg c _)
    (posteriorAnchorSeries_total c _) s k
    (posteriorAnchorSeries_central K s c _ (by simpa using hleft) hright) hk hq hz.1.1 hmean hz.1.2 hM hw hscale hclip
  exact ⟨(Classical.choice H).weaken le_rfl (hbudget z hz)⟩

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

theorem solution.{u_1} : type_of% @OAI.TraceReconstruction.initial_sigma_clipped_exists_oai.{u_1} := @OAI.TraceReconstruction.initial_sigma_clipped_exists_oai.{u_1}
