-- Prove2me | solution 1 for GreenTao.prime_majorant_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-06T02:30:37.881603+00:00
-- url     : https://prove2.me/submissions/10bdd4e9-65d5-4789-8344-84e9c61546ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GreenTao_prime_weight_fixed_modulus_mean
import Theorems.Thm_GreenTao_prime_sieve_slow_cutoff
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter GreenTao
open scoped Topology BigOperators

private lemma scale_pos (k : ℕ) (hk : 3 ≤ k) : 0 < primeScale k := by
  unfold primeScale
  have : 0 < k := by omega
  positivity

private lemma interval_pos (k : ℕ) : 0 < primeInterval k := by
  unfold primeInterval
  positivity

private lemma interval_small (k : ℕ) (hk : 3 ≤ k) : 4 * primeInterval k < 1 := by
  have hp : (8 : ℝ) ≤ 2 ^ k := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hf : (1 : ℝ) ≤ (Nat.factorial (k + 4) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 4)
  unfold primeInterval
  have hd : (0 : ℝ) < 2 ^ k * (Nat.factorial (k + 4) : ℝ) := by positivity
  rw [mul_one_div, div_lt_one hd]
  nlinarith

private lemma weight_nonneg (k W : ℕ) {m : ℕ+} (x : ZMod (m : ℕ)) :
    0 ≤ primeWeight k W x := by
  unfold primeWeight primeScale
  split_ifs
  · apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 (W * x.val))
  · exact le_rfl

private lemma weight_support (k : ℕ) (hk : 3 ≤ k) (W : ℕ)
    {m : ℕ+} (x : ZMod (m : ℕ)) (hx : 0 < primeWeight k W x) :
    Nat.Prime (W * x.val + 1) ∧ 2 * x.val < (m : ℕ) := by
  unfold primeWeight at hx
  split_ifs at hx with h
  · refine ⟨h.1, ?_⟩
    have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
    have hs := mul_lt_mul_of_pos_right (interval_small k hk) hm
    have hx' : (2 : ℝ) * (x.val : ℝ) < (m : ℝ) := by nlinarith [h.2.2]
    exact_mod_cast hx'
  · exact (lt_irrefl 0 hx).elim

private lemma weight_log_bound (k : ℕ) (hk : 3 ≤ k) (W : ℕ) (hW : 0 < W)
    {m : ℕ+} (hWm : W ≤ (m : ℕ)) (x : ZMod (m : ℕ)) :
    primeWeight k W x ≤ (2 * primeScale k) * Real.log (m : ℝ) := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  have hlog : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast m.pos)
  have hs := (scale_pos k hk).le
  unfold primeWeight
  split_ifs with h
  · have hratio : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hW)).2
      exact_mod_cast Nat.totient_le W
    have harg : (W * x.val + 1 : ℕ) ≤ (m : ℕ) ^ 2 := by
      have hx := x.val_lt
      nlinarith
    have hl : Real.log (W * x.val + 1 : ℕ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        Real.log (W * x.val + 1 : ℕ) ≤ Real.log ((m : ℝ) ^ 2) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast harg
        _ = 2 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
    calc
      _ ≤ primeScale k * Real.log (W * x.val + 1 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast h.1.one_lt.le))
        simpa using mul_le_mul_of_nonneg_left hratio hs
      _ ≤ primeScale k * (2 * Real.log (m : ℝ)) := mul_le_mul_of_nonneg_left hl hs
      _ = _ := by ring
  · positivity

/-- Select a cutoff below a prescribed divergent bound while meeting one eventual
condition for each fixed cutoff. No uniform prime number theorem is assumed. -/
private lemma slow_selection (u : ℕ → ℕ) (hu : Tendsto u atTop atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧ (∀ n, w n ≤ u n) ∧
      ∀ᶠ n in atTop, P (w n) n := by
  classical
  choose B hB using fun j => eventually_atTop.1 (hP j)
  let w : ℕ → ℕ := fun n => Nat.findGreatest (fun j => B j ≤ n) (min (u n) n)
  refine ⟨w, ?_, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro j
    filter_upwards [hu.eventually (eventually_ge_atTop j),
      eventually_ge_atTop j, eventually_ge_atTop (B j)] with n hun hjn hBn
    exact Nat.le_findGreatest (le_min hun hjn) hBn
  · intro n
    exact (Nat.findGreatest_le _).trans (min_le_left _ _)
  · filter_upwards [eventually_ge_atTop (B 0)] with n hn
    exact hB (w n) n (Nat.findGreatest_spec (P := fun j => B j ≤ n)
      (Nat.zero_le (min (u n) n)) hn)

private lemma diagonal_tendsto_zero (k : ℕ) (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (f : Family M) (hf : ∀ n x, 0 ≤ f n x) (C : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ x, f n x ≤ C * Real.log (M n : ℝ)) :
    Tendsto (fun n => diagonalAvg k (f n)) atTop (𝓝 0) := by
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hlim : Tendsto (fun n => (C * Real.log (M n : ℝ)) ^ k / (M n : ℝ))
      atTop (𝓝 0) := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero.comp hMr
    simpa only [Function.comp_apply, id_eq, mul_pow, mul_div_assoc, mul_zero]
      using h.const_mul (C ^ k)
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun n => by
      unfold diagonalAvg avg
      exact div_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun x _ => pow_nonneg (hf n x) k)) (by positivity)
  · filter_upwards [hbound] with n hn
    unfold diagonalAvg avg
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (Fintype.card (ZMod (M n : ℕ)) : ℝ)⁻¹ *
          ∑ _x : ZMod (M n : ℕ), (C * Real.log (M n : ℝ)) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (hf n x) (hn x) k
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
        have hm : (M n : ℝ) ≠ 0 := by exact_mod_cast (M n).ne_zero
        field_simp

theorem solution (k : ℕ) (hk : 3 ≤ k) :
    ∃ (M : ℕ → ℕ+) (W : ℕ → ℕ) (ν f : GreenTao.Family M) (δ : ℝ),
      (∀ n, Nat.Prime (M n : ℕ)) ∧
      Tendsto (fun n => (M n : ℕ)) atTop atTop ∧
      (∀ n, 0 < W n) ∧
      GreenTao.Pseudorandom k M ν ∧
      (∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x) ∧
      0 < δ ∧ δ ≤ 1 ∧
      (∀ᶠ n in atTop, δ ≤ GreenTao.avg (f n)) ∧
      Tendsto (fun n => GreenTao.diagonalAvg k (f n)) atTop (𝓝 0) ∧
      (∀ n x, 0 < f n x →
        Nat.Prime (W n * x.val + 1) ∧ 2 * x.val < (M n : ℕ)) := by
  classical
  choose p hp hprime using Nat.exists_infinite_primes
  let M : ℕ → ℕ+ := fun n => ⟨p n, (hprime n).pos⟩
  have hM : Tendsto (fun n => (M n : ℕ)) atTop atTop :=
    tendsto_atTop_mono hp tendsto_id
  obtain ⟨u, hu, hsieve⟩ := prime_sieve_slow_cutoff k hk M hprime hM
  let δ : ℝ := min (primeScale k * primeInterval k / 2) 1
  have hδ : 0 < δ := lt_min (by positivity [scale_pos k hk, interval_pos k]) zero_lt_one
  have hδmean : δ < primeScale k * primeInterval k := by
    have hpos := mul_pos (scale_pos k hk) (interval_pos k)
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨w, hw, hwu, hgood⟩ := slow_selection u hu
    (fun j n => δ ≤ avg (primeWeight k (primorial j) (m := M n)) ∧
      primorial j ≤ (M n : ℕ)) (by
        intro j
        have hmean := prime_weight_fixed_modulus_mean k hk (primorial j)
          (primorial_pos j) M hM
        filter_upwards [hmean.eventually (eventually_gt_nhds hδmean),
          hM.eventually (eventually_ge_atTop (primorial j))] with n h₁ h₂
        exact ⟨h₁.le, h₂⟩)
  let W : ℕ → ℕ := fun n => primorial (w n)
  obtain ⟨ν, hν, hdom⟩ := hsieve w hw hwu
  let f : Family M := fun n x => min (primeWeight k (W n) x) (ν n x)
  have hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x := by
    intro n x
    exact ⟨le_min (weight_nonneg k (W n) x) (hν.1 n x), min_le_right _ _⟩
  have heq : ∀ᶠ n in atTop, f n = primeWeight k (W n) := by
    filter_upwards [hdom] with n hn
    funext x
    exact min_eq_left (hn x)
  refine ⟨M, W, ν, f, δ, hprime, hM, (fun n => primorial_pos (w n)),
    hν, hf, hδ, min_le_right _ _, ?_, ?_, ?_⟩
  · filter_upwards [hgood, heq] with n hn heqn
    rw [heqn]
    exact hn.1
  · apply diagonal_tendsto_zero k M hM f (fun n x => (hf n x).1) (2 * primeScale k)
    filter_upwards [hgood] with n hn
    intro x
    exact (min_le_left _ _).trans
      (weight_log_bound k hk (W n) (primorial_pos (w n)) hn.2 x)
  · intro n x hx
    exact weight_support k hk (W n) x (lt_of_lt_of_le hx (min_le_left _ _))
