-- Prove2me | solution 1 for KellyStochasticNetworks.truncated_reversible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:17:38.137046+00:00
-- url     : https://prove2.me/submissions/642eabab-8284-4371-ac77-6797fe40411f

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

open Finset

/-! ### Products of summable families over `Fin R → ℕ` -/

lemma sn3_hasSum_pi_prod (R : ℕ) : ∀ (f : Fin R → ℕ → ℝ) (a : Fin R → ℝ),
    (∀ i n, 0 ≤ f i n) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun n : Fin R → ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  induction R with
  | zero =>
    intro f a _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_single default (fun b hb => (hb (Subsingleton.elim b default)).elim)
  | succ R ih =>
    intro f a h0 ha
    set g : (Fin R → ℕ) → ℝ := fun n => ∏ i, f i.succ (n i) with hgdef
    have ih' : HasSum g (∏ i : Fin R, a i.succ) := ih (fun i : Fin R => f i.succ) (fun i : Fin R => a i.succ)
      (fun (i : Fin R) n => h0 _ _) (fun i : Fin R => ha _)
    have hf0 : ∀ n, 0 ≤ f 0 n := fun n => h0 0 n
    have hg0 : ∀ n, 0 ≤ g n := fun n => Finset.prod_nonneg fun i _ => h0 _ _
    have hsum : Summable fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      apply summable_mul_of_summable_norm
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using (ha 0).summable
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using ih'.summable
    have hm := HasSum.mul (ha 0) ih' hsum
    have hfun : (fun n : Fin (R + 1) → ℕ => ∏ i, f i (n i)) ∘ (Fin.consEquiv (fun _ => ℕ))
        = fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      funext x
      simp [Fin.consEquiv, Fin.prod_univ_succ, hgdef]
    rw [← (Fin.consEquiv (fun _ : Fin (R + 1) => ℕ)).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm

/-! ### The immigration–death network: detailed balance of product weights -/

lemma sn3_Tout_Tin {R : ℕ} (k : Fin R) (n : Fin R → ℕ) : Tout k (Tin k n) = n := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn3_Tin_Tout {R : ℕ} (k : Fin R) (m : Fin R → ℕ) (hm : 1 ≤ m k) : Tin k (Tout k m) = m := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn3_rates {R : ℕ} (ν : Fin R → ℝ) (n m : Fin R → ℕ) :
    openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)) n m
      = (∑ k, if m = Tin k n then ν k else 0) + ∑ j, if m = Tout j n then (n j : ℝ) else 0 := by
  unfold openMigrationRates closedMigrationRates
  simp only [zero_mul, ite_self, Finset.sum_const_zero, one_mul, zero_add]
  ring

lemma sn3_prod_update {R : ℕ} (g : Fin R → ℕ → ℝ) (n : Fin R → ℕ) (k : Fin R) :
    ∏ r, g r (Tin k n r) = g k (n k + 1) * ∏ r ∈ univ.erase k, g r (n r) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ k)]
  congr 1
  · simp [Tin]
  · apply Finset.prod_congr rfl
    intro r hr
    have : r ≠ k := Finset.ne_of_mem_erase hr
    simp [Tin, this]

lemma sn3_term {R : ℕ} (ν : Fin R → ℝ) (g : Fin R → ℕ → ℝ)
    (hg : ∀ r t, g r (t + 1) * ((t : ℝ) + 1) = g r t * ν r) (n m : Fin R → ℕ) (k : Fin R) :
    (∏ r, g r (n r)) * (if m = Tin k n then ν k else 0)
      = (∏ r, g r (m r)) * (if n = Tout k m then (m k : ℝ) else 0) := by
  by_cases h : m = Tin k n
  · subst h
    rw [if_pos rfl, if_pos (sn3_Tout_Tin k n).symm, sn3_prod_update]
    have e : (Tin k n k : ℝ) = (n k : ℝ) + 1 := by simp [Tin]
    rw [e, ← Finset.mul_prod_erase univ (fun r => g r (n r)) (mem_univ k)]
    have := hg k (n k)
    calc g k (n k) * (∏ r ∈ univ.erase k, g r (n r)) * ν k
        = (g k (n k) * ν k) * ∏ r ∈ univ.erase k, g r (n r) := by ring
      _ = (g k (n k + 1) * ((n k : ℝ) + 1)) * ∏ r ∈ univ.erase k, g r (n r) := by rw [this]
      _ = _ := by ring
  · rw [if_neg h]
    by_cases h2 : n = Tout k m
    · rw [if_pos h2]
      by_cases hmk : 1 ≤ m k
      · exact absurd (by rw [h2, sn3_Tin_Tout k m hmk]) h
      · have : m k = 0 := by omega
        simp [this]
    · rw [if_neg h2]; simp

lemma sn3_detailed {R : ℕ} (ν : Fin R → ℝ) (g : Fin R → ℕ → ℝ)
    (hg : ∀ r t, g r (t + 1) * ((t : ℝ) + 1) = g r t * ν r) :
    DetailedBalance (fun n : Fin R → ℕ => ∏ r, g r (n r))
      (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by
  intro n m
  simp only [sn3_rates, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    exact (sn3_term ν g hg m n k).symm
  · apply Finset.sum_congr rfl; intro k _
    exact sn3_term ν g hg n m k

lemma sn3_full_of_detailed {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (h : DetailedBalance π q) :
    FullBalance π q := by
  intro j
  rw [← tsum_mul_left]
  congr 1; ext k; exact h j k

lemma sn3_hg (ν : ℝ) (c : ℝ) (t : ℕ) :
    c * (ν ^ (t + 1) / ((t + 1).factorial : ℝ)) * ((t : ℝ) + 1) = c * (ν ^ t / (t.factorial : ℝ)) * ν := by
  rw [Nat.factorial_succ]
  push_cast
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma sn3_lossWeight_detailed {R : ℕ} (ν : Fin R → ℝ) :
    DetailedBalance (fun n : Fin R → ℕ => lossWeight ν n)
      (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by
  have := sn3_detailed ν (fun r t => ν r ^ t / (t.factorial : ℝ)) (fun r t => by
    have := sn3_hg (ν r) 1 t; simpa using this)
  exact this

/-! ### Erlang's formula: bounds and strict monotonicity -/

/-- The denominator `∑_{k ≤ N} ν^k / k!`. -/
noncomputable def sn3S (N : ℕ) (ν : ℝ) : ℝ := ∑ k ∈ range (N + 1), ν ^ k / (k.factorial : ℝ)

lemma sn3_erlang_eq (ν : ℝ) (N : ℕ) : erlang ν N = (ν ^ N / (N.factorial : ℝ)) / sn3S N ν := rfl

lemma sn3_S_ge (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ν ^ N / (N.factorial : ℝ) + ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) = sn3S N ν := by
  unfold sn3S; rw [sum_range_succ]; ring

lemma sn3_S_pos (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 1 ≤ sn3S N ν := by
  unfold sn3S
  rw [sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have : 0 ≤ ∑ k ∈ range N, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    sum_nonneg (fun k _ => by positivity)
  linarith

lemma sn3_erlang_nonneg (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 0 ≤ erlang ν N := by
  rw [sn3_erlang_eq]
  have := sn3_S_pos N hν
  positivity

lemma sn3_erlang_lt_one (N : ℕ) (hN : 1 ≤ N) {ν : ℝ} (hν : 0 ≤ ν) : erlang ν N < 1 := by
  rw [sn3_erlang_eq, div_lt_one (by linarith [sn3_S_pos N hν]), ← sn3_S_ge N hν]
  have h1 : 1 ≤ ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ k ∈ range M, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      sum_nonneg (fun k _ => by positivity)
    linarith
  linarith

lemma sn3_pow_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {i k : ℕ} (hki : k ≤ i) :
    a ^ i * b ^ k ≤ b ^ i * a ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
  have h1 : a ^ d ≤ b ^ d := pow_le_pow_left₀ ha hab d
  have h2 : 0 ≤ a ^ k := pow_nonneg ha k
  have h3 : 0 ≤ b ^ k := pow_nonneg (le_trans ha hab) k
  calc a ^ (k + d) * b ^ k = (a ^ k * b ^ k) * a ^ d := by ring
    _ ≤ (a ^ k * b ^ k) * b ^ d := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
    _ = b ^ (k + d) * a ^ k := by ring

lemma sn3_erlang_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    erlang a N < erlang b N := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_erlang_eq, sn3_erlang_eq,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.mul_sum, Finset.mul_sum, ← sub_neg, ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range (N + 1), a ^ N / (N.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
      - b ^ N / (N.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
      = (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) := by
    intro k _; ring
  rw [Finset.sum_congr rfl key]
  have hle : ∀ k ∈ range (N + 1),
      (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) ≤ 0 := by
    intro k hk
    have hk' : k ≤ N := by simp at hk; omega
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [sn3_pow_le ha (le_of_lt hab) hk'])
      (by positivity)
  have hlt : (a ^ N * b ^ 0 - b ^ N * a ^ 0) / ((N.factorial : ℝ) * (Nat.factorial 0 : ℕ)) < 0 := by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := pow_lt_pow_left₀ hab ha (by omega : N ≠ 0)
    linarith
  have h := Finset.sum_lt_sum (s := range (N + 1))
    (f := fun k => (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial))
    (g := fun _ => (0 : ℝ)) hle ⟨0, by simp, hlt⟩
  simp only [Finset.sum_const_zero] at h
  exact h

/-- The carried load `ν(1 − E(ν, N)) = ∑_{k ≤ N} k ν^k/k! / ∑_{k ≤ N} ν^k/k!`. -/
lemma sn3_carried_eq (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ν * (1 - erlang ν N)
      = (∑ k ∈ range (N + 1), (k : ℝ) * (ν ^ k / (k.factorial : ℝ))) / sn3S N ν := by
  have hS := sn3_S_pos N hν
  have hS0 : sn3S N ν ≠ 0 := by linarith
  rw [sn3_erlang_eq, eq_div_iff hS0]
  have e1 : ν * (1 - ν ^ N / (N.factorial : ℝ) / sn3S N ν) * sn3S N ν
      = ν * (sn3S N ν - ν ^ N / (N.factorial : ℝ)) := by field_simp
  rw [e1, ← sn3_S_ge N hν, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma sn3_carried_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a * (1 - erlang a N) < b * (1 - erlang b N) := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_carried_eq N ha, sn3_carried_eq N hb,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_pos]
  set w : ℕ → ℝ → ℝ := fun k ν => ν ^ k / (k.factorial : ℝ) with hw
  set X : ℕ → ℕ → ℝ := fun i k => w i b * w k a - w i a * w k b with hX
  have hD1 : (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b)
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hD2 : ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), -((k : ℝ) * X i k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hterm : ∀ i k : ℕ, 0 ≤ ((i : ℝ) - k) * X i k := by
    intro i k
    simp only [hX, hw]
    have e : b ^ i / (i.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
        - a ^ i / (i.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
        = (b ^ i * a ^ k - a ^ i * b ^ k) / ((i.factorial : ℝ) * k.factorial) := by ring
    rw [e]
    rcases le_total k i with hki | hik
    · have hc : (k : ℝ) ≤ i := by exact_mod_cast hki
      apply mul_nonneg (by linarith)
      apply div_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hki]
    · have hc : (i : ℝ) ≤ k := by exact_mod_cast hik
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hik]
  have h2D : 2 * ((∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    rw [hD1, two_mul]
    nth_rewrite 2 [hD2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hpos : 0 < ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun k _ => hterm i k))
    refine ⟨1, by simp; omega, ?_⟩
    apply Finset.sum_pos' (fun k _ => hterm 1 k)
    refine ⟨0, by simp, ?_⟩
    simp only [hX, hw]
    norm_num
    linarith
  have hconv : ∀ ν₁ ν₂ : ℝ, (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      (i : ℝ) * (ν₁ ^ i / (i.factorial : ℝ)) * (ν₂ ^ j / (j.factorial : ℝ)))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i ν₁ * w k ν₂ := fun _ _ => rfl
  rw [hconv b a, hconv a b]
  linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (A : Set S)
    (h : DetailedBalance π q) (Z : ℝ) (hZ0 : Z ≠ 0)
    (hZ : HasSum (fun j : A => π (j : S)) Z) :
    DetailedBalance (fun j : A => π (j : S) / Z) (truncatedRates q A)
      ∧ HasSum (fun j : A => π (j : S) / Z) 1 := by
  refine ⟨fun j k => ?_, ?_⟩
  · simp only [truncatedRates]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, h]
  · have := hZ.div_const Z
    rwa [div_self hZ0] at this
