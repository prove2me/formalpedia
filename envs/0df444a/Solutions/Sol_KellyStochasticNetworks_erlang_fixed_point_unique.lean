-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_fixed_point_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:17:41.784747+00:00
-- url     : https://prove2.me/submissions/989ed90f-0e4b-4872-a983-071d6cbc621b

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance
import Theorems.Thm_AGT_brouwer_fixed_point

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

lemma sn3_load_nonneg {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r)
    (E : Fin J → ℝ) (hK : ∀ j, E j ∈ Set.Icc (0 : ℝ) 1) (j : Fin J) :
    0 ≤ ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r) := by
  apply Finset.sum_nonneg; intro r _
  apply mul_nonneg (mul_nonneg (by positivity) (le_of_lt (hν r)))
  apply Finset.prod_nonneg; intro i _
  exact pow_nonneg (by linarith [(hK i).2]) _

lemma sn3_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) (E E' : Fin J → ℝ)
    (hK : ∀ j, E j ∈ Set.Icc (0 : ℝ) 1) (hF : ErlangFixedPoint A ν C E)
    (hK' : ∀ j, E' j ∈ Set.Icc (0 : ℝ) 1) (hF' : ErlangFixedPoint A ν C E') : E = E' := by
  -- loads, reduced intensities, and the fact that no link is fully blocked
  set L : (Fin J → ℝ) → Fin J → ℝ := fun E j => ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r)
    with hLdef
  have hρ0 : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ∀ j, 0 ≤ (1 - E j)⁻¹ * L E j := by
    intro E hK j
    exact mul_nonneg (inv_nonneg.2 (by linarith [(hK j).2])) (sn3_load_nonneg A ν hν E hK j)
  have hlt : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
      ∀ j, E j < 1 := by
    intro E hK hF j
    rw [hF j]; exact sn3_erlang_lt_one _ (hC j) (hρ0 E hK j)
  have hcar : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
      ∀ j, (1 - E j)⁻¹ * L E j * (1 - erlang ((1 - E j)⁻¹ * L E j) (C j)) = L E j := by
    intro E hK hF j
    rw [← hF j]
    have : 1 - E j ≠ 0 := by linarith [hlt E hK hF j]
    field_simp
  -- logarithmic coordinates
  set x : (Fin J → ℝ) → Fin J → ℝ := fun E j => -Real.log (1 - E j) with hx
  have hexp : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j, Real.exp (-x E j) = 1 - E j := by
    intro E h j; simp only [hx, neg_neg]; exact Real.exp_log (by linarith [h j])
  have hprod : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ r,
      ∏ i, (1 - E i) ^ (A i r) = Real.exp (-∑ i, (A i r : ℝ) * x E i) := by
    intro E h r
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl; intro i _
    rw [← hexp E h i, ← Real.exp_nat_mul]; congr 1; ring
  have hl := hlt E hK hF
  have hl' := hlt E' hK' hF'
  -- the per-link terms are nonnegative, and vanish only when the blocking agrees
  set T : Fin J → ℝ := fun j => (x E j - x E' j) * (L E j - L E' j) with hT
  have hTpos : ∀ j, E j ≠ E' j → 0 < T j := by
    intro j hne
    have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → erlang a (C j) ≤ erlang b (C j) := by
      intro a b ha hab
      rcases eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact le_of_lt (sn3_erlang_strict _ (hC j) ha h)
    have key : ∀ (E E' : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
        (∀ j, E' j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E' → E j < E' j →
        x E j < x E' j ∧ L E j < L E' j := by
      intro E E' hK hF hK' hF' hlt'
      have h1 := hlt E hK hF j
      have h2 := hlt E' hK' hF' j
      constructor
      · simp only [hx, neg_lt_neg_iff]
        exact Real.log_lt_log (by linarith) (by linarith)
      · have hρ : (1 - E j)⁻¹ * L E j < (1 - E' j)⁻¹ * L E' j := by
          by_contra hc
          push Not at hc
          have := hmono _ _ (hρ0 E' hK' j) hc
          rw [← hF j, ← hF' j] at this
          linarith
        rw [← hcar E hK hF j, ← hcar E' hK' hF' j]
        exact sn3_carried_strict _ (hC j) (hρ0 E hK j) hρ
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨h1, h2⟩ := key E E' hK hF hK' hF' h
      simp only [hT]; nlinarith
    · obtain ⟨h1, h2⟩ := key E' E hK' hF' hK hF h
      simp only [hT]; nlinarith
  have hTnn : ∀ j, 0 ≤ T j := by
    intro j
    by_cases h : E j = E' j
    · simp only [hT, hx, h, sub_self, zero_mul, le_refl]
    · exact le_of_lt (hTpos j h)
  -- the sum of the per-link terms is a sum over routes of nonpositive terms
  set s : (Fin J → ℝ) → Fin R → ℝ := fun E r => ∑ i, (A i r : ℝ) * x E i with hs
  have hLe : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j,
      L E j = ∑ r, (A j r : ℝ) * ν r * Real.exp (-s E r) := by
    intro E h j
    simp only [hLdef, hs]
    apply Finset.sum_congr rfl; intro r _
    rw [hprod E h r]
  have hsum : ∑ j, T j = ∑ r, ν r * ((s E r - s E' r) *
      (Real.exp (-s E r) - Real.exp (-s E' r))) := by
    simp only [hT]
    rw [show (∑ j, (x E j - x E' j) * (L E j - L E' j))
        = ∑ j, ∑ r, (x E j - x E' j) * ((A j r : ℝ) * ν r *
            (Real.exp (-s E r) - Real.exp (-s E' r))) from by
      apply Finset.sum_congr rfl; intro j _
      rw [hLe E hl j, hLe E' hl' j, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; ring]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hroute : ∀ r, ν r * ((s E r - s E' r) * (Real.exp (-s E r) - Real.exp (-s E' r))) ≤ 0 := by
    intro r
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hν r))
    rcases le_total (s E r) (s E' r) with h | h
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hle0 : ∑ j, T j ≤ 0 := by
    rw [hsum]; exact Finset.sum_nonpos (fun r _ => hroute r)
  have hzero : ∀ j ∈ Finset.univ, T j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hTnn j)).1
      (le_antisymm hle0 (Finset.sum_nonneg (fun j _ => hTnn j)))
  funext j
  by_contra hne
  have := hTpos j hne
  rw [hzero j (Finset.mem_univ j)] at this
  exact lt_irrefl _ this

lemma sn3_exists {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ ErlangFixedPoint A ν C E := by
  set ρt : (Fin J → ℝ) → Fin J → ℝ := fun E j => ∑ r, (A j r : ℝ) * ν r *
    ((1 - E j) ^ (A j r - 1) * ∏ i ∈ Finset.univ.erase j, (1 - E i) ^ (A i r)) with hρt
  set F : (Fin J → ℝ) → (Fin J → ℝ) := fun E j => erlang (ρt E j) (C j) with hF
  set K : Set (Fin J → ℝ) := Set.Icc 0 1 with hK
  have hmemK : ∀ E, E ∈ K ↔ ∀ j, E j ∈ Set.Icc (0 : ℝ) 1 := by
    intro E
    simp only [hK, Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  have hρt0 : ∀ E ∈ K, ∀ j, 0 ≤ ρt E j := by
    intro E hE j
    have h := (hmemK E).1 hE
    apply Finset.sum_nonneg; intro r _
    apply mul_nonneg (mul_nonneg (by positivity) (le_of_lt (hν r)))
    apply mul_nonneg (pow_nonneg (by linarith [(h j).2]) _)
    apply Finset.prod_nonneg; intro i _
    exact pow_nonneg (by linarith [(h i).2]) _
  have hρc : ∀ j, Continuous fun E : Fin J → ℝ => ρt E j := by
    intro j
    simp only [hρt]
    fun_prop
  have hcont : ContinuousOn F K := by
    apply continuousOn_pi.2; intro j
    simp only [hF, erlang]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro E hE
    have := sn3_S_pos (C j) (hρt0 E hE j)
    unfold sn3S at this
    linarith
  have hmaps : Set.MapsTo F K K := by
    intro E hE
    exact (hmemK _).2 fun j => ⟨sn3_erlang_nonneg _ (hρt0 E hE j),
      le_of_lt (sn3_erlang_lt_one _ (hC j) (hρt0 E hE j))⟩
  have hne : K.Nonempty := ⟨0, (hmemK 0).2 fun j => by simp⟩
  obtain ⟨E, hE, hfix⟩ := AGT.brouwer_fixed_point (convex_Icc 0 1) isCompact_Icc hne F hcont hmaps
  refine ⟨E, (hmemK E).1 hE, fun j => ?_⟩
  have h1 : E j = erlang (ρt E j) (C j) := (congrFun hfix j).symm
  have hlt : E j < 1 := by rw [h1]; exact sn3_erlang_lt_one _ (hC j) (hρt0 E hE j)
  have hne1 : (1 - E j) ≠ 0 := by linarith
  have hρ : ρt E j = (1 - E j)⁻¹ * ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r) := by
    simp only [hρt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (1 - E i) ^ (A i r)) (Finset.mem_univ j)]
    rcases Nat.eq_zero_or_pos (A j r) with h0 | hpos
    · simp [h0]
    · obtain ⟨a, ha⟩ : ∃ a, A j r = a + 1 := ⟨A j r - 1, by omega⟩
      rw [ha, Nat.add_sub_cancel, pow_succ]
      field_simp
  conv_lhs => rw [h1]
  rw [hρ]

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃! E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ ErlangFixedPoint A ν C E := by
  obtain ⟨E, hEK, hEfix⟩ := sn3_exists A ν C hν hC
  exact ⟨E, ⟨hEK, hEfix⟩, fun E' hE' => sn3_unique A ν C hν hC E' E hE'.1 hE'.2 hEK hEfix⟩
