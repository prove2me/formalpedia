-- Prove2me | solution 1 for NymanBeurling.damped_moebius_bounded_mean_square
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:55:30.941296+00:00
-- url     : https://prove2.me/submissions/5c22b4f9-ec43-4967-af0a-272b4015baa9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_damped_moebius_finite_head_approximation
import Theorems.Thm_NymanBeurling_damped_moebius_iterated_tail_bound

set_option autoImplicit false
open Filter Topology Finset

private lemma coefficient_sum_shift (L n : ℕ) (ε : ℝ) :
    (∑ d ∈ Finset.Ioc 0 (L+1),
      ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε)*(((n+1)%d:ℕ):ℝ)/(d:ℝ)) =
    ∑ k : Fin L,
      ((ArithmeticFunction.moebius (k.val+2) : ℝ)/(k.val+2:ℝ)^ε)*
        (((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ) := by
  let f : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε)*(((n+1)%d:ℕ):ℝ)/(d:ℝ)
  have hset : Finset.range (L+2) = insert 0 (Finset.Ioc 0 (L+1)) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hr : (∑ d ∈ Finset.range (L+2), f d) = ∑ d ∈ Finset.Ioc 0 (L+1), f d := by
    rw [hset, Finset.sum_insert (by simp)]
    simp [f]
  have hf : (∑ k : Fin L,
      ((ArithmeticFunction.moebius (k.val+2) : ℝ)/(k.val+2:ℝ)^ε)*
        (((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ)) =
      ∑ k ∈ Finset.range L, f (k+2) := by
    simpa only [f, Nat.cast_add, Nat.cast_ofNat] using
      Fin.sum_univ_eq_sum_range (fun k => f (k+2)) L
  rw [hf]
  change (∑ d ∈ Finset.Ioc 0 (L+1), f d) = _
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by
    simp only [f, Nat.mod_one, Nat.cast_zero, mul_zero, zero_div]
  have hfirst : (∑ d ∈ Finset.range 2, f d) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [hf0, hf1]
  rw [← hr, show L+2=2+L by omega, Finset.sum_range_add, hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.add_comm 2 k]

theorem solution :
    ∃ B : ℝ, ∃ᶠ ε : ℝ in 𝓝[>] 0, ∃ᶠ N : ℕ in atTop, ∀ H : ℕ,
      ∑ n ∈ Finset.range H, (1 + ∑ d ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε)*(((n+1)%d:ℕ):ℝ)/(d:ℝ))^2 /
        ((n+1:ℝ)*(n+2:ℝ)) ≤ B := by
  obtain ⟨H₀, ε₀, hε₀, htail⟩ :=
    NymanBeurling.damped_moebius_iterated_tail_bound 1 (by norm_num)
  obtain ⟨ε₁, hε₁, hhead⟩ :=
    NymanBeurling.damped_moebius_finite_head_approximation H₀ 1 (by norm_num)
  refine ⟨2, ?_⟩
  apply Filter.Eventually.frequently
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro ε hε
  have hεa : ε < ε₀ := hε.2.trans_le (min_le_left _ _)
  have hεb : ε < ε₁ := hε.2.trans_le (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := htail ε hε.1 hεa
  obtain ⟨N₁, hN₁⟩ := hhead ε hε.1 hεb
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop (max N₀ N₁ + 1)] with N hN
  have hN0 : N₀ ≤ N-1 := by omega
  have hN1 : N₁ ≤ N-1 := by omega
  have hshift : N-1+1=N := by omega
  let w (n : ℕ) : ℝ :=
    (1 + ∑ k : Fin (N-1),
      ((ArithmeticFunction.moebius (k.val+2) : ℝ)/(k.val+2:ℝ)^ε)*
        (((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ))^2 /
      ((n+1:ℝ)*(n+2:ℝ))
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have ha : (∑ n ∈ Finset.range H₀, w n) < 1 := hN₁ (N-1) hN1
  have hb (H : ℕ) : (∑ n ∈ Finset.Ico H₀ H, w n) < 1 := hN₀ (N-1) hN0 H
  intro H
  have hsame (n : ℕ) := coefficient_sum_shift (N-1) n ε
  rw [hshift] at hsame
  simp_rw [hsame]
  change (∑ n ∈ Finset.range H, w n) ≤ 2
  by_cases hH : H₀ ≤ H
  · rw [← Finset.sum_range_add_sum_Ico w hH]
    have := hb H
    linarith
  · have hle : (∑ n ∈ Finset.range H, w n) ≤ ∑ n ∈ Finset.range H₀, w n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun n _ _ => hw n)
    linarith
