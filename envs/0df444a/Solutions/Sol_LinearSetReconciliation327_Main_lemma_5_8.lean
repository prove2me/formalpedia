-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T14:12:16.867982+00:00
-- url     : https://prove2.me/submissions/904e1ac9-cee9-4bb0-ba69-81221ec2d035

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

set_option maxHeartbeats 2000000

/-! ## Auxiliary lemmas for Lemma 5.8 (entropy cost of a recursive node)

We reproduce the elementary prefix-tail estimates (Lemma 4.6), the `hN` identity and some
expectation and counting lemmas.  The main proof then uses crude but sufficient bounds:
`Q_s ≤ Y`, `Q_s ≥ Y·2^{-s}`, `Σ_s Q_s ≲ Y/ρ` and `Σ_s s·Q_s ≲ Y/ρ²`, which give
`Σ_s h_Y(2^{-c}Q_s) ≤ 2^{-C}·poly(C)·(M+1)·Y ≤ h_N(Y)/8` for large `C`. -/

/-- All unmarked logarithms are to base two. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

lemma lg_two : lg 2 = 1 := by
  rw [lg_eq_log_div, div_self (ne_of_gt (by linarith [Real.log_two_gt_d9] : (0 : ℝ) < Real.log 2))]

lemma lg_exp_one : lg (Real.exp 1) = 1 / Real.log 2 := by
  rw [lg_eq_log_div, Real.log_exp]

lemma one_le_lg_exp : (1 : ℝ) ≤ lg (Real.exp 1) := by
  rw [lg_exp_one]
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [le_div_iff₀ h0]
  linarith

lemma lg_exp_one_le_two : lg (Real.exp 1) ≤ 2 := by
  rw [lg_exp_one]
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [div_le_iff₀ h0]
  linarith [Real.log_two_gt_d9]

/-- `log x / x ≤ log e` for `x ≥ 1`. -/
lemma lg_div_self_le {x : ℝ} (hx : 1 ≤ x) : lg x / x ≤ lg (Real.exp 1) := by
  have hx0 : 0 < x := by linarith
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have h1 : lg x / x = (Real.log x / x) / Real.log 2 := by
    rw [lg_eq_log_div]
    field_simp
  rw [h1, lg_exp_one, div_le_div_iff_of_pos_right h0, div_le_one hx0]
  exact hlogx

/-! ### The platform functions `G` and `hN` -/

lemma G_nonneg (a : ℕ) (z : ℝ) : 0 ≤ G a z := by
  unfold G
  exact le_min zero_le_one (Real.rpow_nonneg (by norm_num) _)

lemma G_le_one (a : ℕ) (z : ℝ) : G a z ≤ 1 := min_le_left _ _

lemma G_le_rpow (a : ℕ) (z : ℝ) : G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := min_le_right _ _

/-- `2^{-r} = (1/2)^r` for natural `r`. -/
lemma two_rpow_neg_nat (r : ℕ) : (2 : ℝ) ^ (-(r : ℝ)) = (1 / 2 : ℝ) ^ r := by
  have h1 : (2 : ℝ) ^ (-(r : ℝ)) = ((2 : ℝ) ^ (-1 : ℝ)) ^ (r : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h1, Real.rpow_neg_one, Real.rpow_natCast]
  norm_num

lemma two_rpow_neg_le_one (s : ℕ) : (2 : ℝ) ^ (-(s : ℝ)) ≤ 1 := by
  rw [two_rpow_neg_nat]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Tail estimate: if `z < k + 1` and `a ≥ k + 1` then `G a z ≤ (1/2)^{a-k-1}`. -/
lemma G_tail_le {z : ℝ} {k a : ℕ} (hz : z < (k : ℝ) + 1) (ha : k + 1 ≤ a) :
    G a z ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := by
  have hcast : ((a - (k + 1) : ℕ) : ℝ) = (a : ℝ) - ((k : ℝ) + 1) := by
    have h := Nat.sub_add_cancel ha
    have h' := congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linarith
  have h2 : z - (a : ℝ) ≤ -(((a - (k + 1) : ℕ)) : ℝ) := by
    linarith
  calc G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := G_le_rpow a z
    _ ≤ (2 : ℝ) ^ (-(((a - (k + 1) : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    _ = (1 / 2 : ℝ) ^ (a - (k + 1)) := two_rpow_neg_nat _

lemma tsum_half_pow : ∑' r : ℕ, (1 / 2 : ℝ) ^ r = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

lemma summable_half_pow : Summable fun r : ℕ => (1 / 2 : ℝ) ^ r :=
  summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

lemma tsum_half_pow_mul : ∑' r : ℕ, (r : ℝ) * (1 / 2 : ℝ) ^ r = 2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

lemma summable_half_pow_mul : Summable fun r : ℕ => (r : ℝ) * (1 / 2 : ℝ) ^ r := by
  simpa [div_pow] using
    summable_pow_mul_geometric_of_norm_lt_one (k := 1) (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

/-- Shifting a summable nonnegative sequence down by `k` only decreases its finite sums. -/
lemma sum_shift_le_tsum {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hsum : Summable f)
    {s : Finset ℕ} {k : ℕ} (hk : ∀ a ∈ s, k ≤ a) :
    ∑ a ∈ s, f (a - k) ≤ ∑' i, f i := by
  have hinj : Set.InjOn (fun a : ℕ => a - k) (s : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hk a ha
    have h2 := hk b hb
    have hab' : a - k = b - k := hab
    omega
  rw [← Finset.sum_image hinj]
  exact hsum.sum_le_tsum _ (fun i _ => hf i)

lemma head_card_le (n k : ℕ) :
    ((range n).filter (fun a => a ≤ k)).card ≤ k + 1 := by
  have h : (range n).filter (fun a => a ≤ k) ⊆ range (k + 1) := by
    intro a ha
    simp only [mem_filter, mem_range] at ha
    simp only [mem_range]
    omega
  calc ((range n).filter (fun a => a ≤ k)).card ≤ (range (k + 1)).card := card_le_card h
    _ = k + 1 := by simp

/-- Head of the first sum: the first `k+1` terms contribute at most `k+1`. -/
lemma sum_G_head_le (z : ℝ) (k n : ℕ) :
    ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z ≤ (k : ℝ) + 1 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => a ≤ k), (1 : ℝ) :=
    sum_le_sum (fun a _ => G_le_one a z)
  rw [sum_const, nsmul_eq_mul, mul_one] at h1
  have h2 : ((((range n).filter (fun a => a ≤ k)).card : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
    have hc : (((range n).filter (fun a => a ≤ k)).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast head_card_le n k
    push_cast at hc
    linarith
  linarith

/-- Tail of the first sum: geometric decay contributes at most `2`. -/
lemma sum_G_tail_le (z : ℝ) (k n : ℕ) (hkz' : z < (k : ℝ) + 1) :
    ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z ≤ 2 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    refine sum_le_sum (fun a ha => ?_)
    simp only [mem_filter, mem_range] at ha
    exact G_tail_le hkz' (by omega)
  have h2 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (1 / 2 : ℝ) ^ r) (fun i => by positivity)
      summable_half_pow (s := (range n).filter (fun a => ¬ a ≤ k)) (k := k + 1) (fun a ha => by
        simp only [mem_filter, mem_range] at ha
        omega)
    rw [tsum_half_pow] at h
    exact h
  linarith

/-- Head of the second sum: at most `(k+1) z ≤ z(1+z)`. -/
lemma sum_aG_head_le (z : ℝ) (k n : ℕ) (hz : 0 ≤ z) (hkz : (k : ℝ) ≤ z) :
    ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z ≤ z * (z + 1) := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z
      ≤ ∑ a ∈ (range n).filter (fun a => a ≤ k), z := by
    refine sum_le_sum (fun a ha => ?_)
    simp only [mem_filter, mem_range] at ha
    have ha_le : (a : ℝ) ≤ (k : ℝ) := by exact_mod_cast ha.2
    have hG1 : G a z ≤ 1 := G_le_one a z
    have hG0 : 0 ≤ G a z := G_nonneg a z
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  rw [sum_const, nsmul_eq_mul] at h1
  have hcard : ((((range n).filter (fun a => a ≤ k)).card : ℕ) : ℝ) ≤ z + 1 := by
    have hc : (((range n).filter (fun a => a ≤ k)).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast head_card_le n k
    push_cast at hc
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcard hz]

/-- Tail of the second sum: `∑_{a>k} a G_a(z) ≤ 2k+4 ≤ 2z+4`. -/
lemma sum_aG_tail_le (z : ℝ) (k n : ℕ) (hkz : (k : ℝ) ≤ z)
    (hkz' : z < (k : ℝ) + 1) :
    ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (a : ℝ) * G a z ≤ 2 * z + 4 := by
  classical
  set T : Finset ℕ := (range n).filter (fun a => ¬ a ≤ k) with hT
  have h1 : ∑ a ∈ T, (a : ℝ) * G a z
      ≤ ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    refine sum_le_sum (fun a ha => ?_)
    rw [hT] at ha
    simp only [mem_filter, mem_range] at ha
    have hka : k + 1 ≤ a := by omega
    have hgt : G a z ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := G_tail_le hkz' hka
    have hG0 : 0 ≤ G a z := G_nonneg a z
    have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := by positivity
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  have hdecomp : ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1))
      = ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)))
        + ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    have hpt : ∀ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1))
        = ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (a - (k + 1))
          + (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
      intro a ha
      rw [hT] at ha
      simp only [mem_filter, mem_range] at ha
      have hka : k + 1 ≤ a := by omega
      have hcast : (a : ℝ) = (k : ℝ) + 1 + ((a - (k + 1) : ℕ) : ℝ) := by
        have h := Nat.sub_add_cancel hka
        have h' := congrArg (fun x : ℕ => (x : ℝ)) h
        push_cast at h'
        linarith
      rw [hcast]
      ring
    rw [sum_congr rfl hpt, sum_add_distrib, mul_sum]
  have hb1 : ∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (1 / 2 : ℝ) ^ r) (fun i => by positivity)
      summable_half_pow (s := T) (k := k + 1)
      (fun a ha => by rw [hT] at ha; simp only [mem_filter] at ha; omega)
    rw [tsum_half_pow] at h
    exact h
  have hb2 : ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (r : ℝ) * (1 / 2 : ℝ) ^ r)
      (fun i => by positivity) summable_half_pow_mul (s := T) (k := k + 1)
      (fun a ha => by rw [hT] at ha; simp only [mem_filter] at ha; omega)
    rw [tsum_half_pow_mul] at h
    exact h
  calc ∑ a ∈ T, (a : ℝ) * G a z
      ≤ ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := h1
    _ = ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)))
          + ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := hdecomp
    _ ≤ 2 * z + 4 := by
        have h2 : ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1))) ≤ ((k : ℝ) + 1) * 2 :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
        linarith

/-- `∑_{a<n} G_a(z) ≤ z + 32`. -/
lemma sum_G_le (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    ∑ a ∈ range n, G a z ≤ z + 32 := by
  classical
  set k := Nat.floor z with hk
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hkz' : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsplit : ∑ a ∈ range n, G a z
      = ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
        + ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hhead := sum_G_head_le z k n
  have htail := sum_G_tail_le z k n hkz'
  linarith

/-- `∑_{a<n} a·G_a(z) ≤ 32(1+z)^2`. -/
lemma sum_aG_le (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    ∑ a ∈ range n, (a : ℝ) * G a z ≤ 32 * (1 + z) ^ 2 := by
  classical
  set k := Nat.floor z with hk
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hkz' : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsplit : ∑ a ∈ range n, (a : ℝ) * G a z
      = ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z
        + ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (a : ℝ) * G a z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hhead := sum_aG_head_le z k n hz hkz
  have htail := sum_aG_tail_le z k n hkz hkz'
  have hfin : z * (z + 1) + (2 * z + 4) ≤ 32 * (1 + z) ^ 2 := by
    nlinarith [hz, sq_nonneg z]
  linarith

/-- `h_N(z) = z log(eN/z)` for `z > 0`. -/
lemma hN_eq {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {z : ℝ} (hz : 0 < z) :
    hN N z = z * lg (Real.exp 1 * N) - z * lg z := by
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨Real.exp_ne_zero 1, hN0⟩
  rw [hN, if_neg (ne_of_gt hz)]
  simp only [lg]
  rw [Real.logb_div heN (ne_of_gt hz)]
  ring

/-- `h_N(z) = z log(eN/z)` for `z > 0`, in quotient form. -/
lemma hN_eq' {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {z : ℝ} (hz : 0 < z) :
    hN N z = z * lg (Real.exp 1 * N / z) := by
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨Real.exp_ne_zero 1, hN0⟩
  rw [hN_eq hN0 hz, ← mul_sub]
  congr 1
  simp only [lg]
  rw [← Real.logb_div heN (ne_of_gt hz)]

/-- `G_0(z) = 1` for `z ≥ 0`. -/
lemma G_zero (z : ℝ) (hz : 0 ≤ z) : G 0 z = 1 := by
  unfold G
  rw [min_eq_left]
  have h : (0 : ℝ) ≤ z - 0 := by linarith
  simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) h

/-- `2^{-s} ≤ G_s(z)` for `z ≥ 0`. -/
lemma two_rpow_neg_le_G (s : ℕ) (z : ℝ) (hz : 0 ≤ z) : (2 : ℝ) ^ (-(s : ℝ)) ≤ G s z := by
  unfold G
  refine le_min (two_rpow_neg_le_one s) ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : (-(s : ℝ)) ≤ z - (s : ℝ))

/-! ### Expectation over the uniform law -/

lemma expU_mono {α : Type} [Fintype α] (hα : 0 < Fintype.card α) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : expU f ≤ expU g := by
  unfold expU
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma expU_nonneg {α : Type} [Fintype α] (hα : 0 < Fintype.card α) {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ expU f := by
  unfold expU
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (by positivity)

lemma expU_const {α : Type} [Fintype α] (hα : 0 < Fintype.card α) (r : ℝ) :
    expU (fun _ : α => r) = r := by
  unfold expU
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  field_simp

lemma expU_finset_sum {α ι : Type} [Fintype α] (_hα : 0 < Fintype.card α)
    (s : Finset ι) (f : α → ι → ℝ) :
    expU (fun a => ∑ i ∈ s, f a i) = ∑ i ∈ s, expU (fun a => f a i) := by
  unfold expU
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]

lemma expU_mul_const {α : Type} [Fintype α] (_hα : 0 < Fintype.card α) (f : α → ℝ) (r : ℝ) :
    expU (fun a => r * f a) = r * expU f := by
  unfold expU
  rw [← Finset.mul_sum]
  field_simp

/-! ### Counting lemmas for rows -/

/-- The size of row `j` is bounded by `⌈N/m⌉`. -/
lemma rowLen_le_ceil {N m j : ℕ} (hm : 0 < m) : rowLen N m j ≤ ⌈(N : ℝ) / (m : ℝ)⌉₊ := by
  rw [rowLen]
  have hmaps : Set.MapsTo (fun p : ℕ => p / m)
      ↑((range N).filter (fun p => p % m = j)) ↑(range ⌈(N : ℝ) / (m : ℝ)⌉₊) := by
    intro p hp
    simp only [mem_coe, mem_filter, mem_range] at hp ⊢
    obtain ⟨hpN, -⟩ := hp
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdiv : ((p / m : ℕ) : ℝ) ≤ (p : ℝ) / (m : ℝ) := Nat.cast_div_le
    have hlt : (p : ℝ) / (m : ℝ) < (N : ℝ) / (m : ℝ) := by
      rw [div_lt_div_iff_of_pos_right hmR]
      exact_mod_cast hpN
    have h2 : ((p / m : ℕ) : ℝ) < (N : ℝ) / (m : ℝ) := lt_of_le_of_lt hdiv hlt
    have h3 : ¬ (⌈(N : ℝ) / (m : ℝ)⌉₊ ≤ p / m) := by
      rw [Nat.ceil_le]
      linarith
    omega
  have hinj : Set.InjOn (fun p : ℕ => p / m) ↑((range N).filter (fun p => p % m = j)) := by
    intro p hp q hq hpq
    simp only [mem_coe, mem_filter, mem_range] at hp hq
    change p / m = q / m at hpq
    have hp1 := Nat.div_add_mod p m
    have hq1 := Nat.div_add_mod q m
    rw [hpq] at hp1
    rw [hq.2] at hq1
    omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- The size of row `j` is at most `2N/m`. -/
lemma rowLen_le_two {N m j : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (rowLen N m j : ℝ) ≤ 2 * (N : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : (rowLen N m j : ℝ) ≤ (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast rowLen_le_ceil (N := N) (m := m) (j := j) hm
  have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]
    linarith
  have h2 : (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) < (N : ℝ) / (m : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  calc (rowLen N m j : ℝ) ≤ (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) := h1
    _ ≤ (N : ℝ) / (m : ℝ) + 1 := le_of_lt h2
    _ ≤ 2 * (N : ℝ) / (m : ℝ) := by
        rw [show 2 * (N : ℝ) / (m : ℝ) = (N : ℝ) / (m : ℝ) + (N : ℝ) / (m : ℝ) by ring]
        linarith

/-- The card of the `π`-fiber over row `j` is the row length. -/
lemma card_fiber_eq_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) :
    ((univ.filter (fun p : Fin N => (π p).val % m = j)).card) = rowLen N m j := by
  rw [rowLen]
  refine Finset.card_bij (fun p (_ : p ∈ univ.filter (fun p : Fin N => (π p).val % m = j)) => (π p).val)
    ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_range] at hp ⊢
    exact ⟨(π p).isLt, hp⟩
  · intro p _ q _ h
    exact π.injective (Fin.ext h)
  · intro q hq
    simp only [mem_filter, mem_range] at hq
    exact ⟨π.symm ⟨q, hq.1⟩, by simp [hq.2], by simp⟩

/-- A row image has at most `rowLen` elements. -/
lemma rowImage_card_le_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    (rowImage N m π j S).card ≤ rowLen N m j := by
  classical
  unfold rowImage
  calc ((univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).image
        (fun i => (π i).val / m)).card
      ≤ ((univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).card) :=
        Finset.card_image_le
    _ ≤ ((univ.filter (fun i : Fin N => (π i).val % m = j)).card) :=
        Finset.card_le_card (by
          intro i
          simp only [mem_filter, mem_univ, true_and]
          tauto)
    _ = rowLen N m j := card_fiber_eq_rowLen π

/-- `sigma jCard Nj r ≤ Nj`. -/
lemma sigma_le {jCard Nj r : ℕ} (h : jCard ≤ Nj) : HintParams.sigma jCard Nj r ≤ Nj := by
  unfold HintParams.sigma
  rw [Nat.ceil_le]
  have hsum_le : (∑ h ∈ range (r + 1), (Nj - jCard).choose h) ≤ 2 ^ (Nj - jCard) := by
    by_cases hle : r + 1 ≤ Nj - jCard + 1
    · have hsub : range (r + 1) ⊆ range (Nj - jCard + 1) := by
        intro x hx
        simp only [mem_range] at hx ⊢
        omega
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun x => (Nj - jCard).choose x) (fun i _ _ => Nat.zero_le _)
      rwa [Nat.sum_range_choose] at h2
    · have hsub : range (Nj - jCard + 1) ⊆ range (r + 1) := by
        intro x hx
        simp only [mem_range] at hx ⊢
        omega
      have hzero : ∀ x ∈ range (r + 1), x ∉ range (Nj - jCard + 1) →
          (Nj - jCard).choose x = 0 := by
        intro x hx hx'
        simp only [mem_range] at hx hx'
        exact Nat.choose_eq_zero_of_lt (by omega)
      rw [← Finset.sum_subset hsub hzero, Nat.sum_range_choose]
  have hmain : (2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) ≤ 2 ^ Nj := by
    calc 2 ^ jCard * (∑ h ∈ range (r + 1), (Nj - jCard).choose h)
        ≤ 2 ^ jCard * 2 ^ (Nj - jCard) := Nat.mul_le_mul_left _ hsum_le
      _ = 2 ^ (jCard + (Nj - jCard)) := (Nat.pow_add _ _ _).symm
      _ = 2 ^ Nj := by rw [Nat.add_sub_cancel' h]
  have hpos : (0 : ℝ) < ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ) := by
    have h2 : 0 < (2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) := by
      have h3 : 0 < ∑ h ∈ range (r + 1), (Nj - jCard).choose h := by
        apply Finset.sum_pos'
        · intro x _; exact Nat.zero_le _
        · refine ⟨0, by simp, ?_⟩
          simp
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) h3
    exact_mod_cast h2
  have hmainR : ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((Nj : ℕ) : ℝ) := by
    have h1 : ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)
        ≤ ((2 ^ Nj : ℕ) : ℝ) := by exact_mod_cast hmain
    have h2 : ((2 ^ Nj : ℕ) : ℝ) = (2 : ℝ) ^ ((Nj : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
      norm_num
    rw [h2] at h1
    exact h1
  have hlg : lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ))
      ≤ (Nj : ℝ) := by
    calc lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ))
        ≤ lg ((2 : ℝ) ^ ((Nj : ℕ) : ℝ)) := Real.logb_le_logb_of_le (by norm_num) hpos hmainR
      _ = (Nj : ℝ) := by
            simp only [lg]
            rw [Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
  simpa using hlg

/-- `sigmaStar` is at most the row length. -/
lemma sigmaStar_le_rowLen (P : HintParams) {N X Y j : ℕ} (π : Equiv.Perm (Fin N)) :
    (P.sigmaStar N X Y π j : ℝ) ≤ (rowLen N (P.rows X Y) j : ℝ) := by
  classical
  have h := sigma_le (jCard := (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card)
    (Nj := rowLen N (P.rows X Y) j) (r := (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card)
    (rowImage_card_le_rowLen π _)
  unfold HintParams.sigmaStar
  dsimp only
  exact_mod_cast h

/-! ### Numeric lemmas -/

/-- For `C ≥ 40`, `60 C² ≤ 2^C / 8`. -/
lemma sixty_sq_le_pow (C : ℕ) (hC : 40 ≤ C) : 60 * (C : ℝ) ^ 2 ≤ (2 : ℝ) ^ C * (1 / 8) := by
  induction C, hC using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
      have hstep : 60 * ((m : ℝ) + 1) ^ 2 ≤ 2 * (60 * (m : ℝ) ^ 2) := by nlinarith
      calc 60 * ((m + 1 : ℕ) : ℝ) ^ 2 = 60 * ((m : ℝ) + 1) ^ 2 := by push_cast; ring
        _ ≤ 2 * (60 * (m : ℝ) ^ 2) := hstep
        _ ≤ 2 * ((2 : ℝ) ^ m * (1 / 8)) := by linarith
        _ = (2 : ℝ) ^ (m + 1) * (1 / 8) := by rw [pow_succ]; ring

lemma two_rpow_neg_sixty (C : ℕ) (hC : 40 ≤ C) :
    (2 : ℝ) ^ (-(C : ℝ)) * (60 * (C : ℝ) ^ 2) ≤ 1 / 8 := by
  have h := sixty_sq_le_pow C hC
  have h2 : (2 : ℝ) ^ (-(C : ℝ)) = ((2 : ℝ) ^ C)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h2, inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ C)]
  linarith

/-- The summand `2^{-c} Q_s` of Lemma 5.8. -/
def Qterm (P : HintParams) (N X Y s : ℕ) : ℝ := ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s

/-- The pointwise profile whose expectation is `Q_s`. -/
def nodeProfile (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (s : ℕ) : ℝ :=
  ∑ j ∈ range (P.rows X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))

lemma Q_eq_expU (P : HintParams) (N X Y s : ℕ) :
    P.Q N X Y s = expU (fun π => nodeProfile P N X Y π s) := rfl

/-- Lemma 5.8, PDF p.23 (printed p.22). `A`, then `C`, are sufficiently large. -/
theorem lemma_5_8 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∑ s ∈ range (P.ell N X Y), hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) ≤ hN N Y / 8 := by
  refine ⟨0, fun A _ => ⟨40, fun C hC => ?_⟩⟩
  intro n lam N X Y P hargs hrule
  simp only [HintParams.NodeArgs] at hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs
  have hrows : P.rows X Y = Y := by
    by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
    · have h := hrule
      unfold HintParams.rule at h
      rw [if_pos h1] at h
      exact absurd h (by decide)
    · by_cases h2 : (HintParams.D N X Y : ℝ) ≤ (P.C : ℝ) ^ 3 * P.lamStar * P.lgn ^ 6 / P.eta ^ 2
      · have h := hrule
        unfold HintParams.rule at h
        rw [if_neg h1, if_pos h2] at h
        exact absurd h (by decide)
      · have h := hrule
        unfold HintParams.rule at h
        rw [if_neg h1, if_neg h2] at h
        split_ifs at h with h3
        exact h3
  have hcdef : P.c N X Y = 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + C := by
    unfold HintParams.c
    rw [if_pos hrule]
  rcases Nat.eq_zero_or_pos Y with hY0 | hYpos
  · subst hY0
    have hrows0 : P.rows X 0 = 0 := hrows
    have hQzero : ∀ s, P.Q N X 0 s = 0 := by
      intro s
      have h1 : P.Q N X 0 s = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ j ∈ range (P.rows X 0), G s ((P.sigmaStar N X 0 π j : ℝ) + (P.c N X 0 : ℝ))) := rfl
      rw [h1, hrows0]
      simp [expU]
    simp only [hQzero, mul_zero]
    simp [hN]
  · -- main case `Y ≥ 1`
    have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
    have hYne : (Y : ℝ) ≠ 0 := ne_of_gt hYposR
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
    have hYN' : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
    have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
      rw [Fintype.card_perm, Fintype.card_fin]
      exact Nat.factorial_pos N
    set M : ℝ := lg ((N : ℝ) / (Y : ℝ)) with hM
    set ρ : ℝ := (Y : ℝ) / (N : ℝ) with hρ
    have hM0 : 0 ≤ M := by
      rw [hM]
      exact Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hYposR]; linarith)
    have hρpos : 0 < ρ := by rw [hρ]; positivity
    have hρle1 : ρ ≤ 1 := by rw [hρ, div_le_one hNposR]; exact hYN'
    have hρM : ρ * M ≤ lg (Real.exp 1) := by
      have hx1 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
        rw [le_div_iff₀ hYposR]; linarith
      have h := lg_div_self_le hx1
      have h1eq : ρ * M = lg ((N : ℝ) / (Y : ℝ)) / ((N : ℝ) / (Y : ℝ)) := by
        rw [hρ, hM]
        field_simp
      rw [h1eq]
      exact h
    have hc_le : (P.c N X Y : ℝ) ≤ (C : ℝ) + 2 * M + 2 := by
      have hceil : ((⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ M + 1 := by
        have h := Nat.ceil_lt_add_one (R := ℝ) (a := lg ((N : ℝ) / (Y : ℝ)))
          (by rw [← hM]; exact hM0)
        rw [← hM] at h
        linarith
      rw [hcdef]
      push_cast
      linarith
    -- `2^{-c} ≤ 2^{-C} ρ²`
    have hC0_le : ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2 := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hk : M ≤ ((⌈M⌉₊ : ℕ) : ℝ) := Nat.le_ceil M
      have hNM : (2 : ℝ) ^ M = (N : ℝ) / (Y : ℝ) := by
        rw [hM]
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      have hpowc : (2 : ℝ) ^ (P.c N X Y)
          = (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ (2 * ((⌈M⌉₊ : ℕ) : ℝ)) := by
        rw [hcdef, ← Real.rpow_natCast]
        have he : (((2 * ⌈M⌉₊ + C : ℕ)) : ℝ) = (C : ℝ) + 2 * ((⌈M⌉₊ : ℕ) : ℝ) := by
          push_cast
          ring
        rw [he, Real.rpow_add h2pos]
      have hge2 : (2 : ℝ) ^ (2 * M) ≤ (2 : ℝ) ^ (2 * ((⌈M⌉₊ : ℕ) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
      have hsq : (2 : ℝ) ^ (2 * M) = ((N : ℝ) / (Y : ℝ)) * ((N : ℝ) / (Y : ℝ)) := by
        rw [show (2 : ℝ) * M = M + M by ring, Real.rpow_add (by norm_num), hNM]
      have hbig : (2 : ℝ) ^ (C : ℝ) * (((N : ℝ) / (Y : ℝ)) * ((N : ℝ) / (Y : ℝ)))
          ≤ (2 : ℝ) ^ (P.c N X Y) := by
        have hh : (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ (2 * M) ≤ (2 : ℝ) ^ (P.c N X Y) := by
          rw [hpowc]
          exact mul_le_mul_of_nonneg_left hge2 (by positivity)
        rwa [hsq] at hh
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (C : ℝ) * (((N : ℝ) / (Y : ℝ)) * ((N : ℝ) / (Y : ℝ))) := by
        positivity
      have hinv : ((2 : ℝ) ^ (C : ℝ) * (((N : ℝ) / (Y : ℝ)) * ((N : ℝ) / (Y : ℝ))))⁻¹
          = (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2 := by
        rw [hρ, mul_inv, mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_div]
        ring
      calc ((2 : ℝ) ^ (P.c N X Y))⁻¹
          ≤ ((2 : ℝ) ^ (C : ℝ) * (((N : ℝ) / (Y : ℝ)) * ((N : ℝ) / (Y : ℝ))))⁻¹ := by
            rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (P.c N X Y)) hpos]
            exact hbig
        _ = (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2 := hinv
    -- row-wise bound on `sigmaStar`
    have hσle : ∀ (π : Equiv.Perm (Fin N)) (j : ℕ),
        (P.sigmaStar N X Y π j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
      intro π j
      have h1 := sigmaStar_le_rowLen (P := P) (N := N) (X := X) (Y := Y) (j := j) π
      have h2 : (rowLen N (P.rows X Y) j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
        rw [hrows]
        exact rowLen_le_two hYpos hYN
      linarith
    -- basic bounds on `Q`
    have hQ_nonneg : ∀ s : ℕ, 0 ≤ P.Q N X Y s := by
      intro s
      rw [Q_eq_expU]
      apply expU_nonneg hcard
      intro π
      simp only [nodeProfile]
      exact Finset.sum_nonneg (fun j _ => G_nonneg _ _)
    have hQ_le : ∀ s : ℕ, P.Q N X Y s ≤ (Y : ℝ) := by
      intro s
      rw [Q_eq_expU]
      calc expU (fun π => nodeProfile P N X Y π s)
          ≤ expU (fun _ : Equiv.Perm (Fin N) => (Y : ℝ)) := by
            apply expU_mono hcard
            intro π
            simp only [nodeProfile]
            rw [hrows]
            calc ∑ j ∈ range Y, G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                ≤ ∑ j ∈ range Y, (1 : ℝ) := Finset.sum_le_sum (fun j _ => G_le_one _ _)
              _ = (Y : ℝ) := by simp
        _ = (Y : ℝ) := expU_const hcard _
    have hQ_ge : ∀ s : ℕ, (Y : ℝ) * (2 : ℝ) ^ (-(s : ℝ)) ≤ P.Q N X Y s := by
      intro s
      rw [Q_eq_expU]
      calc (Y : ℝ) * (2 : ℝ) ^ (-(s : ℝ))
          = expU (fun _ : Equiv.Perm (Fin N) => (Y : ℝ) * (2 : ℝ) ^ (-(s : ℝ))) :=
            (expU_const hcard _).symm
        _ ≤ expU (fun π => nodeProfile P N X Y π s) := by
            apply expU_mono hcard
            intro π
            simp only [nodeProfile]
            rw [hrows]
            calc (Y : ℝ) * (2 : ℝ) ^ (-(s : ℝ)) = ∑ j ∈ range Y, (2 : ℝ) ^ (-(s : ℝ)) := by simp
              _ ≤ ∑ j ∈ range Y, G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) :=
                  Finset.sum_le_sum (fun j _ => two_rpow_neg_le_G s _ (by positivity))
    -- first moment
    have hQ_sum_le : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
        ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := by
      have hexp : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
          = expU (fun π : Equiv.Perm (Fin N) =>
              ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s) := by
        rw [expU_finset_sum hcard]
        exact Finset.sum_congr rfl (fun s _ => Q_eq_expU P N X Y s)
      rw [hexp]
      calc expU (fun π => ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s)
          ≤ expU (fun _ : Equiv.Perm (Fin N) =>
              (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
            apply expU_mono hcard
            intro π
            simp only [nodeProfile]
            rw [hrows]
            rw [Finset.sum_comm]
            have h1 : ∀ j ∈ range Y,
                ∑ s ∈ range (P.ell N X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                ≤ ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) + 32 :=
              fun j _ => sum_G_le _ (by positivity) _
            calc ∑ j ∈ range Y, ∑ s ∈ range (P.ell N X Y),
                  G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                ≤ ∑ j ∈ range Y, (((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) + 32) :=
                  Finset.sum_le_sum h1
              _ = (∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)) + (Y : ℝ) * ((P.c N X Y : ℝ) + 32) := by
                  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  ring
              _ ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) + (Y : ℝ) * ((P.c N X Y : ℝ) + 32) := by
                  have hσ : ∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)
                      ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) := by
                    calc ∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)
                        ≤ ∑ j ∈ range Y, (2 * (N : ℝ) / (Y : ℝ)) :=
                          Finset.sum_le_sum (fun j _ => hσle π j)
                      _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) := by simp
                  linarith
              _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := by ring
        _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := expU_const hcard _
    -- second moment
    have hQs_sum_le : ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
        ≤ 32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2 := by
      have hexp : ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
          = expU (fun π : Equiv.Perm (Fin N) =>
              ∑ s ∈ range (P.ell N X Y), (s : ℝ) * nodeProfile P N X Y π s) := by
        rw [expU_finset_sum hcard]
        exact Finset.sum_congr rfl (fun s _ => by
          rw [Q_eq_expU, expU_mul_const hcard])
      rw [hexp]
      calc expU (fun π => ∑ s ∈ range (P.ell N X Y), (s : ℝ) * nodeProfile P N X Y π s)
          ≤ expU (fun _ : Equiv.Perm (Fin N) =>
              32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2) := by
            apply expU_mono hcard
            intro π
            simp only [nodeProfile]
            rw [hrows]
            have hswap : ∑ s ∈ range (P.ell N X Y), (s : ℝ) * ∑ j ∈ range Y,
                  G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                = ∑ j ∈ range Y, ∑ s ∈ range (P.ell N X Y), (s : ℝ) *
                  G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
            rw [hswap]
            have h1 : ∀ j ∈ range Y,
                ∑ s ∈ range (P.ell N X Y), (s : ℝ) * G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                ≤ 32 * (1 + ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))) ^ 2 :=
              fun j _ => sum_aG_le _ (by positivity) _
            calc ∑ j ∈ range Y, ∑ s ∈ range (P.ell N X Y),
                  (s : ℝ) * G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
                ≤ ∑ j ∈ range Y, 32 * (1 + ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))) ^ 2 :=
                  Finset.sum_le_sum h1
              _ ≤ ∑ j ∈ range Y, 32 * (1 + (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ))) ^ 2 := by
                  apply Finset.sum_le_sum
                  intro j _
                  have h2 : (P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)
                      ≤ 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) := by linarith [hσle π j]
                  have h3 : (0 : ℝ) ≤ 1 + ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) := by linarith [hσle π j]
                  have h4 : (1 + ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))) ^ 2
                      ≤ (1 + (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ))) ^ 2 := by
                    apply pow_le_pow_left₀ h3
                    linarith [hσle π j]
                  linarith
              _ = (Y : ℝ) * (32 * (1 + (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ))) ^ 2) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              _ = 32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2 := by ring
        _ = 32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2 := expU_const hcard _
    -- the summand estimate
    have hterm : ∀ s : ℕ, hN Y (Qterm P N X Y s)
        ≤ Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ)) := by
      intro s
      simp only [Qterm]
      by_cases hx : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s = 0
      · rw [hx, hN]; simp
      · have hxpos : 0 < ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s := by
          have hxnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s :=
            mul_nonneg (by positivity) (hQ_nonneg s)
          rcases lt_or_eq_of_le hxnn with h | h
          · exact h
          · exact absurd h.symm hx
        rw [hN_eq' hYne hxpos]
        have hpow : (2 : ℝ) ^ (-(P.c N X Y : ℝ)) * (2 : ℝ) ^ (-(s : ℝ))
            = (2 : ℝ) ^ (-((P.c N X Y : ℝ) + (s : ℝ))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(P.c N X Y : ℝ)) := by positivity
        have hge' : (Y : ℝ) * (2 : ℝ) ^ (-((P.c N X Y : ℝ) + (s : ℝ)))
            ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s := by
          have h1 := hQ_ge s
          have h2 : (2 : ℝ) ^ (-(P.c N X Y : ℝ)) = ((2 : ℝ) ^ (P.c N X Y))⁻¹ := by
            rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
          calc (Y : ℝ) * (2 : ℝ) ^ (-((P.c N X Y : ℝ) + (s : ℝ)))
              = (2 : ℝ) ^ (-(P.c N X Y : ℝ)) * ((Y : ℝ) * (2 : ℝ) ^ (-(s : ℝ))) := by
                rw [← hpow]; ring
            _ ≤ (2 : ℝ) ^ (-(P.c N X Y : ℝ)) * P.Q N X Y s :=
                mul_le_mul_of_nonneg_left h1 hc0
            _ = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s := by rw [h2]
        have hYle : (Y : ℝ) ≤ (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
            * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ)) := by
          have hpos2 : (0 : ℝ) < (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hge' hpos2.le
          have hid : (Y : ℝ) * (2 : ℝ) ^ (-((P.c N X Y : ℝ) + (s : ℝ)))
              * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ)) = Y := by
            rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            have h0 : -((P.c N X Y : ℝ) + (s : ℝ)) + ((s : ℝ) + (P.c N X Y : ℝ)) = 0 := by ring
            rw [h0, Real.rpow_zero, mul_one]
          rwa [hid] at hmul
        have hbase : Real.exp 1 * (Y : ℝ) / (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
            ≤ Real.exp 1 * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ)) := by
          rw [div_le_iff₀ hxpos]
          calc Real.exp 1 * (Y : ℝ)
              ≤ Real.exp 1 * ((((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
                  * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ))) :=
                mul_le_mul_of_nonneg_left hYle (by positivity)
            _ = Real.exp 1 * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ))
                  * (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) := by ring
        have hval : lg (Real.exp 1 * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ)))
            = lg (Real.exp 1) + ((s : ℝ) + (P.c N X Y : ℝ)) := by
          simp only [lg]
          rw [Real.logb_mul (Real.exp_ne_zero 1) (by positivity),
            Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
        have hlog : lg (Real.exp 1 * (Y : ℝ) / (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s))
            ≤ lg (Real.exp 1) + ((s : ℝ) + (P.c N X Y : ℝ)) := by
          calc lg (Real.exp 1 * (Y : ℝ) / (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s))
              ≤ lg (Real.exp 1 * (2 : ℝ) ^ ((s : ℝ) + (P.c N X Y : ℝ))) := by
                apply Real.logb_le_logb_of_le (by norm_num)
                · exact div_pos (by positivity) hxpos
                · exact hbase
            _ = lg (Real.exp 1) + ((s : ℝ) + (P.c N X Y : ℝ)) := hval
        have hfin : (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
            * lg (Real.exp 1 * (Y : ℝ) / (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s))
            ≤ (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
              * (lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          calc lg (Real.exp 1 * (Y : ℝ) / (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s))
              ≤ lg (Real.exp 1) + ((s : ℝ) + (P.c N X Y : ℝ)) := hlog
            _ = lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ) := by ring
        exact hfin
    -- split the sum
    have hL : ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
        ≤ (lg (Real.exp 1) + (P.c N X Y : ℝ))
            * (((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
          + ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s := by
      have h1 : ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
          ≤ ∑ s ∈ range (P.ell N X Y),
              Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ)) :=
        Finset.sum_le_sum (fun s _ => hterm s)
      have h3 : ∑ s ∈ range (P.ell N X Y), Qterm P N X Y s
          = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s := by
        rw [Finset.mul_sum]
        rfl
      have h4 : ∑ s ∈ range (P.ell N X Y), Qterm P N X Y s * (s : ℝ)
          = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [Qterm]
        ring
      have hsplit : ∀ s : ℕ, Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ))
          = Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ)) + Qterm P N X Y s * (s : ℝ) := by
        intro s; ring
      calc ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
          ≤ ∑ s ∈ range (P.ell N X Y),
              Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ) + (s : ℝ)) := h1
        _ = ∑ s ∈ range (P.ell N X Y), (Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ))
              + Qterm P N X Y s * (s : ℝ)) := by
            rw [Finset.sum_congr rfl (fun s _ => hsplit s)]
        _ = (∑ s ∈ range (P.ell N X Y), Qterm P N X Y s * (lg (Real.exp 1) + (P.c N X Y : ℝ)))
              + ∑ s ∈ range (P.ell N X Y), Qterm P N X Y s * (s : ℝ) := by
            rw [Finset.sum_add_distrib]
        _ = (lg (Real.exp 1) + (P.c N X Y : ℝ)) * (∑ s ∈ range (P.ell N X Y), Qterm P N X Y s)
              + ∑ s ∈ range (P.ell N X Y), Qterm P N X Y s * (s : ℝ) := by
            rw [← Finset.sum_mul]
            ring
        _ = (lg (Real.exp 1) + (P.c N X Y : ℝ))
              * (((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
            + ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s := by
            rw [h3, h4]
    -- bound the two pieces
    have hR2 : ρ ^ 2 * (2 * (N : ℝ) / (Y : ℝ)) = 2 * ρ := by
      rw [hρ]; field_simp
    have hρsqM : ρ ^ 2 * M ≤ 2 := by
      have h1 : ρ * M ≤ 2 := by linarith [hρM, lg_exp_one_le_two]
      nlinarith [hρpos.le, hρle1, h1]
    have hbound1 : (lg (Real.exp 1) + (P.c N X Y : ℝ))
        * (((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
        ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
          * ((C : ℝ) ^ 2 + 44 * (C : ℝ) + 160 + M * (2 * (C : ℝ) + 80)) := by
      have h1 : (lg (Real.exp 1) + (P.c N X Y : ℝ)) ≤ (C : ℝ) + 2 * M + 4 := by
        linarith [hc_le, lg_exp_one_le_two]
      have h2 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
          ≤ (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2
            * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
        calc ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
            ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹
                * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
              apply mul_le_mul_of_nonneg_left hQ_sum_le (by positivity)
          _ ≤ ((2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2)
                * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
              apply mul_le_mul_of_nonneg_right hC0_le (by positivity)
      have h3 : ρ ^ 2 * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) ≤ (C : ℝ) + 40 := by
        have h4 : ρ ^ 2 * (P.c N X Y : ℝ) ≤ ρ ^ 2 * ((C : ℝ) + 2 * M + 2) := by
          apply mul_le_mul_of_nonneg_left hc_le (by positivity)
        have h5 : ρ ^ 2 ≤ 1 := by nlinarith [hρpos.le, hρle1]
        have h6 : ρ ^ 2 * 32 ≤ 32 := by nlinarith
        have hC2 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
        have h8 : ρ ^ 2 * (C : ℝ) ≤ (C : ℝ) := by nlinarith
        have hdist : ρ ^ 2 * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)
            = ρ ^ 2 * (2 * (N : ℝ) / (Y : ℝ)) + ρ ^ 2 * (P.c N X Y : ℝ) + ρ ^ 2 * 32 := by ring
        rw [hdist]
        have hρ2 : (0 : ℝ) ≤ ρ := hρpos.le
        nlinarith [hR2, h4, hρsqM, hρ2, hρle1, h5, h6, h8]
      calc (lg (Real.exp 1) + (P.c N X Y : ℝ))
            * (((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
          ≤ ((C : ℝ) + 2 * M + 4) * ((2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2
              * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))) := by
            apply mul_le_mul h1 h2
              (mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => hQ_nonneg s)))
              (by linarith [hM0])
        _ = (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
              * (((C : ℝ) + 2 * M + 4)
                * (ρ ^ 2 * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))) := by ring
        _ ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (((C : ℝ) + 2 * M + 4) * ((C : ℝ) + 40)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left h3 (by linarith [hM0])
        _ = (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
              * ((C : ℝ) ^ 2 + 44 * (C : ℝ) + 160 + M * (2 * (C : ℝ) + 80)) := by ring
    have hbound2 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
        ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (32 * ((C : ℝ) + 9) ^ 2) := by
      have h2 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
          ≤ (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2
            * (32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2) := by
        calc ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
            ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹
                * (32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2) := by
              apply mul_le_mul_of_nonneg_left hQs_sum_le (by positivity)
          _ ≤ ((2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2)
                * (32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2) := by
              apply mul_le_mul_of_nonneg_right hC0_le (by positivity)
      have h3 : ρ * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ≤ (C : ℝ) + 9 := by
        have h4 : ρ * (2 * (N : ℝ) / (Y : ℝ)) = 2 := by rw [hρ]; field_simp
        have h5 : ρ * (P.c N X Y : ℝ) ≤ ρ * ((C : ℝ) + 2 * M + 2) := by
          apply mul_le_mul_of_nonneg_left hc_le hρpos.le
        have h6 : ρ * M ≤ 2 := by linarith [hρM, lg_exp_one_le_two]
        nlinarith [h4, h5, h6, hρle1, hρpos.le]
      calc ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), (s : ℝ) * P.Q N X Y s
          ≤ (2 : ℝ) ^ (-(C : ℝ)) * ρ ^ 2
            * (32 * (Y : ℝ) * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) ^ 2) := h2
        _ = (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
              * (32 * (ρ * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ))) ^ 2) := by ring
        _ ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (32 * ((C : ℝ) + 9) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have h7 : (0 : ℝ) ≤ ρ * (1 + 2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ)) := by
              apply mul_nonneg hρpos.le
              positivity
            nlinarith [h3, h7]
    -- assemble
    have hpoly : 33 * (C : ℝ) ^ 2 + 620 * (C : ℝ) + 2752 ≤ 60 * (C : ℝ) ^ 2 := by
      have hC40 : (40 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
      nlinarith
    have hmain_le : ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
        ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2 + M * (2 * (C : ℝ) + 80)) := by
      calc ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
          ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
              * ((C : ℝ) ^ 2 + 44 * (C : ℝ) + 160 + M * (2 * (C : ℝ) + 80))
            + (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (32 * ((C : ℝ) + 9) ^ 2) := by
            linarith [hL, hbound1, hbound2]
        _ = (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ)
              * ((33 * (C : ℝ) ^ 2 + 620 * (C : ℝ) + 2752) + M * (2 * (C : ℝ) + 80)) := by ring
        _ ≤ (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2 + M * (2 * (C : ℝ) + 80)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hpoly]
    have hfin_le : (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2 + M * (2 * (C : ℝ) + 80))
        ≤ (Y : ℝ) / 8 + M * (Y : ℝ) / 8 := by
      have hb1 := two_rpow_neg_sixty C hC
      have hb2 : (2 : ℝ) ^ (-(C : ℝ)) * (2 * (C : ℝ) + 80) ≤ 1 / 8 := by
        have hC40 : (40 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
        have hle : 2 * (C : ℝ) + 80 ≤ 60 * (C : ℝ) ^ 2 := by nlinarith
        nlinarith [hb1, hle]
      have h1 : (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2) ≤ (Y : ℝ) * (1 / 8) := by
        calc (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2)
            = (Y : ℝ) * ((2 : ℝ) ^ (-(C : ℝ)) * (60 * (C : ℝ) ^ 2)) := by ring
          _ ≤ (Y : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hb1 hYposR.le
      have h2 : (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (M * (2 * (C : ℝ) + 80))
          ≤ M * (Y : ℝ) * (1 / 8) := by
        calc (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (M * (2 * (C : ℝ) + 80))
            = (M * (Y : ℝ)) * ((2 : ℝ) ^ (-(C : ℝ)) * (2 * (C : ℝ) + 80)) := by ring
          _ ≤ (M * (Y : ℝ)) * (1 / 8) :=
              mul_le_mul_of_nonneg_left hb2 (by nlinarith [hM0, hYposR.le])
      have hsplit : (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2 + M * (2 * (C : ℝ) + 80))
          = (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (60 * (C : ℝ) ^ 2)
            + (2 : ℝ) ^ (-(C : ℝ)) * (Y : ℝ) * (M * (2 * (C : ℝ) + 80)) := by ring
      rw [hsplit]
      linarith
    have hhN : hN N Y = (Y : ℝ) * (M + lg (Real.exp 1)) := by
      rw [hN, if_neg (ne_of_gt hYposR)]
      have h1 : Real.exp 1 * (N : ℝ) / (Y : ℝ) = Real.exp 1 * ((N : ℝ) / (Y : ℝ)) := by ring
      rw [h1]
      have h2 : lg (Real.exp 1 * ((N : ℝ) / (Y : ℝ))) = lg (Real.exp 1) + M := by
        simp only [lg]
        rw [Real.logb_mul (Real.exp_ne_zero 1) (by positivity)]
        rfl
      rw [h2]
      ring
    calc ∑ s ∈ range (P.ell N X Y), hN Y (Qterm P N X Y s)
        ≤ (Y : ℝ) / 8 + M * (Y : ℝ) / 8 := le_trans hmain_le hfin_le
      _ = (Y : ℝ) * (M + 1) / 8 := by ring
      _ ≤ (Y : ℝ) * (M + lg (Real.exp 1)) / 8 := by
          nlinarith [hYposR.le, one_le_lg_exp]
      _ = hN N Y / 8 := by rw [hhN]


end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 5.8 — submission wrapper matching the target statement. -/
theorem solution :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∑ s ∈ range (P.ell N X Y), hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) ≤ hN N Y / 8 :=
  LinearSetReconciliation327.Main.lemma_5_8