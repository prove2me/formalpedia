-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-17T03:17:22.380371+00:00
-- url     : https://prove2.me/submissions/3cd76c1e-dac0-46e4-a678-63dbacf823a2

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_4
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_6
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_8

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## Lemma 5.9 (Child space and density contraction) — per-node infrastructure

This file is **self-contained**: the elementary toolkit of Lemma 5.8 that it needs (the `lg`
normalisations, the platform functions `G`/`hN`, the `expU` (Lemma 4.6) bounds, row counting,
`σ ≤ rowLen`, and `60 C² ≤ 2^C/8`) is reproduced below verbatim, because a `Theorems.Thm_*` import
exports only that theorem's *statement*.

On top of it sits the per-node material of §5 that Lemma 5.9 needs: the density `ρ = Y/N` and its
floor, the three stopping rules read as arithmetic (`m = Y`, `N < D log¹⁰ n`,
`C³ λ_* log^{6+2A} n < N`), the column count `ℓ = O(A log¹⁴ n)`, the first moment of the profile
`Q`, and the density contraction `Σ_s Y_s ≤ ρY/4` (`capY_sum_le`), then the mixed per-rule budget
`child_bounds`, `lemma_5_9` and `solution`.
-/

/-- ### Toolkit reproduced from Lemma 5.8 -/
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

def nodeProfile (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (s : ℕ) : ℝ :=
  ∑ j ∈ range (P.rows X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))

lemma Q_eq_expU (P : HintParams) (N X Y s : ℕ) :
    P.Q N X Y s = expU (fun π => nodeProfile P N X Y π s) := rfl

lemma sum_add_const (Y : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    ∑ j ∈ range Y, (a j + c) = (∑ j ∈ range Y, a j) + (Y : ℝ) * c := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Q_nonneg (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (s : ℕ) : 0 ≤ P.Q N X Y s := by
  rw [Q_eq_expU]
  refine expU_nonneg ?_ (fun π => ?_)
  · rw [Fintype.card_perm, Fintype.card_fin]; exact Nat.factorial_pos N
  · exact Finset.sum_nonneg (fun j _ => G_nonneg _ _)

lemma Q_le_Y (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (hrows : P.rows X Y = Y) (s : ℕ) :
    P.Q N X Y s ≤ (Y : ℝ) := by
  rw [Q_eq_expU]
  have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]; exact Nat.factorial_pos N
  calc expU (fun π => nodeProfile P N X Y π s)
      ≤ expU (fun _ : Equiv.Perm (Fin N) => (Y : ℝ)) := by
        refine expU_mono hcard (fun π => ?_)
        simp only [nodeProfile]
        rw [hrows]
        calc ∑ j ∈ range Y, G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
            ≤ ∑ j ∈ range Y, (1 : ℝ) := Finset.sum_le_sum (fun j _ => G_le_one _ _)
          _ = (Y : ℝ) := by simp
    _ = (Y : ℝ) := expU_const hcard _

/-- First moment of the profile: `∑_s Q_s ≲ Y (N/Y + c)`. -/
lemma Q_sum_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrows : P.rows X Y = Y) (hY : 1 ≤ Y) :
    ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
      ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := by
  classical
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_pos N
  have hσle : ∀ (π : Equiv.Perm (Fin N)) (j : ℕ),
      (P.sigmaStar N X Y π j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
    intro π j
    have h1 := sigmaStar_le_rowLen (P := P) (N := N) (X := X) (Y := Y) (j := j) π
    have h2 : (rowLen N (P.rows X Y) j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
      rw [hrows]
      exact rowLen_le_two (by omega) hYN
    linarith
  have hexp : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
      = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s) := by
    rw [expU_finset_sum hcard]
    exact Finset.sum_congr rfl (fun s _ => Q_eq_expU P N X Y s)
  rw [hexp]
  calc expU (fun π => ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s)
      ≤ expU (fun _ : Equiv.Perm (Fin N) =>
          (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
        refine expU_mono hcard (fun π => ?_)
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
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
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


/-! ### The density of a node and the per-node estimates -/

/-- The density `ρ = Y/N` of a node. -/
def nodeDens (N Y : ℕ) : ℝ := (Y : ℝ) / (N : ℝ)

/-- The density floor `ε = 1/(2 log¹³ n)`; every recursive node has density `> ε`. -/
def densFloor (P : HintParams) : ℝ := (2 * P.lgn ^ 13)⁻¹

lemma nodeDens_nonneg (N Y : ℕ) : 0 ≤ nodeDens N Y := by
  unfold nodeDens; positivity

lemma nodeDens_le_one {N Y : ℕ} (hN : 1 ≤ N) (hYN : Y ≤ N) : nodeDens N Y ≤ 1 := by
  unfold nodeDens
  rw [div_le_one (by exact_mod_cast (by omega : 0 < N))]
  exact_mod_cast hYN

lemma nodeDens_pos {N Y : ℕ} (hN : 0 < N) (hY : 0 < Y) : 0 < nodeDens N Y := by
  unfold nodeDens; positivity

lemma one_le_lgn {P : HintParams} (hn : 2 ≤ P.n) : 1 ≤ P.lgn := by
  show (1 : ℝ) ≤ lg (P.n : ℝ)
  rw [← lg_two]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hn)

/-- The recursive rule forces `rows X Y = Y`, i.e. `X ≤ Y log³ n`. -/
lemma rows_eq_of_rule {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .recursive) :
    P.rows X Y = Y := by
  unfold HintParams.rule at h
  split_ifs at h with h1 h2 h3 <;> simp_all

lemma X_le_of_rows {P : HintParams} {X Y : ℕ} (hlgn : 0 < P.lgn) (h : P.rows X Y = Y) :
    (X : ℝ) ≤ (Y : ℝ) * P.lgn ^ 3 := by
  unfold HintParams.rows at h
  have h3 : (0 : ℝ) < P.lgn ^ 3 := by positivity
  have hc : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ Y := by
    have h1 : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ max Y ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := le_max_right _ _
    rwa [h] at h1
  have h2 : (X : ℝ) / P.lgn ^ 3 ≤ (Y : ℝ) := Nat.ceil_le.mp hc
  calc (X : ℝ) = (X : ℝ) / P.lgn ^ 3 * P.lgn ^ 3 := by field_simp
    _ ≤ (Y : ℝ) * P.lgn ^ 3 := by nlinarith

lemma D_le_N (N X Y : ℕ) : HintParams.D N X Y ≤ N := by
  unfold HintParams.D; omega

lemma D_le_sum (N X Y : ℕ) : HintParams.D N X Y ≤ X + Y := by
  unfold HintParams.D; omega

/-- The first (cheap) rule does not apply at a recursive node. -/
lemma N_lt_lgn_D {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (N : ℝ) < P.lgn ^ 10 * (HintParams.D N X Y : ℝ) := by
  have hnot : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) := by
    intro hc
    have hr : P.rule N X Y = .cheap := by
      unfold HintParams.rule
      rw [if_pos hc]
    rw [hrule] at hr
    exact absurd hr (by decide)
  have h10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
  have hlt : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hnot
  calc (N : ℝ) = (N : ℝ) / P.lgn ^ 10 * P.lgn ^ 10 := by field_simp
    _ < (HintParams.D N X Y : ℝ) * P.lgn ^ 10 := by nlinarith
    _ = P.lgn ^ 10 * (HintParams.D N X Y : ℝ) := by ring

/-- The second (small) rule does not apply at a recursive node. -/
lemma Nthresh_lt {P : HintParams} {N X Y : ℕ} (hrule : P.rule N X Y = .recursive) :
    (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (HintParams.D N X Y : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have h1 : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) := by
    intro hc
    have hr : P.rule N X Y = .cheap := by
      unfold HintParams.rule
      rw [if_pos hc]
    rw [hrule] at hr
    exact absurd hr (by decide)
  have hr : P.rule N X Y = .small := by
    unfold HintParams.rule
    rw [if_neg h1, if_pos hcon]
  rw [hrule] at hr
  exact absurd hr (by decide)

lemma lamStar_ge_C (P : HintParams) : (P.C : ℝ) ≤ (P.lamStar : ℝ) := by
  unfold HintParams.lamStar
  have h1 : (0 : ℝ) ≤ (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  push_cast
  nlinarith [h1, h2]

/-- `1/η² = log^{2A} n`. -/
lemma inv_eta_sq (P : HintParams) : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := by
  have hL : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  rw [hL, inv_pow, inv_inv, ← pow_mul]
  congr 1
  omega

/-- The recursive rule also rules out small instances: `C⁴ log^{6+2A} n < N`. -/
lemma Nthresh_le_N {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A) < (N : ℝ) := by
  have h1 := Nthresh_lt (P := P) (N := N) (X := X) (Y := Y) hrule
  have h2 := lamStar_ge_C P
  have h3 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le_N N X Y
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hC : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  have hL6 : (0 : ℝ) < P.lgn ^ 6 := by positivity
  have hLA : (0 : ℝ) < P.lgn ^ (2 * P.A) := by positivity
  have hLbig : (0 : ℝ) < P.lgn ^ (6 + 2 * P.A) := by positivity
  have heta : ((P.eta ^ 2)⁻¹) = P.lgn ^ (2 * P.A) := inv_eta_sq P
  have hsplit : P.lgn ^ 6 * P.lgn ^ (2 * P.A) = P.lgn ^ (6 + 2 * P.A) := by
    rw [← pow_add]
  have h1' : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A))
      < (HintParams.D N X Y : ℝ) := by
    have h := h1
    rw [div_eq_mul_inv, heta] at h
    linarith [h]
  rw [hsplit] at h1'
  have h4 : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) < (N : ℝ) := by
    linarith [h1', h3]
  have h5 : (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)
      = (P.C : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) := by ring
  have h6 : (P.C : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A))
      ≤ (P.lamStar : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) := by
    apply mul_le_mul_of_nonneg_right h2
    positivity
  have h7 : (P.lamStar : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A))
      = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) := by ring
  linarith [h4, h5, h6, h7]



lemma two_pow_ge_linear : ∀ A : ℕ, 100 ≤ A → 4096 * A + 409600 ≤ 2 ^ (A - 30) := by
  intro A hA
  induction A, hA using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hsub : m + 1 - 30 = (m - 30) + 1 := by omega
      rw [hsub, pow_succ]
      have h2 : 4096 ≤ 2 ^ (m - 30) := by
        have h70 : 70 ≤ m - 30 := by omega
        calc (4096 : ℕ) ≤ 2 ^ 70 := by norm_num
          _ ≤ 2 ^ (m - 30) := Nat.pow_le_pow_right (by norm_num) h70
      have hstep : 4096 * (m + 1) + 409600 = (4096 * m + 409600) + 4096 := by ring
      rw [hstep]
      nlinarith [ih, h2]

lemma two_pow_ge_linear_R (A : ℕ) (hA : 100 ≤ A) :
    4096 * (A : ℝ) + 409600 ≤ (2 : ℝ) ^ (A - 30) := by
  have h := two_pow_ge_linear A hA
  have h' : ((4096 * A + 409600 : ℕ) : ℝ) ≤ ((2 ^ (A - 30) : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((2 ^ (A - 30) : ℕ) : ℝ) = (2 : ℝ) ^ (A - 30) := by push_cast; ring
  rw [h2] at h'
  push_cast at h'
  linarith

/-- `512 A + 25600 ≤ 2^A` for `A ≥ 100`. -/
lemma linear_le_two_pow (A : ℕ) (hA : 100 ≤ A) : 512 * (A : ℝ) + 25600 ≤ (2 : ℝ) ^ A := by
  have h := two_pow_ge_linear_R A hA
  have h2 : (2 : ℝ) ^ A = (2 : ℝ) ^ (A - 30) * (2 : ℝ) ^ 30 := by
    rw [← pow_add]; congr 1; omega
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (A - 30) := one_le_pow₀ (by norm_num)
  rw [h2]
  nlinarith [h, h3]

/-- `log x ≤ 2x` for `x ≥ 1`. -/
lemma lg_le_two_mul (x : ℝ) (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, div_le_iff₀ h0]
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  nlinarith [Real.log_two_gt_d9]

/-- Monotonicity of `lg` on nonnegative arguments. -/
lemma lg_le_lg_of_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (h : x ≤ y) : lg x ≤ lg y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]
    simp only [lg, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) hy
  · exact Real.logb_le_logb_of_le (by norm_num) hpos h

lemma lg_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x :=
  Real.logb_nonneg (by norm_num) hx

lemma lg_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : lg (x * y) = lg x + lg y := by
  simp only [lg, Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]

lemma lg_pow_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  rw [lg_eq_log_div, lg_eq_log_div, Real.log_pow]
  push_cast
  field_simp

lemma lg_sixteen : lg (16 : ℝ) = 4 := by
  have h : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h, lg_pow_pos (by norm_num)]
  simp [lg_two]

lemma lg_three_le_two : lg (3 : ℝ) ≤ 2 := by
  have h4 : lg (4 : ℝ) = 2 := by
    have h : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h, lg_pow_pos (by norm_num)]
    simp [lg_two]
  rw [← h4]
  exact lg_le_lg_of_le (by norm_num) (by norm_num) (by norm_num : (3 : ℝ) ≤ 4)

/-- `L^30 · 2^{A-30} ≤ L^A` for `L ≥ 2`, `A ≥ 30`. -/
lemma lgn_pow_ge {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 30 ≤ P.A) :
    P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ P.A := by
  have hp : (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ (P.A - 30) :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ P.lgn) _
  have hpos : (0 : ℝ) < P.lgn ^ 30 := by positivity
  calc P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ 30 * P.lgn ^ (P.A - 30) := by
        nlinarith [hp, hpos]
    _ = P.lgn ^ (30 + (P.A - 30)) := (pow_add _ _ _).symm
    _ = P.lgn ^ P.A := by rw [show 30 + (P.A - 30) = P.A by omega]

/-- `L^{2A-34} ≥ 2^A` for `L ≥ 2`, `A ≥ 34`. -/
lemma lgn_pow_ge_two {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 34 ≤ P.A) :
    (2 : ℝ) ^ P.A ≤ P.lgn ^ (2 * P.A - 34) := by
  have h1 : (2 : ℝ) ^ P.A ≤ P.lgn ^ P.A :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ P.lgn) _
  have h2 : P.lgn ^ P.A ≤ P.lgn ^ (2 * P.A - 34) :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P.lgn) (by omega)
  linarith

/-- `384 (4A+200) log^30 n · η ≤ 1`: the margin term of a recursive node is negligible. -/
lemma eta_margin_small {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 100 ≤ P.A) :
    384 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 30 * P.eta ≤ 1 := by
  have hA30 : 30 ≤ P.A := by omega
  have hp : P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ P.A := lgn_pow_ge hL hA30
  have hpos : (0 : ℝ) < P.lgn ^ 30 := by positivity
  have hposA : (0 : ℝ) < P.lgn ^ P.A := by positivity
  have hx : (0 : ℝ) < P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) := by positivity
  have heta : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  have hinv : (P.lgn ^ P.A)⁻¹ ≤ (P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30))⁻¹ :=
    (inv_le_inv₀ hposA hx).mpr hp
  have h1 : P.lgn ^ 30 * P.eta ≤ ((2 : ℝ) ^ (P.A - 30))⁻¹ := by
    rw [heta]
    calc P.lgn ^ 30 * (P.lgn ^ P.A)⁻¹
        ≤ P.lgn ^ 30 * (P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hpos.le
      _ = ((2 : ℝ) ^ (P.A - 30))⁻¹ := by
          rw [mul_inv]
          field_simp
  have hnum : 384 * (4 * (P.A : ℝ) + 200) ≤ (2 : ℝ) ^ (P.A - 30) := by
    have h := two_pow_ge_linear_R P.A hA
    have hc : 384 * (4 * (P.A : ℝ) + 200) = 1536 * (P.A : ℝ) + 76800 := by ring
    rw [hc]
    linarith
  have hc0 : (0 : ℝ) ≤ 384 * (4 * (P.A : ℝ) + 200) := by positivity
  calc 384 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 30 * P.eta
      = 384 * (4 * (P.A : ℝ) + 200) * (P.lgn ^ 30 * P.eta) := by ring
    _ ≤ 384 * (4 * (P.A : ℝ) + 200) * ((2 : ℝ) ^ (P.A - 30))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hc0
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact hnum

/-! ### Basic estimates at a recursive node -/

lemma N_lt_two_lgn13 {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hL : 1 ≤ P.lgn) (hrule : P.rule N X Y = .recursive) :
    (N : ℝ) < 2 * P.lgn ^ 13 * (Y : ℝ) := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hrows := rows_eq_of_rule hrule
  have hX := X_le_of_rows hlgn hrows
  have h1 := N_lt_lgn_D hL hrule
  have h10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
  have hD : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
    have h := D_le_sum N X Y
    exact_mod_cast h
  have hp10 : P.lgn ^ 13 = P.lgn ^ 10 * P.lgn ^ 3 := by rw [← pow_add]
  have h1013 : P.lgn ^ 10 ≤ P.lgn ^ 13 := by
    rw [hp10]
    have h3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL
    nlinarith [h10.le, h3]
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hid : P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ))
      = (Y : ℝ) * P.lgn ^ 13 + (Y : ℝ) * P.lgn ^ 10 := by
    have hp : P.lgn ^ 10 * P.lgn ^ 3 = P.lgn ^ 13 := by rw [← pow_add]
    calc P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ))
        = (Y : ℝ) * (P.lgn ^ 10 * P.lgn ^ 3) + (Y : ℝ) * P.lgn ^ 10 := by ring
      _ = (Y : ℝ) * P.lgn ^ 13 + (Y : ℝ) * P.lgn ^ 10 := by rw [hp]
  have s1 : P.lgn ^ 10 * (HintParams.D N X Y : ℝ) ≤ P.lgn ^ 10 * ((X : ℝ) + (Y : ℝ)) :=
    mul_le_mul_of_nonneg_left hD h10.le
  have s2 : P.lgn ^ 10 * ((X : ℝ) + (Y : ℝ)) ≤ P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ h10.le
    linarith
  have s3 : (Y : ℝ) * P.lgn ^ 10 ≤ (Y : ℝ) * P.lgn ^ 13 :=
    mul_le_mul_of_nonneg_left h1013 hY0
  linarith [h1, s1, s2, hid, s3]

lemma Y_ge_one {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hL : 1 ≤ P.lgn) (hrule : P.rule N X Y = .recursive) : 1 ≤ Y := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  by_contra hc
  push_neg at hc
  have h0 : Y = 0 := by omega
  rw [h0] at h
  push_cast at h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h13 : (0 : ℝ) < P.lgn ^ 13 := by
    have : (0 : ℝ) < P.lgn := by linarith
    positivity
  nlinarith [h, hNpos, h13]

lemma dens_gt {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) : densFloor P < nodeDens N Y := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h13 : (0 : ℝ) < 2 * P.lgn ^ 13 := by
    have : (0 : ℝ) < P.lgn := by linarith
    positivity
  unfold densFloor nodeDens
  rw [inv_eq_one_div, lt_div_iff₀ hNpos]
  have h2 : (N : ℝ) / (2 * P.lgn ^ 13) < (Y : ℝ) :=
    (div_lt_iff₀ h13).mpr (by linarith)
  have heq : 1 / (2 * P.lgn ^ 13) * (N : ℝ) = (N : ℝ) / (2 * P.lgn ^ 13) := by ring
  rw [heq]
  exact h2

lemma Nmax_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) : (P.Nmax N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hY1 := Y_ge_one hargs hL hrule
  have hrows := rows_eq_of_rule hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hratio : (N : ℝ) / (Y : ℝ) < 2 * P.lgn ^ 13 := by
    rw [div_lt_iff₀ hYposR]
    linarith
  unfold HintParams.Nmax
  rw [hrows]
  have hceil : (⌈(N : ℝ) / (Y : ℝ)⌉₊ : ℝ) < (N : ℝ) / (Y : ℝ) + 1 := by
    apply Nat.ceil_lt_add_one
    positivity
  have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
    calc (1 : ℝ) = 1 ^ 13 := by norm_num
      _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL 13
  linarith [hceil, hratio, h13]

/-- `c = 2⌈log(N/Y)⌉ + C` in terms of the density. -/
lemma c_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hY : 1 ≤ Y)
    (hrule : P.rule N X Y = .recursive) :
    (P.c N X Y : ℝ) ≤ (P.C : ℝ) + 2 * lg ((N : ℝ) / (Y : ℝ)) + 2 := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hcdef : P.c N X Y = 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C := by
    unfold HintParams.c
    rw [if_pos hrule]
  rw [hcdef]
  have hM0 : 0 ≤ lg ((N : ℝ) / (Y : ℝ)) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hYposR]
    exact_mod_cast (by omega : 1 * Y ≤ N)
  have hceil : ((⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ lg ((N : ℝ) / (Y : ℝ)) + 1 := by
    have := Nat.ceil_lt_add_one hM0
    linarith
  push_cast
  linarith

/-- `2^{-c} ≤ 2^{-C} ρ²`. -/
lemma two_rpow_c_inv_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hY : 1 ≤ Y) (hrule : P.rule N X Y = .recursive) :
    ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hratio : (0 : ℝ) < (N : ℝ) / (Y : ℝ) := div_pos hNposR hYposR
  have hcdef : P.c N X Y = 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C := by
    unfold HintParams.c
    rw [if_pos hrule]
  have hNM : (2 : ℝ) ^ (lg ((N : ℝ) / (Y : ℝ))) = (N : ℝ) / (Y : ℝ) :=
    Real.rpow_logb (b := 2) (x := (N : ℝ) / (Y : ℝ)) (by norm_num) (by norm_num) hratio
  have hk : (N : ℝ) / (Y : ℝ) ≤ (2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    have h2 : (2 : ℝ) ^ (lg ((N : ℝ) / (Y : ℝ)))
        ≤ (2 : ℝ) ^ ((⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact Nat.le_ceil _
    rw [hNM, Real.rpow_natCast] at h2
    exact h2
  have hsq : ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    have hbase : ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊)) ^ 2 :=
      pow_le_pow_left₀ hratio.le hk 2
    have heq : ((2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊)) ^ 2
        = (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
      rw [← pow_mul]; congr 1; omega
    linarith [hbase, heq]
  have hpowc : (2 : ℝ) ^ (P.c N X Y)
      = (2 : ℝ) ^ P.C * (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    rw [hcdef, show 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C
        = P.C + 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ by omega, pow_add]
  have key : (2 : ℝ) ^ P.C * ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (P.c N X Y) := by
    rw [hpowc]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  calc ((2 : ℝ) ^ (P.c N X Y))⁻¹
      ≤ ((2 : ℝ) ^ P.C * ((N : ℝ) / (Y : ℝ)) ^ 2)⁻¹ :=
        (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (P.c N X Y)) (by positivity)).mpr key
    _ = (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by
        rw [mul_inv, ← Real.rpow_natCast (2 : ℝ) P.C,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← inv_pow, inv_div]
        simp only [nodeDens]

/-- The number of children of a recursive node: `ℓ ≤ (4A+200) log¹⁴ n`. -/
lemma ell_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 2 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (P.ell N X Y : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hNmax := Nmax_le hargs hL1 hrule
  have hBX : (P.BX N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
    have hle : P.BX N X Y ≤ P.Nmax N X Y := by unfold HintParams.BX; exact min_le_left _ _
    have hle' : (P.BX N X Y : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hle
    linarith
  have hBY : (P.BY N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
    have hle : P.BY N X Y ≤ P.Nmax N X Y := by unfold HintParams.BY; exact min_le_left _ _
    have hle' : (P.BY N X Y : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hle
    linarith
  have hK1 : ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ 13 * lg P.lgn + 6 := by
    have hlg0 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
    rcases Nat.eq_zero_or_pos (P.Nmax N X Y) with h0 | hpos
    · have hzero : lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) = 0 := by
        rw [h0]; push_cast; simp [lg]
      rw [hzero]
      simp only [Nat.ceil_zero, Nat.cast_zero]
      nlinarith
    · have hN1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hpos
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hx0 : (0 : ℝ) ≤ Real.exp 1 * (P.Nmax N X Y : ℝ) := by positivity
      have hge1 : (1 : ℝ) ≤ Real.exp 1 * (P.Nmax N X Y : ℝ) := by nlinarith [he1, hN1]
      have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
        calc (1 : ℝ) = 1 ^ 13 := by norm_num
          _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL1 13
      have hge3 : (1 : ℝ) ≤ Real.exp 1 * (3 * P.lgn ^ 13) := by nlinarith [he1, h13]
      have hxle : Real.exp 1 * (P.Nmax N X Y : ℝ) ≤ Real.exp 1 * (3 * P.lgn ^ 13) := by
        have hpos' : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        nlinarith [hNmax, hpos']
      have hlg : lg (Real.exp 1 * (P.Nmax N X Y : ℝ))
          ≤ lg (Real.exp 1 * (3 * P.lgn ^ 13)) := lg_le_lg_of_le hx0 hge3 hxle
      have hval : lg (Real.exp 1 * (3 * P.lgn ^ 13))
          = lg (Real.exp 1) + lg 3 + 13 * lg P.lgn := by
        have heq : Real.exp 1 * (3 * P.lgn ^ 13) = Real.exp 1 * 3 * P.lgn ^ 13 := by ring
        rw [heq]
        rw [lg_mul_pos (by positivity) (by positivity)]
        rw [lg_mul_pos (Real.exp_pos 1) (by norm_num)]
        rw [lg_pow_pos hlgn]
        push_cast
        ring
      have h1 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
      have h3 : lg 3 ≤ 2 := lg_three_le_two
      have hlg0' : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := lg_nonneg_of_one_le hge1
      have hceil : ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
          ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) + 1 := by
        have h := Nat.ceil_lt_add_one hlg0'
        linarith
      linarith
  have hK2 : ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) ≤ 2 * (P.A : ℝ) * lg P.lgn + 5 := by
    have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
      rw [div_eq_mul_inv, inv_eta_sq]
    have hval : lg (16 * P.lgn ^ (2 * P.A)) = 4 + (2 : ℝ) * (P.A : ℝ) * lg P.lgn := by
      rw [lg_mul_pos (by norm_num) (by positivity)]
      rw [lg_pow_pos hlgn]
      rw [lg_sixteen]
      push_cast
      ring
    have hgoal : lg (16 / P.eta ^ 2) = 4 + (2 : ℝ) * (P.A : ℝ) * lg P.lgn := by
      rw [heta, hval]
    have hlg0 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
    have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
    have hx0 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
      rw [hgoal]
      nlinarith [hlg0, hA0]
    have hceil := Nat.ceil_lt_add_one hx0
    linarith [hceil, hgoal]
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) + (P.BY N X Y : ℝ)
      * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) + (P.BY N X Y : ℝ)
      + ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  rw [hell]
  have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
    calc (1 : ℝ) = 1 ^ 13 := by norm_num
      _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL1 13
  have hlg2 : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
  have h14 : P.lgn ≤ P.lgn ^ 14 := by
    calc P.lgn = P.lgn ^ 1 := by ring
      _ ≤ P.lgn ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  have h13' : P.lgn ^ 13 ≤ P.lgn ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  have h14' : (1 : ℝ) ≤ P.lgn ^ 14 := by
    calc (1 : ℝ) = 1 ^ 14 := by norm_num
      _ ≤ P.lgn ^ 14 := pow_le_pow_left₀ (by norm_num) hL1 14
  have hBY0 : (0 : ℝ) ≤ (P.BY N X Y : ℝ) := Nat.cast_nonneg _
  have hBX0 : (0 : ℝ) ≤ (P.BX N X Y : ℝ) := Nat.cast_nonneg _
  have hprod : (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
      ≤ (3 * P.lgn ^ 13) * (13 * lg P.lgn + 6) := by
    apply mul_le_mul hBY hK1 (Nat.cast_nonneg _) (by positivity)
  have hprod2 : (3 * P.lgn ^ 13) * (13 * lg P.lgn + 6)
      ≤ (3 * P.lgn ^ 13) * (13 * (2 * P.lgn) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hexpand : (3 * P.lgn ^ 13) * (13 * (2 * P.lgn) + 6)
      = 78 * P.lgn ^ 14 + 18 * P.lgn ^ 13 := by
    have hp : P.lgn ^ 13 * P.lgn = P.lgn ^ 14 := (pow_succ P.lgn 13).symm
    nlinarith [hp]
  nlinarith [hprod, hprod2, hexpand, hBX, hBY, hK1, hK2, hlg2, hA0, h14, h13', h14',
    hBX0, hBY0, hlgn]

/-- Arithmetic of the margin term: `6 a L^17 η Y ≤ ρ Y / 32`. -/
lemma margin_arith {a ρ Y L η : ℝ} (hY : 0 ≤ Y) (hL : 0 < L)
    (hm : 384 * a * L ^ 30 * η ≤ 1) (hρlb : 1 / (2 * L ^ 13) ≤ ρ) :
    6 * a * L ^ 17 * η * Y ≤ ρ * Y / 32 := by
  have hL13 : (0 : ℝ) < 64 * L ^ 13 := by positivity
  have hkey : 384 * a * L ^ 30 * η * Y ≤ Y := by
    have h := mul_le_mul_of_nonneg_right hm hY
    linarith [h]
  have hid : 6 * a * L ^ 17 * η * Y * (64 * L ^ 13) = 384 * a * L ^ 30 * η * Y := by
    have hpw : L ^ 17 * L ^ 13 = L ^ 30 := by rw [← pow_add]
    rw [← hpw]
    ring
  have hK : 6 * a * L ^ 17 * η * Y ≤ Y / (64 * L ^ 13) := by
    rw [le_div_iff₀ hL13, hid]
    exact hkey
  have h1' : (1 : ℝ) ≤ 2 * L ^ 13 * ρ := by
    have h5 := mul_le_mul_of_nonneg_right hρlb (by positivity : (0 : ℝ) ≤ 2 * L ^ 13)
    have h6 : (1 / (2 * L ^ 13)) * (2 * L ^ 13) = 1 := by field_simp
    linarith [h5, h6]
  have h2 : Y / (64 * L ^ 13) ≤ ρ * Y / 32 := by
    rw [div_le_iff₀ hL13]
    nlinarith [h1', hY]
  linarith [hK, h2]

/-- **Density contraction.** At a recursive node the total density of the children is at most `ρ/4`. -/
lemma capY_sum_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 2 ≤ P.lgn)
    (hA : 100 ≤ P.A) (hC : 40 ≤ P.C) (hrule : P.rule N X Y = .recursive) :
    ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ) ≤ nodeDens N Y * (Y : ℝ) / 4 := by
  classical
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith only [hL]
  have hlgn : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hrows := rows_eq_of_rule hrule
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL1 hrule
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY1
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrho0 : (0 : ℝ) < nodeDens N Y := nodeDens_pos (by omega) (by omega)
  have hrho_le1 : nodeDens N Y ≤ 1 := nodeDens_le_one hN1 hYN
  have hrho_lb : (1 : ℝ) / (2 * P.lgn ^ 13) ≤ nodeDens N Y := by
    have h := dens_gt hargs hL1 hrule
    unfold densFloor at h
    rw [inv_eq_one_div] at h
    exact le_of_lt h
  have heta0 : (0 : ℝ) < P.eta := by
    unfold HintParams.eta
    positivity
  have hell := ell_le hargs hL hrule
  have hell0 : (0 : ℝ) ≤ (P.ell N X Y : ℝ) := Nat.cast_nonneg _
  -- ## Step 1: the pointwise bound obtained by dropping the `min`
  have hcap : ∀ s ∈ range (P.ell N X Y),
      (P.capY N X Y s : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
        + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by
    intro s _
    have hQ0 : (0 : ℝ) ≤ P.Q N X Y s := Q_nonneg (P := P) hN1 s
    have h1 : (P.capY N X Y s : ℝ)
        ≤ ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      unfold HintParams.capY
      exact_mod_cast min_le_right Y _
    have h2 : ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by
      have hz : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by positivity
      have h := Nat.ceil_lt_add_one hz
      linarith only [h]
    linarith only [h1, h2]
  -- ## Step 2: sum the pointwise bound
  have hsplit : ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)
      ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
        + (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
        + (P.ell N X Y : ℝ) := by
    calc ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)
        ≤ ∑ s ∈ range (P.ell N X Y), (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) := Finset.sum_le_sum hcap
      _ = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
            + (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
            + (P.ell N X Y : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.mul_sum]
          ring
  -- ## Step 3: the three terms are each at most `ρY/32`
  have hc := c_le hargs hY1 hrule
  have hYleN : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
  have hratio1 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
    rw [le_div_iff₀ hYposR]
    linarith only [hYleN]
  have hρM : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ)) ≤ lg (Real.exp 1) := by
    have heq : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ))
        = lg ((N : ℝ) / (Y : ℝ)) / ((N : ℝ) / (Y : ℝ)) := by
      unfold nodeDens
      field_simp
    rw [heq]
    exact lg_div_self_le hratio1
  have hρC : nodeDens N Y * (P.c N X Y : ℝ) ≤ (P.C : ℝ) + 6 := by
    have h1 : nodeDens N Y * (P.c N X Y : ℝ)
        ≤ nodeDens N Y * ((P.C : ℝ) + 2 * lg ((N : ℝ) / (Y : ℝ)) + 2) :=
      mul_le_mul_of_nonneg_left hc hrho0.le
    nlinarith only [h1, hρM, hrho_le1, lg_exp_one_le_two]
  have hnum : (2 : ℝ) ^ (-(P.C : ℝ)) * ((P.C : ℝ) + 40) ≤ 1 / 32 := by
    have h1 := two_rpow_neg_sixty P.C hC
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(P.C : ℝ)) := by positivity
    have hC1 : (4 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast (by omega : 4 ≤ P.C)
    have hle : 4 * ((P.C : ℝ) + 40) ≤ 60 * (P.C : ℝ) ^ 2 := by
      nlinarith only [hC1, sq_nonneg ((P.C : ℝ) - 4)]
    have h2 := mul_le_mul_of_nonneg_left hle hpos.le
    linarith only [h1, h2]
  have htermQ : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
      ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have h1 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 :=
      two_rpow_c_inv_le hargs hY1 hrule
    have h2 : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
        ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) :=
      Q_sum_le (P := P) hargs hrows hY1
    have h3 : (0 : ℝ) ≤ ∑ s ∈ range (P.ell N X Y), P.Q N X Y s :=
      Finset.sum_nonneg (fun s _ => Q_nonneg (P := P) hN1 s)
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by positivity
    have h5 := mul_le_mul h1 h2 h3 h4
    have hkey : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2
        * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))
        ≤ nodeDens N Y * (Y : ℝ) / 32 := by
      have hfac : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2
          * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))
          = (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y * (Y : ℝ))
            * (2 + nodeDens N Y * (P.c N X Y : ℝ) + 32 * nodeDens N Y) := by
        unfold nodeDens
        field_simp
      rw [hfac]
      have h2 : 2 + nodeDens N Y * (P.c N X Y : ℝ) + 32 * nodeDens N Y ≤ (P.C : ℝ) + 40 := by
        linarith only [hρC, hrho_le1]
      have hρY0 : (0 : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by positivity
      have hfac2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(P.C : ℝ)) := by positivity
      have hb := mul_le_mul_of_nonneg_left h2 (mul_nonneg hfac2 hρY0)
      have hfin : (2 : ℝ) ^ (-(P.C : ℝ)) * ((P.C : ℝ) + 40) * (nodeDens N Y * (Y : ℝ))
          ≤ (1 / 32) * (nodeDens N Y * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_right hnum hρY0
      nlinarith only [hb, hfin]
    linarith only [h5, hkey]
  have hD1 : (HintParams.D N X Y : ℝ) + 1 ≤ 3 * ((Y : ℝ) * P.lgn ^ 3) := by
    have hX := X_le_of_rows hlgn hrows
    have hDle : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
      have h := D_le_sum N X Y
      exact_mod_cast h
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) := le_of_lt hYposR
    have hY1R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
    have hL3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL1
    have hL3pos : (0 : ℝ) < P.lgn ^ 3 := by positivity
    nlinarith only [hX, hDle, hY0, hL3, hY1R, hL3pos]
  have htermM : (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
      ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have hstep1 : (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
        ≤ (P.ell N X Y : ℝ) * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3))) := by
      have h1 : 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)
          ≤ 2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)) := by
        nlinarith only [hD1, heta0]
      exact mul_le_mul_of_nonneg_left h1 hell0
    have hstep2 : (P.ell N X Y : ℝ) * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)))
        ≤ ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14)
          * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3))) := by
      apply mul_le_mul_of_nonneg_right hell
      positivity
    have hid2 : ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14)
        * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)))
        = 6 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 17 * P.eta * (Y : ℝ) := by
      have hpw : P.lgn ^ 14 * P.lgn ^ 3 = P.lgn ^ 17 := by rw [← pow_add]
      rw [← hpw]
      ring
    have hmarg := eta_margin_small hL hA
    have hconst := margin_arith (a := 4 * (P.A : ℝ) + 200) (ρ := nodeDens N Y) (Y := (Y : ℝ))
      (L := P.lgn) (η := P.eta) (le_of_lt hYposR) hlgn hmarg hrho_lb
    linarith only [hstep1, hstep2, hid2, hconst]
  have htermO : (P.ell N X Y : ℝ) ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have hNth := Nthresh_le_N hL1 hrule
    have hρ2 : (1 : ℝ) / (4 * P.lgn ^ 26) ≤ (nodeDens N Y) ^ 2 := by
      have h2 : (0 : ℝ) < 1 / (2 * P.lgn ^ 13) := by positivity
      have h3 : (1 / (2 * P.lgn ^ 13)) ^ 2 ≤ (nodeDens N Y) ^ 2 := by
        nlinarith only [hrho_lb, h2, hrho0]
      have h4 : (1 / (2 * P.lgn ^ 13)) ^ 2 = 1 / (4 * P.lgn ^ 26) := by
        have hp : P.lgn ^ 13 * P.lgn ^ 13 = P.lgn ^ 26 := by rw [← pow_add]
        field_simp
        nlinarith only [hp]
      linarith only [h3, h4]
    -- `2^A L^14 ≤ ρ² N`
    have hpowsplit : P.lgn ^ (6 + 2 * P.A)
        = P.lgn ^ (2 * P.A - 34) * P.lgn ^ 14 * P.lgn ^ 26 := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hpowbig : 4 * (2 : ℝ) ^ P.A
        ≤ (P.C : ℝ) ^ 4 * P.lgn ^ (2 * P.A - 34) := by
      have h1 : (2 : ℝ) ^ P.A ≤ P.lgn ^ (2 * P.A - 34) := lgn_pow_ge_two hL (by omega)
      have h2 : (4 : ℝ) ≤ (P.C : ℝ) ^ 4 := by
        have hC1 : (4 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast (by omega : 4 ≤ P.C)
        nlinarith only [hC1, sq_nonneg ((P.C : ℝ) - 4)]
      have h3 : (0 : ℝ) < P.lgn ^ (2 * P.A - 34) := by positivity
      nlinarith only [h1, h2, h3]
    have hellin : 32 * (P.ell N X Y : ℝ) ≤ (2 : ℝ) ^ P.A * P.lgn ^ 14 := by
      have h1 : 32 * (P.ell N X Y : ℝ) ≤ 32 * ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14) := by
        nlinarith only [hell, hell0]
      have h2 : 512 * (P.A : ℝ) + 25600 ≤ (2 : ℝ) ^ P.A := linear_le_two_pow P.A hA
      have h3 : (0 : ℝ) ≤ P.lgn ^ 14 := by positivity
      have h4 : 32 * (4 * (P.A : ℝ) + 200) = 128 * (P.A : ℝ) + 6400 := by ring
      have h5 : 128 * (P.A : ℝ) + 6400 ≤ 512 * (P.A : ℝ) + 25600 := by
        have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
        linarith only [hA0]
      nlinarith only [h1, h2, h3, h4, h5]
    -- `ρ² N` is bigger than `2^A L^14`
    have h6 : (1 : ℝ) / (4 * P.lgn ^ 26) * (N : ℝ) ≤ (nodeDens N Y) ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hρ2 (le_of_lt hNposR)
    have h7 : (1 : ℝ) / (4 * P.lgn ^ 26) * (N : ℝ)
        = (N : ℝ) / (4 * P.lgn ^ 26) := by ring
    have h8 : ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26) < (N : ℝ) / (4 * P.lgn ^ 26) := by
      have hpos : (0 : ℝ) < 1 / (4 * P.lgn ^ 26) := by positivity
      have h := mul_lt_mul_of_pos_right hNth hpos
      calc ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26)
          = ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) * (1 / (4 * P.lgn ^ 26)) := by ring
        _ < (N : ℝ) * (1 / (4 * P.lgn ^ 26)) := h
        _ = (N : ℝ) / (4 * P.lgn ^ 26) := by ring
    have h10 : (2 : ℝ) ^ P.A * P.lgn ^ 14
        ≤ ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * P.lgn ^ 26)]
      rw [hpowsplit]
      have hpos40 : (0 : ℝ) < P.lgn ^ 14 * P.lgn ^ 26 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hpowbig hpos40.le
      nlinarith only [hmul]
    have h11 : (2 : ℝ) ^ P.A * P.lgn ^ 14 ≤ (nodeDens N Y) ^ 2 * (N : ℝ) := by
      linarith only [h6, h7, h8, h10]
    have hρY_eq : nodeDens N Y * (Y : ℝ) = (nodeDens N Y) ^ 2 * (N : ℝ) := by
      unfold nodeDens
      field_simp
    have h12 : 32 * (P.ell N X Y : ℝ) ≤ (nodeDens N Y) ^ 2 * (N : ℝ) := le_trans hellin h11
    rw [hρY_eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith only [h12]
  have hρY0 : (0 : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by positivity
  linarith only [hsplit, htermQ, htermM, htermO]

/-! ## Lemma 5.9 (child space and density contraction) — proof

Paper alignment: `2609-version/5hintsketch.tex`, `lem:hint-mean-contraction` /
`lem:hint-local-cost` (PDF p.24).  The four claims are proved in the paper's order: inside-hint
budget, entropy budget, density budget, and the mixed per-rule budget.

Paper inputs used (as in the paper):
* `lemma_5_8` (`lem:hint-entropy-cost`) — the entropy cost `Σ_s h_Y(2^{-c}Q_s) ≤ h_N(Y)/8`;
* `lemma_4_4` (`lem:entropy-mass`) — subadditivity of `h_N`;
* Lemma 4.6 (`lem:prefix-sums`) — the `G`-sum estimates `sum_G_le` etc. (proved above).
-/

/-! ### Step 0: the `h_N` toolbox -/

lemma one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)

/-- as in the paper: `lg` is monotone on positive arguments (form used for the margin estimates). -/
lemma lg_le_lg_of_pos {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y :=
  Real.logb_le_logb_of_le (by norm_num) hx h

/-- `λ_* ≥ 1` in `ℝ`, from `C ≥ 1` (Lemma 5.9's recursive node always has `C ≥ 1`). -/
lemma lamStar_ge_one_of_C {P : HintParams} (hC : (1 : ℝ) ≤ (P.C : ℝ)) :
    (1 : ℝ) ≤ (P.lamStar : ℝ) := by
  have h2 : (P.C : ℝ) ≤ (P.lamStar : ℝ) := by
    unfold HintParams.lamStar
    push_cast
    have h3 : (0 : ℝ) ≤ (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) := Nat.cast_nonneg _
    nlinarith
  linarith

/-- `h_N(z) = z log(eN/z)` for `z > 0`, in quotient form. -/
lemma hN_eq_quot {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {z : ℝ} (hz : 0 < z) :
    hN N z = z * lg (Real.exp 1 * (N : ℝ) / z) := by
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨Real.exp_ne_zero 1, hN0⟩
  rw [hN_eq hN0 hz, ← mul_sub]
  congr 1
  simp only [lg]
  rw [← Real.logb_div heN (ne_of_gt hz)]

lemma lg_div_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : lg (x / y) = lg x - lg y := by
  simp only [lg, Real.logb_div (ne_of_gt hx) (ne_of_gt hy)]

/-- `log t ≤ (t-1) log e` for `t ≥ 1`. -/
lemma lg_le_sub_one_mul {x : ℝ} (hx : 1 ≤ x) : lg x ≤ (x - 1) * lg (Real.exp 1) := by
  have h0 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : lg x = Real.log x / Real.log 2 := rfl
  have h3 : lg (Real.exp 1) = 1 / Real.log 2 := lg_exp_one
  have h4 : lg (Real.exp 1) * Real.log 2 = 1 := by
    rw [h3, div_mul_cancel₀ 1 (ne_of_gt h0)]
  calc lg x = Real.log x / Real.log 2 := h2
    _ = Real.log x * (1 / Real.log 2) := by ring
    _ = Real.log x * lg (Real.exp 1) := by rw [h3]
    _ ≤ (x - 1) * lg (Real.exp 1) := by
        apply mul_le_mul_of_nonneg_right h1 (le_of_lt (by rw [h3]; positivity))

/-- `log(eN/z) ≥ 0` for `0 < z ≤ N`: the paper's outside cost is nonnegative. -/
lemma lg_expN_div_nonneg {N : ℕ} {z : ℝ} (hz : 0 < z) (hzN : z ≤ (N : ℝ)) :
    0 ≤ lg (Real.exp 1 * (N : ℝ) / z) := by
  apply Real.logb_nonneg (by norm_num)
  rw [one_le_div hz]
  have h1 : (1 : ℝ) ≤ Real.exp 1 := one_le_exp_one
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- `h_N(z) ≥ 0` on `[0,N]`. -/
lemma hN_nonneg {N : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hzN : z ≤ (N : ℝ)) : 0 ≤ hN N z := by
  rcases eq_or_lt_of_le hz0 with h | h
  · rw [← h]; simp [hN]
  · rw [hN, if_neg (ne_of_gt h)]
    exact mul_nonneg h.le (lg_expN_div_nonneg h hzN)

/-- as in the paper: `z log(eN/z)` is nondecreasing on `[0,N]`, so raising a child capacity up to
`2^{-c}Q_s + b` only increases the entropy cost. -/
lemma hN_mono {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hvN : v ≤ (N : ℝ)) :
    hN N u ≤ hN N v := by
  rcases eq_or_lt_of_le hu0 with hu | hu
  · rw [← hu]
    have hzero : hN N (0 : ℝ) = 0 := by simp [hN]
    rw [hzero]
    exact hN_nonneg (le_trans hu0 huv) hvN
  · have hv0 : 0 < v := lt_of_lt_of_le hu huv
    have hN0 : (N : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hv0 hvN
      exact ne_of_gt hpos
    set t : ℝ := v / u with ht
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ hu]; linarith
    have hvt : v = t * u := by rw [ht]; field_simp
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have ht0 : (0 : ℝ) ≤ t - 1 := by linarith
    have htu : 0 < t * u := by positivity
    have hlog : lg (Real.exp 1 * (N : ℝ) / u) = lg (Real.exp 1 * (N : ℝ) / v) + lg t := by
      have h1 : Real.exp 1 * (N : ℝ) / u = (Real.exp 1 * (N : ℝ) / v) * t := by
        rw [hvt]; field_simp
      rw [h1, lg_mul_pos (by positivity) htpos]
    have hBv : lg (Real.exp 1) ≤ lg (Real.exp 1 * (N : ℝ) / v) := by
      have hge1 : (1 : ℝ) ≤ Real.exp 1 * (N : ℝ) / v := by
        rw [le_div_iff₀ hv0]
        nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1), hvN, Real.exp_pos 1, Nat.cast_nonneg (α := ℝ) N]
      have hge2 : Real.exp 1 ≤ Real.exp 1 * (N : ℝ) / v := by
        rw [le_div_iff₀ hv0]
        nlinarith [hvN, Real.exp_pos 1]
      exact lg_le_lg_of_le (le_of_lt (Real.exp_pos 1)) hge1 hge2
    have hlt : lg t ≤ (t - 1) * lg (Real.exp 1) := lg_le_sub_one_mul ht1
    have hmul : (t - 1) * lg (Real.exp 1) ≤ (t - 1) * lg (Real.exp 1 * (N : ℝ) / v) :=
      mul_le_mul_of_nonneg_left hBv ht0
    have h7 : (0 : ℝ) ≤ (t - 1) * lg t := mul_nonneg ht0 (lg_nonneg_of_one_le ht1)
    have hkey : t * lg t ≤ (t - 1) * lg (Real.exp 1 * (N : ℝ) / u) := by
      nlinarith [hlog, hmul, hlt, h7]
    have hdiv : lg (Real.exp 1 * (N : ℝ)) - lg u = lg (Real.exp 1 * (N : ℝ) / u) :=
      (lg_div_pos (by positivity) hu).symm
    have hexp : hN N v - hN N u
        = u * ((t - 1) * lg (Real.exp 1 * (N : ℝ) / u) - t * lg t) := by
      rw [hvt, hN_eq hN0 hu, hN_eq hN0 htu, lg_mul_pos htpos hu, ← hdiv]
      ring
    have hnn : 0 ≤ u * ((t - 1) * lg (Real.exp 1 * (N : ℝ) / u) - t * lg t) :=
      mul_nonneg (le_of_lt hu) (by linarith)
    linarith [hexp, hnn]

/-- as in the paper: subadditivity of `h_N` on `[0,N]` (Lemma 4.4, "entropy and total mass"). -/
lemma hN_add_le {N : ℕ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ (N : ℝ)) :
    hN N (u + v) ≤ hN N u + hN N v :=
  (lemma_4_4 N).2 u v hu hv huv

/-! ### Step 1: the reference placement (Definition 5.7) — label counts per row -/

lemma filter_range_lt (N k : ℕ) : (range N).filter (fun i => i < k) = range (min N k) := by
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- as in the paper: summing the row images of `S` over the rows of a permutation counts every
coordinate of `S ∩ [N]` at most once. -/
lemma sum_rowImage_card_le (N m : ℕ) (hm : 0 < m) (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    ∑ j ∈ range m, (rowImage N m π j S).card ≤ S.card := by
  classical
  have h1 : ∀ j ∈ range m, (rowImage N m π j S).card
      ≤ (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).card := by
    intro j _
    exact Finset.card_image_le
  have hstep : ∑ j ∈ range m,
        (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).card
      = (univ.filter (fun i : Fin N => i.val ∈ S)).card := by
    have hfilter : ∀ j : ℕ,
        (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j))
          = (univ.filter (fun i : Fin N => i.val ∈ S)).filter
            (fun i => (π i).val % m = j) := by
      intro j
      rw [← Finset.filter_filter]
    simp only [hfilter]
    rw [Finset.card_eq_sum_card_fiberwise (s := univ.filter (fun i : Fin N => i.val ∈ S))
      (t := range m) (f := fun i : Fin N => (π i).val % m)
      (fun i _ => mem_range.mpr (Nat.mod_lt _ hm))]
  have h2 : (univ.filter (fun i : Fin N => i.val ∈ S)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (f := fun i : Fin N => i.val) (t := S)
    · intro i hi
      simpa only [mem_coe, mem_filter, mem_univ, true_and] using hi
    · intro a _ b _ hab
      exact Fin.ext hab
  calc ∑ j ∈ range m, (rowImage N m π j S).card
      ≤ ∑ j ∈ range m,
          (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).card :=
        Finset.sum_le_sum h1
    _ = (univ.filter (fun i : Fin N => i.val ∈ S)).card := hstep
    _ ≤ S.card := h2

/-- `2^r ≥ r + 1`, the crude bound behind `(r+1) ≤ 2^r` in the `σ` count.  Stated as its own lemma so
that the induction hypothesis is not polluted by the surrounding context. -/
lemma two_pow_ge_succ (r : ℕ) : ((r : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ r := by
  induction r with
  | zero => simp
  | succ k ih =>
      have h5 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have h6 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hstep : ((k : ℝ) + 1) + 1 ≤ (2 : ℝ) ^ k * 2 := by nlinarith [ih, h5, h6]
      calc ((k + 1 : ℕ) : ℝ) + 1 = ((k : ℝ) + 1) + 1 := by push_cast; ring
        _ ≤ (2 : ℝ) ^ k * 2 := hstep
        _ = (2 : ℝ) ^ (k + 1) := (pow_succ (2 : ℝ) k).symm


/-- the hint labels of the reference placement number at most `X` (Definition 5.7, equation (8)). -/
lemma card_refHintLabels_le (N X Y : ℕ) : (HintParams.refHintLabels N X Y).card ≤ X := by
  classical
  have hsub : HintParams.refHintLabels N X Y ⊆ range X := by
    intro i hi
    simp only [HintParams.refHintLabels, mem_filter, mem_range] at hi ⊢
    have h1 : HintParams.D N X Y ≤ X + Y := D_le_sum N X Y
    omega
  calc (HintParams.refHintLabels N X Y).card ≤ (range X).card := Finset.card_le_card hsub
    _ = X := by simp

/-- the outside-hint nonzero labels of the reference placement number at most `Y`. -/
lemma card_refOutLabels_le (N X Y : ℕ) (hYN : Y ≤ N) : (HintParams.refOutLabels N X Y).card ≤ Y := by
  classical
  have _hYN : Y ≤ N := hYN
  have hD : Y ≤ HintParams.D N X Y := by
    unfold HintParams.D
    omega
  have hDY : HintParams.D N X Y ≤ (HintParams.D N X Y - Y) + Y :=
    le_of_eq (Nat.sub_add_cancel hD).symm
  have hmaps : Set.MapsTo (fun i => i - (HintParams.D N X Y - Y))
      ↑(HintParams.refOutLabels N X Y) ↑(range Y) := by
    intro i hi
    simp only [HintParams.refOutLabels, mem_filter, mem_range, Finset.mem_coe] at hi
    simp only [mem_coe, mem_range]
    have h2 : HintParams.D N X Y - Y ≤ i := hi.2.1
    have h3 : i < HintParams.D N X Y := hi.2.2
    have h4 : i - (HintParams.D N X Y - Y) + (HintParams.D N X Y - Y) = i :=
      Nat.sub_add_cancel h2
    omega
  have hinj : Set.InjOn (fun i => i - (HintParams.D N X Y - Y))
      ↑(HintParams.refOutLabels N X Y) := by
    intro a ha b hb hab
    simp only [HintParams.refOutLabels, mem_filter, mem_range, Finset.mem_coe] at ha hb
    have ha2 : HintParams.D N X Y - Y ≤ a := ha.2.1
    have hb2 : HintParams.D N X Y - Y ≤ b := hb.2.1
    have ha' : a - (HintParams.D N X Y - Y) + (HintParams.D N X Y - Y) = a :=
      Nat.sub_add_cancel ha2
    have hb' : b - (HintParams.D N X Y - Y) + (HintParams.D N X Y - Y) = b :=
      Nat.sub_add_cancel hb2
    have hkey : a - (HintParams.D N X Y - Y) = b - (HintParams.D N X Y - Y) := hab
    calc a = a - (HintParams.D N X Y - Y) + (HintParams.D N X Y - Y) := ha'.symm
      _ = b - (HintParams.D N X Y - Y) + (HintParams.D N X Y - Y) := by rw [hkey]
      _ = b := hb'
  calc (HintParams.refOutLabels N X Y).card
      ≤ (range Y).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Y := by simp

/-- as in the paper: `σ_{j,r} ≤ |J_j| + r log(2N_j+2) + 1` — the sharp per-row count of
Definition 5.7, used for the first moment. -/
lemma sigma_le_refined {jCard Nj r : ℕ} (h : jCard ≤ Nj) :
    (HintParams.sigma jCard Nj r : ℝ) ≤ (jCard : ℝ) + (r : ℝ) * lg (2 * (Nj : ℝ) + 2) + 1 := by
  classical
  set M := Nj - jCard with hM
  set S := ∑ h ∈ range (r + 1), M.choose h with hS
  have hMle : M ≤ Nj := by omega
  have hS1 : 1 ≤ S := by
    rw [hS]
    simpa using Finset.single_le_sum (f := fun i => M.choose i) (fun i _ => Nat.zero_le _)
      (by simp : 0 ∈ range (r + 1))
  have hS1R : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
  have hSle : (S : ℝ) ≤ ((r : ℝ) + 1) * ((M : ℝ) + 1) ^ r := by
    have hSsum : (S : ℝ) = ∑ i ∈ range (r + 1), ((M.choose i : ℕ) : ℝ) := by
      rw [hS, Nat.cast_sum]
    rw [hSsum]
    have hpt : ∀ i ∈ range (r + 1), ((M.choose i : ℕ) : ℝ) ≤ ((M : ℝ) + 1) ^ r := by
      intro i hi
      simp only [mem_range] at hi
      have h1 : ((M.choose i : ℕ) : ℝ) ≤ (M : ℝ) ^ i := by
        exact_mod_cast Nat.choose_le_pow M i
      have h2 : (M : ℝ) ^ i ≤ ((M : ℝ) + 1) ^ i :=
        pow_le_pow_left₀ (Nat.cast_nonneg M) (by linarith) i
      have h3 : ((M : ℝ) + 1) ^ i ≤ ((M : ℝ) + 1) ^ r :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (M : ℝ) + 1) (by omega)
      linarith
    calc ∑ i ∈ range (r + 1), ((M.choose i : ℕ) : ℝ)
        ≤ ∑ i ∈ range (r + 1), ((M : ℝ) + 1) ^ r := Finset.sum_le_sum hpt
      _ = ((r : ℝ) + 1) * ((M : ℝ) + 1) ^ r := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hlg : lg ((S : ℝ)) ≤ (r : ℝ) * lg (2 * (Nj : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have hSval : (S : ℝ) = 1 := by rw [hS]; simp
      rw [hSval]
      simp [lg]
    · have h2r : ((r : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ r := two_pow_ge_succ r
      have hstep : (S : ℝ) ≤ (2 * ((M : ℝ) + 1)) ^ r := by
        calc (S : ℝ) ≤ ((r : ℝ) + 1) * ((M : ℝ) + 1) ^ r := hSle
          _ ≤ (2 : ℝ) ^ r * ((M : ℝ) + 1) ^ r :=
              mul_le_mul_of_nonneg_right h2r (by positivity)
          _ = (2 * ((M : ℝ) + 1)) ^ r := by rw [mul_pow]
      calc lg (S : ℝ) ≤ lg ((2 * ((M : ℝ) + 1)) ^ r) :=
            lg_le_lg_of_le (by positivity)
              (one_le_pow₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) M])) hstep
        _ = (r : ℝ) * lg (2 * ((M : ℝ) + 1)) := lg_pow_pos (by positivity) r
        _ ≤ (r : ℝ) * lg (2 * (Nj : ℝ) + 2) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
            apply lg_le_lg_of_le (by positivity)
              (by nlinarith [Nat.cast_nonneg (α := ℝ) Nj])
            have h4 : (M : ℝ) ≤ (Nj : ℝ) := by exact_mod_cast hMle
            linarith
  have hargeq : lg (((2 ^ jCard * S : ℕ) : ℝ)) = (jCard : ℝ) + lg (S : ℝ) := by
    have h1 : ((2 ^ jCard * S : ℕ) : ℝ) = (2 : ℝ) ^ jCard * (S : ℝ) := by push_cast; ring
    rw [h1, lg_mul_pos (by positivity) (by positivity)]
    have h2 : lg ((2 : ℝ) ^ jCard) = (jCard : ℝ) := by
      rw [lg_pow_pos (by norm_num), lg_two]
      ring
    rw [h2]
  have harg1 : (1 : ℝ) ≤ ((2 ^ jCard * S : ℕ) : ℝ) := by
    have h1 : ((2 ^ jCard * S : ℕ) : ℝ) = (2 : ℝ) ^ jCard * (S : ℝ) := by push_cast; ring
    rw [h1]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ jCard := one_le_pow₀ (by norm_num)
    have h3 : (0 : ℝ) < (S : ℝ) := by linarith
    nlinarith
  have hceil : (HintParams.sigma jCard Nj r : ℝ)
      ≤ lg (((2 ^ jCard * S : ℕ) : ℝ)) + 1 := by
    unfold HintParams.sigma
    have h0 : 0 ≤ lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)) := by
      apply Real.logb_nonneg (by norm_num)
      exact harg1
    have hlt := Nat.ceil_lt_add_one (R := ℝ)
      (a := lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ))) h0
    linarith
  linarith [hargeq, hceil, hlg]

/-- `σ_j^* ≤ |J_j^*| + y_j^* log(2N_max+2) + 1`. -/
lemma sigmaStar_le_sharp (P : HintParams) {N X Y j : ℕ} (hm : 0 < P.rows X Y)
    (π : Equiv.Perm (Fin N)) :
    (P.sigmaStar N X Y π j : ℝ)
      ≤ ((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ)
        + lg (2 * (P.Nmax N X Y : ℝ) + 2)
          * ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ) + 1 := by
  classical
  have hjc : (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card
      ≤ rowLen N (P.rows X Y) j := rowImage_card_le_rowLen π _
  have h1 := sigma_le_refined
    (jCard := (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card)
    (Nj := rowLen N (P.rows X Y) j)
    (r := (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card) hjc
  have hlen : (rowLen N (P.rows X Y) j : ℝ) ≤ (P.Nmax N X Y : ℝ) := by
    have h4 := rowLen_le_ceil (N := N) (m := P.rows X Y) (j := j) hm
    unfold HintParams.Nmax
    exact_mod_cast h4
  have h2 : lg (2 * (rowLen N (P.rows X Y) j : ℝ) + 2) ≤ lg (2 * (P.Nmax N X Y : ℝ) + 2) := by
    apply lg_le_lg_of_le (by positivity)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) (P.Nmax N X Y)])
    linarith
  have h5 : (0 : ℝ) ≤ ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ) :=
    Nat.cast_nonneg _
  have h3 : lg (2 * (rowLen N (P.rows X Y) j : ℝ) + 2)
      * ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ)
      ≤ lg (2 * (P.Nmax N X Y : ℝ) + 2)
      * ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ) :=
    mul_le_mul_of_nonneg_right h2 h5
  unfold HintParams.sigmaStar
  dsimp only
  linarith [h1, h3]

/-! ### Step 2: the sharp first moment `Σ_s Q_s ≤ X + O(C h_N(Y))`

This is the paper's `eq:lemma-5-8-bound-of-Qs`: `Σ_j σ_j^* ≤ X + Y log(2N_max+2) + Y`, then
Lemma 4.6 sums the `G`-profiles, and `c ≤ C + 2log(e/ρ) + 2`. -/

lemma Q_sum_le_sharp (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrows : P.rows X Y = Y) (hY : 1 ≤ Y) (hrule : P.rule N X Y = .recursive)
    (hC1 : (1 : ℝ) ≤ (P.C : ℝ)) :
    ∑ s ∈ range (P.ell N X Y), P.Q N X Y s ≤ (X : ℝ) + 50 * (P.C : ℝ) * hN N Y := by
  classical
  have hargs0 := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs0
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrN : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
    rw [le_div_iff₀ hYposR]
    have h6 : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
    linarith
  have hm0 : 0 < P.rows X Y := by rw [hrows]; omega
  have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_pos N
  have hLm0 : (0 : ℝ) ≤ lg (2 * (P.Nmax N X Y : ℝ) + 2) := by
    apply Real.logb_nonneg (by norm_num)
    have h6 : (0 : ℝ) ≤ (P.Nmax N X Y : ℝ) := Nat.cast_nonneg _
    linarith
  have hjsum : ∀ π : Equiv.Perm (Fin N), ∑ j ∈ range (P.rows X Y),
      (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card ≤ X := fun π =>
    le_trans (sum_rowImage_card_le N (P.rows X Y) hm0 π _) (card_refHintLabels_le N X Y)
  have hrsum : ∀ π : Equiv.Perm (Fin N), ∑ j ∈ range (P.rows X Y),
      (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card ≤ Y := fun π =>
    le_trans (sum_rowImage_card_le N (P.rows X Y) hm0 π _) (card_refOutLabels_le N X Y hYN)
  have hprof : ∀ π : Equiv.Perm (Fin N),
      ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s
        ≤ (X : ℝ) + lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ)
          + (Y : ℝ) * ((P.c N X Y : ℝ) + 33) := by
    intro π
    have hswap : ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s
        = ∑ j ∈ range (P.rows X Y), ∑ s ∈ range (P.ell N X Y),
            G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) := by
      simp only [nodeProfile]
      rw [Finset.sum_comm]
    rw [hswap]
    have h1 : ∑ j ∈ range (P.rows X Y), ∑ s ∈ range (P.ell N X Y),
          G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
        ≤ ∑ j ∈ range (P.rows X Y),
            ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ) + 32) :=
      Finset.sum_le_sum (fun j _ => sum_G_le _ (by positivity) _)
    have h2 : ∑ j ∈ range (P.rows X Y),
          ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ) + 32)
        = (∑ j ∈ range (P.rows X Y), (P.sigmaStar N X Y π j : ℝ))
          + (Y : ℝ) * ((P.c N X Y : ℝ) + 32) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hrows]
      ring
    have h3 : ∑ j ∈ range (P.rows X Y), (P.sigmaStar N X Y π j : ℝ)
        ≤ (X : ℝ) + lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ) + (Y : ℝ) := by
      have h4 : ∑ j ∈ range (P.rows X Y), (P.sigmaStar N X Y π j : ℝ)
          ≤ ∑ j ∈ range (P.rows X Y),
              (((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ)
                + lg (2 * (P.Nmax N X Y : ℝ) + 2)
                  * ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ)
                + 1) :=
        Finset.sum_le_sum (fun j _ => sigmaStar_le_sharp P hm0 π)
      have e1 : ∑ j ∈ range (P.rows X Y),
            (((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ)
              + lg (2 * (P.Nmax N X Y : ℝ) + 2)
                * ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ) + 1)
          = (∑ j ∈ range (P.rows X Y),
              ((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ))
            + lg (2 * (P.Nmax N X Y : ℝ) + 2)
              * (∑ j ∈ range (P.rows X Y),
                ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ))
            + (Y : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one, hrows]
      have h4' : ∑ j ∈ range (P.rows X Y), (P.sigmaStar N X Y π j : ℝ)
          ≤ (∑ j ∈ range (P.rows X Y),
              ((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ))
            + lg (2 * (P.Nmax N X Y : ℝ) + 2)
              * (∑ j ∈ range (P.rows X Y),
                ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ))
            + (Y : ℝ) := le_trans h4 (le_of_eq e1)
      have h5 : (∑ j ∈ range (P.rows X Y),
            ((rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card : ℝ)) ≤ (X : ℝ) := by
        have h6 := hjsum π
        exact_mod_cast h6
      have h6 : (∑ j ∈ range (P.rows X Y),
            ((rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card : ℝ)) ≤ (Y : ℝ) := by
        have h7 := hrsum π
        exact_mod_cast h7
      nlinarith [h4', h5, h6, hLm0]
    linarith [h1, h2, h3]
  have hexp : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
      = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s) := by
    rw [expU_finset_sum hcard]
    exact Finset.sum_congr rfl (fun s _ => Q_eq_expU P N X Y s)
  rw [hexp]
  have hmain : expU (fun π : Equiv.Perm (Fin N) =>
        ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s)
      ≤ (X : ℝ) + lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ)
        + (Y : ℝ) * ((P.c N X Y : ℝ) + 33) := by
    calc expU (fun π : Equiv.Perm (Fin N) =>
          ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s)
        ≤ expU (fun _ : Equiv.Perm (Fin N) =>
            (X : ℝ) + lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ)
              + (Y : ℝ) * ((P.c N X Y : ℝ) + 33)) := expU_mono hcard hprof
      _ = _ := expU_const hcard _
  set Ll : ℝ := lg (Real.exp 1 * (N : ℝ) / (Y : ℝ)) with hLl
  have hYN' : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
  have hLl1 : (1 : ℝ) ≤ Ll := by
    have h1 : Real.exp 1 ≤ Real.exp 1 * (N : ℝ) / (Y : ℝ) := by
      rw [le_div_iff₀ hYposR]
      nlinarith [Real.exp_pos 1, hYN']
    have h2 : (1 : ℝ) ≤ lg (Real.exp 1) := one_le_lg_exp
    have h3 : lg (Real.exp 1) ≤ lg (Real.exp 1 * (N : ℝ) / (Y : ℝ)) :=
      lg_le_lg_of_pos (Real.exp_pos 1) h1
    rw [hLl]
    linarith
  have hhN : hN N Y = (Y : ℝ) * Ll := by
    rw [hN_eq_quot (ne_of_gt hNposR) hYposR, ← hLl]
  have hLm_le : lg (2 * (P.Nmax N X Y : ℝ) + 2) ≤ Ll + 2 := by
    have hNmax2 : (P.Nmax N X Y : ℝ) ≤ 2 * ((N : ℝ) / (Y : ℝ)) := by
      unfold HintParams.Nmax
      rw [hrows]
      have h1 : ((⌈(N : ℝ) / (Y : ℝ)⌉₊ : ℕ) : ℝ) < (N : ℝ) / (Y : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
        rw [le_div_iff₀ hYposR]
        linarith
      linarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
      rw [le_div_iff₀ hYposR]
      linarith
    have hx : 2 * (P.Nmax N X Y : ℝ) + 2 ≤ 8 * ((N : ℝ) / (Y : ℝ)) := by
      nlinarith [hNmax2, h2]
    have h8 : 8 * ((N : ℝ) / (Y : ℝ)) ≤ 4 * (Real.exp 1 * (N : ℝ) / (Y : ℝ)) := by
      have h9 : (2 : ℝ) ≤ Real.exp 1 := by
        have h10 := Real.add_one_le_exp (1 : ℝ)
        linarith
      have h10 : (0 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by positivity
      have hnorm : 4 * (Real.exp 1 * (N : ℝ) / (Y : ℝ))
          = (4 * Real.exp 1) * ((N : ℝ) / (Y : ℝ)) := by ring
      rw [hnorm]
      have hm := mul_le_mul_of_nonneg_right (by linarith : (8 : ℝ) ≤ 4 * Real.exp 1) h10
      linarith [hm]
    have h11 : lg (2 * (P.Nmax N X Y : ℝ) + 2) ≤ lg (8 * ((N : ℝ) / (Y : ℝ))) :=
      lg_le_lg_of_le (by positivity) (by nlinarith [hrN]) hx
    have h12 : lg (8 * ((N : ℝ) / (Y : ℝ))) ≤ lg (4 * (Real.exp 1 * (N : ℝ) / (Y : ℝ))) :=
      lg_le_lg_of_le (by positivity) (by nlinarith [one_le_exp_one, hrN]) h8
    have h14 : lg (4 : ℝ) = 2 := by
      have h15 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      rw [h15, lg_pow_pos (by norm_num), lg_two]
      norm_num
    have h13 : lg (4 * (Real.exp 1 * (N : ℝ) / (Y : ℝ))) = 2 + Ll := by
      rw [lg_mul_pos (by norm_num) (by positivity), h14, hLl]
    rw [h13] at h12
    linarith [h11, h12]
  have hc_le : (P.c N X Y : ℝ) ≤ (P.C : ℝ) + 2 * Ll + 2 := by
    have hbase := c_le (P := P) hargs hY hrule
    have h1 : lg ((N : ℝ) / (Y : ℝ)) ≤ Ll := by
      have hx0 : (0 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by positivity
      have hnorm : Real.exp 1 * (N : ℝ) / (Y : ℝ) = Real.exp 1 * ((N : ℝ) / (Y : ℝ)) := by ring
      have hy1 : (1 : ℝ) ≤ Real.exp 1 * ((N : ℝ) / (Y : ℝ)) := by
        have h := mul_le_mul one_le_exp_one hrN zero_le_one (le_of_lt (Real.exp_pos 1))
        simpa using h
      have hle : (N : ℝ) / (Y : ℝ) ≤ Real.exp 1 * ((N : ℝ) / (Y : ℝ)) := by
        have h := mul_le_mul_of_nonneg_right one_le_exp_one hx0
        linarith [h]
      rw [hLl, hnorm]
      exact lg_le_lg_of_le hx0 hy1 hle
    linarith
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := le_of_lt hYposR
  have hYl : (Y : ℝ) ≤ hN N Y := by rw [hhN]; nlinarith [hY0, hLl1]
  have hCpos : (0 : ℝ) < (P.C : ℝ) := by linarith
  have hfin : (X : ℝ) + lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ)
      + (Y : ℝ) * ((P.c N X Y : ℝ) + 33) ≤ (X : ℝ) + 50 * (P.C : ℝ) * hN N Y := by
    have h1 : lg (2 * (P.Nmax N X Y : ℝ) + 2) * (Y : ℝ) ≤ (Ll + 2) * (Y : ℝ) :=
      mul_le_mul_of_nonneg_right hLm_le hY0
    have h2 : (Y : ℝ) * ((P.c N X Y : ℝ) + 33) ≤ (Y : ℝ) * ((P.C : ℝ) + 2 * Ll + 2 + 33) :=
      mul_le_mul_of_nonneg_left (by linarith [hc_le]) hY0
    have h3 : (Y : ℝ) * (P.C : ℝ) ≤ (P.C : ℝ) * hN N Y := by
      have h4 : (0 : ℝ) ≤ (P.C : ℝ) := le_of_lt hCpos
      nlinarith [hYl, h4]
    nlinarith [h1, h2, h3, hhN, hLl1, hY0, hC1, hYl]
  linarith [hmain, hfin]

/-! ### Step 3: the rules and the two column counts -/

/-- The cheap rule fires only when `D ≤ N/log¹⁰ n` (as in the paper's first stopping rule). -/
lemma rule_cheap_D {P : HintParams} {N X Y : ℕ} (hrule : P.rule N X Y = .cheap) :
    (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10 := by
  by_contra hcon
  push_neg at hcon
  have h1 : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) := not_le.mpr hcon
  have hr : P.rule N X Y = .small ∨ P.rule N X Y = .recursive ∨ P.rule N X Y = .direct := by
    unfold HintParams.rule
    rw [if_neg h1]
    split_ifs with h2 h3
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hr with h | h | h <;> rw [hrule] at h <;> exact absurd h (by decide)

/-- `n = 2^{log n}`. -/
lemma n_eq_two_rpow (P : HintParams) (hn : 2 ≤ P.n) : (P.n : ℝ) = (2 : ℝ) ^ P.lgn := by
  have hpos : (0 : ℝ) < (P.n : ℝ) := by
    have h1 : 0 < P.n := by omega
    exact_mod_cast h1
  exact (Real.rpow_logb (b := (2 : ℝ)) (x := (P.n : ℝ)) (by norm_num)
    (by norm_num : (2 : ℝ) ≠ 1) hpos).symm

/-- `λ_* ≥ 1`: the paper's instance parameter is at least one. -/
lemma lamStar_ge_one (P : HintParams) (hC : 1 ≤ P.C) : (1 : ℝ) ≤ (P.lamStar : ℝ) := by
  have h1 : 1 ≤ P.lamStar := by
    unfold HintParams.lamStar
    omega
  exact_mod_cast h1

/-- as in the paper: the recursion parameters force `log n ≥ 72` (this is what makes every
`log`-power budget below absolute rather than dependent on `C`). -/
lemma lgn_ge_72 (P : HintParams) (hn : 2 ≤ P.n) {N X Y : ℕ} (hNn : N ≤ P.n)
    (hC8 : (10 ^ 8 : ℝ) ≤ (P.C : ℝ)) (hrule : P.rule N X Y = .recursive) :
    (72 : ℝ) ≤ P.lgn := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lgn hn
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have h1 := Nthresh_le_N (P := P) (N := N) (X := X) (Y := Y) hL1 hrule
  have h3 : (N : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hNn
  have h4 : (P.n : ℝ) = (2 : ℝ) ^ P.lgn := n_eq_two_rpow P hn
  have h5 : (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A) ≤ (2 : ℝ) ^ P.lgn := by
    rw [← h4]; linarith
  have hlgC : (24 : ℝ) ≤ lg (P.C : ℝ) := by
    have h6 : lg ((10 : ℝ) ^ 8) ≤ lg (P.C : ℝ) :=
      lg_le_lg_of_le (by norm_num) (by linarith) hC8
    have h7 : lg ((10 : ℝ) ^ 8) = 8 * lg 10 := by
      rw [lg_pow_pos (by norm_num)]; norm_num
    have h8 : (3 : ℝ) ≤ lg 10 := by
      have h9 : lg ((2 : ℝ) ^ (3 : ℕ)) ≤ lg 10 :=
        lg_le_lg_of_le (by norm_num) (by norm_num) (by norm_num : (2 : ℝ) ^ (3 : ℕ) ≤ 10)
      rw [lg_pow_pos (by norm_num), lg_two] at h9
      push_cast at h9
      linarith
    rw [h7] at h6
    linarith
  have hpos1 : (0 : ℝ) < (P.C : ℝ) ^ 4 := by positivity
  have hpos2 : (0 : ℝ) < P.lgn ^ (6 + 2 * P.A) := by positivity
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ P.lgn := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hlgn)
    simpa using hh
  have h6 : lg ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) ≤ P.lgn := by
    have h7 : lg ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) ≤ lg ((2 : ℝ) ^ P.lgn) :=
      lg_le_lg_of_le (by positivity) hpow2 h5
    have h8 : lg ((2 : ℝ) ^ P.lgn) = P.lgn := by
      rw [lg, Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
    rw [h8] at h7
    exact h7
  have h9 : lg ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A))
      = 4 * lg (P.C : ℝ) + lg (P.lgn ^ (6 + 2 * P.A)) := by
    rw [lg_mul_pos (x := (P.C : ℝ) ^ 4) (y := P.lgn ^ (6 + 2 * P.A)) hpos1 hpos2,
      lg_pow_pos (x := (P.C : ℝ)) (by linarith : (0 : ℝ) < (P.C : ℝ))]
    norm_num
  have h10 : (0 : ℝ) ≤ lg (P.lgn ^ (6 + 2 * P.A)) := by
    apply Real.logb_nonneg (by norm_num)
    exact one_le_pow₀ hL1
  rw [h9] at h6
  linarith

lemma A_le_lgn (P : HintParams) (hn : 2 ≤ P.n) {N X Y : ℕ} (hNn : N ≤ P.n)
    (hC8 : (10 ^ 8 : ℝ) ≤ (P.C : ℝ)) (hrule : P.rule N X Y = .recursive) :
    (P.A : ℝ) ≤ P.lgn := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lgn hn
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have h72 := lgn_ge_72 P hn hNn hC8 hrule
  have hlgL : (1 : ℝ) ≤ lg P.lgn := by
    have h2 : lg (2 : ℝ) ≤ lg P.lgn := lg_le_lg_of_le (by norm_num) (by linarith) (by linarith)
    rwa [lg_two] at h2
  have hlgC : (24 : ℝ) ≤ lg (P.C : ℝ) := by
    have h6 : lg ((10 : ℝ) ^ 8) ≤ lg (P.C : ℝ) :=
      lg_le_lg_of_le (by norm_num) (by linarith) hC8
    have h7 : lg ((10 : ℝ) ^ 8) = 8 * lg 10 := by
      rw [lg_pow_pos (by norm_num)]; norm_num
    have h8 : (3 : ℝ) ≤ lg 10 := by
      have h9 : lg ((2 : ℝ) ^ (3 : ℕ)) ≤ lg 10 :=
        lg_le_lg_of_le (by norm_num) (by norm_num) (by norm_num : (2 : ℝ) ^ (3 : ℕ) ≤ 10)
      rw [lg_pow_pos (by norm_num), lg_two] at h9
      push_cast at h9
      linarith
    rw [h7] at h6
    linarith
  have h1 := Nthresh_lt (P := P) (N := N) (X := X) (Y := Y) hrule
  have heta : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := inv_eta_sq P
  have h2 : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) < (P.n : ℝ) := by
    have h := h1
    rw [div_eq_mul_inv, heta] at h
    have h4 : (HintParams.D N X Y : ℝ) ≤ (P.n : ℝ) := by
      have h5 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le_N N X Y
      have h6 : (N : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hNn
      linarith
    calc (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
        = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by
          rw [pow_add]
          ring
      _ < (HintParams.D N X Y : ℝ) := h
      _ ≤ (P.n : ℝ) := h4
  have h4 : (P.n : ℝ) = (2 : ℝ) ^ P.lgn := n_eq_two_rpow P hn
  have h5 : lg ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)) ≤ P.lgn := by
    have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ P.lgn := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hlgn)
      simpa using hh
    have h6 : lg ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A))
        ≤ lg ((2 : ℝ) ^ P.lgn) := by
      rw [h4] at h2
      exact lg_le_lg_of_le (by positivity) hpow2 (le_of_lt h2)
    have h7 : lg ((2 : ℝ) ^ P.lgn) = P.lgn := by
      rw [lg, Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
    rw [h7] at h6
    exact h6
  have hlam : (1 : ℝ) ≤ (P.lamStar : ℝ) := lamStar_ge_one_of_C (P := P) (by linarith)
  have h6 : lg ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A))
      = lg ((P.C : ℝ) ^ 3) + lg (P.lamStar : ℝ) + ((6 + 2 * P.A : ℕ) : ℝ) * lg P.lgn := by
    have hCpos' : (0 : ℝ) < (P.C : ℝ) := by linarith
    have hlam0' : (0 : ℝ) < (P.lamStar : ℝ) := by linarith
    rw [lg_mul_pos (x := (P.C : ℝ) ^ 3 * (P.lamStar : ℝ))
        (y := P.lgn ^ (6 + 2 * P.A)) (by positivity) (by positivity),
      lg_mul_pos (x := (P.C : ℝ) ^ 3) (y := (P.lamStar : ℝ)) (pow_pos hCpos' 3) hlam0',
      lg_pow_pos (x := P.lgn) hlgn]
  have hC3 : (72 : ℝ) ≤ lg ((P.C : ℝ) ^ 3) := by
    have h8 : lg ((P.C : ℝ) ^ 3) = 3 * lg (P.C : ℝ) := lg_pow_pos (by linarith) 3
    rw [h8]; linarith
  have hlam0 : (0 : ℝ) ≤ lg (P.lamStar : ℝ) := lg_nonneg_of_one_le hlam
  rw [h6] at h5
  have h13 : ((6 + 2 * P.A : ℕ) : ℝ) ≤ ((6 + 2 * P.A : ℕ) : ℝ) * lg P.lgn := by
    have h14 : (1 : ℝ) ≤ lg P.lgn := hlgL
    have h15 : (0 : ℝ) ≤ ((6 + 2 * P.A : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h14, h15]
  have h16 : ((6 + 2 * P.A : ℕ) : ℝ) = 6 + 2 * (P.A : ℝ) := by push_cast; ring
  rw [h16] at h13 h5
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
  nlinarith [h5, h13, hC3, hlam0, hA0]

lemma ell_le_abs (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hL : 2 ≤ P.lgn) (hA : (P.A : ℝ) ≤ P.lgn) (hrule : P.rule N X Y = .recursive) :
    (P.ell N X Y : ℝ) ≤ 204 * P.lgn ^ 15 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hell := ell_le (P := P) hargs hL hrule
  have hp15 : (1 : ℝ) ≤ P.lgn ^ 15 := one_le_pow₀ hL1
  have hp14 : P.lgn ^ 14 ≤ P.lgn ^ 15 := pow_le_pow_right₀ hL1 (by norm_num)
  calc (P.ell N X Y : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 := hell
    _ ≤ (4 * P.lgn + 200) * P.lgn ^ 14 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 4 * P.lgn ^ 15 + 200 * P.lgn ^ 14 := by ring
    _ ≤ 204 * P.lgn ^ 15 := by nlinarith [hp14, hp15]

/-- the number of columns, `C`-dependent form: this is the paper's `ℓ = O(C log³ n)`, used for the
cheap leaves (their CR sketch costs only `O(Y/log^8 n)`). -/
lemma ell_le_C (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 32 ≤ P.lgn)
    (hA : (P.A : ℝ) ≤ P.lgn) (hC1 : (1 : ℝ) ≤ (P.C : ℝ)) (hrule : P.rule N X Y = .recursive) :
    (P.ell N X Y : ℝ) ≤ 21 * (P.C : ℝ) * P.lgn ^ 3 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hNmax := Nmax_le (P := P) hargs hL1 hrule
  have hBX : (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := by
    have hle : (P.BX N X Y : ℝ) ≤ ((⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
      have h : P.BX N X Y ≤ ⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ := by
        unfold HintParams.BX
        exact min_le_right _ _
      exact_mod_cast h
    have hlt : ((⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ)
        < P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hBY : (P.BY N X Y : ℝ) ≤ 4 * (P.C : ℝ) * P.lgn + 5 := by
    have h1 : (P.BY N X Y : ℝ) ≤ ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) + 4 := by
      have h : P.BY N X Y ≤ ⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ + 4 := by
        unfold HintParams.BY
        exact min_le_right _ _
      exact_mod_cast h
    have h2 : ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ)
        < (P.C : ℝ) * lg (P.lgn + 2) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (by linarith : (0 : ℝ) ≤ (P.C : ℝ))
        (by apply Real.logb_nonneg (by norm_num); linarith))
    have h3 : lg (P.lgn + 2) ≤ 4 * P.lgn := by
      have h4 : lg (P.lgn + 2) ≤ (P.lgn + 2 - 1) * lg (Real.exp 1) :=
        lg_le_sub_one_mul (by linarith)
      have h5 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
      nlinarith [h4, h5, hlgn]
    have hC0 : (0 : ℝ) ≤ (P.C : ℝ) := by linarith
    nlinarith [h1, h2, h3, hC0, hlgn]
  have hNmax1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by
    have hrows : P.rows X Y = Y := rows_eq_of_rule hrule
    have hYN : Y ≤ N := hargs.2.2.2.2.2
    have hY1 : 1 ≤ Y := Y_ge_one hargs hL1 hrule
    unfold HintParams.Nmax
    rw [hrows]
    have hx : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hY1 : (0 : ℝ) < (Y : ℝ))]
      have h6 : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
      linarith
    exact le_trans hx (Nat.le_ceil _)
  have hK1 : ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ 13 * lg P.lgn + 6 := by
    have hlgL0 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
    have hx0 : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := by
      apply Real.logb_nonneg (by norm_num)
      have h1 : (1 : ℝ) ≤ Real.exp 1 := one_le_exp_one
      nlinarith [hNmax1, h1]
    have hceil := Nat.ceil_lt_add_one hx0
    have hbound : lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) ≤ 5 + 13 * lg P.lgn := by
      have h1 : lg (Real.exp 1 * (P.Nmax N X Y : ℝ))
          = lg (Real.exp 1) + lg (P.Nmax N X Y : ℝ) :=
        lg_mul_pos (by positivity) (by positivity)
      have h2 : lg (P.Nmax N X Y : ℝ) ≤ lg (3 * P.lgn ^ 13) := by
        apply lg_le_lg_of_le (Nat.cast_nonneg _) (by nlinarith [one_le_pow₀ (n := 13) hL1]) hNmax
      have h3 : lg (3 * P.lgn ^ 13) = lg 3 + 13 * lg P.lgn := by
        rw [lg_mul_pos (by norm_num) (by positivity), lg_pow_pos hlgn]
        push_cast
        ring
      have h4 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
      have h5 : lg 3 ≤ 2 := lg_three_le_two
      linarith [h1, h2, h3, h4, h5]
    linarith [hceil, hbound]
  have hK2 : ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) ≤ 4 * (P.A : ℝ) * P.lgn + 5 := by
    have hval : lg (16 / P.eta ^ 2) = 4 + 2 * (P.A : ℝ) * lg P.lgn := by
      have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
        rw [div_eq_mul_inv, inv_eta_sq]
      rw [heta, lg_mul_pos (by norm_num) (by positivity), lg_pow_pos hlgn, lg_sixteen]
      push_cast
      ring
    have hx0 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
      rw [hval]
      have h1 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
      have h2 : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, h2]
    have hceil := Nat.ceil_lt_add_one hx0
    have hlgL : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
    have hAlg : 2 * (P.A : ℝ) * lg P.lgn ≤ 4 * (P.A : ℝ) * P.lgn := by
      have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_left hlgL (by linarith : (0 : ℝ) ≤ 2 * (P.A : ℝ))
      nlinarith [h]
    linarith [hceil, hval, hAlg]
  have hdef : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) + (P.BY N X Y : ℝ)
      * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) + (P.BY N X Y : ℝ)
      + ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  -- multiply out the `B_Y · log(e N_max)` term
  have hprod : (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
      ≤ (4 * (P.C : ℝ) * P.lgn + 5) * (13 * lg P.lgn + 6) :=
    mul_le_mul hBY hK1 (Nat.cast_nonneg _) (by positivity)
  have hlgL2 : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have hprod2 : (4 * (P.C : ℝ) * P.lgn + 5) * (13 * lg P.lgn + 6)
      ≤ (4 * (P.C : ℝ) * P.lgn + 5) * (13 * (2 * P.lgn) + 6) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hexp : (4 * (P.C : ℝ) * P.lgn + 5) * (13 * (2 * P.lgn) + 6)
      = 104 * (P.C : ℝ) * P.lgn ^ 2 + 24 * (P.C : ℝ) * P.lgn + 130 * P.lgn + 30 := by ring
  have hprodall : (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
      ≤ 104 * (P.C : ℝ) * P.lgn ^ 2 + 24 * (P.C : ℝ) * P.lgn + 130 * P.lgn + 30 :=
    calc (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
        ≤ (4 * (P.C : ℝ) * P.lgn + 5) * (13 * lg P.lgn + 6) := hprod
      _ ≤ (4 * (P.C : ℝ) * P.lgn + 5) * (13 * (2 * P.lgn) + 6) := hprod2
      _ = 104 * (P.C : ℝ) * P.lgn ^ 2 + 24 * (P.C : ℝ) * P.lgn + 130 * P.lgn + 30 := hexp
  have hcel2 : ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) ≤ 4 * P.lgn ^ 2 + 5 := by
    have h1 : 4 * (P.A : ℝ) * P.lgn ≤ 4 * P.lgn ^ 2 := by nlinarith [hA, hlgn]
    linarith [hK2, h1]
  rw [hdef]
  have hassemble : (P.BX N X Y : ℝ)
      + (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
      + (P.BY N X Y : ℝ) + ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) + 10
      ≤ P.lgn ^ 3 + 105 * (P.C : ℝ) * P.lgn ^ 2 + 28 * (P.C : ℝ) * P.lgn + 130 * P.lgn
        + 4 * P.lgn ^ 2 + 51 := by
    linarith [hBX, hprodall, hBY, hcel2]
  have hL2nn : (0 : ℝ) ≤ P.lgn ^ 2 := by positivity
  have hkey1 : 105 * (P.C : ℝ) * P.lgn ^ 2 ≤ 5 * (P.C : ℝ) * P.lgn ^ 3 := by
    have h1 : (105 : ℝ) ≤ 5 * P.lgn := by linarith
    have h2 : (0 : ℝ) ≤ (P.C : ℝ) * P.lgn ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    nlinarith [h3]
  have hkey2 : 28 * (P.C : ℝ) * P.lgn ≤ 4 * (P.C : ℝ) * P.lgn ^ 3 := by
    have h1 : (28 : ℝ) ≤ 4 * P.lgn ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hL hL2nn
      nlinarith [h]
    have h2 : (0 : ℝ) ≤ (P.C : ℝ) * P.lgn := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    nlinarith [h3]
  have hkey3 : P.lgn ^ 3 + 4 * P.lgn ^ 2 + 130 * P.lgn + 51 ≤ 12 * P.lgn ^ 3 := by
    have hLnn : (0 : ℝ) ≤ P.lgn := by linarith
    have h1 : 32 * P.lgn ^ 2 ≤ P.lgn ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hL hL2nn
      nlinarith [h]
    have h2 : (130 : ℝ) * P.lgn ≤ 8 * P.lgn ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hL hLnn
      nlinarith [h]
    have h3 : (51 : ℝ) ≤ 8 * P.lgn ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hL hLnn
      nlinarith [h]
    nlinarith [h1, h2, h3]
  have hkey4 : 12 * P.lgn ^ 3 ≤ 12 * (P.C : ℝ) * P.lgn ^ 3 := by
    have h1 : (12 : ℝ) ≤ 12 * (P.C : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ P.lgn ^ 3 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    nlinarith [h3]
  linarith [hassemble, hkey1, hkey2, hkey3, hkey4]

/-! ### Step 4: the margin budgets (`η log³¹ n` negligible, `Y` dominates `log²⁸ n`) -/

/-- `100000 η log³¹ n ≤ 1`: with `η = log^{-A} n` and `A ≥ 100` every margin term carrying `η` is
negligible — the paper's `ℓ b log(e/η) ≤ O(A² Y log^{18-A} n) ≤ ρY/8`. -/
lemma eta_small (P : HintParams) (hL : 2 ≤ P.lgn) (hA : 100 ≤ P.A) :
    100000 * (P.eta * P.lgn ^ 31) ≤ 1 := by
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have heta : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  have hLA : P.lgn ^ P.A = P.lgn ^ 31 * P.lgn ^ (P.A - 31) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow : (100000 : ℝ) ≤ P.lgn ^ (P.A - 31) := by
    have h1 : (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ (P.A - 31) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (P.A - 31) ≤ P.lgn ^ (P.A - 31) :=
      pow_le_pow_left₀ (by norm_num) hL _
    have h3 : (2 : ℝ) ^ 17 = 131072 := by norm_num
    linarith [h1, h2, h3]
  have hp31 : (0 : ℝ) < P.lgn ^ 31 := by positivity
  have hpA : (0 : ℝ) < P.lgn ^ P.A := by positivity
  have hkey : 100000 * P.lgn ^ 31 ≤ P.lgn ^ P.A := by
    rw [hLA]
    nlinarith [hpow, hp31]
  calc 100000 * (P.eta * P.lgn ^ 31) = 100000 * P.lgn ^ 31 / P.lgn ^ P.A := by
        rw [heta]
        field_simp
    _ ≤ 1 := by
        rw [div_le_one hpA]
        exact hkey

/-- as in the paper: the second stopping rule gives `Y ≥ C³ λ_* log^{3+2A} n / 2`, so `Y` dominates
`log²⁸ n` outright (this is what keeps every budget absolute rather than `C`-dependent). -/
lemma Y_ge_pow28 {P : HintParams} {N X Y : ℕ}
    (hYlow : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A) ≤ 2 * (Y : ℝ))
    (hL1 : (1 : ℝ) ≤ P.lgn) (hC8 : (10 ^ 8 : ℝ) ≤ (P.C : ℝ))
    (hlam : (1 : ℝ) ≤ (P.lamStar : ℝ)) (hA : 50 ≤ P.A) :
    (10 : ℝ) ^ 6 * P.lgn ^ 28 ≤ (Y : ℝ) := by
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hC3 : (10 : ℝ) ^ 8 ≤ (P.C : ℝ) ^ 3 := by
    have h1 : (P.C : ℝ) ≤ (P.C : ℝ) ^ 3 := by
      have h2 : (1 : ℝ) ≤ (P.C : ℝ) := by linarith
      have h3 : (1 : ℝ) ≤ (P.C : ℝ) ^ 2 := one_le_pow₀ h2
      calc (P.C : ℝ) = (P.C : ℝ) * 1 := by ring
        _ ≤ (P.C : ℝ) * (P.C : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = (P.C : ℝ) ^ 3 := by ring
    linarith [hC8, h1]
  have hexp : 28 ≤ 3 + 2 * P.A := by omega
  have hpow : P.lgn ^ 28 ≤ P.lgn ^ (3 + 2 * P.A) := pow_le_pow_right₀ hL1 hexp
  have h1 : (10 : ℝ) ^ 8 * P.lgn ^ 28
      ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A) := by
    have h2 : (10 : ℝ) ^ 8 * 1 * 1 ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * 1 := by
      nlinarith [hC3, hlam]
    calc (10 : ℝ) ^ 8 * P.lgn ^ 28 = (10 : ℝ) ^ 8 * 1 * 1 * P.lgn ^ 28 := by ring
      _ ≤ ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * 1) * P.lgn ^ (3 + 2 * P.A) := by
          apply mul_le_mul h2 hpow (by positivity) (by positivity)
      _ = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A) := by ring
  have h4 : (10 : ℝ) ^ 6 ≤ (10 : ℝ) ^ 8 := by norm_num
  nlinarith [h1, hYlow, h4]

/-! ### Step 5: the four conclusions at one recursive node -/

/-- as in the paper: at a cheap child the row count is only `O(Y / log⁸ n)` — the cheap rule gives
`D_s ≤ Y/log¹⁰ n` and `log(Y_s + 2) ≤ log n + 1` because `Y_s ≤ Y ≤ N ≤ n`. -/
lemma cheap_child_len (P : HintParams) (CR : CRFamily) {KCR : ℝ} {N Y Xs Ys : ℕ}
    (hCR : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hn2 : 2 ≤ P.n) (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hYN : Y ≤ N) (hY2 : (2 : ℝ) ≤ (Y : ℝ))
    (hcheapD : (HintParams.D Y Xs Ys : ℝ) ≤ (Y : ℝ) / P.lgn ^ 10) :
    (CR.rows Y (HintParams.D Y Xs Ys) : ℝ)
      ≤ |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lgn hn2
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have htY : HintParams.D Y Xs Ys ≤ Y := by unfold HintParams.D; omega
  have h1 : (CR.rows Y (HintParams.D Y Xs Ys) : ℝ)
      ≤ KCR * ((HintParams.D Y Xs Ys : ℝ) * lg ((Y : ℝ) + 2) ^ 2) := hCR Y _ htY
  have h4 : lg ((Y : ℝ) + 2) ≤ P.lgn + 1 := by
    have h5 : (Y : ℝ) + 2 ≤ 2 * (N : ℝ) := by
      have h6 : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
      linarith
    have h7 : lg ((Y : ℝ) + 2) ≤ lg (2 * (N : ℝ)) :=
      lg_le_lg_of_le (by positivity) (by linarith) h5
    have h8 : lg (2 * (N : ℝ)) ≤ 1 + P.lgn := by
      rw [lg_mul_pos (by norm_num) (by positivity), lg_two]
      have h9 : lg (N : ℝ) ≤ P.lgn :=
        lg_le_lg_of_le (by positivity)
          (by exact_mod_cast (le_trans hN1 hNn) : (1 : ℝ) ≤ (P.n : ℝ)) (by exact_mod_cast hNn)
      linarith
    linarith [h7, h8]
  have h3 : lg ((Y : ℝ) + 2) ^ 2 ≤ (P.lgn + 1) ^ 2 := by
    have h9 : (0 : ℝ) ≤ lg ((Y : ℝ) + 2) := by
      apply Real.logb_nonneg (by norm_num)
      linarith
    exact pow_le_pow_left₀ h9 h4 2
  have h10 : (HintParams.D Y Xs Ys : ℝ) * lg ((Y : ℝ) + 2) ^ 2
      ≤ ((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2 :=
    mul_le_mul hcheapD h3 (by positivity) (by positivity)
  have h11 : (0 : ℝ) ≤ (HintParams.D Y Xs Ys : ℝ) * lg ((Y : ℝ) + 2) ^ 2 := by positivity
  calc (CR.rows Y (HintParams.D Y Xs Ys) : ℝ)
      ≤ KCR * ((HintParams.D Y Xs Ys : ℝ) * lg ((Y : ℝ) + 2) ^ 2) := h1
    _ ≤ |KCR| * ((HintParams.D Y Xs Ys : ℝ) * lg ((Y : ℝ) + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self KCR) h11
    _ ≤ |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h10 (abs_nonneg KCR)

section
set_option maxHeartbeats 1600000

open Classical in
/-- as in the paper: the four conclusions of Lemma 5.9 at a recursive node — the three inequalities
`eq:hint-rounded-sums` and the mixed budget `eq:hint-local-cost`.  `K` is the paper's hidden
constant of `O(C h_N(Y))`; the paper's `1/4` and `1/8` factors are kept verbatim. -/
lemma child_bounds (P : HintParams) (K : ℝ) (CR : CRFamily) {KCR : ℝ} {N X Y : ℕ}
    (hargs : P.NodeArgs N X Y) (hrule : P.rule N X Y = .recursive)
    (hCR : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hA100 : 100 ≤ P.A) (hC8 : (10 ^ 8 : ℝ) ≤ (P.C : ℝ)) (hK250 : 250 ≤ K)
    (hKC : K ≤ (P.C : ℝ)) (hKC2 : 4000 * |KCR| ≤ (P.C : ℝ))
    (h58 : ∑ s ∈ range (P.ell N X Y), hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)
      ≤ hN N Y / 8) :
    (∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ) ≤ (X : ℝ) + K * ((P.C : ℝ) * hN N Y)) ∧
    (∑ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s) ≤ hN N Y / 4) ∧
    (∑ s ∈ range (P.ell N X Y), ((P.capY N X Y s : ℝ) / (Y : ℝ)) ≤ ((Y : ℝ) / (N : ℝ)) / 4) ∧
    (∑ s ∈ (range (P.ell N X Y)).filter
          (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .recursive),
        ((P.capX N X Y s : ℝ) + (P.C : ℝ) ^ 2 * hN Y (P.capY N X Y s)) +
      ∑ s ∈ (range (P.ell N X Y)).filter
          (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .direct), (P.capX N X Y s : ℝ) +
      ∑ s ∈ (range (P.ell N X Y)).filter
          (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .cheap),
        (CR.rows Y (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s)) : ℝ) ≤
      (X : ℝ) + (P.C : ℝ) ^ 2 * hN N Y) := by
  classical
  have hargs0 := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs0
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lgn hn2
  have hlgn : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hrows : P.rows X Y = Y := rows_eq_of_rule hrule
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL1 hrule
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY1
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := le_of_lt hYposR
  have hY1R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hC1 : (1 : ℝ) ≤ (P.C : ℝ) := by linarith only [hC8]
  have hCpos : (0 : ℝ) < (P.C : ℝ) := by linarith only [hC1]
  have hrho0 : (0 : ℝ) < nodeDens N Y := nodeDens_pos (by omega) (by omega)
  have hrho1 : nodeDens N Y ≤ 1 := nodeDens_le_one hN1 hYN
  have hL2 : (2 : ℝ) ≤ P.lgn := by linarith only [lgn_ge_72 P hn2 hNn hC8 hrule]
  have hL32 : (32 : ℝ) ≤ P.lgn := by linarith only [lgn_ge_72 P hn2 hNn hC8 hrule]
  have hAle : (P.A : ℝ) ≤ P.lgn := A_le_lgn P hn2 hNn hC8 hrule
  have hell : (P.ell N X Y : ℝ) ≤ 204 * P.lgn ^ 15 := ell_le_abs P hargs hL2 hAle hrule
  have hellC : (P.ell N X Y : ℝ) ≤ 21 * (P.C : ℝ) * P.lgn ^ 3 :=
    ell_le_C P hargs hL32 hAle hC1 hrule
  have hell0 : (0 : ℝ) ≤ (P.ell N X Y : ℝ) := Nat.cast_nonneg _
  have hlam1' : (1 : ℝ) ≤ (P.lamStar : ℝ) := lamStar_ge_one_of_C (P := P) (by linarith)
  have heta0 : (0 : ℝ) ≤ P.eta := by
    unfold HintParams.eta
    positivity
  -- ## `h_N` in quotient form
  set Ll : ℝ := lg (Real.exp 1 * (N : ℝ) / (Y : ℝ)) with hLl
  have hLl1 : (1 : ℝ) ≤ Ll := by
    have h1 : Real.exp 1 ≤ Real.exp 1 * (N : ℝ) / (Y : ℝ) := by
      rw [le_div_iff₀ hYposR]
      have h6 : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
      nlinarith only [Real.exp_pos 1, h6]
    have h2 : (1 : ℝ) ≤ lg (Real.exp 1) := one_le_lg_exp
    have h3 : lg (Real.exp 1) ≤ lg (Real.exp 1 * (N : ℝ) / (Y : ℝ)) :=
      lg_le_lg_of_pos (Real.exp_pos 1) h1
    rw [hLl]
    linarith only [h2, h3]
  have hhN : hN N Y = (Y : ℝ) * Ll := by
    rw [hN_eq_quot (ne_of_gt hNposR) hYposR, ← hLl]
  have hhN0 : (0 : ℝ) ≤ hN N Y := by rw [hhN]; positivity
  have hYlN : (Y : ℝ) ≤ hN N Y := by rw [hhN]; nlinarith only [hY0, hLl1]
  have hρLl : nodeDens N Y * Ll ≤ 4 := by
    have h1 : Ll = lg (Real.exp 1) + lg ((N : ℝ) / (Y : ℝ)) := by
      have hmul : Real.exp 1 * (N : ℝ) / (Y : ℝ) = Real.exp 1 * ((N : ℝ) / (Y : ℝ)) := by ring
      rw [hLl, hmul, lg_mul_pos (by positivity) (by positivity)]
    have hratio1 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
      rw [le_div_iff₀ hYposR]
      have h6 : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
      linarith only [h6]
    have h2 : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ)) ≤ lg (Real.exp 1) := by
      have heq : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ))
          = lg ((N : ℝ) / (Y : ℝ)) / ((N : ℝ) / (Y : ℝ)) := by
        unfold nodeDens
        field_simp
      rw [heq]
      exact lg_div_self_le hratio1
    have h3 : nodeDens N Y ≤ 1 := hrho1
    have h4 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
    nlinarith only [h1, h2, h3, h4, hrho0]
  -- ## the margin `b` and the scalar `T` of the paper's budget calculation
  -- the additive margin of equation (19): `b = 2 η (D+1) + 1`; the `+1` pays for the ceiling
  -- and is what makes `b ≥ 1`, which the entropy estimate `hNb` needs.
  set b : ℝ := 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 with hb
  have hb0 : (0 : ℝ) ≤ b := by rw [hb]; positivity
  have hb1 : 1 ≤ b := by
    have h1 : (0 : ℝ) ≤ 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by positivity
    rw [hb]
    linarith only [h1]
  have hXle : (X : ℝ) ≤ (Y : ℝ) * P.lgn ^ 3 := X_le_of_rows hlgn hrows
  have hDsum : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
    have h := D_le_sum N X Y
    have h' : (HintParams.D N X Y : ℝ) ≤ ((X + Y : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at h'
    linarith only [h']
  have hD1 : (HintParams.D N X Y : ℝ) + 1 ≤ 3 * ((Y : ℝ) * P.lgn ^ 3) := by
    have hL3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL1
    have hL3pos : (0 : ℝ) < P.lgn ^ 3 := by positivity
    have hY1R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
    nlinarith only [hXle, hDsum, hL3, hY1R, hL3pos]
  have hbble : b ≤ 6 * P.eta * (Y : ℝ) * P.lgn ^ 3 + 1 := by
    rw [hb]
    have h1 : 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)
        ≤ 2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)) :=
      mul_le_mul_of_nonneg_left hD1 (by positivity)
    linarith only [h1]
  -- ## the second stopping rule: `C³ λ_* log^{3+2A} n ≤ 2Y`
  have hYlow : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A) ≤ 2 * (Y : ℝ) := by
    have h1 := Nthresh_lt (P := P) (N := N) (X := X) (Y := Y) hrule
    have heta : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := inv_eta_sq P
    have h2 : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
        < (HintParams.D N X Y : ℝ) := by
      have h := h1
      rw [div_eq_mul_inv, heta] at h
      have heq : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
          = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by
        rw [pow_add]
        ring
      rw [heq]
      exact h
    have hL3pos : (0 : ℝ) < P.lgn ^ 3 := by positivity
    have hsum : (X : ℝ) + (Y : ℝ) ≤ 2 * (Y : ℝ) * P.lgn ^ 3 := by
      have hL3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL1
      nlinarith only [hXle, hL3, hYposR]
    have hsplit : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
        = ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A)) * P.lgn ^ 3 := by
      have hp : P.lgn ^ (6 + 2 * P.A) = P.lgn ^ (3 + 2 * P.A) * P.lgn ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring
    rw [hsplit] at h2
    have hpos : (0 : ℝ) < (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (3 + 2 * P.A) := by
      have h3 : (0 : ℝ) < (P.C : ℝ) ^ 3 := by positivity
      have h4 : (0 : ℝ) < (P.lamStar : ℝ) := lt_of_lt_of_le hCpos (lamStar_ge_C P)
      have h5 : (0 : ℝ) < P.lgn ^ (3 + 2 * P.A) := by positivity
      positivity
    nlinarith only [h2, hsum, hL3pos, hpos, hDsum]
  -- ## the two absolute budgets
  have heps : 100000 * (P.eta * P.lgn ^ 31) ≤ 1 := eta_small P hL2 hA100
  have hY28 : (10 : ℝ) ^ 6 * P.lgn ^ 28 ≤ (Y : ℝ) :=
    Y_ge_pow28 (P := P) (N := N) (X := X) (Y := Y) hYlow hL1 hC8 hlam1' (by omega)
  have hY2 : (2 : ℝ) ≤ (Y : ℝ) := by
    have hp : (1 : ℝ) ≤ P.lgn ^ 28 := one_le_pow₀ (n := 28) hL1
    nlinarith only [hY28, hp]
  have hp13 : (0 : ℝ) < P.lgn ^ 13 := by positivity
  -- margin 1: `1300 η Y L^18 ≤ Y/(32 L^13)`
  have hmA : 1300 * P.eta * (Y : ℝ) * P.lgn ^ 18 ≤ (Y : ℝ) / (32 * P.lgn ^ 13) := by
    have h2 : P.lgn ^ 18 * P.lgn ^ 13 = P.lgn ^ 31 := by rw [← pow_add]
    have h3 : 1300 * P.eta * (Y : ℝ) * P.lgn ^ 18 * (32 * P.lgn ^ 13)
        = 41600 * (P.eta * P.lgn ^ 31) * (Y : ℝ) := by
      rw [← h2]; ring
    have h1 : 1300 * P.eta * (Y : ℝ) * P.lgn ^ 18 * (32 * P.lgn ^ 13) ≤ (Y : ℝ) := by
      rw [h3]
      nlinarith only [heps, hY0]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 32 * P.lgn ^ 13)]
    exact h1
  -- margin 2: `300 L^15 ≤ Y/(32 L^13)`
  have hmB : 300 * P.lgn ^ 15 ≤ (Y : ℝ) / (32 * P.lgn ^ 13) := by
    have h2 : P.lgn ^ 15 * P.lgn ^ 13 = P.lgn ^ 28 := by rw [← pow_add]
    have h3 : 300 * P.lgn ^ 15 * (32 * P.lgn ^ 13) = 9600 * P.lgn ^ 28 := by
      rw [← h2]; ring
    have h1 : 300 * P.lgn ^ 15 * (32 * P.lgn ^ 13) ≤ (Y : ℝ) := by
      rw [h3]
      nlinarith only [hY28]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 32 * P.lgn ^ 13)]
    exact h1
  -- margin 3: `3900 η Y L^19 ≤ Y Ll / 16`
  have hmC : 3900 * P.eta * (Y : ℝ) * P.lgn ^ 19 ≤ (Y : ℝ) * Ll / 16 := by
    have h1 : 62400 * (P.eta * P.lgn ^ 19) ≤ 1 := by
      have h2 : P.lgn ^ 19 ≤ P.lgn ^ 31 := pow_le_pow_right₀ hL1 (by norm_num)
      have h3 : P.eta * P.lgn ^ 19 ≤ P.eta * P.lgn ^ 31 := mul_le_mul_of_nonneg_left h2 heta0
      nlinarith only [h3, heps]
    have h2 : 3900 * P.eta * (Y : ℝ) * P.lgn ^ 19 ≤ (Y : ℝ) / 16 := by
      have h3 : 3900 * (P.eta * P.lgn ^ 19) ≤ 1 / 16 := by nlinarith only [h1]
      have h4 : 3900 * (P.eta * P.lgn ^ 19) * (Y : ℝ) ≤ (1 / 16) * (Y : ℝ) :=
        mul_le_mul_of_nonneg_right h3 hY0
      nlinarith only [h4]
    have h5 : (Y : ℝ) / 16 ≤ (Y : ℝ) * Ll / 16 := by
      have h6 : (Y : ℝ) * 1 ≤ (Y : ℝ) * Ll := mul_le_mul_of_nonneg_left hLl1 hY0
      linarith only [h6]
    linarith only [h2, h5]
  -- margin 4: `900 L^16 ≤ Y Ll / 16`
  have hmD : 900 * P.lgn ^ 16 ≤ (Y : ℝ) * Ll / 16 := by
    have h1 : 14400 * P.lgn ^ 16 ≤ (Y : ℝ) := by
      have h2 : P.lgn ^ 16 ≤ P.lgn ^ 28 := pow_le_pow_right₀ hL1 (by norm_num)
      nlinarith only [hY28, h2]
    have h2 : 900 * P.lgn ^ 16 ≤ (Y : ℝ) / 16 := by nlinarith only [h1]
    have h3 : (Y : ℝ) / 16 ≤ (Y : ℝ) * Ll / 16 := by
      have h6 : (Y : ℝ) * 1 ≤ (Y : ℝ) * Ll := mul_le_mul_of_nonneg_left hLl1 hY0
      linarith only [h6]
    linarith only [h2, h3]
  -- the density floor `ρ ≥ 1/(2 log¹³ n)`
  have hρlb : (1 : ℝ) / (2 * P.lgn ^ 13) ≤ nodeDens N Y := by
    have h := dens_gt (P := P) hargs hL1 hrule
    unfold densFloor at h
    rw [inv_eq_one_div] at h
    exact le_of_lt h
  -- ## the three margin inequalities
  set T : ℝ := 1300 * P.eta * (Y : ℝ) * P.lgn ^ 18 + 300 * P.lgn ^ 15 with hT
  have hT0 : (0 : ℝ) ≤ T := by
    rw [hT]; positivity
  have hTsplit : T ≤ (Y : ℝ) / (16 * P.lgn ^ 13) := by
    have h1 : (Y : ℝ) / (32 * P.lgn ^ 13) + (Y : ℝ) / (32 * P.lgn ^ 13)
        = (Y : ℝ) / (16 * P.lgn ^ 13) := by
      field_simp
      ring
    rw [hT]
    linarith only [hmA, hmB, h1]
  have hlb : (P.ell N X Y : ℝ) * b ≤ T := by
    have h1 : (P.ell N X Y : ℝ) * b
        ≤ (204 * P.lgn ^ 15) * (6 * P.eta * (Y : ℝ) * P.lgn ^ 3 + 1) :=
      mul_le_mul hell hbble hb0 (by positivity)
    have h2 : (204 * P.lgn ^ 15) * (6 * P.eta * (Y : ℝ) * P.lgn ^ 3 + 1) ≤ T := by
      rw [hT]
      have hp : P.lgn ^ 15 * P.lgn ^ 3 = P.lgn ^ 18 := by rw [← pow_add]
      have hp0 : (0 : ℝ) < P.lgn ^ 15 := by positivity
      have hp18 : (0 : ℝ) < P.lgn ^ 18 := by positivity
      have hetaY : (0 : ℝ) ≤ P.eta * (Y : ℝ) := mul_nonneg heta0 hY0
      nlinarith only [hp, hp0, hp18, hetaY]
    linarith only [h1, h2]
  have hT1 : T ≤ nodeDens N Y * (Y : ℝ) / 8 := by
    have h1 : (Y : ℝ) / (16 * P.lgn ^ 13) ≤ nodeDens N Y * (Y : ℝ) / 8 := by
      have h5 : (1 / (2 * P.lgn ^ 13)) * (Y : ℝ) ≤ nodeDens N Y * (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hρlb hY0
      have h6 : (1 / (2 * P.lgn ^ 13)) * (Y : ℝ) = (Y : ℝ) / (2 * P.lgn ^ 13) := by ring
      have h7 : (Y : ℝ) / (2 * P.lgn ^ 13) / 8 = (Y : ℝ) / (16 * P.lgn ^ 13) := by
        field_simp; ring
      nlinarith only [h5, h6, h7]
    linarith only [hTsplit, h1]
  have hT2 : T ≤ 200 * (P.C : ℝ) * hN N Y := by
    have h1 : (Y : ℝ) / (16 * P.lgn ^ 13) ≤ (Y : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * P.lgn ^ 13)]
      have h2 : (1 : ℝ) ≤ 16 * P.lgn ^ 13 := by
        have h3 : (1 : ℝ) ≤ P.lgn ^ 13 := one_le_pow₀ hL1
        nlinarith only [h3]
      nlinarith only [h2, hY0]
    have h3 : (Y : ℝ) ≤ 200 * (P.C : ℝ) * hN N Y := by
      have h4 : (2 : ℝ) ≤ 200 * (P.C : ℝ) := by nlinarith only [hC1]
      nlinarith only [h4, hYlN, hY0]
    linarith only [hTsplit, h1, h3]
  have hT3 : 3 * P.lgn * T ≤ hN N Y / 8 := by
    have h1 : 3 * P.lgn * (1300 * P.eta * (Y : ℝ) * P.lgn ^ 18)
        = 3900 * P.eta * (Y : ℝ) * P.lgn ^ 19 := by
      have hp : P.lgn * P.lgn ^ 18 = P.lgn ^ 19 := (pow_succ' P.lgn 18).symm
      rw [← hp]; ring
    have h2 : 3 * P.lgn * (300 * P.lgn ^ 15) = 900 * P.lgn ^ 16 := by
      have hp : P.lgn * P.lgn ^ 15 = P.lgn ^ 16 := (pow_succ' P.lgn 15).symm
      rw [← hp]; ring
    rw [hT]
    have h3 : 3 * P.lgn * (1300 * P.eta * (Y : ℝ) * P.lgn ^ 18 + 300 * P.lgn ^ 15)
        = 3 * P.lgn * (1300 * P.eta * (Y : ℝ) * P.lgn ^ 18) + 3 * P.lgn * (300 * P.lgn ^ 15) := by
      ring
    rw [h3, h1, h2]
    have h4 : hN N Y / 8 = (Y : ℝ) * Ll / 8 := by rw [hhN]
    rw [h4]
    linarith only [hmC, hmD]
  -- ## the outside mass: paper `eq:hint-outside-mass`
  have hout : ∑ s ∈ range (P.ell N X Y), ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
      ≤ nodeDens N Y * (Y : ℝ) / 8 := by
    have h1 : ∑ s ∈ range (P.ell N X Y), ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
        ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s := by
      rw [Finset.mul_sum]
    have h2 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 :=
      two_rpow_c_inv_le hargs hY1 hrule
    have h3 := Q_sum_le_sharp P hargs hrows hY1 hrule hC1
    have h4 : (0 : ℝ) ≤ ∑ s ∈ range (P.ell N X Y), P.Q N X Y s :=
      Finset.sum_nonneg (fun s _ => Q_nonneg (P := P) hN1 s)
    have h5 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
        ≤ ((2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2)
          * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y) :=
      mul_le_mul h2 h3 h4 (by positivity)
    have hρX : (nodeDens N Y) ^ 2 * (X : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by
      have h6 : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXN
      have h7 : (nodeDens N Y) ^ 2 * (N : ℝ) = nodeDens N Y * (Y : ℝ) := by
        unfold nodeDens
        field_simp
      nlinarith only [h6, h7, hrho0]
    have hρH : (nodeDens N Y) ^ 2 * (50 * (P.C : ℝ) * hN N Y)
        ≤ nodeDens N Y * (Y : ℝ) * (200 * (P.C : ℝ)) := by
      have h8 : (nodeDens N Y) ^ 2 * hN N Y = (nodeDens N Y * (Y : ℝ)) * (nodeDens N Y * Ll) := by
        rw [hhN]; ring
      have h9 : nodeDens N Y * (Y : ℝ) * (nodeDens N Y * Ll) ≤ nodeDens N Y * (Y : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left hρLl (by positivity)
      nlinarith only [h8, h9]
    have hnum : (2 : ℝ) ^ (-(P.C : ℝ)) * (1 + 200 * (P.C : ℝ)) ≤ 1 / 8 := by
      have hC40 : 40 ≤ P.C := by
        by_contra hcon
        push_neg at hcon
        have hconR : (P.C : ℝ) < 40 := by exact_mod_cast hcon
        linarith only [hconR, hC8]
      have h10 := two_rpow_neg_sixty P.C hC40
      have h11 : (1 + 200 * (P.C : ℝ)) ≤ 60 * (P.C : ℝ) ^ 2 := by nlinarith only [hC8, sq_nonneg ((P.C : ℝ) - 4)]
      have h12 : (0 : ℝ) < (2 : ℝ) ^ (-(P.C : ℝ)) := by positivity
      nlinarith only [h10, h11, h12]
    have h13 : (nodeDens N Y) ^ 2 * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y)
        ≤ nodeDens N Y * (Y : ℝ) * (1 + 200 * (P.C : ℝ)) := by
      have h14 : (nodeDens N Y) ^ 2 * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y)
          = (nodeDens N Y) ^ 2 * (X : ℝ)
            + (nodeDens N Y) ^ 2 * (50 * (P.C : ℝ) * hN N Y) := by ring
      rw [h14]
      nlinarith only [hρX, hρH]
    have h15 : (2 : ℝ) ^ (-(P.C : ℝ))
        * ((nodeDens N Y) ^ 2 * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y))
        ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y * (Y : ℝ) * (1 + 200 * (P.C : ℝ))) :=
      mul_le_mul_of_nonneg_left h13 (by positivity)
    have h16 : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y * (Y : ℝ) * (1 + 200 * (P.C : ℝ)))
        ≤ nodeDens N Y * (Y : ℝ) / 8 := by
      have h17 : (0 : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by positivity
      have h18 : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y * (Y : ℝ) * (1 + 200 * (P.C : ℝ)))
          = (nodeDens N Y * (Y : ℝ)) * ((2 : ℝ) ^ (-(P.C : ℝ)) * (1 + 200 * (P.C : ℝ))) := by
        ring
      rw [h18]
      nlinarith only [hnum, h17]
    have h19 : ((2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2)
        * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y)
        = (2 : ℝ) ^ (-(P.C : ℝ))
          * ((nodeDens N Y) ^ 2 * ((X : ℝ) + 50 * (P.C : ℝ) * hN N Y)) := by ring
    rw [h19] at h5
    linarith only [h1, h5, h15, h16]
  -- ## the pointwise cap bounds
  have hcapX : ∀ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ) ≤ P.Q N X Y s + b := by
    intro s _
    have h1 : (P.capX N X Y s : ℝ)
        ≤ ((⌈P.Q N X Y s + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      unfold HintParams.capX
      exact_mod_cast min_le_right Y _
    have h2 : (0 : ℝ) ≤ P.Q N X Y s + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
      have h3 : (0 : ℝ) ≤ P.Q N X Y s := Q_nonneg (P := P) hN1 s
      have h4 : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := Nat.cast_nonneg _
      positivity
    have h3 : ((⌈P.Q N X Y s + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < P.Q N X Y s + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one h2
    rw [hb]
    linarith only [h1, h3]
  have hcapY : ∀ s ∈ range (P.ell N X Y),
      (P.capY N X Y s : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s + b := by
    intro s _
    have h1 : (P.capY N X Y s : ℝ)
        ≤ ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      unfold HintParams.capY
      exact_mod_cast min_le_right Y _
    have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
        + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
      have h3 : (0 : ℝ) ≤ P.Q N X Y s := Q_nonneg (P := P) hN1 s
      have h4 : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := Nat.cast_nonneg _
      positivity
    have h3 : ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one h2
    rw [hb]
    linarith only [h1, h3]
  have hcapYle : ∀ s, (P.capY N X Y s : ℝ) ≤ (Y : ℝ) := by
    intro s
    have h1 : P.capY N X Y s ≤ Y := by
      unfold HintParams.capY
      exact min_le_left _ _
    exact_mod_cast h1
  -- every child capacity plus the margin still sits below `Y` (paper: `2^{-c}Q_s + b ≤ ρY/4 ≤ Y`)
  have hell1 : (1 : ℝ) ≤ (P.ell N X Y : ℝ) := by
    have h1 : 1 ≤ P.ell N X Y := by
      unfold HintParams.ell
      omega
    exact_mod_cast h1
  have hsmall : ∀ s ∈ range (P.ell N X Y),
      ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s + b ≤ (Y : ℝ) := by
    intro s hs
    have h1 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
        ≤ ∑ t ∈ range (P.ell N X Y), ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y t := by
      apply Finset.single_le_sum (f := fun t => ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y t)
      · intro t _
        have h3 : (0 : ℝ) ≤ P.Q N X Y t := Q_nonneg (P := P) hN1 t
        positivity
      · exact hs
    have h2 : b ≤ T := by
      have h3 : b ≤ (P.ell N X Y : ℝ) * b := by
        calc b = 1 * b := by ring
          _ ≤ (P.ell N X Y : ℝ) * b := mul_le_mul_of_nonneg_right hell1 hb0
      linarith only [h3, hlb]
    have h4 : nodeDens N Y * (Y : ℝ) / 4 ≤ (Y : ℝ) := by
      have h5 : nodeDens N Y * (Y : ℝ) ≤ 1 * (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hrho1 hY0
      linarith only [h5]
    linarith only [h1, hout, h2, hT1, h4]
  -- ## Part 1: `Σ_s X_s ≤ X + O(C h_N(Y))` (paper `eq:hint-rounded-sums`, first claim)
  have hpart1_250 : ∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ)
      ≤ (X : ℝ) + 250 * ((P.C : ℝ) * hN N Y) := by
    have h1 : ∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ)
        ≤ ∑ s ∈ range (P.ell N X Y), (P.Q N X Y s + b) := Finset.sum_le_sum hcapX
    have h2 : ∑ s ∈ range (P.ell N X Y), (P.Q N X Y s + b)
        = (∑ s ∈ range (P.ell N X Y), P.Q N X Y s) + (P.ell N X Y : ℝ) * b := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h3 := Q_sum_le_sharp P hargs hrows hY1 hrule hC1
    have h5 : 50 * (P.C : ℝ) * hN N Y + (P.ell N X Y : ℝ) * b ≤ 250 * ((P.C : ℝ) * hN N Y) := by
      nlinarith only [hlb, hT2, hCpos, hhN0]
    linarith only [h1, h2.le, h2.ge, h3, h5]
  have hpart1 : ∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ)
      ≤ (X : ℝ) + K * ((P.C : ℝ) * hN N Y) := by
    refine le_trans hpart1_250 ?_
    have h7 : (0 : ℝ) ≤ (P.C : ℝ) * hN N Y := by positivity
    nlinarith only [h7, hK250]
  -- ## Part 2: `Σ_s h_Y(Y_s) ≤ h_N(Y)/4` (paper `eq:hint-rounded-sums`, second claim)
  -- `b ≤ Y`: the margin is dominated by the child capacity (paper: `2^{-c}Q_s + b ≤ ρY/4 ≤ Y`)
  have hbY : b ≤ (Y : ℝ) := by
    have hell1n : 1 ≤ P.ell N X Y := by exact_mod_cast hell1
    have hs0 : (0 : ℕ) ∈ Finset.range (P.ell N X Y) := by
      rw [Finset.mem_range]
      omega
    have h1 := hsmall 0 hs0
    have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y 0 := by
      have h3 : (0 : ℝ) ≤ P.Q N X Y 0 := Q_nonneg (P := P) hN1 0
      positivity
    linarith only [h1, h2]
  have hNb : hN Y b ≤ 3 * P.lgn * b := by
    have hbpos : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb1
    have h1 : hN Y b = b * lg (Real.exp 1 * (Y : ℝ) / b) :=
      hN_eq_quot (N := Y) (z := b) (ne_of_gt hYposR) hbpos
    have hexpY : (0 : ℝ) < Real.exp 1 * (Y : ℝ) := mul_pos (Real.exp_pos 1) hYposR
    have h2 : Real.exp 1 * (Y : ℝ) / b ≤ Real.exp 1 * (Y : ℝ) := by
      rw [div_le_iff₀ hbpos]
      calc Real.exp 1 * (Y : ℝ) = Real.exp 1 * (Y : ℝ) * 1 := by ring
        _ ≤ Real.exp 1 * (Y : ℝ) * b := mul_le_mul_of_nonneg_left hb1 hexpY.le
    have h3 : (1 : ℝ) ≤ Real.exp 1 * (Y : ℝ) / b := by
      rw [le_div_iff₀ hbpos]
      calc (1 : ℝ) * b = b := by ring
        _ ≤ (Y : ℝ) := hbY
        _ ≤ Real.exp 1 * (Y : ℝ) := by
            have h := mul_le_mul_of_nonneg_right one_le_exp_one hY0
            linarith only [h]
    have hx : (0 : ℝ) ≤ Real.exp 1 * (Y : ℝ) / b := div_nonneg (by positivity) hb0
    have hy : (1 : ℝ) ≤ Real.exp 1 * (Y : ℝ) := by
      have h := mul_le_mul one_le_exp_one hY1R zero_le_one (le_of_lt (Real.exp_pos 1))
      simpa using h
    have h4 : lg (Real.exp 1 * (Y : ℝ) / b) ≤ lg (Real.exp 1 * (Y : ℝ)) :=
      lg_le_lg_of_le hx hy h2
    have h5 : lg (Real.exp 1 * (Y : ℝ)) = lg (Real.exp 1) + lg (Y : ℝ) :=
      lg_mul_pos (by positivity) (by positivity)
    have h6 : lg (Y : ℝ) ≤ P.lgn := by
      have h7 : lg (Y : ℝ) ≤ lg (N : ℝ) :=
        lg_le_lg_of_le hY0 (by exact_mod_cast hN1) (by exact_mod_cast hYN)
      have h8 : lg (N : ℝ) ≤ lg (P.n : ℝ) :=
        lg_le_lg_of_le (by positivity)
          (by exact_mod_cast (le_trans hN1 hNn) : (1 : ℝ) ≤ (P.n : ℝ)) (by exact_mod_cast hNn)
      have h9 : P.lgn = lg (P.n : ℝ) := rfl
      linarith only [h7, h8, h9]
    have h7 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
    have h8 : b * lg (Real.exp 1 * (Y : ℝ) / b) ≤ b * (lg (Real.exp 1) + lg (Y : ℝ)) := by
      rw [← h5]
      exact mul_le_mul_of_nonneg_left h4 hb0
    nlinarith only [h1, h8, h6, h7, hb0, hL2]
  have hpart2 : ∑ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s) ≤ hN N Y / 4 := by
    have h1 : ∀ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s)
        ≤ hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) + hN Y b := by
      intro s hs
      have hnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s := by
        have h3 : (0 : ℝ) ≤ P.Q N X Y s := Q_nonneg (P := P) hN1 s
        positivity
      have hmono := hN_mono (N := Y) (u := (P.capY N X Y s : ℝ))
        (v := ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s + b)
        (Nat.cast_nonneg _) (hcapY s hs) (hsmall s hs)
      have hadd := hN_add_le (N := Y) hnn hb0 (hsmall s hs)
      linarith only [hmono, hadd]
    have h2 : ∑ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s)
        ≤ (∑ s ∈ range (P.ell N X Y),
            hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)) + (P.ell N X Y : ℝ) * hN Y b := by
      have h3 := Finset.sum_le_sum h1
      have h4 : ∑ s ∈ range (P.ell N X Y),
          (hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) + hN Y b)
          = (∑ s ∈ range (P.ell N X Y),
              hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s)) + (P.ell N X Y : ℝ) * hN Y b := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith only [h3, h4.le, h4.ge]
    have h5 : (P.ell N X Y : ℝ) * hN Y b ≤ hN N Y / 8 := by
      have h6 : (P.ell N X Y : ℝ) * hN Y b ≤ (P.ell N X Y : ℝ) * (3 * P.lgn * b) :=
        mul_le_mul_of_nonneg_left hNb hell0
      have h7 : (P.ell N X Y : ℝ) * (3 * P.lgn * b) = 3 * P.lgn * ((P.ell N X Y : ℝ) * b) := by ring
      have h8 : 3 * P.lgn * ((P.ell N X Y : ℝ) * b) ≤ 3 * P.lgn * T :=
        mul_le_mul_of_nonneg_left hlb (by linarith)
      linarith only [h6, h7.le, h7.ge, h8, hT3]
    linarith only [h2, h5, h58]
  -- ## Part 3: `Σ_s ρ_s ≤ ρ/4` (paper `eq:hint-rounded-sums`, third claim)
  have hpart3 : ∑ s ∈ range (P.ell N X Y), ((P.capY N X Y s : ℝ) / (Y : ℝ))
      ≤ ((Y : ℝ) / (N : ℝ)) / 4 := by
    have h1 : ∑ s ∈ range (P.ell N X Y), ((P.capY N X Y s : ℝ) / (Y : ℝ))
        = (∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)) / (Y : ℝ) := by
      rw [Finset.sum_div]
    have hC40nat : 40 ≤ P.C := by
      by_contra hcon
      push_neg at hcon
      have hconR : (P.C : ℝ) < 40 := by exact_mod_cast hcon
      linarith only [hconR, hC8]
    have h2 := capY_sum_le (P := P) hargs hL2 hA100 hC40nat hrule
    have h3 : (∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)) * (1 / (Y : ℝ))
        ≤ (nodeDens N Y * (Y : ℝ) / 4) * (1 / (Y : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (nodeDens N Y * (Y : ℝ) / 4) * (1 / (Y : ℝ)) = nodeDens N Y / 4 := by
      field_simp
    have h5 : (∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)) * (1 / (Y : ℝ))
        = (∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)) / (Y : ℝ) := by ring
    have h6 : nodeDens N Y / 4 = ((Y : ℝ) / (N : ℝ)) / 4 := by
      unfold nodeDens
      ring
    rw [h1, ← h6, ← h5]
    linarith only [h3, h4.le, h4.ge]
  refine ⟨hpart1, hpart2, hpart3, ?_⟩
  -- ## Part 4: the mixed per-rule budget `eq:hint-local-cost`
  set I : Finset ℕ := range (P.ell N X Y) with hI
  set frec : Finset ℕ := I.filter (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .recursive)
    with hfrec
  set fdir : Finset ℕ := I.filter (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .direct)
    with hfdir
  set fcheap : Finset ℕ := I.filter (fun s => P.rule Y (P.capX N X Y s) (P.capY N X Y s) = .cheap)
    with hfcheap
  have hsub_rec : frec ⊆ I := by rw [hfrec]; exact Finset.filter_subset _ _
  have hsub_cheap : fcheap ⊆ I := by rw [hfcheap]; exact Finset.filter_subset _ _
  have hIcard : I.card = P.ell N X Y := by rw [hI]; simp
  -- the cheap leaves: `D_s ≤ Y/log¹⁰ n`, so the CR sketch costs only `O(Y/log⁸ n)` (as in the paper)
  have hcheapD : ∀ s ∈ fcheap,
      (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s) : ℝ) ≤ (Y : ℝ) / P.lgn ^ 10 := by
    intro s hs
    rw [hfcheap] at hs
    simp only [Finset.mem_filter] at hs
    exact rule_cheap_D (P := P) (N := Y) (X := P.capX N X Y s) (Y := P.capY N X Y s) hs.2
  have hcheapLen : ∀ s ∈ fcheap,
      (CR.rows Y (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s)) : ℝ)
        ≤ |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2) := by
    intro s hs
    exact cheap_child_len P CR hCR hn2 hN1 hNn hYN hY2 (hcheapD s hs)
  have hcheap_sum : ∑ s ∈ fcheap,
      (CR.rows Y (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s)) : ℝ)
      ≤ (P.C : ℝ) ^ 2 * hN N Y / 8 := by
    have h0 : (0 : ℝ) ≤ |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2) := by positivity
    have h1 : ∑ s ∈ fcheap,
        (CR.rows Y (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s)) : ℝ)
        ≤ ∑ s ∈ fcheap, |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2) :=
      Finset.sum_le_sum hcheapLen
    have h2 : ∑ s ∈ fcheap, |KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2)
        = (fcheap.card : ℝ) * (|KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (fcheap.card : ℝ) ≤ (P.ell N X Y : ℝ) := by
      have h4 : fcheap.card ≤ I.card := Finset.card_le_card hsub_cheap
      have h5 : (fcheap.card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast h4
      rwa [hIcard] at h5
    have h6 : (fcheap.card : ℝ) * (|KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2))
        ≤ (21 * (P.C : ℝ) * P.lgn ^ 3) * (|KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_right (le_trans h3 hellC) h0
    -- `84 |KCR| C Y ≤ C² h_N`
    have h672 : 672 * |KCR| ≤ (P.C : ℝ) := by nlinarith only [hKC2]
    have h7 : (21 * (P.C : ℝ) * P.lgn ^ 3) * (|KCR| * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2))
        ≤ (P.C : ℝ) ^ 2 * hN N Y / 8 := by
      have h9 : (P.lgn + 1) ^ 2 ≤ 4 * P.lgn ^ 2 := by nlinarith only [hL1, hlgn]
      have hp10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
      have key : (21 * (P.C : ℝ) * P.lgn ^ 3) * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2)
          ≤ 84 * (P.C : ℝ) * (Y : ℝ) := by
        have h11 : (21 * (P.C : ℝ) * P.lgn ^ 3) * (((Y : ℝ) / P.lgn ^ 10) * (P.lgn + 1) ^ 2)
            ≤ (21 * (P.C : ℝ) * P.lgn ^ 3) * (((Y : ℝ) / P.lgn ^ 10) * (4 * P.lgn ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h9 (by positivity)
        have h12 : (21 * (P.C : ℝ) * P.lgn ^ 3) * (((Y : ℝ) / P.lgn ^ 10) * (4 * P.lgn ^ 2))
            ≤ 84 * (P.C : ℝ) * (Y : ℝ) := by
          have hp10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
          have hmono : (21 * (P.C : ℝ) * P.lgn ^ 3) * (((Y : ℝ) / P.lgn ^ 10) * (4 * P.lgn ^ 2))
              = 84 * (P.C : ℝ) * (Y : ℝ) * ((P.lgn ^ 3 * P.lgn ^ 2) / P.lgn ^ 10) := by ring
          rw [hmono]
          have hrat : (P.lgn ^ 3 * P.lgn ^ 2) / P.lgn ^ 10 ≤ 1 := by
            rw [div_le_one hp10]
            calc P.lgn ^ 3 * P.lgn ^ 2 = P.lgn ^ 5 := by rw [← pow_add]
              _ ≤ P.lgn ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
          have hCY : (0 : ℝ) ≤ 84 * (P.C : ℝ) * (Y : ℝ) := by positivity
          have hmul := mul_le_mul_of_nonneg_left hrat hCY
          linarith only [hmul]
        linarith only [h11, h12]
      have h13 : |KCR| * (84 * (P.C : ℝ) * (Y : ℝ)) ≤ (P.C : ℝ) ^ 2 * hN N Y / 8 := by
        have h14 : 672 * |KCR| * (Y : ℝ) ≤ (P.C : ℝ) * hN N Y := by
          have ha : 672 * |KCR| * (Y : ℝ) ≤ (P.C : ℝ) * (Y : ℝ) := by
            apply mul_le_mul_of_nonneg_right h672 hY0
          have hb : (P.C : ℝ) * (Y : ℝ) ≤ (P.C : ℝ) * hN N Y :=
            mul_le_mul_of_nonneg_left hYlN (le_of_lt hCpos)
          linarith only [ha, hb]
        nlinarith only [h14, hY0, hCpos, hhN0, abs_nonneg KCR]
      have h15 : (0 : ℝ) ≤ |KCR| := abs_nonneg KCR
      nlinarith only [key, h13, h15, hY0, hCpos]
    linarith only [h1, h2.le, h2.ge, h6, h7]
  -- the recursive and direct children are charged by the first two claims
  have hcapYleI : ∀ s ∈ I, (0 : ℝ) ≤ hN Y (P.capY N X Y s) := by
    intro s _
    exact hN_nonneg (Nat.cast_nonneg _) (hcapYle s)
  have hcX : ∑ s ∈ frec, (P.capX N X Y s : ℝ) + ∑ s ∈ fdir, (P.capX N X Y s : ℝ)
      ≤ ∑ s ∈ I, (P.capX N X Y s : ℝ) := by
    have hdisj : Disjoint frec fdir := by
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      rw [hfrec] at hs1
      rw [hfdir] at hs2
      simp only [Finset.mem_filter] at hs1 hs2
      rw [hs1.2] at hs2
      exact absurd hs2.2 (by decide)
    rw [← Finset.sum_union hdisj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [hfrec, hfdir]
      exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro x _ _; exact Nat.cast_nonneg _
  have hch : ∑ s ∈ frec, hN Y (P.capY N X Y s) ≤ ∑ s ∈ I, hN Y (P.capY N X Y s) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_rec (fun x hx _ => hcapYleI x hx)
  have hI1 : ∑ s ∈ I, (P.capX N X Y s : ℝ) = ∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ) := by
    rw [hI]
  have hI2 : ∑ s ∈ I, hN Y (P.capY N X Y s) = ∑ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s) := by
    rw [hI]
  have hfinal : ∑ s ∈ frec, ((P.capX N X Y s : ℝ) + (P.C : ℝ) ^ 2 * hN Y (P.capY N X Y s))
      + ∑ s ∈ fdir, (P.capX N X Y s : ℝ) + ∑ s ∈ fcheap,
        (CR.rows Y (HintParams.D Y (P.capX N X Y s) (P.capY N X Y s)) : ℝ)
      ≤ (X : ℝ) + (P.C : ℝ) ^ 2 * hN N Y := by
    have hsplit : ∑ s ∈ frec, ((P.capX N X Y s : ℝ) + (P.C : ℝ) ^ 2 * hN Y (P.capY N X Y s))
        = (∑ s ∈ frec, (P.capX N X Y s : ℝ))
          + (P.C : ℝ) ^ 2 * (∑ s ∈ frec, hN Y (P.capY N X Y s)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : (P.C : ℝ) ^ 2 * (∑ s ∈ frec, hN Y (P.capY N X Y s))
        ≤ (P.C : ℝ) ^ 2 * (hN N Y / 4) := by
      have h2 : (0 : ℝ) ≤ (P.C : ℝ) ^ 2 := by positivity
      have h3 : ∑ s ∈ I, hN Y (P.capY N X Y s) ≤ hN N Y / 4 := by
        rw [hI2]; exact hpart2
      exact mul_le_mul_of_nonneg_left (le_trans hch h3) h2
    have h4 : 250 * (P.C : ℝ) * hN N Y + (P.C : ℝ) ^ 2 * (hN N Y / 4)
        + (P.C : ℝ) ^ 2 * hN N Y / 8 ≤ (P.C : ℝ) ^ 2 * hN N Y := by
      have h5 : 250 * (P.C : ℝ) ≤ (P.C : ℝ) ^ 2 / 8 := by
        have h1 : (2000 : ℝ) ≤ (P.C : ℝ) := by linarith only [hC8]
        have h2 : (0 : ℝ) ≤ (P.C : ℝ) := le_of_lt hCpos
        have h3 := mul_le_mul_of_nonneg_right h1 h2
        nlinarith only [h3]
      have h6 : (0 : ℝ) ≤ hN N Y := hhN0
      have h7 := mul_le_mul_of_nonneg_right h5 h6
      have h8 : (0 : ℝ) ≤ (P.C : ℝ) ^ 2 * hN N Y := by positivity
      nlinarith only [h7, h8]
    have h7 : ∑ s ∈ I, (P.capX N X Y s : ℝ) ≤ (X : ℝ) + 250 * (P.C : ℝ) * hN N Y := by
      rw [hI1]
      calc ∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ)
          ≤ (X : ℝ) + 250 * ((P.C : ℝ) * hN N Y) := hpart1_250
        _ = (X : ℝ) + 250 * (P.C : ℝ) * hN N Y := by ring
    have h11 : (0 : ℝ) ≤ hN N Y := hhN0
    linarith only [hsplit.le, hsplit.ge, hcX, h1, hcheap_sum, h7, h4, hCpos, h11]
  exact hfinal
end

/-! ### Step 6: the statement of Lemma 5.9 -/

open Classical in
/-- Lemma 5.9 (Child space and density contraction), PDF p.24 (printed p.23). The hidden constant `K`
of `O(C h_N(Y))` precedes `A` and `C`. `Len_CR(s)` is the actual length of the child's CR sketch for
a CR family with the row bound of Proposition 2.3. -/
theorem lemma_5_9 (KCR : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ) (CR : CRFamily),
      (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      let I := range (P.ell N X Y)
      let Xs := P.capX N X Y
      let Ys := P.capY N X Y
      (∑ s ∈ I, (Xs s : ℝ) ≤ (X : ℝ) + K * ((C : ℝ) * hN N Y)) ∧
      (∑ s ∈ I, hN Y (Ys s) ≤ hN N Y / 4) ∧
      (∑ s ∈ I, ((Ys s : ℝ) / (Y : ℝ)) ≤ ((Y : ℝ) / (N : ℝ)) / 4) ∧
      (∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .recursive),
            ((Xs s : ℝ) + (C : ℝ) ^ 2 * hN Y (Ys s)) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .direct), (Xs s : ℝ) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .cheap),
            (CR.rows Y (HintParams.D Y (Xs s) (Ys s)) : ℝ) ≤
        (X : ℝ) + (C : ℝ) ^ 2 * hN N Y) := by
  classical
  -- the platform's Lemma 5.8 has opaque `A₀, C₀`: absorb them before choosing ours
  obtain ⟨A₀₅₈, hA₅₈⟩ := lemma_5_8
  refine ⟨10 ^ 7 * |KCR| + 10 ^ 7, by positivity, max A₀₅₈ 100, ?_⟩
  intro A hA
  obtain ⟨C₀₅₈, hC₅₈⟩ := hA₅₈ A (le_trans (le_max_left _ _) hA)
  have hA100 : 100 ≤ A := le_trans (le_max_right _ _) hA
  refine ⟨max C₀₅₈ (⌈10 ^ 8 * |KCR|⌉₊ + 10 ^ 8 + A), ?_⟩
  intro C hC
  have hC₅₈' : C₀₅₈ ≤ C := le_trans (le_max_left _ _) hC
  have hCbig : ⌈10 ^ 8 * |KCR|⌉₊ + 10 ^ 8 + A ≤ C := le_trans (le_max_right _ _) hC
  have hC8n : 10 ^ 8 ≤ C := by omega
  have hC8 : (10 ^ 8 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC8n
  have habs : |KCR| * 10 ^ 7 ≤ (⌈10 ^ 8 * |KCR|⌉₊ : ℝ) := by
    have h1 : (10 : ℝ) ^ 8 * |KCR| ≤ (⌈10 ^ 8 * |KCR|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : |KCR| * 10 ^ 7 ≤ (10 : ℝ) ^ 8 * |KCR| := by nlinarith [abs_nonneg KCR]
    linarith [h1, h2]
  have hKle : 10 ^ 7 * |KCR| + 10 ^ 7 ≤ (C : ℝ) := by
    have hCbigR : (⌈10 ^ 8 * |KCR|⌉₊ : ℝ) + (10 : ℝ) ^ 8 + (A : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast hCbig
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
    have h78 : (10 : ℝ) ^ 7 ≤ (10 : ℝ) ^ 8 := by norm_num
    linarith [habs, hCbigR, hA0, h78]
  have hK250 : (250 : ℝ) ≤ 10 ^ 7 * |KCR| + 10 ^ 7 := by
    have h1 : (0 : ℝ) ≤ |KCR| := abs_nonneg KCR
    push_cast
    nlinarith
  have hKC2 : 4000 * |KCR| ≤ (C : ℝ) := by
    have h1 : (0 : ℝ) ≤ |KCR| := abs_nonneg KCR
    nlinarith [habs]
  intro n lam N X Y CR hCR P hargs hrule
  dsimp only
  exact child_bounds P (10 ^ 7 * |KCR| + 10 ^ 7) CR hargs hrule hCR hA100 hC8 hK250 hKle hKC2
    (hC₅₈ C hC₅₈' n lam N X Y hargs hrule)

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 5.9 — submission wrapper matching the target statement. -/
theorem solution (KCR : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ) (CR : CRFamily),
      (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      let I := range (P.ell N X Y)
      let Xs := P.capX N X Y
      let Ys := P.capY N X Y
      (∑ s ∈ I, (Xs s : ℝ) ≤ (X : ℝ) + K * ((C : ℝ) * hN N Y)) ∧
      (∑ s ∈ I, hN Y (Ys s) ≤ hN N Y / 4) ∧
      (∑ s ∈ I, ((Ys s : ℝ) / (Y : ℝ)) ≤ ((Y : ℝ) / (N : ℝ)) / 4) ∧
      (∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .recursive),
            ((Xs s : ℝ) + (C : ℝ) ^ 2 * hN Y (Ys s)) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .direct), (Xs s : ℝ) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .cheap),
            (CR.rows Y (HintParams.D Y (Xs s) (Ys s)) : ℝ) ≤
        (X : ℝ) + (C : ℝ) ^ 2 * hN N Y) :=
  LinearSetReconciliation327.Main.lemma_5_9 KCR



