-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-16T16:22:22.147033+00:00
-- url     : https://prove2.me/submissions/69f62d23-5f49-402b-bf26-cc40e2cc1dbb

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_3
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_8

set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

set_option maxHeartbeats 2000000

/-!
## Lemma 5.6: sufficient child capacities

This file is the submission form of Lemma 5.6.  The platform environment contains only `Mathlib`,
the `Definitions.Def_*` modules and the `Theorems.Thm_*` milestones, so the shared toolkit that used
to live in `Solutions.Sol_5_6_infra` and the row-prediction theory of Lemma 5.2 are reproduced here
(they are also the content of the platform's Lemma 5.2 module, which cannot be imported together with
Lemma 5.3 because the two milestones contain the same helper declarations).
-/


/-! ## Shared analytic and probabilistic toolkit for the HintSketch milestones -/

/-! ### Elementary analytic toolkit -/

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

/-! ### Expectation over the uniform law -/

lemma expU_mono_card {α : Type} [Fintype α] (hα : 0 < Fintype.card α) {f g : α → ℝ}
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

lemma expU_finset_sum {α ι : Type} [Fintype α] (hα : 0 < Fintype.card α)
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
      push_cast
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
lemma rowImage_card_le_rowLen_infra {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
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
      have hzero : ∑ h ∈ range (r + 1), (Nj - jCard).choose h
          = ∑ h ∈ range (Nj - jCard + 1), (Nj - jCard).choose h := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx1 hx2
        simp only [mem_range] at hx1 hx2
        exact Nat.choose_eq_zero_of_lt (by omega)
      rw [hzero, Nat.sum_range_choose]
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
    calc ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)
        ≤ ((2 ^ Nj : ℕ) : ℝ) := by exact_mod_cast hmain
      _ = (2 : ℝ) ^ Nj := by rw [Nat.cast_pow]; norm_num
      _ = (2 : ℝ) ^ ((Nj : ℕ) : ℝ) := by rw [Real.rpow_natCast]
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
    (rowImage_card_le_rowLen_infra π _)
  unfold HintParams.sigmaStar
  dsimp only
  exact_mod_cast h

/-! ### The profile `Q` and its first moment -/

/-- The pointwise profile whose expectation is `Q_s`. -/
def nodeProfile (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (s : ℕ) : ℝ :=
  ∑ j ∈ range (P.rows X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))

lemma Q_eq_expU (P : HintParams) (N X Y s : ℕ) :
    P.Q N X Y s = expU (fun π => nodeProfile P N X Y π s) := rfl

/-- Splitting a summand into a term plus a constant. -/
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
        refine expU_mono_card hcard (fun π => ?_)
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
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
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
        refine expU_mono_card hcard (fun π => ?_)
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

/-- Exponential beats linear: `4096 A + 409600 ≤ 2^(A-30)` for `A ≥ 100`. -/
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




/-! ## Generic probability helpers -/

lemma prU_congr' {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  classical
  have hf : Finset.univ.filter P = Finset.univ.filter Q := by
    ext a; simp [h a]
  unfold prU
  rw [hf]

lemma prU_mono' {α : Type} [Fintype α] [Nonempty α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    prU P ≤ prU Q := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hsub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  have hcard : ((Finset.univ.filter P).card : ℝ) ≤ ((Finset.univ.filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  unfold prU
  exact (div_le_div_iff_of_pos_right hpos).mpr hcard

lemma prU_le_one {α : Type} [Fintype α] (P : α → Prop) : prU P ≤ 1 := by
  classical
  unfold prU
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · have hisempty : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    have h0 : (Finset.univ.filter P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact fun x _ => hisempty.false x
    rw [h0]; simp
  · have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ _

lemma prU_le_sum' {α ι : Type} [Fintype α] [Nonempty α] (P : α → Prop)
    (s : Finset ι) (Q : ι → α → Prop) (h : ∀ a, P a → ∃ i ∈ s, Q i a) :
    prU P ≤ ∑ i ∈ s, prU (Q i) := by
  classical
  have hsub : Finset.univ.filter P ⊆ s.biUnion (fun i => Finset.univ.filter (Q i)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨i, hi, hia⟩ := h a ha
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [hia]⟩
  have hcard : (Finset.univ.filter P).card ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := by
    calc (Finset.univ.filter P).card
        ≤ (s.biUnion (fun i => Finset.univ.filter (Q i))).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
  have hcardR : ((Finset.univ.filter P).card : ℝ)
      ≤ ∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ) := by
    exact_mod_cast hcard
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hterm : ∀ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ)
      = prU (Q i) := by
    intro i _; unfold prU; rfl
  unfold prU
  calc ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)
      ≤ (∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ)) / (Fintype.card α : ℝ) := by
        apply (div_le_div_iff_of_pos_right hpos).mpr
        exact hcardR
    _ = ∑ i ∈ s, (((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ)) := by
        rw [Finset.sum_div]
    _ = ∑ i ∈ s, prU (Q i) := Finset.sum_congr rfl hterm

/-- **Zero-fibre of a surjective linear map.** For a surjective `𝔽₂`-linear map the preimage of `0`
carries probability `1/|W|`. -/
lemma prU_ker_eq' {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (ψ : V →ₗ[ZMod 2] W) (hsurj : Function.Surjective ψ) :
    prU (fun x => ψ x = 0) = (Fintype.card W : ℝ)⁻¹ := by
  classical
  have hker : Nat.card (LinearMap.ker ψ)
      = (Finset.univ.filter (fun x : V => ψ x = 0)).card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
    try simp [LinearMap.mem_ker]
  have hquot : Nat.card (V ⧸ LinearMap.ker ψ) = Fintype.card W := by
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv]
    rw [LinearMap.range_eq_top.mpr hsurj]
    rw [Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  have hmain : Nat.card V = (Finset.univ.filter (fun x : V => ψ x = 0)).card * Fintype.card W := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ψ), hker, hquot]
  have hcast : (Fintype.card V : ℝ)
      = ((Finset.univ.filter (fun x : V => ψ x = 0)).card : ℝ) * (Fintype.card W : ℝ) := by
    have h := hmain
    rw [Nat.card_eq_fintype_card] at h
    rw [h]
    push_cast
    ring
  have hne : ((Finset.univ.filter (fun x : V => ψ x = 0)).card : ℝ) ≠ 0 := by
    have hmem : (0 : V) ∈ Finset.univ.filter (fun x : V => ψ x = 0) := by simp
    have hpos : 0 < (Finset.univ.filter (fun x : V => ψ x = 0)).card :=
      Finset.card_pos.mpr ⟨0, hmem⟩
    exact_mod_cast hpos.ne'
  have hW : (Fintype.card W : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast hpos.ne'
  unfold prU
  rw [hcast]
  field_simp

/-! ## `rowBit` basics -/

lemma rowBit_symmDiff {ℓ K : ℕ} (β : Fin ℓ → Fin K → ZMod 2) (C C' : Finset ℕ) (s : Fin ℓ) :
    HintParams.rowBit β (symmDiff C C') s
      = HintParams.rowBit β C s + HintParams.rowBit β C' s :=
  sum_symmDiff_char_two (fun a : ZMod 2 => CharTwo.add_self_eq_zero a) C C'
    (fun v => if h : v < K then β s ⟨v, h⟩ else 0)

lemma rowBit_add {ℓ K : ℕ} (β β' : Fin ℓ → Fin K → ZMod 2) (C : Finset ℕ) (s : Fin ℓ) :
    HintParams.rowBit (β + β') C s
      = HintParams.rowBit β C s + HintParams.rowBit β' C s := by
  rw [HintParams.rowBit, HintParams.rowBit, HintParams.rowBit]
  have hfun : (fun v => if h : v < K then (β + β') s ⟨v, h⟩ else 0)
      = fun v => (if h : v < K then β s ⟨v, h⟩ else 0)
          + (if h : v < K then β' s ⟨v, h⟩ else 0) := by
    funext v
    by_cases hv : v < K <;> simp [hv, Pi.add_apply]
  rw [hfun, Finset.sum_add_distrib]

lemma rowBit_smul {ℓ K : ℕ} (c : ZMod 2) (β : Fin ℓ → Fin K → ZMod 2) (C : Finset ℕ)
    (s : Fin ℓ) :
    HintParams.rowBit (c • β) C s = c * HintParams.rowBit β C s := by
  rw [HintParams.rowBit, HintParams.rowBit, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : v < K
  · simp [hv, Pi.smul_apply, smul_eq_mul]
  · simp [hv]

/-! ## The single-candidate separation estimate -/

/-- For a fixed candidate support `C ≠ S`, the probability that the first `a` row measurements of `C`
and `S` agree is `2^{-a}`, provided both lie in `range Nj` with `Nj ≤ K`. -/
theorem prU_prefix_eq {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {C S : Finset ℕ} (hC : C ⊆ range Nj) (hS : S ⊆ range Nj) (hCS : C ≠ S) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∀ i : Fin a, HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      = ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  set D : Finset ℕ := symmDiff C S with hD
  have hDsub : D ⊆ range Nj := by
    intro x hx
    rw [hD, Finset.mem_symmDiff] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hC h1
    · exact hS h1
  have hDne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hCS
    have h1 : ∀ x, x ∈ C ↔ x ∈ S := by
      intro x
      constructor
      · intro hx
        by_contra hxs
        have hmem : x ∈ D := by rw [hD, Finset.mem_symmDiff]; exact Or.inl ⟨hx, hxs⟩
        rw [h] at hmem; exact Finset.notMem_empty x hmem
      · intro hx
        by_contra hxc
        have hmem : x ∈ D := by rw [hD, Finset.mem_symmDiff]; exact Or.inr ⟨hx, hxc⟩
        rw [h] at hmem; exact Finset.notMem_empty x hmem
    ext x; exact h1 x
  obtain ⟨v₀, hv₀⟩ := hDne
  have hv₀K : v₀ < K := Nat.lt_of_lt_of_le (Finset.mem_range.mp (hDsub hv₀)) hNjK
  -- the linear map
  set Φ : (Fin ℓ → Fin K → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    { toFun := fun β i => HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
      map_add' := by
        intro x y
        ext i
        exact rowBit_add x y D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
      map_smul' := by
        intro c x
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact rowBit_smul c x D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ } with hΦ
  have hsurj : Function.Surjective Φ := by
    intro w
    refine ⟨fun s w' => if (w' : ℕ) = v₀ then (if h : s.val < a then w ⟨s.val, h⟩ else 0) else 0,
      ?_⟩
    ext i
    have hi : i.val < a := i.isLt
    simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [HintParams.rowBit, Finset.sum_eq_single v₀]
    · simp [hi, hv₀K]
    · intro b hbD hbne
      have hbK : b < K := Nat.lt_of_lt_of_le (Finset.mem_range.mp (hDsub hbD)) hNjK
      simp [hbK, hbne]
    · intro hnot
      exact absurd hv₀ hnot
  have hiff : ∀ β : Fin ℓ → Fin K → ZMod 2, (Φ β = 0) ↔
      (∀ i : Fin a, HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
        = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := by
    intro β
    constructor
    · intro h i
      have h1 := congr_fun h i
      simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
      have h2 : HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [hD]; exact rowBit_symmDiff β C S _
      rw [h2] at h1
      have hy : HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ = 0 :=
        CharTwo.add_self_eq_zero _
      have hh : HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [h1, hy]
      exact add_right_cancel hh
    · intro h
      funext i
      simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      have h2 : HintParams.rowBit β D ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            + HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
        rw [hD]; exact rowBit_symmDiff β C S _
      rw [h2, h i]
      exact CharTwo.add_self_eq_zero _
  rw [prU_congr' (fun β => (hiff β).symm)]
  rw [prU_ker_eq' Φ hsurj]
  have hcard : Fintype.card (Fin a → ZMod 2) = 2 ^ a := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hcard, Nat.cast_pow, ← Real.rpow_natCast]
  norm_num

/-! ## Union bound over the candidate family -/

/-- If `C ≠ S`, the first `a` row measurements of `C` and `S` agree with probability `2^{-a}`; a union
bound over the candidate family `Ah` gives the failure probability. -/
theorem prU_exists_prefix_eq {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {S : Finset ℕ} (hS : S ⊆ range Nj) (Ah : Finset (Finset ℕ))
    (hAh : ∀ C ∈ Ah, C ⊆ range Nj) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      ≤ ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  haveI : Nonempty (Fin ℓ → Fin K → ZMod 2) := ⟨fun _ _ => 0⟩
  have hub := prU_le_sum'
    (P := fun β : Fin ℓ → Fin K → ZMod 2 =>
      ∃ C ∈ Ah.erase S, ∀ i : Fin a,
        HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
    (s := Ah.erase S)
    (Q := fun C β => ∀ i : Fin a,
        HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
    (fun _ hβ => hβ)
  calc prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩)
      ≤ ∑ C ∈ Ah.erase S, prU (fun β : Fin ℓ → Fin K → ZMod 2 => ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := hub
    _ = ∑ C ∈ Ah.erase S, ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl (fun C hC => ?_)
        exact prU_prefix_eq ha hNjK (hAh C (Finset.mem_erase.mp hC).2) hS
          (Finset.mem_erase.mp hC).1
    _ = ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Counting the candidate supports -/

/-- The candidate supports in `range Nj` with at most `y` coordinates outside `Jj`. -/
def candSet (Nj : ℕ) (Jj : Finset ℕ) (y : ℕ) : Finset (Finset ℕ) :=
  (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)

/-- `(C ∩ Jj) ∪ (C \ Jj) = C`. -/
lemma eq_inter_union_sdiff (C Jj : Finset ℕ) : (C ∩ Jj) ∪ (C \ Jj) = C := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The number of supports in `range Nj` with exactly `r` coordinates outside `Jj`. -/
lemma card_candidates_eq {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (r : ℕ) :
    ((range Nj).powerset.filter (fun C => (C \ Jj).card = r)).card
      = 2 ^ Jj.card * (Nj - Jj.card).choose r := by
  classical
  set D : Finset ℕ := range Nj \ Jj with hDdef
  have hDcard : D.card = Nj - Jj.card := by
    rw [hDdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
  have hbij : ((range Nj).powerset.filter (fun C => (C \ Jj).card = r)).card
      = (Jj.powerset ×ˢ D.powersetCard r).card := by
    refine Finset.card_bij (fun C _ => (C ∩ Jj, C \ Jj)) ?_ ?_ ?_
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_powerset] at hC
      obtain ⟨hCsub, hCcard⟩ := hC
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right, ?_, hCcard⟩
      intro x hx
      rw [hDdef, Finset.mem_sdiff]
      exact ⟨hCsub (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    · intro C1 _ C2 _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      calc C1 = (C1 ∩ Jj) ∪ (C1 \ Jj) := (eq_inter_union_sdiff C1 Jj).symm
        _ = (C2 ∩ Jj) ∪ (C2 \ Jj) := by rw [h1, h2]
        _ = C2 := eq_inter_union_sdiff C2 Jj
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset] at hp
      obtain ⟨hPsub, hQsub, hQcard⟩ := hp
      have hQJ : ∀ x, x ∈ p.2 → x ∉ Jj := by
        intro x hx
        have h := hQsub hx
        rw [hDdef, Finset.mem_sdiff] at h
        exact h.2
      have hCJ : (p.1 ∪ p.2) ∩ Jj = p.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxj⟩
          · exact hx
          · exact absurd hxj (hQJ x hx)
        · intro hx; exact ⟨Or.inl hx, hPsub hx⟩
      have hCsd : (p.1 ∪ p.2) \ Jj = p.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxj⟩
          · exact absurd (hPsub hx) hxj
          · exact hx
        · intro hx; exact ⟨Or.inr hx, hQJ x hx⟩
      refine ⟨p.1 ∪ p.2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, by rw [hCsd, hQcard]⟩
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hJj (hPsub h)
        · have h' := hQsub h
          rw [hDdef, Finset.mem_sdiff] at h'
          exact h'.1
      · simp only [hCJ, hCsd]
  rw [hbij, Finset.card_product, Finset.card_powerset, Finset.card_powersetCard, hDcard]

/-- The number of supports in `range Nj` with at most `y` coordinates outside `Jj`. -/
lemma card_candidates_le_eq {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (y : ℕ) :
    ((range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)).card
      = 2 ^ Jj.card * ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h := by
  classical
  set A : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) with hA
  have hmap : Set.MapsTo (fun C => (C \ Jj).card) ↑A ↑(range (y + 1)) := by
    intro C hC
    simp only [hA, Finset.coe_filter, Set.mem_setOf_eq] at hC
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hC.2)
  have hfib : ∀ r ∈ range (y + 1),
      {C ∈ A | (C \ Jj).card = r}.card = 2 ^ Jj.card * (Nj - Jj.card).choose r := by
    intro r hr
    have hrle : r ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hset : {C ∈ A | (C \ Jj).card = r}
        = (range Nj).powerset.filter (fun C => (C \ Jj).card = r) := by
      ext C
      simp only [hA, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hrle⟩, h3⟩
    rw [hset, card_candidates_eq Jj hJj r]
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc ∑ r ∈ range (y + 1), {C ∈ A | (C \ Jj).card = r}.card
      = ∑ r ∈ range (y + 1), 2 ^ Jj.card * (Nj - Jj.card).choose r :=
        Finset.sum_congr rfl hfib
    _ = 2 ^ Jj.card * ∑ r ∈ range (y + 1), (Nj - Jj.card).choose r := by
        rw [Finset.mul_sum]

/-- The candidate family of supports with at most `y` outside coordinates is no larger than
`2 ^ σ_{j,y}`. -/
theorem card_candidates_le_two_pow_sigma {Nj : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) (y : ℕ) :
    ((candSet Nj Jj y).card : ℝ)
      ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj y : ℝ) := by
  classical
  have hval0 : candSet Nj Jj y = (range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y) := rfl
  rw [hval0]
  set X : ℕ := 2 ^ Jj.card * ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h with hX
  have hXpos : 0 < X := by
    rw [hX]
    have h1 : 0 < 2 ^ Jj.card := by positivity
    have h2 : 0 < ∑ h ∈ range (y + 1), (Nj - Jj.card).choose h := by
      have hmem : 0 ∈ range (y + 1) := Finset.mem_range.mpr (Nat.succ_pos y)
      have hle := Finset.single_le_sum (f := fun h => (Nj - Jj.card).choose h)
        (fun i _ => Nat.zero_le _) hmem
      rw [Nat.choose_zero_right] at hle
      exact Nat.lt_of_lt_of_le Nat.one_pos hle
    exact Nat.mul_pos h1 h2
  have hval : (((range Nj).powerset.filter (fun C => (C \ Jj).card ≤ y)).card : ℝ) = (X : ℝ) := by
    rw [card_candidates_le_eq Jj hJj y, hX]
  rw [hval]
  have hceil : Real.logb 2 (X : ℝ) ≤ (HintParams.sigma Jj.card Nj y : ℝ) := by
    rw [HintParams.sigma]
    exact Nat.le_ceil _
  calc (X : ℝ) = (2 : ℝ) ^ Real.logb 2 (X : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hXpos)]
    _ ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj y : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil

/-! ## Auxiliary list facts -/

lemma mem_take_finRange {ℓ a : ℕ} {x : Fin ℓ} (h : x ∈ List.take a (List.finRange ℓ)) :
    x.val < a := by
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨j, hj, hje⟩ := h
  have hj2 : j < (List.finRange ℓ).length := by omega
  have h1 : (List.finRange ℓ)[j]'hj2 = x := by rw [← hje]
  have h2 : ((List.finRange ℓ)[j]'hj2).val = j := by
    rw [List.getElem_finRange]
    simp
  have hx : x.val = j := by rw [← h1]; exact h2
  omega

/-- Pointwise form of equality of the two prefixes. -/
lemma forall_prefix_eq_iff {ℓ a : ℕ} (ha : a ≤ ℓ) {β β' : Fin ℓ → ZMod 2} :
    (List.take a (List.finRange ℓ)).map β = (List.take a (List.finRange ℓ)).map β'
      ↔ ∀ i : Fin a, β ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
          = β' ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ := by
  rw [List.map_inj_left]
  constructor
  · intro h i
    refine h ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩ ?_
    rw [List.mem_take_iff_getElem]
    refine ⟨i.val, ?_, ?_⟩
    · rw [List.length_finRange]
      exact Nat.lt_min.mpr ⟨i.isLt, Nat.lt_of_lt_of_le i.isLt ha⟩
    · rw [List.getElem_finRange]
      exact Fin.ext rfl
  · intro h s hs
    have := mem_take_finRange (ℓ := ℓ) (a := a) hs
    exact h ⟨s.val, this⟩

/-- The list form of the union-bound separation estimate. -/
theorem prU_exists_prefix_eq_list {ℓ K Nj a : ℕ} (ha : a ≤ ℓ) (hNjK : Nj ≤ K)
    {S : Finset ℕ} (hS : S ⊆ range Nj) (Ah : Finset (Finset ℕ))
    (hAh : ∀ C ∈ Ah, C ⊆ range Nj) :
    prU (fun β : Fin ℓ → Fin K → ZMod 2 =>
        ∃ C ∈ Ah.erase S, (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
      ≤ ((Ah.erase S).card : ℝ) * ((2 : ℝ) ^ (a : ℝ))⁻¹ := by
  classical
  have hiff : ∀ β : Fin ℓ → Fin K → ZMod 2,
      (∃ C ∈ Ah.erase S, (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
      ↔ (∃ C ∈ Ah.erase S, ∀ i : Fin a,
          HintParams.rowBit β C ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩
            = HintParams.rowBit β S ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩) := by
    intro β
    constructor
    · rintro ⟨C, hC, hCe⟩
      exact ⟨C, hC, (forall_prefix_eq_iff ha).mp hCe⟩
    · rintro ⟨C, hC, hCe⟩
      exact ⟨C, hC, (forall_prefix_eq_iff ha).mpr hCe⟩
  rw [prU_congr' hiff]
  exact prU_exists_prefix_eq ha hNjK hS Ah hAh

/-- `Option.map` of the head of the singleton list. -/
lemma toList_head?_singleton_map {α β : Type} (a : α) (f : α → β) :
    Option.map f (({a} : Finset α).toList.head?) = some (f a) := by
  rw [Finset.toList_singleton]
  rfl

/-! ## Numeric facts about the row geometry -/

/-- Under the standing assumptions of a non-leaf node, there is at least one row. -/
lemma rows_pos (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y) :
    1 ≤ P.rows X Y := by
  by_contra h
  have hm0 : P.rows X Y = 0 := by omega
  have hlgn : 0 < P.lgn := by
    rw [HintParams.lgn, lg]
    exact Real.logb_pos (by norm_num) (by exact_mod_cast hargs.1)
  have hY : Y = 0 := by
    have h1 : Y ≤ P.rows X Y := le_max_left _ _
    omega
  have hX : X = 0 := by
    have hc : ⌈(X:ℝ) / P.lgn ^ 3⌉₊ = 0 := by
      have h2 : ⌈(X:ℝ)/P.lgn^3⌉₊ ≤ P.rows X Y := le_max_right _ _
      omega
    have hpos : (0:ℝ) < P.lgn ^ 3 := by positivity
    have hle : (X:ℝ) ≤ 0 := by
      by_contra hh
      rw [not_le] at hh
      have h3 : 0 < (X:ℝ)/P.lgn^3 := div_pos hh hpos
      have h4 := Nat.le_ceil ((X:ℝ)/P.lgn^3)
      rw [hc] at h4
      simp at h4
      linarith
    have h5 : (X:ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg X)
    exact_mod_cast h5
  have hD : HintParams.D N X Y = 0 := by
    rw [HintParams.D, hX, hY]
    simp
  have hrule : P.rule N X Y = HintParams.Rule.cheap := by
    rw [HintParams.rule, hD]
    simp only [Nat.cast_zero]
    rw [if_pos (show (0:ℝ) ≤ (N:ℝ) / P.lgn ^ 10 by positivity)]
  rcases hnl with hh | hh
  · rw [hrule] at hh
    exact absurd hh (by decide)
  · rw [hrule] at hh
    exact absurd hh (by decide)

/-- A row of `m ≥ 1` rows has at most `⌈N/m⌉` coordinates. -/
lemma rowLen_le_Nmax (N m j : ℕ) (hm : 1 ≤ m) :
    rowLen N m j ≤ ⌈(N : ℝ) / (m : ℝ)⌉₊ := by
  classical
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  unfold rowLen
  have hmaps : ∀ p ∈ (range N).filter (fun p => p % m = j),
      p / m ∈ range ⌈(N:ℝ)/(m:ℝ)⌉₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_range]
    have hpN' : (p : ℝ) < (N : ℝ) := by exact_mod_cast hp.1
    have hdiv : (p : ℝ) / (m : ℝ) < (N : ℝ) / (m : ℝ) := div_lt_div_of_pos_right hpN' hmpos
    have hpm : ((p / m : ℕ) : ℝ) ≤ (p : ℝ) / (m : ℝ) := Nat.cast_div_le
    have h3 : ((p / m : ℕ) : ℝ) < (⌈(N:ℝ)/(m:ℝ)⌉₊ : ℝ) := by
      have h4 := Nat.le_ceil ((N:ℝ)/(m:ℝ))
      linarith
    exact_mod_cast h3
  have hinj : Set.InjOn (fun p => p / m) ↑((range N).filter (fun p => p % m = j)) := by
    intro p hp q hq heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
    have heq' : p / m = q / m := heq
    have e1 : p = m * (p/m) + j := by rw [← hp.2]; exact (Nat.div_add_mod p m).symm
    have e2 : q = m * (q/m) + j := by rw [← hq.2]; exact (Nat.div_add_mod q m).symm
    rw [e1, e2, heq']
  have hres := Finset.card_le_card_of_injOn (fun p => p / m) (by
    intro p hp
    exact hmaps p (by simpa using hp)) hinj
  simpa [Finset.card_range] using hres

/-- A row image has at most `rowLen` elements (alias of `rowImage_card_le_rowLen_infra`). -/
lemma rowImage_card_le_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    (rowImage N m π j S).card ≤ rowLen N m j :=
  rowImage_card_le_rowLen_infra π S

/-! ## The structural analysis of one row worker -/

/-- If no wrong candidate with at most `y` outside-hint positions matches the prefix, the worker
predicts the true bit. -/
theorem wp_correct
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (haL : a < ℓ)
    (hSn : S ⊆ range (rowLen N m j.val))
    (hBX : ¬ BX < Jj.card)
    (hyBY : (S \ Jj).card ≤ BY)
    (hyNj : (S \ Jj).card ≤ rowLen N m j.val - Jj.card)
    (hσa : HintParams.sigma Jj.card (rowLen N m j.val) (S \ Jj).card + cc ≤ a)
    (hnobad : ∀ C ∈ (range (rowLen N m j.val)).powerset, (C \ Jj).card ≤ (S \ Jj).card →
        (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) → C = S) :
    HintParams.workerPredict N m ℓ K BX BY cc j β Jj z
      = some (HintParams.rowBit β S ⟨a, haL⟩) := by
  classical
  set Nj := rowLen N m j.val with hNj
  set y := (S \ Jj).card with hy
  have hyBY' : y ≤ BY := by rw [hy]; exact hyBY
  have hyNj' : y ≤ Nj - Jj.card := by rw [hy, hNj]; exact hyNj
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  have hp_eq : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) = z := hz.symm
  have hSfam : S ∈ HintParams.family Nj β Jj y z := by
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSn, by rw [hy], by rw [htake, hp_eq]⟩
  have hfam1 : (HintParams.family Nj β Jj y z).card = 1 := by
    have hsub : HintParams.family Nj β Jj y z ⊆ {S} := by
      intro C hC
      simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hC
      obtain ⟨hCsub, hCcard, hCpre⟩ := hC
      rw [htake] at hCpre
      have hle : (C \ Jj).card ≤ (S \ Jj).card := by rw [hCcard, hy]
      have hpre : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
          = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
        rw [hCpre, hp_eq]
      rw [hnobad C (Finset.mem_powerset.mpr hCsub) hle hpre]
      simp
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h2
    have h3 := Finset.card_pos.mpr ⟨S, hSfam⟩
    omega
  have hp : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) y = true := by
    rw [decide_eq_true_iff]
    exact ⟨by rw [hzl, hy]; exact hσa, hfam1⟩
  have hlt0 : ∀ r < y, (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) r = false := by
    intro r hr
    rw [decide_eq_false_iff_not]
    rintro ⟨-, hcard⟩
    obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.mp hcard
    have hC₀mem : C₀ ∈ HintParams.family Nj β Jj r z := by rw [hC₀]; simp
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hC₀mem
    obtain ⟨hCsub, hCcard, hCpre⟩ := hC₀mem
    rw [htake] at hCpre
    have hle : (C₀ \ Jj).card ≤ (S \ Jj).card := by rw [hCcard, ← hy]; exact Nat.le_of_lt hr
    have hpre : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C₀)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
      rw [hCpre, hp_eq]
    have hCS : C₀ = S := hnobad C₀ (Finset.mem_powerset.mpr hCsub) hle hpre
    rw [hCS, ← hy] at hCcard
    omega
  have hlt : ∀ r < y, (!(fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
      (HintParams.family Nj β Jj r z).card = 1)) r) = true := by
    intro r hr
    rw [hlt0 r hr]
    rfl
  have hfind : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
      decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) = some y := by
    rw [List.find?_range_eq_some]
    exact ⟨hp, List.mem_range.mpr (by omega), hlt⟩
  have hfam : HintParams.family Nj β Jj y z = {S} := by
    obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.mp hfam1
    have hC₀S : S = C₀ := by
      have hmem : S ∈ ({C₀} : Finset (Finset ℕ)) := hC₀ ▸ hSfam
      simpa using hmem
    rw [hC₀, ← hC₀S]
  rw [HintParams.workerPredict]
  try simp only []
  rw [if_neg hBX]
  try simp only []
  rw [hfind]
  try simp only []
  rw [dif_pos (by omega : z.length < ℓ)]
  rw [hfam, Finset.toList_singleton]
  simp [hzl]

/-- If the worker returns `⊥` although the true support was in reach, some wrong candidate with at
most `y` outside-hint positions matches the prefix. -/
theorem wp_none_bad
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (haL : a < ℓ)
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (hSn : S ⊆ range (rowLen N m j.val))
    (hBX : ¬ BX < Jj.card)
    (hyBY : (S \ Jj).card ≤ BY)
    (hyNj : (S \ Jj).card ≤ rowLen N m j.val - Jj.card)
    (hσa : HintParams.sigma Jj.card (rowLen N m j.val) (S \ Jj).card + cc ≤ a)
    (hnone : HintParams.workerPredict N m ℓ K BX BY cc j β Jj z = none) :
    ∃ C ∈ candSet (rowLen N m j.val) Jj (S \ Jj).card, C ≠ S ∧
      (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
  classical
  set Nj := rowLen N m j.val with hNj
  set y := (S \ Jj).card with hy
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  have hp_eq : (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) = z := hz.symm
  have hSfam : S ∈ HintParams.family Nj β Jj y z := by
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSn, by rw [hy], by rw [htake, hp_eq]⟩
  rw [HintParams.workerPredict] at hnone
  try simp only [] at hnone
  rw [if_neg hBX] at hnone
  try simp only [] at hnone
  rcases hf : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
      decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) with _ | r
  · have hfalse : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) y = false := by
      have hnot := (List.find?_eq_none.mp hf) y (List.mem_range.mpr (by omega))
      cases hb : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
          (HintParams.family Nj β Jj r z).card = 1)) y
      · rfl
      · exact absurd hb hnot
    rw [decide_eq_false_iff_not] at hfalse
    have hge2 : 1 < (HintParams.family Nj β Jj y z).card := by
      have hpos := Finset.card_pos.mpr ⟨S, hSfam⟩
      have hne1 : (HintParams.family Nj β Jj y z).card ≠ 1 :=
        fun h1 => hfalse ⟨by rw [hzl, hy]; exact hσa, h1⟩
      omega
    have hw : ∃ C ∈ HintParams.family Nj β Jj y z, C ≠ S := by
      by_contra hh
      have hh' : ∀ C, C ∈ HintParams.family Nj β Jj y z → C = S := by
        intro C hC
        by_contra hne
        exact hh ⟨C, hC, hne⟩
      have hsub : HintParams.family Nj β Jj y z ⊆ {S} := fun C hC => by
        simp [hh' C hC]
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h2
      omega
    obtain ⟨C, hCmem, hCS⟩ := hw
    simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCmem
    obtain ⟨hCsub, hCcard, hCpre⟩ := hCmem
    rw [htake] at hCpre
    refine ⟨C, ?_, hCS, ?_⟩
    · simp only [candSet, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hCsub, by rw [hCcard, hy]⟩
    · rw [hCpre, hp_eq]
  · rw [hf] at hnone
    try simp only [] at hnone
    rw [dif_pos (by omega : z.length < ℓ)] at hnone
    have hp : (fun r => decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
        (HintParams.family Nj β Jj r z).card = 1)) r = true :=
      (List.find?_range_eq_some.mp hf).1
    rw [decide_eq_true_iff] at hp
    obtain ⟨-, hcard1⟩ := hp
    have hcard0 : (HintParams.family Nj β Jj r z).card = 0 := by
      have hnil : (HintParams.family Nj β Jj r z).toList = [] := by
        cases htl : (HintParams.family Nj β Jj r z).toList with
        | nil => rfl
        | cons a l =>
          rw [htl] at hnone
          exact absurd hnone (by simp)
      rw [← Finset.length_toList, hnil]
      rfl
    omega

/-- If the worker predicts a wrong bit, the qualifying candidate came from a family whose index is
within the `σ + c ≤ a` budget. -/
theorem wp_wrong_elig
    {ℓ K N m : ℕ} {BX BY cc : ℕ} {j : Fin m} {β : Fin ℓ → Fin K → ZMod 2}
    {Jj S : Finset ℕ} {z : List (ZMod 2)} {a : ℕ}
    (haL : a < ℓ)
    (hz : z = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S))
    (hzl : z.length = a)
    (hwr : ∃ b, HintParams.workerPredict N m ℓ K BX BY cc j β Jj z = some b ∧
      b ≠ HintParams.rowBit β S ⟨a, haL⟩) :
    ∃ C ∈ (range (rowLen N m j.val)).powerset, C ≠ S ∧
      (C \ Jj).card ∈ (range (min BY (rowLen N m j.val - Jj.card) + 1)).filter
          (fun r => HintParams.sigma Jj.card (rowLen N m j.val) r + cc ≤ a) ∧
      (List.take a (List.finRange ℓ)).map (HintParams.rowBit β C)
        = (List.take a (List.finRange ℓ)).map (HintParams.rowBit β S) := by
  classical
  set Nj := rowLen N m j.val with hNj
  obtain ⟨b, hb, hbne⟩ := hwr
  have htake : List.take z.length (List.finRange ℓ) = List.take a (List.finRange ℓ) := by rw [hzl]
  rw [HintParams.workerPredict] at hb
  try simp only [] at hb
  by_cases hBX : BX < Jj.card
  · rw [if_pos hBX] at hb
    simp at hb
  · rw [if_neg hBX] at hb
    try simp only [] at hb
    rcases hf : (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
        decide (HintParams.sigma Jj.card Nj r + cc ≤ z.length ∧
          (HintParams.family Nj β Jj r z).card = 1)) with _ | r
    · rw [hf] at hb
      simp only [] at hb
      simp at hb
    · rw [hf] at hb
      try simp only [] at hb
      by_cases hlt : z.length < ℓ
      · rw [dif_pos hlt] at hb
        rw [Option.map_eq_some_iff] at hb
        obtain ⟨C, hChead, hCb⟩ := hb
        have hCmem : C ∈ HintParams.family Nj β Jj r z :=
          Finset.mem_toList.mp (List.mem_of_mem_head? hChead)
        obtain ⟨hp, hrmem, -⟩ := List.find?_range_eq_some.mp hf
        rw [decide_eq_true_iff] at hp
        obtain ⟨hσr, -⟩ := hp
        simp only [HintParams.family, Finset.mem_filter, Finset.mem_powerset] at hCmem
        obtain ⟨hCsub, hCcard, hCpre⟩ := hCmem
        rw [htake] at hCpre
        have hCS : C ≠ S := by
          intro hCS
          rw [hCS] at hCb
          exact hbne (by rw [← hCb]; congr 1; exact Fin.ext hzl)
        refine ⟨C, Finset.mem_powerset.mpr hCsub, hCS, ?_, ?_⟩
        · rw [hCcard]
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_range]
            exact List.mem_range.mp hrmem
          · rw [hzl] at hσr; exact hσr
        · rw [hCpre, hz]
      · rw [dif_neg hlt] at hb
        simp at hb

/-! ## The cardinality of the qualifying family -/

/-- The family of supports whose index qualifies for the `σ + c ≤ a` budget has at most
`2^{a-c}` elements. -/
theorem card_elig_le {Nj cc a BY : ℕ} (Jj : Finset ℕ) (hJj : Jj ⊆ range Nj) :
    let Ae := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈
        (range (min BY (Nj - Jj.card) + 1)).filter
          (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a))
    (Ae.card : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) - (cc : ℝ)) := by
  classical
  dsimp only
  set R' : Finset ℕ := (range (min BY (Nj - Jj.card) + 1)).filter
      (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a) with hR'
  set Ae : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈ R') with hAe
  by_cases hne : R'.Nonempty
  · set Rmax := R'.max' hne with hRmax
    have hRmaxmem : Rmax ∈ R' := Finset.max'_mem R' hne
    have hRmaxle : ∀ r ∈ R', r ≤ Rmax := fun r hr => Finset.le_max' R' r hr
    have hσR : HintParams.sigma Jj.card Nj Rmax + cc ≤ a :=
      (Finset.mem_filter.mp hRmaxmem).2
    have hsub : Ae ⊆ candSet Nj Jj Rmax := by
      intro C hC
      simp only [hAe, candSet, Finset.mem_filter, Finset.mem_powerset] at hC ⊢
      exact ⟨hC.1, hRmaxle _ hC.2⟩
    have h1 : (Ae.card : ℝ) ≤ ((candSet Nj Jj Rmax).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((candSet Nj Jj Rmax).card : ℝ)
        ≤ (2 : ℝ) ^ (HintParams.sigma Jj.card Nj Rmax : ℝ) :=
      card_candidates_le_two_pow_sigma Jj hJj Rmax
    have h3 : (2 : ℝ) ^ (HintParams.sigma Jj.card Nj Rmax : ℝ)
        ≤ (2 : ℝ) ^ ((a : ℝ) - (cc : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h4 : (HintParams.sigma Jj.card Nj Rmax : ℝ) + (cc : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast hσR
      linarith
    exact le_trans h1 (le_trans h2 h3)
  · have hempty : R' = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hne ⟨x, hx⟩)
    have hAe0 : Ae = ∅ := by
      rw [hAe, hempty]
      simp
    rw [hAe0, Finset.card_empty, Nat.cast_zero]
    positivity


/-! ## Lemma 5.2 -/

/-- Lemma 5.2, PDF p.21 (printed p.20): for a regular row of a non-leaf node, after `a < ℓ` recovered
bits of the true transcript. The probability is over the coins of the row. -/
theorem lemma_5_2 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val)) (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) (a : Fin (P.ell N X Y)) :
    let sch := P.scheme N X Y
    let σ : ℝ := (HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card : ℝ)
    let c : ℝ := (P.c N X Y : ℝ)
    let q : sch.Rand → Option (ZMod 2) := fun β =>
      sch.predict j β Jj (sch.truePrefix j β Sj a.val)
    prU (fun β : sch.Rand => q β = none) ≤ G a.val (σ + c) ∧
    prU (fun β : sch.Rand => ∃ b, q β = some b ∧ b ≠ sch.code j β Sj a) ≤
      ((2 : ℝ) ^ (P.c N X Y))⁻¹ * G a.val (σ + c) := by
  classical
  dsimp only
  set Nj := rowLen N (P.rows X Y) j.val with hNj
  set cc : ℕ := P.c N X Y with hcc
  set σn : ℕ := HintParams.sigma Jj.card Nj (Sj \ Jj).card with hσn
  -- basic numeric facts
  have hm1 : 1 ≤ P.rows X Y := rows_pos P N X Y hargs hnl
  have hNK : Nj ≤ P.Nmax N X Y := by rw [hNj]; exact rowLen_le_Nmax N (P.rows X Y) j.val hm1
  have hJcard : Jj.card ≤ P.BX N X Y := by
    by_contra hh
    exact hreg (Or.inl (by omega))
  have hyBY : (Sj \ Jj).card ≤ P.BY N X Y := by
    by_contra hh
    exact hreg (Or.inr (by omega))
  have hyNj : (Sj \ Jj).card ≤ Nj - Jj.card := by
    have hsub : Sj \ Jj ⊆ range Nj \ Jj := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hSj (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    calc (Sj \ Jj).card ≤ (range Nj \ Jj).card := Finset.card_le_card hsub
      _ = Nj - Jj.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJj, Finset.card_range]
  -- the true prefix
  have hzdef : ∀ β : (P.scheme N X Y).Rand,
      (P.scheme N X Y).truePrefix j β Sj a.val
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj) :=
    fun β => rfl
  have hzlen : ∀ β : (P.scheme N X Y).Rand,
      ((P.scheme N X Y).truePrefix j β Sj a.val).length = a.val := by
    intro β
    rw [hzdef β, List.length_map, List.length_take, List.length_finRange,
      Nat.min_eq_left (le_of_lt a.isLt)]
  -- the two candidate families
  set Ah1 : Finset (Finset ℕ) := candSet Nj Jj (Sj \ Jj).card with hAh1
  set R' : Finset ℕ := (range (min (P.BY N X Y) (Nj - Jj.card) + 1)).filter
      (fun r => HintParams.sigma Jj.card Nj r + cc ≤ a.val) with hR'
  set Ae : Finset (Finset ℕ) := (range Nj).powerset.filter (fun C => (C \ Jj).card ∈ R') with hAe
  -- the bad events
  have hbad1 : ∀ β : (P.scheme N X Y).Rand, σn + cc ≤ a.val →
      (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none ∨
      (∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ (P.scheme N X Y).code j β Sj a) →
      (∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) := by
    intro β hσa hcase
    have hσa' : HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card + cc
        ≤ a.val := hσa
    rcases hcase with hnone | ⟨b, hb, hbne⟩
    · obtain ⟨C, hCmem, hCS, hCmat⟩ :=
        wp_none_bad (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hSj (by omega : ¬ P.BX N X Y < Jj.card) hyBY hyNj hσa' hnone
      refine ⟨C, Finset.mem_erase.mpr ⟨hCS, ?_⟩, hCmat⟩
      rwa [hAh1]
    · by_contra hno
      have hgood : ∀ C ∈ (range (rowLen N (P.rows X Y) j.val)).powerset,
          (C \ Jj).card ≤ (Sj \ Jj).card →
          (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β C)
            = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj) →
          C = Sj := by
        intro C hCpow hCcard hCmat
        by_contra hCS
        exact hno ⟨C, Finset.mem_erase.mpr ⟨hCS, by
          rw [hAh1]
          exact Finset.mem_filter.mpr ⟨hCpow, hCcard⟩⟩, hCmat⟩
      have hq := wp_correct (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hSj
        (by omega : ¬ P.BX N X Y < Jj.card) hyBY hyNj hσa' hgood
      have hq' : (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val)
          = some ((P.scheme N X Y).code j β Sj a) := hq
      rw [hq'] at hb
      exact hbne (by simpa using hb.symm)
  -- the second bad event
  have hbad2 : ∀ β : (P.scheme N X Y).Rand,
      (∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ (P.scheme N X Y).code j β Sj a) →
      (∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) := by
    intro β hwr
    have hwr' : ∃ b, HintParams.workerPredict N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y)
        (P.BX N X Y) (P.BY N X Y) (P.c N X Y) j β Jj
        ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
        b ≠ HintParams.rowBit β Sj ⟨a.val, a.isLt⟩ := by
      obtain ⟨b, hb, hbne⟩ := hwr
      exact ⟨b, hb, fun hcontra => hbne hcontra⟩
    obtain ⟨C, hCpow, hCS, hCidx, hCmat⟩ :=
      wp_wrong_elig (haL := a.isLt) (hz := hzdef β) (hzl := hzlen β) hwr'
    refine ⟨C, Finset.mem_erase.mpr ⟨hCS, ?_⟩, hCmat⟩
    rw [hAe]
    exact Finset.mem_filter.mpr ⟨hCpow, hCidx⟩
  -- cardinality bounds
  have hAh1card : ((Ah1.erase Sj).card : ℝ) ≤ (2:ℝ)^(σn:ℝ) := by
    have h1 : ((Ah1.erase Sj).card : ℝ) ≤ (Ah1.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset Sj Ah1)
    have h2 : (Ah1.card : ℝ) ≤ (2:ℝ)^(σn:ℝ) := by
      rw [hAh1]
      exact card_candidates_le_two_pow_sigma Jj hJj (Sj \ Jj).card
    exact le_trans h1 h2
  have hAecard : ((Ae.erase Sj).card : ℝ) ≤ (2:ℝ)^((a.val:ℝ) - (cc:ℝ)) := by
    have h1 : ((Ae.erase Sj).card : ℝ) ≤ (Ae.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset Sj Ae)
    have h2 : (Ae.card : ℝ) ≤ (2:ℝ)^((a.val:ℝ) - (cc:ℝ)) := by
      have h3 := card_elig_le (Nj := Nj) (cc := cc) (a := a.val) (BY := P.BY N X Y) Jj hJj
      simpa only [hAe, hR'] using h3
    exact le_trans h1 h2
  -- the probabilities of the bad events
  have hpowpos : (0:ℝ) < ((2:ℝ)^((a.val:ℝ)))⁻¹ := by
    apply inv_pos.mpr
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hPr1 : prU (fun β : (P.scheme N X Y).Rand =>
      ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj))
      ≤ ((2:ℝ)^(σn:ℝ)) * ((2:ℝ)^(a.val:ℝ))⁻¹ := by
    refine le_trans (prU_exists_prefix_eq_list (ℓ := P.ell N X Y) (K := P.Nmax N X Y)
      (Nj := Nj) (a := a.val) (le_of_lt a.isLt) hNK hSj Ah1 ?_) ?_
    · intro C hC
      have := Finset.mem_filter.mp hC
      exact Finset.mem_powerset.mp this.1
    · exact mul_le_mul_of_nonneg_right hAh1card (le_of_lt hpowpos)
  have hPr2 : prU (fun β : (P.scheme N X Y).Rand =>
      ∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
          (HintParams.rowBit β C)
        = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj))
      ≤ ((2:ℝ)^((a.val:ℝ) - (cc:ℝ))) * ((2:ℝ)^(a.val:ℝ))⁻¹ := by
    refine le_trans (prU_exists_prefix_eq_list (ℓ := P.ell N X Y) (K := P.Nmax N X Y)
      (Nj := Nj) (a := a.val) (le_of_lt a.isLt) hNK hSj Ae ?_) ?_
    · intro C hC
      have := Finset.mem_filter.mp hC
      exact Finset.mem_powerset.mp this.1
    · exact mul_le_mul_of_nonneg_right hAecard (le_of_lt hpowpos)
  -- arithmetic
  have hA : ((2:ℝ)^(σn:ℝ)) * ((2:ℝ)^(a.val:ℝ))⁻¹ = (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
    rw [Real.rpow_sub (by norm_num), div_eq_mul_inv]
  have hB : ((2:ℝ)^((a.val:ℝ) - (cc:ℝ))) * ((2:ℝ)^(a.val:ℝ))⁻¹ = ((2:ℝ)^(cc:ℝ))⁻¹ := by
    have h1 : ((a.val:ℝ) - (cc:ℝ)) = (a.val:ℝ) + (-(cc:ℝ)) := by ring
    rw [h1, Real.rpow_add (by norm_num), Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
    field_simp
  have hB' : a.val < σn + cc → ((2:ℝ)^(cc:ℝ))⁻¹ ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
    intro hlt
    calc ((2:ℝ)^(cc:ℝ))⁻¹ = (2:ℝ)^(-(cc:ℝ)) :=
          (Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) _).symm
      _ ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have h4 : (a.val:ℝ) < (σn:ℝ) + (cc:ℝ) := by exact_mod_cast hlt
          linarith
  -- final assembly
  constructor
  · by_cases hcase : σn + cc ≤ a.val
    · have hmono : prU (fun β : (P.scheme N X Y).Rand =>
          (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ prU (fun β : (P.scheme N X Y).Rand =>
          ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
              (HintParams.rowBit β C)
            = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
        prU_mono' (fun β hnone => hbad1 β hcase (Or.inl hnone))
      calc prU (fun β : (P.scheme N X Y).Rand =>
            (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := le_trans hmono (le_trans hPr1 (le_of_eq hA))
        _ ≤ G a.val ((σn:ℝ) + (cc:ℝ)) := by
            rw [G]
            apply le_min
            · have hz : (σn:ℝ) - (a.val:ℝ) ≤ 0 := by
                have h1 : (σn:ℝ) + (cc:ℝ) ≤ (a.val:ℝ) := by exact_mod_cast hcase
                have h2 : (0:ℝ) ≤ (cc:ℝ) := Nat.cast_nonneg cc
                linarith
              calc (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) ≤ (2:ℝ)^(0:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
                _ = 1 := Real.rpow_zero 2
            · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              have h2 : (0:ℝ) ≤ (cc:ℝ) := Nat.cast_nonneg cc
              linarith
    · have hcase' : a.val < σn + cc := by omega
      calc prU (fun β : (P.scheme N X Y).Rand =>
            (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = none)
          ≤ 1 := prU_le_one _
        _ = G a.val ((σn:ℝ) + (cc:ℝ)) := by
            rw [G]
            have hlt' : (a.val:ℝ) < (σn:ℝ) + (cc:ℝ) := by exact_mod_cast hcase'
            have hz : (0:ℝ) ≤ (σn:ℝ) + (cc:ℝ) - (a.val:ℝ) := by linarith
            have hone : (1:ℝ) ≤ (2:ℝ)^((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) := by
              calc (1:ℝ) = (2:ℝ)^(0:ℝ) := (Real.rpow_zero 2).symm
                _ ≤ (2:ℝ)^((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
            exact (min_eq_left hone).symm
  · have hmono2 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ prU (fun β : (P.scheme N X Y).Rand =>
        ∃ C ∈ Ae.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
            (HintParams.rowBit β C)
          = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
      prU_mono' (fun β hwr => hbad2 β hwr)
    have hle2 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ ((2:ℝ)^(cc:ℝ))⁻¹ := le_trans hmono2 (le_trans hPr2 (le_of_eq hB))
    have hle1 : prU (fun β : (P.scheme N X Y).Rand =>
        ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
          b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ (2:ℝ)^((σn:ℝ) - (a.val:ℝ)) := by
      by_cases hcase : σn + cc ≤ a.val
      · have hmono1 : prU (fun β : (P.scheme N X Y).Rand =>
            ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
              b ≠ (P.scheme N X Y).code j β Sj a)
            ≤ prU (fun β : (P.scheme N X Y).Rand =>
            ∃ C ∈ Ah1.erase Sj, (List.take a.val (List.finRange (P.ell N X Y))).map
                (HintParams.rowBit β C)
              = (List.take a.val (List.finRange (P.ell N X Y))).map (HintParams.rowBit β Sj)) :=
          prU_mono' (fun β hwr => hbad1 β hcase (Or.inr hwr))
        exact le_trans hmono1 (le_trans hPr1 (le_of_eq hA))
      · have hcase' : a.val < σn + cc := by omega
        exact le_trans hle2 (hB' hcase')
    calc prU (fun β : (P.scheme N X Y).Rand =>
          ∃ b, (P.scheme N X Y).predict j β Jj ((P.scheme N X Y).truePrefix j β Sj a.val) = some b ∧
            b ≠ (P.scheme N X Y).code j β Sj a)
        ≤ min ((2:ℝ)^((σn:ℝ) - (a.val:ℝ))) ((2:ℝ)^(cc:ℝ))⁻¹ := le_min hle1 hle2
      _ = ((2:ℝ)^(P.c N X Y))⁻¹ * G a.val ((σn:ℝ) + (cc:ℝ)) := by
          have hnat : ((2:ℝ)^(P.c N X Y))⁻¹ = ((2:ℝ)^(cc:ℝ))⁻¹ := by
            rw [← hcc, ← Real.rpow_natCast]
          rw [hnat]
          have hG : ((2:ℝ)^(cc:ℝ))⁻¹ * G a.val ((σn:ℝ) + (cc:ℝ))
              = min ((2:ℝ)^((σn:ℝ) - (a.val:ℝ))) ((2:ℝ)^(cc:ℝ))⁻¹ := by
            rw [G, mul_min_of_nonneg (1:ℝ) _ (by positivity), mul_one]
            have hneg : ((2:ℝ)^(cc:ℝ))⁻¹ = (2:ℝ)^(-(cc:ℝ)) :=
              (Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) _).symm
            rw [hneg, ← Real.rpow_add (by norm_num)]
            have harg : -(cc:ℝ) + ((σn:ℝ) + (cc:ℝ) - (a.val:ℝ)) = (σn:ℝ) - (a.val:ℝ) := by
              ring
            rw [harg, min_comm]
          exact hG.symm


/-! ### A. Uniform averages over products and coordinate functions -/

/-- The indicator of a proposition, with the `Classical` decision instance *fixed syntactically*.

A literal `if p then (1 : ℝ) else 0` picks its decision instance by typeclass search, so for an
equality `f a = none` it uses `decidableEqNone` rather than `Classical.propDecidable`, and two such
`if`s are definitionally equal only when their instances are.  Writing every indicator through `ind`
pins the instance, so that `prU P = expU (fun a => ind (P a))` (`prU_eq_avg`) can be used without
instance mismatches. -/
def ind (p : Prop) : ℝ := @ite ℝ p (Classical.propDecidable p) 1 0

lemma ind_nonneg (p : Prop) : 0 ≤ ind p := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (p : Prop) : ind p ≤ 1 := by unfold ind; split_ifs <;> norm_num

open Classical in
/-- `prU` is the average of the indicator function. -/
lemma prU_eq_avg {α : Type} [Fintype α] (P : α → Prop) :
    prU P = expU (fun a => ind (P a)) := by
  classical
  unfold prU expU ind
  congr 1
  rw [Finset.sum_boole]

/-- The uniform average over a product type factorizes. -/
lemma expU_prod {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (f : α × β → ℝ) :
    expU f = expU (fun a => expU (fun b => f (a, b))) := by
  have h1 : ∑ p : α × β, f p = ∑ a, ∑ b, f (a, b) := Fintype.sum_prod_type f
  have h2 : (Fintype.card (α × β) : ℝ) = (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := by
    rw [Fintype.card_prod]; push_cast; ring
  have h3 : ∑ a, (∑ b, f (a, b)) / (Fintype.card β : ℝ)
      = (∑ a, ∑ b, f (a, b)) / (Fintype.card β : ℝ) := (Finset.sum_div ..).symm
  unfold expU
  rw [h1, h2, h3, div_div, mul_comm]

/-- The average of a function of the second coordinate of a product. -/
lemma expU_prod_snd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (g : β → ℝ) : expU (fun p : α × β => g p.2) = expU g := by
  rw [expU_prod]
  exact expU_const (Fintype.card_pos_iff.mpr inferInstance) (expU g)

/-- Overwriting one coordinate of a function. -/
def piUpd {m : ℕ} {R : Type} (j : Fin m) (r : R) (β : Fin m → R) : Fin m → R :=
  fun i => if i = j then r else β i

lemma piUpd_same {m : ℕ} {R : Type} (j : Fin m) (r : R) (β : Fin m → R) :
    piUpd j r β j = r := by simp [piUpd]

lemma piUpd_noteq {m : ℕ} {R : Type} {j i : Fin m} {r : R} {β : Fin m → R} (h : i ≠ j) :
    piUpd j r β i = β i := by simp [piUpd, h]

lemma piUpd_idem {m : ℕ} {R : Type} (j : Fin m) (r r' : R) (β : Fin m → R) :
    piUpd j r' (piUpd j r β) = piUpd j r' β := by
  funext i; by_cases h : i = j <;> simp [piUpd, h]

lemma piUpd_self {m : ℕ} {R : Type} (j : Fin m) (r : R) (β : Fin m → R) (h : β j = r) :
    piUpd j r β = β := by
  funext i; by_cases hi : i = j
  · subst hi; simp [piUpd, h]
  · simp [piUpd, hi]

open Classical in
/-- The fibers of a coordinate projection all have the same cardinality. -/
lemma card_fiber_pi_apply {m : ℕ} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (j : Fin m) (r r' : R) :
    (univ.filter (fun β : Fin m → R => β j = r')).card
      = (univ.filter (fun β : Fin m → R => β j = r)).card := by
  classical
  refine Finset.card_bij (fun β _ => piUpd j r β) ?_ ?_ ?_
  · intro β hβ
    simp only [mem_filter, mem_univ, true_and] at hβ ⊢
    simp [piUpd]
  · intro β hβ β' hβ' heq
    simp only [mem_filter, mem_univ, true_and] at hβ hβ'
    funext i
    by_cases hi : i = j
    · subst hi; rw [hβ, hβ']
    · rw [← piUpd_noteq (β := β) hi, ← piUpd_noteq (β := β') hi, heq]
  · intro β' hβ'
    simp only [mem_filter, mem_univ, true_and] at hβ'
    refine ⟨piUpd j r' β', ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      simp [piUpd]
    · rw [piUpd_idem, piUpd_self j r β' hβ']

open Classical in
/-- Counting the functions with a fixed value at one coordinate. -/
lemma card_pi_apply_eq {m : ℕ} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (j : Fin m) (r : R) :
    (Fintype.card (Fin m → R) : ℕ)
      = Fintype.card R * (univ.filter (fun β : Fin m → R => β j = r)).card := by
  classical
  have hpart : ∑ r' : R, (univ.filter (fun β : Fin m → R => β j = r')).card
      = Fintype.card (Fin m → R) := by
    rw [← Finset.card_univ]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun β : Fin m → R => β j) (t := univ)
      (H := by intro a ha; exact Finset.mem_univ _)]
  rw [← hpart]
  refine Eq.trans (Finset.sum_congr rfl (fun r' _ => card_fiber_pi_apply j r r')) ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

open Classical in
/-- A function of one coordinate of a function type has the average of that coordinate. -/
lemma expU_pi_apply {m : ℕ} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (j : Fin m) (g : R → ℝ) :
    expU (fun β : Fin m → R => g (β j)) = expU g := by
  classical
  obtain ⟨r₀⟩ := (inferInstance : Nonempty R)
  set F : ℕ := (univ.filter (fun β : Fin m → R => β j = r₀)).card with hF
  have hcard : (Fintype.card (Fin m → R) : ℝ) = (Fintype.card R : ℝ) * (F : ℝ) := by
    have h := card_pi_apply_eq j r₀
    have h' : ((Fintype.card R * F : ℕ) : ℝ) = (Fintype.card (Fin m → R) : ℝ) := by
      rw [← h]
    push_cast at h'
    rw [h']
  have hsum : ∑ β : Fin m → R, g (β j) = (∑ r, g r) * (F : ℝ) := by
    have h1 : ∀ β : Fin m → R, g (β j) = ∑ r, (if β j = r then g r else 0) := by
      intro β
      rw [Finset.sum_ite_eq univ (β j) (fun r => g r)]
      simp
    calc ∑ β : Fin m → R, g (β j)
        = ∑ β : Fin m → R, ∑ r, (if β j = r then g r else 0) :=
          Finset.sum_congr rfl (fun β _ => h1 β)
      _ = ∑ r, ∑ β : Fin m → R, (if β j = r then g r else 0) := Finset.sum_comm
      _ = ∑ r, g r * ((univ.filter (fun β : Fin m → R => β j = r)).card : ℝ) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ r, g r * (F : ℝ) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [show (univ.filter (fun β : Fin m → R => β j = r)).card = F from ?_]
          rw [hF]
          exact (card_fiber_pi_apply j r r₀).symm
      _ = (∑ r, g r) * (F : ℝ) := by rw [Finset.sum_mul]
  unfold expU
  rw [hsum, hcard]
  have hFR : ((Fintype.card R : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card R := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  have hF0 : (F : ℝ) ≠ 0 := by
    have h : 0 < F := by
      rw [hF]
      refine Finset.card_pos.mpr ⟨fun _ => r₀, by simp⟩
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  field_simp

/-! ### B. Growth of the candidate family (`sigma` is monotone) -/

/-- The number of candidate supports with at most `r` outside-hint coordinates. -/
def candCnt (a n r : ℕ) : ℕ := 2 ^ a * ∑ h ∈ range (r + 1), (n - a).choose h

lemma sigma_eq_candCnt (a n r : ℕ) :
    HintParams.sigma a n r = ⌈lg (candCnt a n r : ℝ)⌉₊ := rfl

lemma candCnt_pos (a n r : ℕ) : 1 ≤ candCnt a n r := by
  unfold candCnt
  have h1 : 1 ≤ ∑ h ∈ range (r + 1), (n - a).choose h := by
    have hmem : (0 : ℕ) ∈ range (r + 1) := by simp
    calc 1 = (n - a).choose 0 := by simp
      _ ≤ ∑ h ∈ range (r + 1), (n - a).choose h :=
        Finset.single_le_sum (f := fun h => (n - a).choose h) (fun i _ => Nat.zero_le _) hmem
  have h2 : 1 ≤ 2 ^ a := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero a (by norm_num))
  calc 1 = 1 * 1 := by ring
    _ ≤ 2 ^ a * ∑ h ∈ range (r + 1), (n - a).choose h := Nat.mul_le_mul h2 h1

lemma candCnt_mono_r {a n r r' : ℕ} (h : r ≤ r') : candCnt a n r ≤ candCnt a n r' := by
  unfold candCnt
  refine Nat.mul_le_mul_left _ ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Nat.zero_le _)
  intro x hx
  simp only [mem_range] at hx ⊢
  omega

/-- Monotonicity of initial segments. -/
lemma range_subset_of_le {a b : ℕ} (h : a ≤ b) : (range a : Finset ℕ) ⊆ range b := by
  intro x hx
  simp only [mem_range] at hx ⊢
  omega

lemma candCnt_eq_filter_card {a n r : ℕ} (ha : a ≤ n) :
    candCnt a n r = ((range n).powerset.filter (fun C => (C \ range a).card ≤ r)).card := by
  rw [card_candidates_le_eq (range a) (range_subset_of_le ha) r]
  simp [candCnt]

lemma candCnt_mono_a {a a' n r : ℕ} (ha : a ≤ a') (han : a' ≤ n) :
    candCnt a n r ≤ candCnt a' n r := by
  rw [candCnt_eq_filter_card (le_trans ha han), candCnt_eq_filter_card han]
  refine Finset.card_le_card ?_
  intro C hC
  simp only [mem_filter, mem_powerset] at hC ⊢
  refine ⟨hC.1, le_trans (Finset.card_le_card ?_) hC.2⟩
  exact Finset.sdiff_subset_sdiff (le_refl C) (range_subset_of_le ha)

lemma sigma_mono {a a' n r r' : ℕ} (ha : a ≤ a') (hr : r ≤ r') (han : a' ≤ n) :
    HintParams.sigma a n r ≤ HintParams.sigma a' n r' := by
  rw [sigma_eq_candCnt, sigma_eq_candCnt]
  have h1 : candCnt a n r ≤ candCnt a' n r := candCnt_mono_a ha han
  have h2 : candCnt a' n r ≤ candCnt a' n r' := candCnt_mono_r hr
  have h4 : (1 : ℝ) ≤ (candCnt a' n r' : ℝ) := by exact_mod_cast candCnt_pos a' n r'
  have h5 : ((candCnt a n r : ℕ) : ℝ) ≤ ((candCnt a' n r' : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  exact Nat.ceil_mono (lg_le_lg_of_le (by positivity) h4 h5)

lemma candCnt_sat {a n : ℕ} (han : a ≤ n) : candCnt a n (n - a) = 2 ^ n := by
  unfold candCnt
  rw [Nat.sum_range_choose, ← pow_add, show a + (n - a) = n by omega]

lemma sigma_sat {a n : ℕ} (han : a ≤ n) : HintParams.sigma a n (n - a) = n := by
  rw [sigma_eq_candCnt, candCnt_sat han]
  have h2 : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
  rw [← h2, lg_pow_pos (by norm_num : (0 : ℝ) < 2), lg_two, mul_one]
  simp

/-! ### C. Geometry of the rows -/

/-- A coordinate's local index is smaller than its row length. -/
lemma div_lt_rowLen {N m p j : ℕ} (hm : 0 < m) (hpN : p < N) (hpj : p % m = j) :
    p / m < rowLen N m j := by
  classical
  set F : Finset ℕ := (range N).filter (fun x => x % m = j) with hF
  have hrowLen : rowLen N m j = F.card := rfl
  have hj : j < m := hpj ▸ Nat.mod_lt p hm
  have hmaps : ∀ q ∈ range (p / m + 1), (m * q + j) ∈ F := by
    intro q hq
    simp only [mem_range] at hq
    rw [hF, mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have hq' : q ≤ p / m := by omega
      have h2 : m * (p / m) + j = p := by rw [← hpj]; exact Nat.div_add_mod p m
      nlinarith
    · rw [show m * q + j = j + m * q by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hj]
  have hinj : Set.InjOn (fun q => m * q + j) ↑(range (p / m + 1)) := by
    intro a _ b _ hab
    simp only at hab
    exact Nat.mul_left_cancel hm (Nat.add_right_cancel hab)
  have h := Finset.card_le_card_of_injOn (fun q => m * q + j) hmaps hinj
  rw [hrowLen]
  simpa using h

/-- The row image of `[N]` is the full row. -/
lemma rowImage_range {N m j : ℕ} (π : Equiv.Perm (Fin N)) :
    rowImage N m π j (range N)
      = (univ.filter (fun i : Fin N => (π i).val % m = j)).image (fun i => (π i).val / m) := by
  classical
  ext x
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, ⟨i.isLt, hi⟩, rfl⟩

/-- The card of the row image of `[N]` is the row length. -/
lemma rowImage_range_card {N m j : ℕ} (π : Equiv.Perm (Fin N)) :
    (rowImage N m π j (range N)).card = rowLen N m j := by
  classical
  rw [rowImage_range]
  rw [Finset.card_image_of_injOn]
  · exact card_fiber_eq_rowLen π
  · intro a ha b hb hab
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha hb
    have hpa : (π a).val = m * ((π a).val / m) + (π a).val % m := (Nat.div_add_mod _ _).symm
    have hpb : (π b).val = m * ((π b).val / m) + (π b).val % m := (Nat.div_add_mod _ _).symm
    have hval : (π a).val = (π b).val := by
      have h1 : (π a).val / m = (π b).val / m := hab
      rw [hpa, hpb, ha, hb, h1]
    exact π.injective (Fin.ext hval)

/-- A row image is contained in the range of the row length. -/
lemma rowImage_subset_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    rowImage N m π j S ⊆ range (rowLen N m j) := by
  classical
  intro x hx
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and] at hx
  obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hx
  by_cases hm : m = 0
  · subst hm
    have hi' : (π i).val = j := by simpa using hi
    have hpos : 0 < rowLen N 0 j := by
      rw [rowLen]
      refine Finset.card_pos.mpr ⟨j, ?_⟩
      simp only [mem_filter, mem_range]
      exact ⟨hi'.symm ▸ (π i).isLt, by simp⟩
    rw [Nat.div_zero]
    exact Finset.mem_range.mpr hpos
  · exact mem_range.mpr (div_lt_rowLen (p := (π i).val) (Nat.pos_of_ne_zero hm)
      (π i).isLt hi)

lemma rowImage_mono {N m j : ℕ} (π : Equiv.Perm (Fin N)) {S S' : Finset ℕ} (h : S ⊆ S') :
    rowImage N m π j S ⊆ rowImage N m π j S' := by
  classical
  intro x hx
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨i, ⟨hi, hj⟩, rfl⟩ := hx
  exact ⟨i, ⟨h hi, hj⟩, rfl⟩

/-- Row images commute with unions. -/
lemma rowImage_union {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S S' : Finset ℕ) :
    rowImage N m π j (S ∪ S') = rowImage N m π j S ∪ rowImage N m π j S' := by
  classical
  ext x
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, ⟨hi | hi, hj⟩, rfl⟩
    · exact Or.inl ⟨i, ⟨hi, hj⟩, rfl⟩
    · exact Or.inr ⟨i, ⟨hi, hj⟩, rfl⟩
  · rintro (⟨i, ⟨hi, hj⟩, rfl⟩ | ⟨i, ⟨hi, hj⟩, rfl⟩)
    · exact ⟨i, ⟨Or.inl hi, hj⟩, rfl⟩
    · exact ⟨i, ⟨Or.inr hi, hj⟩, rfl⟩

/-- Row images of disjoint sets are disjoint. -/
lemma rowImage_disjoint {N m j : ℕ} (π : Equiv.Perm (Fin N)) {S S' : Finset ℕ}
    (h : Disjoint S S') : Disjoint (rowImage N m π j S) (rowImage N m π j S') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and] at hx hx'
  obtain ⟨i, ⟨hi, hji⟩, rfl⟩ := hx
  obtain ⟨i', ⟨hi', hji'⟩, heq⟩ := hx'
  have hii : i = i' := by
    have : (π i).val = (π i').val := by
      have h1 : (π i).val = m * ((π i).val / m) + (π i).val % m := (Nat.div_add_mod _ _).symm
      have h2 : (π i').val = m * ((π i').val / m) + (π i').val % m := (Nat.div_add_mod _ _).symm
      rw [h1, h2, hji, hji', heq]
    exact π.injective (Fin.ext this)
  subst hii
  exact Finset.disjoint_left.mp h hi hi'

/-- The row image of a set difference. -/
lemma rowImage_sdiff {N m j : ℕ} (π : Equiv.Perm (Fin N)) {S J : Finset ℕ}
    (hS : S ⊆ range N) (hJ : J ⊆ range N) :
    rowImage N m π j S \ rowImage N m π j J = rowImage N m π j (S \ J) := by
  classical
  ext x
  simp only [mem_sdiff, rowImage, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, ⟨hi, hj⟩, rfl⟩, hnot⟩
    refine ⟨i, ⟨⟨hi, ?_⟩, hj⟩, rfl⟩
    rintro hiJ
    exact hnot ⟨i, ⟨hiJ, hj⟩, rfl⟩
  · rintro ⟨i, ⟨⟨hi, hiJ⟩, hj⟩, rfl⟩
    refine ⟨⟨i, ⟨hi, hj⟩, rfl⟩, ?_⟩
    rintro ⟨i', ⟨hi', hj'⟩, heq⟩
    have hii : i = i' := by
      have : (π i).val = (π i').val := by
        have h1 : (π i).val = m * ((π i).val / m) + (π i).val % m := (Nat.div_add_mod _ _).symm
        have h2 : (π i').val = m * ((π i').val / m) + (π i').val % m := (Nat.div_add_mod _ _).symm
        rw [h1, h2, hj, hj', heq]
      exact π.injective (Fin.ext this)
    subst hii
    exact hiJ hi'
/-! ### D. Relabelling invariance

The reference placement of Definition 5.5 distributes `D - Y` hint labels and `Y` outside labels
uniformly over `[N]`.  The row statistics of an arbitrary input depend only on the *cardinalities*
of its hint set and of its outside set, because a uniform permutation can be composed with any fixed
relabelling.  This section supplies that relabelling statement. -/

/-- The coordinates of `[N]` that belong to a set of labels. -/
def toFin (N : ℕ) (S : Finset ℕ) : Finset (Fin N) := univ.filter (fun i => i.val ∈ S)

@[simp] lemma mem_toFin {N : ℕ} {S : Finset ℕ} {i : Fin N} : i ∈ toFin N S ↔ i.val ∈ S := by
  simp [toFin]

/-- Relabelling a set of coordinates by a permutation. -/
def permImg (N : ℕ) (τ : Equiv.Perm (Fin N)) (S : Finset ℕ) : Finset ℕ :=
  ((toFin N S).image τ).image (fun i => i.val)

lemma toFin_permImgF {N : ℕ} (T : Finset (Fin N)) :
    toFin N (T.image (fun i => i.val)) = T := by
  classical
  ext i
  simp only [mem_toFin, mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact Fin.ext hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma toFin_permImg {N : ℕ} (τ : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    toFin N (permImg N τ S) = (toFin N S).image τ := by
  rw [permImg, toFin_permImgF]

lemma toFin_image_val {N : ℕ} {S : Finset ℕ} (hS : S ⊆ range N) :
    (toFin N S).image (fun i : Fin N => i.val) = S := by
  classical
  ext x
  simp only [mem_image, mem_toFin]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx; exact ⟨⟨x, Finset.mem_range.mp (hS hx)⟩, hx, rfl⟩

lemma toFin_card {N : ℕ} {S : Finset ℕ} (hS : S ⊆ range N) : (toFin N S).card = S.card := by
  classical
  calc (toFin N S).card = ((toFin N S).image (fun i : Fin N => i.val)).card := by
        rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext h)]
    _ = S.card := by rw [toFin_image_val hS]

lemma toFin_inj {N : ℕ} {S S' : Finset ℕ} (hS : S ⊆ range N) (hS' : S' ⊆ range N)
    (h : toFin N S = toFin N S') : S = S' := by
  rw [← toFin_image_val hS, h, toFin_image_val hS']

lemma permImg_subset {N : ℕ} (τ : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    permImg N τ S ⊆ range N := by
  intro x hx
  simp only [permImg, mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Finset.mem_range.mpr i.isLt

lemma permImg_card {N : ℕ} (τ : Equiv.Perm (Fin N)) {S : Finset ℕ} (hS : S ⊆ range N) :
    (permImg N τ S).card = S.card := by
  classical
  rw [permImg, Finset.card_image_of_injective _ (fun i j h => Fin.ext h),
    Finset.card_image_of_injective _ τ.injective, toFin_card hS]

lemma permImg_comp {N : ℕ} (τ σ : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    permImg N τ (permImg N σ S) = permImg N (τ * σ) S := by
  classical
  rw [permImg, permImg, permImg, toFin_permImgF, Finset.image_image, Finset.image_image,
    Finset.image_image]
  rfl

lemma mem_permImg {N : ℕ} (τ : Equiv.Perm (Fin N)) (S : Finset ℕ) (x : ℕ) :
    x ∈ permImg N τ S ↔ ∃ i : Fin N, i.val ∈ S ∧ (τ i).val = x := by
  classical
  simp only [permImg, mem_image, mem_toFin]
  constructor
  · rintro ⟨k, ⟨i, hi, hik⟩, hkx⟩
    exact ⟨i, hi, by rw [hik]; exact hkx⟩
  · rintro ⟨i, hi, hix⟩
    exact ⟨τ i, ⟨i, hi, rfl⟩, hix⟩

lemma permImg_disjoint {N : ℕ} (τ : Equiv.Perm (Fin N)) {S S' : Finset ℕ}
    (h : Disjoint S S') : Disjoint (permImg N τ S) (permImg N τ S') := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  rw [mem_permImg] at hx hx'
  obtain ⟨i, hi, hix⟩ := hx
  obtain ⟨i', hi', hix'⟩ := hx'
  have hii : i = i' := τ.injective (Fin.ext (hix.trans hix'.symm))
  subst hii
  exact h hi hi'

lemma permImg_eq_self {N : ℕ} (τ : Equiv.Perm (Fin N)) {S : Finset ℕ} (hS : S ⊆ range N)
    (hfix : ∀ i : Fin N, i.val ∈ S → (τ i).val = i.val) : permImg N τ S = S := by
  classical
  have hsub : (toFin N S).image τ ⊆ toFin N S := by
    intro i hi
    simp only [mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [mem_toFin]
    rw [hfix j (mem_toFin.mp hj)]
    exact mem_toFin.mp hj
  have hcard : ((toFin N S).image τ).card = (toFin N S).card :=
    Finset.card_image_of_injective _ τ.injective
  have heq : (toFin N S).image τ = toFin N S :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [permImg, heq, toFin_image_val hS]

/-- Any two sets of equal cardinality are related by a permutation fixing everything outside their
union. -/
lemma exists_perm_image {α : Type} [Fintype α] [DecidableEq α] {S S' : Finset α}
    (h : S.card = S'.card) :
    ∃ τ : Equiv.Perm α, S'.image τ = S ∧ ∀ a, a ∉ S ∪ S' → τ a = a := by
  classical
  -- The two "moving" parts `S' \ S` and `S \ S'` have the same cardinality, because
  -- `S ∩ S'` is common.  We exchange them and fix everything else.
  have hcard : (S' \ S).card = (S \ S').card := by
    have h1 : (S \ S').card + (S ∩ S').card = S.card := Finset.card_sdiff_add_card_inter S S'
    have h2 : (S' \ S).card + (S' ∩ S).card = S'.card := Finset.card_sdiff_add_card_inter S' S
    have h3 : (S ∩ S').card = (S' ∩ S).card := by rw [Finset.inter_comm]
    omega
  let e : {x // x ∈ S' \ S} ≃ {x // x ∈ S \ S'} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcard])
  have hdisj : Disjoint (S' \ S) (S \ S') := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  let f : α → α := fun x =>
    if hx : x ∈ S' \ S then (e ⟨x, hx⟩).val
    else if hx' : x ∈ S \ S' then (e.symm ⟨x, hx'⟩).val
    else x
  have hf1 : ∀ x (hx : x ∈ S' \ S), f x = (e ⟨x, hx⟩).val := by
    intro x hx
    simp only [f]
    rw [dif_pos hx]
  have hf2 : ∀ x (hx : x ∈ S \ S'), f x = (e.symm ⟨x, hx⟩).val := by
    intro x hx
    have hx1 : x ∉ S' \ S := fun hc => Finset.disjoint_left.mp hdisj hc hx
    simp only [f]
    rw [dif_neg hx1, dif_pos hx]
  have hf3 : ∀ x (hx : x ∉ S' \ S) (hx' : x ∉ S \ S'), f x = x := by
    intro x hx hx'
    simp only [f]
    rw [dif_neg hx, dif_neg hx']
  -- `f` is an involution, hence a permutation.
  have hff : ∀ x, f (f x) = x := by
    intro x
    by_cases hC : x ∈ S' \ S
    · have hmem : f x ∈ S \ S' := by rw [hf1 x hC]; exact (e ⟨x, hC⟩).2
      rw [hf2 (f x) hmem]
      have hsub : (⟨f x, hmem⟩ : {y // y ∈ S \ S'}) = e ⟨x, hC⟩ := Subtype.ext (hf1 x hC)
      rw [hsub, Equiv.symm_apply_apply]
    · by_cases hA : x ∈ S \ S'
      · have hmem : f x ∈ S' \ S := by rw [hf2 x hA]; exact (e.symm ⟨x, hA⟩).2
        rw [hf1 (f x) hmem]
        have hsub : (⟨f x, hmem⟩ : {y // y ∈ S' \ S}) = e.symm ⟨x, hA⟩ := Subtype.ext (hf2 x hA)
        rw [hsub, Equiv.apply_symm_apply]
      · rw [hf3 x hC hA, hf3 x hC hA]
  have hinv : Function.Involutive f := hff
  set τ : Equiv.Perm α := Equiv.ofBijective f ⟨hinv.injective, hinv.surjective⟩ with hτ
  have hτf : ∀ x, τ x = f x := fun x => Equiv.ofBijective_apply _ _ x
  refine ⟨τ, ?_, ?_⟩
  · have hsub : S'.image τ ⊆ S := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [hτf]
      by_cases hC : x ∈ S' \ S
      · have hmem : f x ∈ S \ S' := by rw [hf1 x hC]; exact (e ⟨x, hC⟩).2
        exact (Finset.mem_sdiff.mp hmem).1
      · have hxS : x ∈ S := by
          by_contra hxS
          exact hC (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
        have hA : x ∉ S \ S' := fun hc => (Finset.mem_sdiff.mp hc).2 hx
        rw [hf3 x hC hA]
        exact hxS
    have hc : (S'.image τ).card = S.card := by
      rw [Finset.card_image_of_injective _ τ.injective, h]
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hc.symm)
  · intro a ha
    rw [hτf]
    refine hf3 a ?_ ?_
    · intro hc
      exact ha (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp hc).1))
    · intro hc
      exact ha (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hc).1))
/-- The relabelled-set version of `exists_perm_image`. -/
lemma exists_perm_permImg {N : ℕ} {S S' : Finset ℕ} (hS : S ⊆ range N) (hS' : S' ⊆ range N)
    (h : S.card = S'.card) :
    ∃ τ : Equiv.Perm (Fin N), permImg N τ S' = S ∧
      ∀ i : Fin N, i.val ∉ S ∪ S' → (τ i).val = i.val := by
  classical
  have hc : (toFin N S).card = (toFin N S').card := by
    rw [toFin_card hS, toFin_card hS', h]
  obtain ⟨τ, hτ, hfix⟩ := exists_perm_image hc
  refine ⟨τ, ?_, ?_⟩
  · have h1 : toFin N (permImg N τ S') = toFin N S := by
      rw [toFin_permImg, hτ]
    exact toFin_inj (permImg_subset τ S') hS h1
  · intro i hi
    exact congrArg Fin.val (hfix i (by simpa using hi))

/-- Two disjoint label sets of the prescribed sizes are related by a permutation. -/
lemma exists_perm_permImg_pair {N : ℕ} {A B A' B' : Finset ℕ}
    (hA : A ⊆ range N) (hB : B ⊆ range N) (hA' : A' ⊆ range N) (hB' : B' ⊆ range N)
    (hd : Disjoint A B) (hd' : Disjoint A' B')
    (hcA : A.card = A'.card) (hcB : B.card = B'.card) :
    ∃ τ : Equiv.Perm (Fin N), permImg N τ A' = A ∧ permImg N τ B' = B := by
  classical
  obtain ⟨τ₁, h1, hfix1⟩ := exists_perm_permImg hA hA' hcA
  obtain ⟨τ₂, h2, hfix2⟩ :=
    exists_perm_permImg hB (permImg_subset τ₁ B') (by rw [permImg_card τ₁ hB', hcB])
  have hdisj : Disjoint A (permImg N τ₁ B') := by
    rw [← h1]
    exact permImg_disjoint τ₁ hd'
  refine ⟨τ₂ * τ₁, ?_, ?_⟩
  · rw [← permImg_comp τ₂ τ₁ A', h1]
    refine permImg_eq_self τ₂ hA (fun i hi => hfix2 i ?_)
    intro hmem
    have hnot1 : i.val ∉ permImg N τ₁ B' := fun h => Finset.disjoint_left.mp hdisj hi h
    have hnot2 : i.val ∉ B := fun h => Finset.disjoint_left.mp hd hi h
    rcases Finset.mem_union.mp hmem with h | h
    · exact hnot2 h
    · exact hnot1 h
  · rw [← permImg_comp τ₂ τ₁ B']
    exact h2

/-- The row profile of a pair of label sets, pointwise in the public permutation. -/
def rowProf (P : HintParams) (N X Y s : ℕ) (π : Equiv.Perm (Fin N)) (S1 S2 : Finset ℕ) : ℝ :=
  ∑ j ∈ range (P.rows X Y), G s ((HintParams.sigma (rowImage N (P.rows X Y) π j S1).card
    (rowLen N (P.rows X Y) j) (rowImage N (P.rows X Y) π j S2).card : ℝ) + (P.c N X Y : ℝ))

lemma rowProf_ref (P : HintParams) (N X Y s : ℕ) (π : Equiv.Perm (Fin N)) :
    rowProf P N X Y s π (HintParams.refHintLabels N X Y) (HintParams.refOutLabels N X Y)
      = nodeProfile P N X Y π s := rfl

lemma mem_rowImage' {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) (x : ℕ) :
    x ∈ rowImage N m π j S ↔ ∃ i : Fin N, i.val ∈ S ∧ (π i).val % m = j ∧ (π i).val / m = x := by
  classical
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨hi, h1⟩, h2⟩
    exact ⟨i, hi, h1, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, ⟨hi, h1⟩, h2⟩

/-- The image of a row under a product of permutations. -/
lemma rowImage_mul {N m j : ℕ} (π τ : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    rowImage N m (π * τ) j S = rowImage N m π j (permImg N τ S) := by
  classical
  ext x
  rw [mem_rowImage', mem_rowImage']
  constructor
  · rintro ⟨i, hi, hj, hx⟩
    exact ⟨τ i, by rw [mem_permImg]; exact ⟨i, hi, rfl⟩, hj, hx⟩
  · rintro ⟨k, hk, hj, hx⟩
    rw [mem_permImg] at hk
    obtain ⟨i, hi, hik⟩ := hk
    have hik' : τ i = k := Fin.ext hik
    have hmul : (π * τ) i = π k := by rw [Equiv.Perm.mul_apply, hik']
    refine ⟨i, hi, ?_, ?_⟩
    · rw [hmul]; exact hj
    · rw [hmul]; exact hx

lemma expU_equiv' {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    expU (fun a => f (e a)) = expU f := by
  unfold expU
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

/-- Reindexing the public permutation by a fixed relabelling. -/
lemma expU_rowProf_mul {P : HintParams} {N X Y s : ℕ} (τ : Equiv.Perm (Fin N))
    (S1 S2 : Finset ℕ) :
    expU (fun π : Equiv.Perm (Fin N) => rowProf P N X Y s (π * τ) S1 S2)
      = expU (fun π : Equiv.Perm (Fin N) => rowProf P N X Y s π S1 S2) := by
  classical
  let e : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
    { toFun := fun π => π * τ
      invFun := fun π => π * τ⁻¹
      left_inv := by intro π; simp [mul_assoc]
      right_inv := by intro π; simp [mul_assoc] }
  exact expU_equiv' e (fun π : Equiv.Perm (Fin N) => rowProf P N X Y s π S1 S2)

/-- `G` is monotone in its second (threshold) argument. -/
lemma G_mono {a : ℕ} {z z' : ℝ} (h : z ≤ z') : G a z ≤ G a z' := by
  unfold G
  refine min_le_min le_rfl ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma rowProf_mono {P : HintParams} {N X Y s : ℕ} {S1 S1' S2 S2' : Finset ℕ}
    (h1 : S1 ⊆ S1') (h2 : S2 ⊆ S2') (π : Equiv.Perm (Fin N)) :
    rowProf P N X Y s π S1 S2 ≤ rowProf P N X Y s π S1' S2' := by
  classical
  refine Finset.sum_le_sum (fun j _ => ?_)
  refine G_mono ?_
  have hle1 : (rowImage N (P.rows X Y) π j S1).card
      ≤ (rowImage N (P.rows X Y) π j S1').card :=
    Finset.card_le_card (rowImage_mono π h1)
  have hle2 : (rowImage N (P.rows X Y) π j S2).card
      ≤ (rowImage N (P.rows X Y) π j S2').card :=
    Finset.card_le_card (rowImage_mono π h2)
  have hb1 : (rowImage N (P.rows X Y) π j S1').card ≤ rowLen N (P.rows X Y) j :=
    rowImage_card_le_rowLen π S1'
  have ha : HintParams.sigma (rowImage N (P.rows X Y) π j S1).card
        (rowLen N (P.rows X Y) j) (rowImage N (P.rows X Y) π j S2).card
      ≤ HintParams.sigma (rowImage N (P.rows X Y) π j S1').card
        (rowLen N (P.rows X Y) j) (rowImage N (P.rows X Y) π j S2').card :=
    sigma_mono hle1 hle2 hb1
  have hcast : ((HintParams.sigma (rowImage N (P.rows X Y) π j S1).card
        (rowLen N (P.rows X Y) j) (rowImage N (P.rows X Y) π j S2).card : ℕ) : ℝ)
      ≤ ((HintParams.sigma (rowImage N (P.rows X Y) π j S1').card
        (rowLen N (P.rows X Y) j) (rowImage N (P.rows X Y) π j S2').card : ℕ) : ℝ) := by
    exact_mod_cast ha
  linarith

/-- Finset superset of prescribed cardinality. -/
lemma exists_superset_card {S U : Finset ℕ} {k : ℕ} (hS : S ⊆ U) (hk : S.card ≤ k)
    (hkU : k ≤ U.card) : ∃ T, S ⊆ T ∧ T ⊆ U ∧ T.card = k := by
  classical
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq (s := U \ S) (n := k - S.card) (by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS]
    omega)
  have hT₀U : T₀ ⊆ U := fun x hx => (Finset.mem_sdiff.mp (hT₀sub hx)).1
  have hdisj : Disjoint S T₀ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hT₀sub hx')).2 hx
  refine ⟨S ∪ T₀, Finset.subset_union_left, Finset.union_subset hS hT₀U, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hT₀card]
  omega

/-! ### E. Part 1 of the paper: the means of `U_s` and `V_s`

Lemma 5.6 of the paper, first half (`5hintsketch.tex`): `E U_s ≤ Q_s + D η²` and
`E V_s ≤ 2^{-c} Q_s + D η²`.  The paper sums the per-row prediction bounds of Lemma 5.2 over the
rows, compares the actual input with the reference placement of Definition 5.5 (the candidate family
only grows when hint positions are added and hints are reclassified as outside-hint nonzeros, so
`σ_{j,y_j} ≤ σ_j^*`), and charges the overloaded rows against `E[overloadedMass] ≤ D η²`
(Lemma 5.3).  Second documented deviation from the paper: the paper bounds the probability that a row
is overloaded by the hypergeometric Chernoff machinery of Lemma 5.3 itself; we instead reuse Lemma
5.3's finished bound `E[overloadedMass] ≤ D η²` (`Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_3`)
and only charge each overloaded row one unit per coordinate of `J ∪ supp(x)`. -/

/-! #### E.1 `U_s` and `V_s` as sums of per-row indicators -/

/-- `σ_{j,y_j}`, equation (7), for the actual input in row `j` under the permutation `π`. -/
def actSigma (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (j : ℕ) (x J : Finset ℕ) : ℕ :=
  HintParams.sigma (rowImage N (P.rows X Y) π j J).card (rowLen N (P.rows X Y) j)
    (rowImage N (P.rows X Y) π j x \ rowImage N (P.rows X Y) π j J).card

/-- `U_s` counts the rows that return `⊥`. -/
lemma U_eq_sum_indicator (P : HintParams) (N X Y : ℕ) (lr : (P.scheme N X Y).LocalSeed)
    (x J : Finset ℕ) (s : Fin (P.ell N X Y)) :
    ((P.scheme N X Y).U lr x J s : ℝ)
      = ∑ j : Fin (P.scheme N X Y).m, ind ((P.scheme N X Y).exactPred lr x J s j = none) := by
  classical
  unfold RowScheme.U
  rw [← Finset.sum_boole]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hp : (P.scheme N X Y).exactPred lr x J s a = none <;> simp [ind, hp]

/-- `V_s` counts the rows whose prediction is wrong. -/
lemma V_eq_sum_indicator (P : HintParams) (N X Y : ℕ) (lr : (P.scheme N X Y).LocalSeed)
    (x J : Finset ℕ) (s : Fin (P.ell N X Y)) :
    ((P.scheme N X Y).V lr x J s : ℝ)
      = ∑ j : Fin (P.scheme N X Y).m,
          ind (∃ b, (P.scheme N X Y).exactPred lr x J s j = some b ∧
              b ≠ (P.scheme N X Y).code j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) s) := by
  classical
  unfold RowScheme.V
  rw [← Finset.sum_boole]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hp : ∃ b, (P.scheme N X Y).exactPred lr x J s a = some b ∧
      b ≠ (P.scheme N X Y).code a (lr.2 a) ((P.scheme N X Y).rowOf lr x a) s <;>
    simp [ind, hp]

/-- Averaging a function of the node seed = averaging over the public permutation, then over the
independent row coins. -/
lemma expU_localSeed (P : HintParams) (N X Y : ℕ)
    (F : (P.scheme N X Y).LocalSeed → ℝ) :
    expU F = expU (fun π : Equiv.Perm (Fin N) => expU (fun β => F (π, β))) :=
  expU_prod (f := fun p : Equiv.Perm (Fin N) ×
      (Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand) => F p)

/-- The indicator, on the node seed, that row `j` returns `⊥` (Lemma 5.2's bad event). -/
def predU (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (x J : Finset ℕ)
    (s : Fin (P.ell N X Y)) (j : Fin (P.scheme N X Y).m) (r : (P.scheme N X Y).Rand) : ℝ :=
  ind ((P.scheme N X Y).predict j r (rowImage N (P.rows X Y) π j.val J)
    ((P.scheme N X Y).truePrefix j r (rowImage N (P.rows X Y) π j.val x) s.val) = none)

/-- The indicator, on the node seed, that row `j` predicts wrongly (Lemma 5.2's second event). -/
def predV (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (x J : Finset ℕ)
    (s : Fin (P.ell N X Y)) (j : Fin (P.scheme N X Y).m) (r : (P.scheme N X Y).Rand) : ℝ :=
  ind (∃ b, (P.scheme N X Y).predict j r (rowImage N (P.rows X Y) π j.val J)
      ((P.scheme N X Y).truePrefix j r (rowImage N (P.rows X Y) π j.val x) s.val) = some b ∧
    b ≠ (P.scheme N X Y).code j r (rowImage N (P.rows X Y) π j.val x) s)

/-- The expectation of `U_s` over the node seed: average over the public permutation, then the row
coins, which factorise because every row only uses its own coins. -/
lemma expU_U_split (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (x J : Finset ℕ)
    (s : Fin (P.ell N X Y)) :
    expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).U lr x J s : ℝ))
      = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ j : Fin (P.scheme N X Y).m,
            expU (predU P N X Y π x J s j)) := by
  classical
  have hcardR : 0 < Fintype.card (Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hfun : (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).U lr x J s : ℝ))
      = (fun lr => ∑ j, ind ((P.scheme N X Y).exactPred lr x J s j = none)) := by
    funext lr
    exact U_eq_sum_indicator P N X Y lr x J s
  rw [hfun]
  refine (expU_localSeed P N X Y
    (fun lr => ∑ j, ind ((P.scheme N X Y).exactPred lr x J s j = none))).trans ?_
  apply congrArg expU
  funext π
  rw [expU_finset_sum hcardR Finset.univ
    (fun β (j : Fin (P.scheme N X Y).m) =>
      ind ((P.scheme N X Y).exactPred (π, β) x J s j = none))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpt : (fun β : Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand =>
        ind ((P.scheme N X Y).exactPred (π, β) x J s j = none))
      = (fun β => predU P N X Y π x J s j (β j)) := by
    funext β
    simp only [predU, RowScheme.exactPred, RowScheme.rowOf, RowScheme.truePrefix, HintParams.scheme]
  rw [hpt]
  exact expU_pi_apply j _

/-- The same factorisation for `V_s`. -/
lemma expU_V_split (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (x J : Finset ℕ)
    (s : Fin (P.ell N X Y)) :
    expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).V lr x J s : ℝ))
      = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ j : Fin (P.scheme N X Y).m,
            expU (predV P N X Y π x J s j)) := by
  classical
  have hcardR : 0 < Fintype.card (Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hfun : (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).V lr x J s : ℝ))
      = (fun lr => ∑ j, ind (∃ b, (P.scheme N X Y).exactPred lr x J s j = some b ∧
          b ≠ (P.scheme N X Y).code j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) s)) := by
    funext lr
    exact V_eq_sum_indicator P N X Y lr x J s
  rw [hfun]
  refine (expU_localSeed P N X Y
    (fun lr => ∑ j, ind (∃ b, (P.scheme N X Y).exactPred lr x J s j = some b ∧
      b ≠ (P.scheme N X Y).code j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) s))).trans ?_
  apply congrArg expU
  funext π
  rw [expU_finset_sum hcardR Finset.univ
    (fun β (j : Fin (P.scheme N X Y).m) =>
      ind (∃ b, (P.scheme N X Y).exactPred (π, β) x J s j = some b ∧
        b ≠ (P.scheme N X Y).code j ((π, β).2 j) ((P.scheme N X Y).rowOf (π, β) x j) s))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpt : (fun β : Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand =>
        ind (∃ b, (P.scheme N X Y).exactPred (π, β) x J s j = some b ∧
          b ≠ (P.scheme N X Y).code j ((π, β).2 j) ((P.scheme N X Y).rowOf (π, β) x j) s))
      = (fun β => predV P N X Y π x J s j (β j)) := by
    funext β
    simp only [predV, RowScheme.exactPred, RowScheme.rowOf, RowScheme.truePrefix, HintParams.scheme]
  rw [hpt]
  exact expU_pi_apply j _

/-- The per-row profile summed over `Fin m` is the node profile. -/
lemma sum_fin_rowProf (P : HintParams) (N X Y s : ℕ) (π : Equiv.Perm (Fin N)) :
    (∑ j : Fin (P.scheme N X Y).m, G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)))
      = nodeProfile P N X Y π s := by
  unfold nodeProfile
  exact Fin.sum_univ_eq_sum_range
    (fun i => G s ((P.sigmaStar N X Y π i : ℝ) + (P.c N X Y : ℝ))) ((P.scheme N X Y).m)

/-- The expectation of a sum is the sum of the expectations. -/
lemma expU_add' {α : Type} [Fintype α] (f g : α → ℝ) :
    expU (fun a => f a + g a) = expU f + expU g := by
  unfold expU
  rw [Finset.sum_add_distrib]
  ring

/-- The reference profile reindexed by a relabelling is still `Q_s`. -/
lemma expU_nodeProfile_mul (P : HintParams) {N X Y : ℕ} (s : Fin (P.ell N X Y))
    (τ : Equiv.Perm (Fin N)) :
    expU (fun π : Equiv.Perm (Fin N) => nodeProfile P N X Y (π * τ) s.val)
      = P.Q N X Y s.val := by
  rw [show P.Q N X Y s.val = expU (fun π : Equiv.Perm (Fin N) =>
      rowProf P N X Y s.val π (HintParams.refHintLabels N X Y)
        (HintParams.refOutLabels N X Y)) from Q_eq_expU P N X Y s.val]
  exact expU_rowProf_mul τ _ _

/-! #### E.2 The reference placement of Definition 5.5 -/

/-- The hint labels and the outside-hint labels of the reference placement are disjoint. -/
lemma disjoint_refLabels (N X Y : ℕ) :
    Disjoint (HintParams.refHintLabels N X Y) (HintParams.refOutLabels N X Y) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [HintParams.refHintLabels, HintParams.refOutLabels, Finset.mem_filter,
    Finset.mem_range] at hi hi'
  omega

/-- The reference placement uses all of `[N]` exactly when `D = N`. -/
lemma refLabels_union (N X Y : ℕ) (hD : HintParams.D N X Y = N) :
    HintParams.refHintLabels N X Y ∪ HintParams.refOutLabels N X Y = Finset.range N := by
  classical
  ext i
  simp only [HintParams.refHintLabels, HintParams.refOutLabels, Finset.mem_union,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (⟨hi, -⟩ | ⟨hi, -⟩) <;> exact hi
  · intro hi
    by_cases h : i < HintParams.D N X Y - Y
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨hi, ⟨not_lt.mp h, by omega⟩⟩

/-- When `D = N` every row is saturated in the reference placement: `σ_j^*` is the whole row. -/
lemma sigmaStar_eq_of_D_eq_N (P : HintParams) {N X Y : ℕ}
    (hD : HintParams.D N X Y = N) (π : Equiv.Perm (Fin N)) (j : ℕ) :
    P.sigmaStar N X Y π j = rowLen N (P.rows X Y) j := by
  classical
  have hunion : HintParams.refHintLabels N X Y ∪ HintParams.refOutLabels N X Y = Finset.range N :=
    refLabels_union N X Y hD
  have hcard : (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card
      + (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card
      = rowLen N (P.rows X Y) j := by
    rw [← Finset.card_union_of_disjoint (rowImage_disjoint π (disjoint_refLabels N X Y)),
      ← rowImage_union, hunion, rowImage_range_card]
  have hOle : (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card
      ≤ rowLen N (P.rows X Y) j := rowImage_card_le_rowLen π _
  have hH : (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card
      = rowLen N (P.rows X Y) j
        - (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card := by omega
  have hσ : P.sigmaStar N X Y π j
      = HintParams.sigma (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card
          (rowLen N (P.rows X Y) j)
          (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card := rfl
  rw [hσ, hH]
  have hsat := sigma_sat (a := rowLen N (P.rows X Y) j
      - (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card)
      (n := rowLen N (P.rows X Y) j) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self hOle] at hsat

/-- Paper proof of Lemma 5.6, first documented deviation: the paper "arbitrarily adds hint positions
until `|J ∪ supp(x)| = D`, then reclassifies hints as outside-hint nonzeros until there are `Y`".
When `X + Y ≤ N` this enlargement fits inside `[N]`, and a fixed relabelling carries the reference
placement of Definition 5.5 onto the enlarged pair.  (In the case `X + Y > N` no enlargement is
possible or needed, see `sigmaStar_eq_of_D_eq_N`; this is the same argument.) -/
lemma exists_ref_perm_of_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J) (hXY : X + Y ≤ N) :
    ∃ τ : Equiv.Perm (Fin N), J ⊆ permImg N τ (HintParams.refHintLabels N X Y) ∧
      (x \ J) ⊆ permImg N τ (HintParams.refOutLabels N X Y) := by
  classical
  obtain ⟨hx, hJ, hJc, hyc⟩ := hvalid
  have hD : HintParams.D N X Y = X + Y := by unfold HintParams.D; omega
  have hrefH : (HintParams.refHintLabels N X Y).card = X := by
    unfold HintParams.refHintLabels
    rw [hD]
    have h1 : (Finset.range N).filter (fun i => i < X + Y - Y) = Finset.range X := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [h1, Finset.card_range]
  have hrefO : (HintParams.refOutLabels N X Y).card = Y := by
    unfold HintParams.refOutLabels
    rw [hD]
    have h1 : (Finset.range N).filter (fun i => X + Y - Y ≤ i ∧ i < X + Y)
        = (Finset.range Y).image (fun t => t + X) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hiN, hge, hlt⟩
        exact ⟨i - X, by omega, by omega⟩
      · rintro ⟨t, ht, rfl⟩
        omega
    rw [h1, Finset.card_image_of_injective _ (fun a b hab => Nat.add_right_cancel hab),
      Finset.card_range]
  obtain ⟨A, hyA, hAU, hAcard⟩ := exists_superset_card
    (S := x \ J) (U := Finset.range N \ J) (k := Y)
    (fun a ha => by
      simp only [Finset.mem_sdiff] at ha ⊢
      exact ⟨hx ha.1, ha.2⟩) hyc (by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJ, Finset.card_range]
      omega)
  have hAN : A ⊆ Finset.range N := fun a ha => (Finset.mem_sdiff.mp (hAU ha)).1
  obtain ⟨J'', hJsub, hJ''U, hJ''card⟩ := exists_superset_card
    (S := J) (U := Finset.range N \ A) (k := X)
    (fun a ha => by
      simp only [Finset.mem_sdiff]
      exact ⟨hJ ha, fun hc => (Finset.mem_sdiff.mp (hAU hc)).2 ha⟩) hJc (by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAN, Finset.card_range, hAcard]
      omega)
  have hJ''N : J'' ⊆ Finset.range N := fun a ha => (Finset.mem_sdiff.mp (hJ''U ha)).1
  have hdisj : Disjoint J'' A := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact (Finset.mem_sdiff.mp (hJ''U ha)).2 ha'
  have hHrange : HintParams.refHintLabels N X Y ⊆ Finset.range N :=
    fun a ha => (Finset.mem_filter.mp ha).1
  have hOrange : HintParams.refOutLabels N X Y ⊆ Finset.range N :=
    fun a ha => (Finset.mem_filter.mp ha).1
  obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_permImg_pair (N := N)
    (A := J'') (B := A) (A' := HintParams.refHintLabels N X Y)
    (B' := HintParams.refOutLabels N X Y) hJ''N hAN hHrange hOrange hdisj
    (disjoint_refLabels N X Y) (by rw [hJ''card, hrefH]) (by rw [hAcard, hrefO])
  exact ⟨τ, hJsub.trans (le_of_eq hτ1.symm), hyA.trans (le_of_eq hτ2.symm)⟩

/-! #### E.3 Summing Lemma 5.2 over the rows -/

/-- An overloaded row contains at least one coordinate of `J ∪ supp(x)`, so it costs at least one
unit of `overloadedMass`. -/
lemma overloaded_row_pos (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J) (π : Equiv.Perm (Fin N))
    (j : Fin (P.scheme N X Y).m)
    (hov : P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
      (rowImage N (P.rows X Y) π j.val x)) :
    1 ≤ (rowImage N (P.rows X Y) π j.val (J ∪ x)).card := by
  classical
  obtain ⟨hx, hJ, -, -⟩ := hvalid
  rcases hov with h | h
  · have hpos : 0 < (rowImage N (P.rows X Y) π j.val J).card := by omega
    have hmono : (rowImage N (P.rows X Y) π j.val J).card
        ≤ (rowImage N (P.rows X Y) π j.val (J ∪ x)).card :=
      Finset.card_le_card (rowImage_mono (N := N) (m := P.rows X Y) (j := j.val) π
        (Finset.subset_union_left : J ⊆ J ∪ x))
    omega
  · have hpos : 0 < (rowImage N (P.rows X Y) π j.val x
        \ rowImage N (P.rows X Y) π j.val J).card := by omega
    rw [rowImage_sdiff (N := N) (m := P.rows X Y) (j := j.val) π hx hJ] at hpos
    have hsub : x \ J ⊆ J ∪ x := fun a ha =>
      Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp ha).1)
    have hmono : (rowImage N (P.rows X Y) π j.val (x \ J)).card
        ≤ (rowImage N (P.rows X Y) π j.val (J ∪ x)).card :=
      Finset.card_le_card (rowImage_mono (N := N) (m := P.rows X Y) (j := j.val) π hsub)
    omega

/-- Deviation from the paper, case `X + Y ≤ N`: the actual row statistics are dominated by the
reference profile, because the coupling of `exists_ref_perm_of_le` only adds coordinates. -/
lemma G_row_le_case_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J) (hXY : X + Y ≤ N)
    (τ : Equiv.Perm (Fin N)) (hJsub : J ⊆ permImg N τ (HintParams.refHintLabels N X Y))
    (hxsub : x \ J ⊆ permImg N τ (HintParams.refOutLabels N X Y))
    (π : Equiv.Perm (Fin N)) (s : Fin (P.ell N X Y)) (j : Fin (P.scheme N X Y).m) :
    G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ))
      ≤ G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)) := by
  classical
  obtain ⟨hx, hJ, -, -⟩ := hvalid
  refine G_mono ?_
  dsimp only [actSigma, HintParams.sigmaStar]
  have h1 : (rowImage N (P.rows X Y) π j.val J).card
      ≤ (rowImage N (P.rows X Y) (π * τ) j.val (HintParams.refHintLabels N X Y)).card := by
    rw [rowImage_mul]
    exact Finset.card_le_card (rowImage_mono π hJsub)
  have h2 : (rowImage N (P.rows X Y) π j.val x \ rowImage N (P.rows X Y) π j.val J).card
      ≤ (rowImage N (P.rows X Y) (π * τ) j.val (HintParams.refOutLabels N X Y)).card := by
    rw [rowImage_sdiff (N := N) (m := P.rows X Y) (j := j.val) π hx hJ, rowImage_mul]
    exact Finset.card_le_card (rowImage_mono π hxsub)
  have h3 : (rowImage N (P.rows X Y) (π * τ) j.val (HintParams.refHintLabels N X Y)).card
      ≤ rowLen N (P.rows X Y) j.val := rowImage_card_le_rowLen (π * τ) _
  have h4 := sigma_mono h1 h2 h3
  have hcast : ((HintParams.sigma (rowImage N (P.rows X Y) π j.val J).card
        (rowLen N (P.rows X Y) j.val)
        (rowImage N (P.rows X Y) π j.val x \ rowImage N (P.rows X Y) π j.val J).card : ℕ) : ℝ)
      ≤ ((HintParams.sigma (rowImage N (P.rows X Y) (π * τ) j.val
        (HintParams.refHintLabels N X Y)).card (rowLen N (P.rows X Y) j.val)
        (rowImage N (P.rows X Y) (π * τ) j.val (HintParams.refOutLabels N X Y)).card : ℕ) : ℝ) := by
    exact_mod_cast h4
  linarith

/-- Deviation from the paper, case `X + Y > N`: then `D = N`, the reference placement fills `[N]`,
and `sigma_sat` gives `σ_j^* = ` the row length, so no coupling is needed at all. -/
lemma G_row_le_case_gt (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) (hXY : N < X + Y)
    {x J : Finset ℕ} (π : Equiv.Perm (Fin N)) (s : Fin (P.ell N X Y))
    (j : Fin (P.scheme N X Y).m) :
    G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ))
      ≤ G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) := by
  classical
  have hD : HintParams.D N X Y = N := by unfold HintParams.D; omega
  have hσ : P.sigmaStar N X Y π j = rowLen N (P.rows X Y) j.val :=
    sigmaStar_eq_of_D_eq_N P hD π j.val
  rw [hσ]
  refine G_mono ?_
  dsimp only [actSigma]
  have h1 : HintParams.sigma (rowImage N (P.rows X Y) π j.val J).card
      (rowLen N (P.rows X Y) j.val)
      (rowImage N (P.rows X Y) π j.val x \ rowImage N (P.rows X Y) π j.val J).card
      ≤ rowLen N (P.rows X Y) j.val := sigma_le (rowImage_card_le_rowLen π J)
  have hcast : ((HintParams.sigma (rowImage N (P.rows X Y) π j.val J).card
      (rowLen N (P.rows X Y) j.val)
      (rowImage N (P.rows X Y) π j.val x \ rowImage N (P.rows X Y) π j.val J).card : ℕ) : ℝ)
      ≤ ((rowLen N (P.rows X Y) j.val : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- Core estimate of Part 1: the sum over the rows of the per-row prediction bound.  `ρ = 1` is
`E U_s` (Lemma 5.2, first conjunct) and `ρ = 2^{-c}` is `E V_s` (second conjunct).  Overloaded rows
are charged against `overloadedMass`, exactly as in the paper's
`E U_s ≤ ∑_j (E[G_{s-1}(σ_{j,y_j}+c)] + Pr[j overloaded])`, with `Pr[j overloaded]` paid for by
Lemma 5.3's `E[overloadedMass] ≤ D η²` (the second documented deviation). -/
lemma sum_expU_row_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J) (s : Fin (P.ell N X Y))
    (π : Equiv.Perm (Fin N)) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (f : Fin (P.scheme N X Y).m → (P.scheme N X Y).Rand → ℝ)
    (hf1 : ∀ j r, f j r ≤ 1)
    (hfreg : ∀ j, ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x) →
      expU (f j) ≤ ρ * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)))
    (g : Fin (P.scheme N X Y).m → ℝ) (hg0 : ∀ j, 0 ≤ g j)
    (hg : ∀ j, ρ * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) ≤ g j) :
    (∑ j : Fin (P.scheme N X Y).m, expU (f j))
      ≤ (∑ j : Fin (P.scheme N X Y).m, g j) + (P.overloadedMass N X Y π x J : ℝ) := by
  classical
  have hcardR : 0 < Fintype.card (P.scheme N X Y).Rand := Fintype.card_pos_iff.mpr inferInstance
  have hmass : (∑ j : Fin (P.scheme N X Y).m,
      (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
          (rowImage N (P.rows X Y) π j.val x)
        then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0))
      = (P.overloadedMass N X Y π x J : ℝ) := by
    have h1 : (P.overloadedMass N X Y π x J : ℝ)
        = ∑ i ∈ Finset.range (P.rows X Y),
            (if P.Overloaded N X Y (rowImage N (P.rows X Y) π i J)
                (rowImage N (P.rows X Y) π i x)
              then ((rowImage N (P.rows X Y) π i (J ∪ x)).card : ℝ) else 0) := by
      unfold HintParams.overloadedMass
      push_cast
      rfl
    rw [h1]
    exact Fin.sum_univ_eq_sum_range (fun i =>
      (if P.Overloaded N X Y (rowImage N (P.rows X Y) π i J)
          (rowImage N (P.rows X Y) π i x)
        then ((rowImage N (P.rows X Y) π i (J ∪ x)).card : ℝ) else 0)) (P.rows X Y)
  have hrow : ∀ j : Fin (P.scheme N X Y).m, expU (f j) ≤ g j +
      (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x)
       then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0) := by
    intro j
    by_cases hov : P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x)
    · have h1 : expU (f j) ≤ 1 := by
        refine le_trans (expU_mono_card hcardR (fun r => hf1 j r)) ?_
        exact le_of_eq (expU_const hcardR 1)
      have h2 : (1 : ℝ) ≤ ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) := by
        exact_mod_cast overloaded_row_pos P hargs hvalid π j hov
      rw [if_pos hov]
      linarith [hg0 j]
    · have h1 : expU (f j) ≤ ρ * G s.val
          ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := hfreg j hov
      have h2 : ρ * G s.val
          ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) ≤ g j := hg j
      rw [if_neg hov]
      linarith
  calc (∑ j : Fin (P.scheme N X Y).m, expU (f j))
      ≤ ∑ j : Fin (P.scheme N X Y).m, (g j +
          (if P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
              (rowImage N (P.rows X Y) π j.val x)
            then ((rowImage N (P.rows X Y) π j.val (J ∪ x)).card : ℝ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hrow j)
    _ = (∑ j : Fin (P.scheme N X Y).m, g j) + (P.overloadedMass N X Y π x J : ℝ) := by
        rw [Finset.sum_add_distrib, hmass]

open Classical in
/-- **Lemma 5.6, first bound, as in the paper.**  `E U_s ≤ Q_s + D η²`: the sum over the rows of
Lemma 5.2's bound on the probability of returning `⊥`, compared with the reference placement
(Definition 5.5), plus the `D η²` slack of the overloaded rows (Lemma 5.3), with `Q_s` of
equation (19). -/
lemma expU_U_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J)
    (s : Fin (P.ell N X Y))
    (hmass : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2) :
    expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).U lr x J s : ℝ))
      ≤ P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
  classical
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hcardP : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_pos N
  rw [expU_U_split P hN1 x J s]
  have key : ∀ (τ : Equiv.Perm (Fin N)) (prof : Equiv.Perm (Fin N) → ℝ),
      (∀ π : Equiv.Perm (Fin N), (∑ j : Fin (P.scheme N X Y).m,
          expU (predU P N X Y π x J s j)) ≤ prof π + (P.overloadedMass N X Y π x J : ℝ)) →
      (∀ π, prof π = nodeProfile P N X Y (π * τ) s.val) →
      expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predU P N X Y π x J s j))
        ≤ P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
    intro τ prof hpt hprof
    have h1 : expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predU P N X Y π x J s j))
        ≤ expU (fun π : Equiv.Perm (Fin N) =>
            prof π + (P.overloadedMass N X Y π x J : ℝ)) :=
      expU_mono_card hcardP hpt
    have h2 : expU (fun π : Equiv.Perm (Fin N) =>
          prof π + (P.overloadedMass N X Y π x J : ℝ))
        = expU prof + expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) :=
      expU_add' _ _
    have h3 : expU prof = P.Q N X Y s.val := by
      have hfun : prof = (fun π : Equiv.Perm (Fin N) => nodeProfile P N X Y (π * τ) s.val) :=
        funext hprof
      rw [hfun]
      exact expU_nodeProfile_mul P s τ
    calc expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predU P N X Y π x J s j))
        ≤ expU (fun π : Equiv.Perm (Fin N) =>
            prof π + (P.overloadedMass N X Y π x J : ℝ)) := h1
      _ = expU prof + expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) := h2
      _ ≤ P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
          rw [h3]
          linarith
  by_cases hXY : X + Y ≤ N
  · obtain ⟨τ, hJsub, hxsub⟩ := exists_ref_perm_of_le P hargs hvalid hXY
    refine key τ (fun π => nodeProfile P N X Y (π * τ) s.val) ?_ (fun _ => rfl)
    intro π
    have hf1 : ∀ j r, predU P N X Y π x J s j r ≤ 1 := fun j r => ind_le_one _
    have hfreg : ∀ j, ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x) →
        expU (predU P N X Y π x J s j)
          ≤ 1 * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := by
      intro j hreg
      have h52 := (lemma_5_2 P N X Y hargs (Or.inl hrule) j
        (rowImage N (P.rows X Y) π j.val J) (rowImage N (P.rows X Y) π j.val x)
        (rowImage_subset_rowLen π J) (rowImage_subset_rowLen π x) hreg s).1
      rw [prU_eq_avg] at h52
      have h52' : expU (predU P N X Y π x J s j)
          ≤ G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := h52
      simpa only [one_mul] using h52'
    have hg0 : ∀ j : Fin (P.scheme N X Y).m,
        0 ≤ G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)) :=
      fun j => G_nonneg _ _
    have hg : ∀ j : Fin (P.scheme N X Y).m,
        1 * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ))
          ≤ G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)) := by
      intro j
      rw [one_mul]
      exact G_row_le_case_le P hargs hvalid hXY τ hJsub hxsub π s j
    have hcore := sum_expU_row_le P hargs hvalid s π 1 zero_le_one
      (predU P N X Y π x J s) hf1 hfreg
      (fun j => G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ))) hg0 hg
    rw [sum_fin_rowProf] at hcore
    exact hcore
  · have hgt : N < X + Y := by omega
    refine key 1 (fun π => nodeProfile P N X Y π s.val) ?_ (fun π => by rw [mul_one])
    intro π
    have hf1 : ∀ j r, predU P N X Y π x J s j r ≤ 1 := fun j r => ind_le_one _
    have hfreg : ∀ j, ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x) →
        expU (predU P N X Y π x J s j)
          ≤ 1 * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := by
      intro j hreg
      have h52 := (lemma_5_2 P N X Y hargs (Or.inl hrule) j
        (rowImage N (P.rows X Y) π j.val J) (rowImage N (P.rows X Y) π j.val x)
        (rowImage_subset_rowLen π J) (rowImage_subset_rowLen π x) hreg s).1
      rw [prU_eq_avg] at h52
      have h52' : expU (predU P N X Y π x J s j)
          ≤ G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := h52
      simpa only [one_mul] using h52'
    have hg0 : ∀ j : Fin (P.scheme N X Y).m,
        0 ≤ G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) :=
      fun j => G_nonneg _ _
    have hg : ∀ j : Fin (P.scheme N X Y).m,
        1 * G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ))
          ≤ G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) := by
      intro j
      rw [one_mul]
      exact G_row_le_case_gt P hargs hrule hgt π s j
    have hcore := sum_expU_row_le P hargs hvalid s π 1 zero_le_one
      (predU P N X Y π x J s) hf1 hfreg
      (fun j => G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))) hg0 hg
    rw [sum_fin_rowProf] at hcore
    exact hcore

open Classical in
/-- **Lemma 5.6, second bound, as in the paper.**  `E V_s ≤ 2^{-c} Q_s + D η²`: the same summation,
using Lemma 5.2's wrong-prediction bound, which carries the extra factor `2^{-c}`. -/
lemma expU_V_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J)
    (s : Fin (P.ell N X Y))
    (hmass : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2) :
    expU (fun lr : (P.scheme N X Y).LocalSeed => ((P.scheme N X Y).V lr x J s : ℝ))
      ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
        + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
  classical
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hcardP : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_pos N
  have hρ0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ := by positivity
  rw [expU_V_split P hN1 x J s]
  have key : ∀ (τ : Equiv.Perm (Fin N)) (prof : Equiv.Perm (Fin N) → ℝ),
      (∀ π : Equiv.Perm (Fin N), (∑ j : Fin (P.scheme N X Y).m,
          expU (predV P N X Y π x J s j))
            ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π
              + (P.overloadedMass N X Y π x J : ℝ)) →
      (∀ π, prof π = nodeProfile P N X Y (π * τ) s.val) →
      expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predV P N X Y π x J s j))
        ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
          + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
    intro τ prof hpt hprof
    have h1 : expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predV P N X Y π x J s j))
        ≤ expU (fun π : Equiv.Perm (Fin N) =>
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π + (P.overloadedMass N X Y π x J : ℝ)) :=
      expU_mono_card hcardP hpt
    have h2 : expU (fun π : Equiv.Perm (Fin N) =>
          ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π + (P.overloadedMass N X Y π x J : ℝ))
        = expU (fun π : Equiv.Perm (Fin N) => ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π)
          + expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) :=
      expU_add' _ _
    have h3 : expU (fun π : Equiv.Perm (Fin N) => ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π)
        = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val := by
      have hfun : prof = (fun π : Equiv.Perm (Fin N) => nodeProfile P N X Y (π * τ) s.val) :=
        funext hprof
      rw [hfun, expU_mul_const hcardP, expU_nodeProfile_mul P s τ]
    calc expU (fun π : Equiv.Perm (Fin N) => ∑ j : Fin (P.scheme N X Y).m,
          expU (predV P N X Y π x J s j))
        ≤ expU (fun π : Equiv.Perm (Fin N) =>
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π + (P.overloadedMass N X Y π x J : ℝ)) := h1
      _ = expU (fun π : Equiv.Perm (Fin N) => ((2 : ℝ) ^ (P.c N X Y))⁻¹ * prof π)
          + expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) := h2
      _ ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
          + (HintParams.D N X Y : ℝ) * P.eta ^ 2 := by
          rw [h3]
          linarith
  by_cases hXY : X + Y ≤ N
  · obtain ⟨τ, hJsub, hxsub⟩ := exists_ref_perm_of_le P hargs hvalid hXY
    refine key τ (fun π => nodeProfile P N X Y (π * τ) s.val) ?_ (fun _ => rfl)
    intro π
    have hf1 : ∀ j r, predV P N X Y π x J s j r ≤ 1 := fun j r => ind_le_one _
    have hfreg : ∀ j, ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x) →
        expU (predV P N X Y π x J s j)
          ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
            G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := by
      intro j hreg
      have h52 := (lemma_5_2 P N X Y hargs (Or.inl hrule) j
        (rowImage N (P.rows X Y) π j.val J) (rowImage N (P.rows X Y) π j.val x)
        (rowImage_subset_rowLen π J) (rowImage_subset_rowLen π x) hreg s).2
      rw [prU_eq_avg] at h52
      have h52' : expU (predV P N X Y π x J s j)
          ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
            G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := h52
      exact h52'
    have hmul : (∑ j : Fin (P.scheme N X Y).m, ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
          G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)))
        = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ j : Fin (P.scheme N X Y).m,
          G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ))) :=
      (Finset.mul_sum (s := Finset.univ) (f := fun j : Fin (P.scheme N X Y).m =>
        G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)))
        ((2 : ℝ) ^ (P.c N X Y))⁻¹).symm
    have hcore := sum_expU_row_le P hargs hvalid s π ((2 : ℝ) ^ (P.c N X Y))⁻¹ hρ0
      (predV P N X Y π x J s) hf1 hfreg
      (fun j => ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
        G s.val ((P.sigmaStar N X Y (π * τ) j : ℝ) + (P.c N X Y : ℝ)))
      (fun j => mul_nonneg hρ0 (G_nonneg _ _))
      (fun j => mul_le_mul_of_nonneg_left
        (G_row_le_case_le P hargs hvalid hXY τ hJsub hxsub π s j) hρ0)
    rw [hmul, sum_fin_rowProf] at hcore
    exact hcore
  · have hgt : N < X + Y := by omega
    refine key 1 (fun π => nodeProfile P N X Y π s.val) ?_ (fun π => by rw [mul_one])
    intro π
    have hf1 : ∀ j r, predV P N X Y π x J s j r ≤ 1 := fun j r => ind_le_one _
    have hfreg : ∀ j, ¬ P.Overloaded N X Y (rowImage N (P.rows X Y) π j.val J)
        (rowImage N (P.rows X Y) π j.val x) →
        expU (predV P N X Y π x J s j)
          ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
            G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := by
      intro j hreg
      have h52 := (lemma_5_2 P N X Y hargs (Or.inl hrule) j
        (rowImage N (P.rows X Y) π j.val J) (rowImage N (P.rows X Y) π j.val x)
        (rowImage_subset_rowLen π J) (rowImage_subset_rowLen π x) hreg s).2
      rw [prU_eq_avg] at h52
      have h52' : expU (predV P N X Y π x J s j)
          ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
            G s.val ((actSigma P N X Y π j.val x J : ℝ) + (P.c N X Y : ℝ)) := h52
      exact h52'
    have hmul : (∑ j : Fin (P.scheme N X Y).m, ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
          G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)))
        = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ j : Fin (P.scheme N X Y).m,
          G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))) :=
      (Finset.mul_sum (s := Finset.univ) (f := fun j : Fin (P.scheme N X Y).m =>
        G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)))
        ((2 : ℝ) ^ (P.c N X Y))⁻¹).symm
    have hcore := sum_expU_row_le P hargs hvalid s π ((2 : ℝ) ^ (P.c N X Y))⁻¹ hρ0
      (predV P N X Y π x J s) hf1 hfreg
      (fun j => ((2 : ℝ) ^ (P.c N X Y))⁻¹ *
        G s.val ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)))
      (fun j => mul_nonneg hρ0 (G_nonneg _ _))
      (fun j => mul_le_mul_of_nonneg_left
        (G_row_le_case_gt P hargs hrule hgt π s j) hρ0)
    rw [hmul, sum_fin_rowProf] at hcore
    exact hcore

/-! ### F. Part 2 of the paper: the 2^{-λ*} tails

Equation (19) defines the capacities as the means plus the margin `2 η (D+1)`.  Since `U_s, V_s ≤ Y`
and `capX, capY ≤ Y`, the event `capX < U_s` forces `U_s > E U_s + η(D+1)`; Lemma 4.8
(concentration) then gives `Pr ≤ exp(-2 η² (D+1)²/(5D))`, and the third stopping rule
(`C³ λ* log⁶ n / η² < D`) gives `exp(-2 η² (D+1)²/(5D)) ≤ 2^{-λ*}`. -/

/-! #### F.1 The child rows live inside `[N_max]` -/

/-- A candidate family of row `j` only contains subsets of `range N_j`. -/
lemma family_subset_powerset {ℓ K Nj : ℕ} (β : Fin ℓ → Fin K → ZMod 2) (Jj : Finset ℕ) (r : ℕ)
    (z : List (ZMod 2)) : HintParams.family Nj β Jj r z ⊆ (Finset.range Nj).powerset := by
  intro C hC
  simp only [HintParams.family, Finset.mem_filter] at hC
  exact hC.1

/-- The member selected by `head?` is a subset of `range N_j`. -/
lemma getD_head_subset {Nj : ℕ} {U : Finset (Finset ℕ)}
    (hU : U ⊆ (Finset.range Nj).powerset) :
    (U.toList.head?).getD ∅ ⊆ Finset.range Nj := by
  cases hUl : U.toList with
  | nil => simpa using (Finset.empty_subset (Finset.range Nj))
  | cons C l =>
      have hC : C ∈ U := by rw [← Finset.mem_toList, hUl]; exact List.mem_cons_self ..
      simpa using Finset.mem_powerset.mp (hU hC)

/-- The final row recovery returns a subset of the row `[N_j]`. -/
lemma workerFinal_subset_range {N m ℓ K BX BY : ℕ} (j : Fin m)
    (β : Fin ℓ → Fin K → ZMod 2) (Jj : Finset ℕ) (z : List (ZMod 2)) :
    HintParams.workerFinal N m ℓ K BX BY j β Jj z ⊆ Finset.range (rowLen N m j.val) := by
  classical
  unfold HintParams.workerFinal
  dsimp only
  split_ifs with h1 h2
  · exact Finset.empty_subset _
  · exact getD_head_subset (fun C hC => by
      simp only [Finset.mem_biUnion, Finset.mem_range] at hC
      obtain ⟨r, -, hr⟩ := hC
      exact family_subset_powerset β Jj r z hr)
  · exact Finset.empty_subset _

/-- Lemma 4.8 applies with `K = N_max`: every row estimate is a subset of `[N_j] ⊆ [N_max]`. -/
lemma exactRowEst_card_le_Nmax (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) (x J : Finset ℕ)
    (lr : (P.scheme N X Y).LocalSeed) (j : Fin (P.rows X Y)) :
    ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.Nmax N X Y := by
  classical
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hrows : P.rows X Y = Y := rows_eq_of_rule hrule
  have hm1 : 0 < P.rows X Y := by rw [hrows]; exact Y_ge_one hargs (one_le_lgn hn2) hrule
  have hsub : (P.scheme N X Y).exactRowEst lr x J j
      ⊆ Finset.range (rowLen N (P.rows X Y) j.val) := by
    unfold RowScheme.exactRowEst
    exact workerFinal_subset_range j (lr.2 j) _ _
  have h1 : ((P.scheme N X Y).exactRowEst lr x J j).card ≤ rowLen N (P.rows X Y) j.val := by
    simpa using Finset.card_le_card hsub
  have h2 : rowLen N (P.rows X Y) j.val ≤ P.Nmax N X Y := by
    rw [HintParams.Nmax]
    exact rowLen_le_ceil (N := N) (m := P.rows X Y) (j := j.val) hm1
  exact le_trans h1 h2

/-- The margin of equation (19) gives the `2^{-λ*}` tail, by the third stopping rule. -/
lemma exp_margin_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) (hC : 2 ≤ P.C) :
    Real.exp (-(2 * (P.eta * ((HintParams.D N X Y : ℝ) + 1)) ^ 2
        / (5 * (HintParams.D N X Y : ℝ))))
      ≤ ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hL : 1 ≤ P.lgn := one_le_lgn hn2
  have heta0 : 0 < P.eta := by unfold HintParams.eta; positivity
  have heta2 : (0 : ℝ) < P.eta ^ 2 := by positivity
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL hrule
  have hDY : Y ≤ HintParams.D N X Y := by unfold HintParams.D; omega
  have hDpos : (0 : ℝ) < (HintParams.D N X Y : ℝ) := by
    have h : 0 < HintParams.D N X Y := by omega
    exact_mod_cast h
  have hNth : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
      < (HintParams.D N X Y : ℝ) := Nthresh_lt hrule
  have hkey : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6
      < P.eta ^ 2 * (HintParams.D N X Y : ℝ) := by
    have h' : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 * P.eta ^ 2
        < (HintParams.D N X Y : ℝ) * P.eta ^ 2 :=
      mul_lt_mul_of_pos_right hNth heta2
    rw [div_mul_cancel₀ _ (ne_of_gt heta2)] at h'
    linarith [h']
  have hC2 : (2 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast hC
  have hC3 : Real.log 2 ≤ (2 / 5) * (P.C : ℝ) ^ 3 * P.lgn ^ 6 := by
    have h1 : (2 : ℝ) ^ 3 ≤ (P.C : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hC2 3
    have h6 : (1 : ℝ) ≤ P.lgn ^ 6 := one_le_pow₀ hL
    have hlog : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [h1, h6]
  have hmain : (P.lamStar : ℝ) * Real.log 2
      ≤ 2 * (P.eta * ((HintParams.D N X Y : ℝ) + 1)) ^ 2
        / (5 * (HintParams.D N X Y : ℝ)) := by
    have hlam0 : (0 : ℝ) ≤ (P.lamStar : ℝ) := by positivity
    have hstep1 : (P.lamStar : ℝ) * Real.log 2
        ≤ (P.lamStar : ℝ) * ((2 / 5) * (P.C : ℝ) ^ 3 * P.lgn ^ 6) :=
      mul_le_mul_of_nonneg_left hC3 hlam0
    have hstep2 : (P.lamStar : ℝ) * ((2 / 5) * (P.C : ℝ) ^ 3 * P.lgn ^ 6)
        = (2 / 5) * ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6) := by ring
    have hstep3 : (2 / 5) * ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6)
        ≤ (2 / 5) * (P.eta ^ 2 * (HintParams.D N X Y : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hkey) (by norm_num)
    have hstep4 : (2 / 5) * (P.eta ^ 2 * (HintParams.D N X Y : ℝ))
        ≤ 2 * (P.eta * ((HintParams.D N X Y : ℝ) + 1)) ^ 2
          / (5 * (HintParams.D N X Y : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (HintParams.D N X Y : ℝ))]
      nlinarith [hDpos, heta2, sq_nonneg ((HintParams.D N X Y : ℝ)),
        sq_nonneg ((HintParams.D N X Y : ℝ) + 1)]
    linarith
  calc Real.exp (-(2 * (P.eta * ((HintParams.D N X Y : ℝ) + 1)) ^ 2
        / (5 * (HintParams.D N X Y : ℝ))))
      ≤ Real.exp (-((P.lamStar : ℝ) * Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = ((2 : ℝ) ^ P.lamStar)⁻¹ := by
        rw [← Real.rpow_natCast (2 : ℝ) P.lamStar,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring

/-! #### F.2 The two tails -/

open Classical in
/-- **Lemma 5.6, third bound, as in the paper.**  `Pr[capX < U_s] ≤ 2^{-λ*}` by Lemma 4.8
(concentration) with `Δ = η(D+1)`, the margin in `capX` (equation (19)), and the third stopping
rule. -/
lemma capX_tail (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J)
    (s : Fin (P.ell N X Y))
    (hmass : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2)
    (hC : 2 ≤ P.C) :
    prU (fun lr : (P.scheme N X Y).LocalSeed => P.capX N X Y s.val < (P.scheme N X Y).U lr x J s)
      ≤ ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  classical
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hL : 1 ≤ P.lgn := one_le_lgn hn2
  have heta0 : 0 < P.eta := by unfold HintParams.eta; positivity
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL hrule
  have hrows : P.rows X Y = Y := rows_eq_of_rule hrule
  have hDY : Y ≤ HintParams.D N X Y := by unfold HintParams.D; omega
  have hm1 : 1 ≤ (P.scheme N X Y).m := by
    show 1 ≤ P.rows X Y
    rw [hrows]; exact hY1
  have hDm : (P.scheme N X Y).m ≤ HintParams.D N X Y := by
    show P.rows X Y ≤ HintParams.D N X Y
    rw [hrows]; exact hDY
  have hDJ : (J ∪ x).card ≤ HintParams.D N X Y := by
    have hun : J ∪ x ⊆ Finset.range N := Finset.union_subset hvalid.2.1 hvalid.1
    have h1 : (J ∪ x).card ≤ N := by
      simpa using Finset.card_le_card hun
    have h2 : (J ∪ x).card ≤ X + Y := by
      have hsplit : J ∪ x = J ∪ (x \ J) := by
        ext a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hsplit, Finset.card_union_of_disjoint (Finset.disjoint_sdiff)]
      exact Nat.add_le_add hvalid.2.2.1 hvalid.2.2.2
    unfold HintParams.D
    omega
  have hK : 1 ≤ P.Nmax N X Y := by
    rw [HintParams.Nmax]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hmpos : (0 : ℝ) < (P.rows X Y : ℝ) := by
      have h : 0 < P.rows X Y := by rw [hrows]; omega
      exact_mod_cast h
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr (div_pos hNpos hmpos))
  have hest : ∀ (lr : (P.scheme N X Y).LocalSeed) (j : Fin (P.scheme N X Y).m),
      ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.Nmax N X Y :=
    fun lr j => exactRowEst_card_le_Nmax P hargs hrule x J lr j
  have h48 := (lemma_4_8 (P.scheme N X Y) x J hvalid.1 hvalid.2.1 hm1 (HintParams.D N X Y) hDm hDJ
    (P.Nmax N X Y) hK hest (P.eta * ((HintParams.D N X Y : ℝ) + 1))
    (by positivity)).1 s
  refine le_trans (prU_mono' (fun lr hlt => ?_)) (le_trans h48 (exp_margin_le P hargs hrule hC))
  have hUY : (P.scheme N X Y).U lr x J s ≤ Y := by
    have h1 : (P.scheme N X Y).U lr x J s ≤ (P.scheme N X Y).m := by
      unfold RowScheme.U
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun j => (P.scheme N X Y).exactPred lr x J s j = none) Finset.univ)
    have h2 : (P.scheme N X Y).m = Y := by
      show P.rows X Y = Y
      exact hrows
    omega
  have hexpU := expU_U_le P hargs hrule hvalid s hmass
  have he1 : P.eta ≤ 1 := by
    have h1 : (1 : ℝ) ≤ P.lgn ^ P.A := one_le_pow₀ hL
    have h2 : (0 : ℝ) < P.lgn ^ P.A := lt_of_lt_of_le zero_lt_one h1
    unfold HintParams.eta
    rw [inv_eq_one_div, div_le_one h2]
    simpa using h1
  have hDη : (HintParams.D N X Y : ℝ) * P.eta ^ 2
      ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
    have hDnn : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := Nat.cast_nonneg _
    have h1 : P.eta ^ 2 ≤ P.eta := by
      have h := mul_le_mul_of_nonneg_left he1 heta0.le
      simpa [pow_two, mul_one] using h
    have h2 : (HintParams.D N X Y : ℝ) * P.eta ^ 2
        ≤ (HintParams.D N X Y : ℝ) * P.eta := mul_le_mul_of_nonneg_left h1 hDnn
    have h3 : (HintParams.D N X Y : ℝ) * P.eta
        ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by nlinarith [heta0]
    linarith
  by_cases hcap : Y ≤ ⌈P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊
  · have hcapEq : P.capX N X Y s.val = Y := by
      unfold HintParams.capX
      rw [min_eq_left hcap]
    rw [hcapEq] at hlt
    omega
  · have hlt' : ⌈P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ < Y :=
      not_le.mp hcap
    have hcapEq : P.capX N X Y s.val
        = ⌈P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ := by
      unfold HintParams.capX
      rw [min_eq_right (le_of_lt hlt')]
    rw [hcapEq] at hlt
    have hceil : P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)
        ≤ ((⌈P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hcast : ((⌈P.Q N X Y s.val + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < ((P.scheme N X Y).U lr x J s : ℝ) := by exact_mod_cast hlt
    linarith

open Classical in
/-- **Lemma 5.6, fourth bound, as in the paper.**  `Pr[capY < V_s] ≤ 2^{-λ*}` by Lemma 4.8
(concentration) with `Δ = η(D+1)`. -/
lemma capY_tail (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrule : P.rule N X Y = .recursive) {x J : Finset ℕ} (hvalid : Node.Valid N X Y x J)
    (s : Fin (P.ell N X Y))
    (hmass : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2)
    (hC : 2 ≤ P.C) :
    prU (fun lr : (P.scheme N X Y).LocalSeed => P.capY N X Y s.val < (P.scheme N X Y).V lr x J s)
      ≤ ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  classical
  have hargs' : P.NodeArgs N X Y := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hL : 1 ≤ P.lgn := one_le_lgn hn2
  have heta0 : 0 < P.eta := by unfold HintParams.eta; positivity
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL hrule
  have hrows : P.rows X Y = Y := rows_eq_of_rule hrule
  have hDY : Y ≤ HintParams.D N X Y := by unfold HintParams.D; omega
  have hm1 : 1 ≤ (P.scheme N X Y).m := by
    show 1 ≤ P.rows X Y
    rw [hrows]; exact hY1
  have hDm : (P.scheme N X Y).m ≤ HintParams.D N X Y := by
    show P.rows X Y ≤ HintParams.D N X Y
    rw [hrows]; exact hDY
  have hDJ : (J ∪ x).card ≤ HintParams.D N X Y := by
    have hun : J ∪ x ⊆ Finset.range N := Finset.union_subset hvalid.2.1 hvalid.1
    have h1 : (J ∪ x).card ≤ N := by
      simpa using Finset.card_le_card hun
    have h2 : (J ∪ x).card ≤ X + Y := by
      have hsplit : J ∪ x = J ∪ (x \ J) := by
        ext a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hsplit, Finset.card_union_of_disjoint (Finset.disjoint_sdiff)]
      exact Nat.add_le_add hvalid.2.2.1 hvalid.2.2.2
    unfold HintParams.D
    omega
  have hK : 1 ≤ P.Nmax N X Y := by
    rw [HintParams.Nmax]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hmpos : (0 : ℝ) < (P.rows X Y : ℝ) := by
      have h : 0 < P.rows X Y := by rw [hrows]; omega
      exact_mod_cast h
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr (div_pos hNpos hmpos))
  have hest : ∀ (lr : (P.scheme N X Y).LocalSeed) (j : Fin (P.scheme N X Y).m),
      ((P.scheme N X Y).exactRowEst lr x J j).card ≤ P.Nmax N X Y :=
    fun lr j => exactRowEst_card_le_Nmax P hargs hrule x J lr j
  have h48 := (lemma_4_8 (P.scheme N X Y) x J hvalid.1 hvalid.2.1 hm1 (HintParams.D N X Y) hDm hDJ
    (P.Nmax N X Y) hK hest (P.eta * ((HintParams.D N X Y : ℝ) + 1))
    (by positivity)).2.1 s
  refine le_trans (prU_mono' (fun lr hlt => ?_)) (le_trans h48 (exp_margin_le P hargs hrule hC))
  have hVY : (P.scheme N X Y).V lr x J s ≤ Y := by
    have h1 : (P.scheme N X Y).V lr x J s ≤ (P.scheme N X Y).m := by
      unfold RowScheme.V
      simpa using Finset.card_le_card (Finset.filter_subset
        (fun j => ∃ b, (P.scheme N X Y).exactPred lr x J s j = some b ∧
          b ≠ (P.scheme N X Y).code j (lr.2 j) ((P.scheme N X Y).rowOf lr x j) s) Finset.univ)
    have h2 : (P.scheme N X Y).m = Y := by
      show P.rows X Y = Y
      exact hrows
    omega
  have hexpV := expU_V_le P hargs hrule hvalid s hmass
  have he1 : P.eta ≤ 1 := by
    have h1 : (1 : ℝ) ≤ P.lgn ^ P.A := one_le_pow₀ hL
    have h2 : (0 : ℝ) < P.lgn ^ P.A := lt_of_lt_of_le zero_lt_one h1
    unfold HintParams.eta
    rw [inv_eq_one_div, div_le_one h2]
    simpa using h1
  have hDη : (HintParams.D N X Y : ℝ) * P.eta ^ 2
      ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
    have hDnn : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := Nat.cast_nonneg _
    have h1 : P.eta ^ 2 ≤ P.eta := by
      have h := mul_le_mul_of_nonneg_left he1 heta0.le
      simpa [pow_two, mul_one] using h
    have h2 : (HintParams.D N X Y : ℝ) * P.eta ^ 2
        ≤ (HintParams.D N X Y : ℝ) * P.eta := mul_le_mul_of_nonneg_left h1 hDnn
    have h3 : (HintParams.D N X Y : ℝ) * P.eta
        ≤ P.eta * ((HintParams.D N X Y : ℝ) + 1) := by nlinarith [heta0]
    linarith
  by_cases hcap : Y ≤ ⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
      + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊
  · have hcapEq : P.capY N X Y s.val = Y := by
      unfold HintParams.capY
      rw [min_eq_left hcap]
    rw [hcapEq] at hlt
    omega
  · have hlt' : ⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
        + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ < Y := not_le.mp hcap
    have hcapEq : P.capY N X Y s.val
        = ⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ := by
      unfold HintParams.capY
      rw [min_eq_right (le_of_lt hlt')]
    rw [hcapEq] at hlt
    have hceil : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
        + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)
        ≤ ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hcast : ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < ((P.scheme N X Y).V lr x J s : ℝ) := by exact_mod_cast hlt
    linarith

/-! #### F.3 Lemma 5.6 -/

/-- Lemma 5.6 (Sufficient child capacities), PDF p.23 (printed p.22).  `A`, then `C`, are
sufficiently large.  The source's column `s` is `s + 1` here. -/
theorem lemma_5_6 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        ∀ s : Fin sch.ℓ,
          expU (fun lr : sch.LocalSeed => (sch.U lr x J s : ℝ)) ≤
            P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          expU (fun lr : sch.LocalSeed => (sch.V lr x J s : ℝ)) ≤
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          prU (fun lr : sch.LocalSeed => P.capX N X Y s.val < sch.U lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed => P.capY N X Y s.val < sch.V lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  classical
  obtain ⟨A₃, hA₃⟩ := lemma_5_3
  refine ⟨max A₃ 100, ?_⟩
  intro A hA
  obtain ⟨C₃, hC₃⟩ := hA₃ A (le_trans (le_max_left _ _) hA)
  refine ⟨max C₃ 40, ?_⟩
  intro C hC
  have hCA : C₃ ≤ C := le_trans (le_max_left _ _) hC
  have hC40 : 40 ≤ C := le_trans (le_max_right _ _) hC
  intro n lam N X Y
  dsimp only
  set P : HintParams := ⟨A, C, n, lam⟩ with hP
  intro hargs hrule x J hvalid s
  have hmass : expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ))
      ≤ (HintParams.D N X Y : ℝ) * P.eta ^ 2 :=
    (hC₃ C hCA n lam N X Y hargs (Or.inl hrule)).2 x J hvalid
  have hC2 : 2 ≤ P.C := by
    rw [hP]
    show 2 ≤ C
    omega
  exact ⟨expU_U_le P hargs hrule hvalid s hmass,
    expU_V_le P hargs hrule hvalid s hmass,
    capX_tail P hargs hrule hvalid s hmass hC2,
    capY_tail P hargs hrule hvalid s hmass hC2⟩

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 5.6 (sufficient child capacities) — submission wrapper. -/
theorem solution :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        ∀ s : Fin sch.ℓ,
          expU (fun lr : sch.LocalSeed => (sch.U lr x J s : ℝ)) ≤
            P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          expU (fun lr : sch.LocalSeed => (sch.V lr x J s : ℝ)) ≤
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          prU (fun lr : sch.LocalSeed => P.capX N X Y s.val < sch.U lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed => P.capY N X Y s.val < sch.V lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ :=
  LinearSetReconciliation327.Main.lemma_5_6




