-- Prove2me | solution 1 for InventoryControl.rq_discrete_optimal_R
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T23:29:34.699029+00:00
-- url     : https://prove2.me/submissions/d244e542-69cc-4bb7-b296-5973b8f9fac3

import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

open Finset

/-- Increment identity: `g(k+1) - g(k) = -b₁ + (h+b₁) P(D(L) ≤ k)`. -/
lemma ic5_g_succ (D : DiscreteDemand) (h b1 : ℝ) (k : ℤ) :
    sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k = -b1 + (h + b1) * D.cdf k := by
  have hS : ∑ j ∈ Icc (1 : ℤ) (k + 1), (j : ℝ) * D.p (k + 1 - j).toNat
      = D.cdf k + ∑ j ∈ Icc (1 : ℤ) k, (j : ℝ) * D.p (k - j).toNat := by
    have h1 : ∑ j ∈ Icc (1 : ℤ) (k + 1), (j : ℝ) * D.p (k + 1 - j).toNat
        = ∑ j ∈ Icc (1 : ℤ) (k + 1), D.p (k + 1 - j).toNat
          + ∑ j ∈ Icc (1 : ℤ) (k + 1), ((j : ℝ) - 1) * D.p (k + 1 - j).toNat := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; ring
    have h2 : ∑ j ∈ Icc (1 : ℤ) (k + 1), D.p (k + 1 - j).toNat = D.cdf k := by
      unfold DiscreteDemand.cdf
      apply sum_nbij' (fun j => k + 1 - j) (fun j => k + 1 - j)
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a _; ring
      · intro a _; ring
      · intro a _; rfl
    have h3 : ∑ j ∈ Icc (1 : ℤ) (k + 1), ((j : ℝ) - 1) * D.p (k + 1 - j).toNat
        = ∑ j ∈ Icc (0 : ℤ) k, (j : ℝ) * D.p (k - j).toNat := by
      apply sum_nbij' (fun j => j - 1) (fun j => j + 1)
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a _; ring
      · intro a _; ring
      · intro a _
        have : k + 1 - a = k - (a - 1) := by ring
        rw [this]; push_cast; ring
    have h4 : ∑ j ∈ Icc (1 : ℤ) k, (j : ℝ) * D.p (k - j).toNat
        = ∑ j ∈ Icc (0 : ℤ) k, (j : ℝ) * D.p (k - j).toNat := by
      apply sum_subset
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a ha hn
        simp only [mem_Icc] at ha hn
        have : a = 0 := by omega
        subst this; simp
    rw [h1, h2, h3, h4]
  unfold sPolicyCost
  rw [hS]; push_cast; ring

lemma ic5_cdf_mono (D : DiscreteDemand) {a b : ℤ} (hab : a ≤ b) : D.cdf a ≤ D.cdf b := by
  unfold DiscreteDemand.cdf
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx; simp only [mem_Icc] at hx ⊢; omega
  · intro i _ _; exact D.nonneg _

lemma ic5_cdf_nat (D : DiscreteDemand) (n : ℕ) :
    D.cdf n = ∑ i ∈ range (n + 1), D.p i := by
  unfold DiscreteDemand.cdf
  apply sum_nbij' (fun (j : ℤ) => j.toNat) (fun (i : ℕ) => (i : ℤ))
  · intro a ha; simp only [mem_Icc, mem_range] at ha ⊢; omega
  · intro a ha; simp only [mem_Icc, mem_range] at ha ⊢; omega
  · intro a ha; simp only [mem_Icc] at ha; simp; omega
  · intro a _; simp
  · intro a _; rfl

/-- Increments of `g` are monotone. -/
lemma ic5_d_mono (D : DiscreteDemand) (h b1 : ℝ) (hpos : 0 ≤ h + b1) {a b : ℤ} (hab : a ≤ b) :
    sPolicyCost D h b1 (a + 1) - sPolicyCost D h b1 a
      ≤ sPolicyCost D h b1 (b + 1) - sPolicyCost D h b1 b := by
  rw [ic5_g_succ, ic5_g_succ]
  have := ic5_cdf_mono D hab
  nlinarith

/-- The window sum `W(R, Q) = ∑_{k=R+1}^{R+Q} g(k)`. -/
noncomputable def ic5W (D : DiscreteDemand) (h b1 : ℝ) (R : ℤ) (Q : ℕ) : ℝ :=
  ∑ j ∈ range Q, sPolicyCost D h b1 (R + 1 + j)

lemma ic5_cost_eq (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    rqDiscreteCost D h b1 A μ R Q = (A * μ + ic5W D h b1 R Q) / Q := by
  unfold rqDiscreteCost ic5W
  have : (Q : ℝ) ≠ 0 := by positivity
  field_simp

lemma ic5_W_le_iff (D : DiscreteDemand) (h b1 A μ : ℝ) (R R' : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    rqDiscreteCost D h b1 A μ R Q ≤ rqDiscreteCost D h b1 A μ R' Q
      ↔ ic5W D h b1 R Q ≤ ic5W D h b1 R' Q := by
  rw [ic5_cost_eq D h b1 A μ R Q hQ, ic5_cost_eq D h b1 A μ R' Q hQ]
  have : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [div_le_div_iff_of_pos_right this]
  constructor <;> intro h <;> linarith

lemma ic5_W_shift (D : DiscreteDemand) (h b1 : ℝ) (R : ℤ) (Q : ℕ) :
    ic5W D h b1 (R + 1) Q - ic5W D h b1 R Q
      = ∑ j ∈ range Q, (sPolicyCost D h b1 (R + 1 + j + 1) - sPolicyCost D h b1 (R + 1 + j)) := by
  unfold ic5W
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro j _
  have : R + 1 + 1 + (j : ℤ) = R + 1 + j + 1 := by ring
  rw [this]

lemma ic5_W_succ_right (D : DiscreteDemand) (h b1 : ℝ) (R : ℤ) (Q : ℕ) :
    ic5W D h b1 R (Q + 1) = ic5W D h b1 R Q + sPolicyCost D h b1 (R + Q + 1) := by
  unfold ic5W
  rw [sum_range_succ]
  have : R + 1 + ((Q : ℕ) : ℤ) = R + Q + 1 := by ring
  rw [this]

lemma ic5_W_succ_left (D : DiscreteDemand) (h b1 : ℝ) (R : ℤ) (Q : ℕ) :
    ic5W D h b1 R (Q + 1) = sPolicyCost D h b1 (R + 1) + ic5W D h b1 (R + 1) Q := by
  unfold ic5W
  rw [sum_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [add_comm]
  congr 1
  apply sum_congr rfl; intro j _
  congr 1; ring

section Window

variable (D : DiscreteDemand) (h b1 : ℝ) (hpos : 0 ≤ h + b1) (Q : ℕ) (hQ : 0 < Q) (Rs : ℤ)
  (hW : ∀ R : ℤ, ic5W D h b1 Rs Q ≤ ic5W D h b1 R Q)
include hpos hQ hW

/-- Right of the optimal window, `g` is nondecreasing: `d(k) ≥ 0` for `k ≥ R* + Q`. -/
lemma ic5_d_nonneg_right (k : ℤ) (hk : Rs + Q ≤ k) :
    0 ≤ sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k := by
  have h1 := hW (Rs + 1)
  have h2 := ic5_W_shift D h b1 Rs Q
  have h3 : ∑ j ∈ range Q, (sPolicyCost D h b1 (Rs + 1 + j + 1) - sPolicyCost D h b1 (Rs + 1 + j))
      ≤ ∑ j ∈ range Q, (sPolicyCost D h b1 (Rs + Q + 1) - sPolicyCost D h b1 (Rs + Q)) := by
    apply sum_le_sum; intro j hj
    simp only [mem_range] at hj
    apply ic5_d_mono D h b1 hpos; omega
  rw [sum_const, card_range, nsmul_eq_mul] at h3
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h4 : 0 ≤ sPolicyCost D h b1 (Rs + Q + 1) - sPolicyCost D h b1 (Rs + Q) := by
    by_contra hc; push Not at hc; nlinarith
  exact le_trans h4 (ic5_d_mono D h b1 hpos hk)

/-- Left of the optimal window, `g` is nonincreasing: `d(k) ≤ 0` for `k ≤ R*`. -/
lemma ic5_d_nonpos_left (k : ℤ) (hk : k ≤ Rs) :
    sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k ≤ 0 := by
  have h1 := hW (Rs - 1)
  have h2 := ic5_W_shift D h b1 (Rs - 1) Q
  have h3 : ∑ j ∈ range Q, (sPolicyCost D h b1 (Rs + 1) - sPolicyCost D h b1 Rs)
      ≤ ∑ j ∈ range Q, (sPolicyCost D h b1 (Rs - 1 + 1 + j + 1)
          - sPolicyCost D h b1 (Rs - 1 + 1 + j)) := by
    apply sum_le_sum; intro j _
    apply ic5_d_mono D h b1 hpos; omega
  rw [sum_const, card_range, nsmul_eq_mul] at h3
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e : Rs - 1 + 1 = Rs := by ring
  rw [e] at h2 h3
  have h4 : sPolicyCost D h b1 (Rs + 1) - sPolicyCost D h b1 Rs ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  exact le_trans (ic5_d_mono D h b1 hpos hk) h4

lemma ic5_g_mono_right (t : ℕ) :
    sPolicyCost D h b1 (Rs + Q + 1) ≤ sPolicyCost D h b1 (Rs + Q + 1 + t) := by
  induction t with
  | zero => simp
  | succ n ih =>
    have := ic5_d_nonneg_right D h b1 hpos Q hQ Rs hW (Rs + Q + 1 + n) (by omega)
    have e : Rs + Q + 1 + ((n + 1 : ℕ) : ℤ) = Rs + Q + 1 + n + 1 := by push_cast; ring
    rw [e]; linarith

lemma ic5_g_anti_left (t : ℕ) :
    sPolicyCost D h b1 Rs ≤ sPolicyCost D h b1 (Rs - t) := by
  induction t with
  | zero => simp
  | succ n ih =>
    have := ic5_d_nonpos_left D h b1 hpos Q hQ Rs hW (Rs - (n + 1 : ℕ)) (by omega)
    have e : Rs - ((n + 1 : ℕ) : ℤ) + 1 = Rs - n := by push_cast; ring
    rw [e] at this; linarith

/-- The best window of `Q+1` positions costs at least the best window of `Q` plus the cheaper
neighbour. -/
lemma ic5_W_lower (R : ℤ) :
    ic5W D h b1 Rs Q + min (sPolicyCost D h b1 Rs) (sPolicyCost D h b1 (Rs + Q + 1))
      ≤ ic5W D h b1 R (Q + 1) := by
  rcases le_or_gt Rs R with hR | hR
  · rw [ic5_W_succ_right]
    have h1 := hW R
    have h2 := ic5_g_mono_right D h b1 hpos Q hQ Rs hW (R - Rs).toNat
    have e : Rs + Q + 1 + (((R - Rs).toNat : ℕ) : ℤ) = R + Q + 1 := by omega
    rw [e] at h2
    have := min_le_right (sPolicyCost D h b1 Rs) (sPolicyCost D h b1 (Rs + Q + 1))
    linarith
  · rw [ic5_W_succ_left]
    have h1 := hW (R + 1)
    have h2 := ic5_g_anti_left D h b1 hpos Q hQ Rs hW (Rs - (R + 1)).toNat
    have e : Rs - (((Rs - (R + 1)).toNat : ℕ) : ℤ) = R + 1 := by omega
    rw [e] at h2
    have := min_le_left (sPolicyCost D h b1 Rs) (sPolicyCost D h b1 (Rs + Q + 1))
    linarith

end Window

/-- The recursion target: the window of the next `R` is the optimal window plus the cheaper
neighbour. -/
lemma ic5_W_next (D : DiscreteDemand) (h b1 : ℝ) (Q : ℕ) (Rs : ℤ) :
    ic5W D h b1 (if sPolicyCost D h b1 Rs ≤ sPolicyCost D h b1 (Rs + Q + 1) then Rs - 1 else Rs)
        (Q + 1)
      = ic5W D h b1 Rs Q + min (sPolicyCost D h b1 Rs) (sPolicyCost D h b1 (Rs + Q + 1)) := by
  split_ifs with hc
  · rw [ic5_W_succ_left, min_eq_left hc]
    have e : Rs - 1 + 1 = Rs := by ring
    rw [e]; ring
  · rw [ic5_W_succ_right, min_eq_right (le_of_lt (not_le.mp hc))]

/-- Eq. (5.60). -/
lemma ic5_cost_diff (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    rqDiscreteCost D h b1 A μ (R + 1) Q - rqDiscreteCost D h b1 A μ R Q
      = -b1 + (h + b1) * rqDiscreteReadyRate D (R + 1) Q := by
  rw [ic5_cost_eq D h b1 A μ _ Q hQ, ic5_cost_eq D h b1 A μ _ Q hQ]
  have h1 := ic5_W_shift D h b1 R Q
  have h2 : ∑ j ∈ range Q, (sPolicyCost D h b1 (R + 1 + j + 1) - sPolicyCost D h b1 (R + 1 + j))
      = ∑ j ∈ range Q, (-b1 + (h + b1) * D.cdf (R + 1 + j)) :=
    sum_congr rfl (fun j _ => ic5_g_succ D h b1 _)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at h2
  unfold rqDiscreteReadyRate
  have hQ' : (Q : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination h1.trans h2

lemma ic5_ready_mono (D : DiscreteDemand) (Q : ℕ) (hQ : 0 < Q) {a b : ℤ} (hab : a ≤ b) :
    rqDiscreteReadyRate D a Q ≤ rqDiscreteReadyRate D b Q := by
  unfold rqDiscreteReadyRate
  have hQ' : (0 : ℝ) ≤ 1 / Q := by positivity
  apply mul_le_mul_of_nonneg_left _ hQ'
  apply sum_le_sum; intro j _
  apply ic5_cdf_mono; omega

lemma ic5_cdf_eventually (D : DiscreteDemand) {c : ℝ} (hc : c < 1) : ∃ N : ℕ, c < D.cdf N := by
  have ht := D.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (Ioi_mem_nhds hc))
  exact ⟨N, by rw [ic5_cdf_nat]; exact hN (N + 1) (by omega)⟩

/-- Eq. (5.61): the ready-rate condition characterizes an optimal reorder point. -/
lemma ic5_opt_of_ready (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar : ℤ)
    (hlo : rqDiscreteReadyRate D Rstar Q ≤ b1 / (h + b1))
    (hhi : b1 / (h + b1) < rqDiscreteReadyRate D (Rstar + 1) Q) :
    ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q := by
  have hpos : 0 < h + b1 := by linarith
  have hc : (h + b1) * (b1 / (h + b1)) = b1 := by field_simp
  have up : ∀ t : ℕ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ (Rstar + t) Q := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hd := ic5_cost_diff D h b1 A μ (Rstar + n) Q hQ
      have hm := ic5_ready_mono D Q hQ (show Rstar + 1 ≤ Rstar + n + 1 by omega)
      have e : Rstar + ((n + 1 : ℕ) : ℤ) = Rstar + n + 1 := by push_cast; ring
      rw [e]
      nlinarith
  have down : ∀ t : ℕ,
      rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ (Rstar - t) Q := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hd := ic5_cost_diff D h b1 A μ (Rstar - (n + 1 : ℕ)) Q hQ
      have hm := ic5_ready_mono D Q hQ (show Rstar - ((n + 1 : ℕ) : ℤ) + 1 ≤ Rstar by omega)
      have e : Rstar - ((n + 1 : ℕ) : ℤ) + 1 = Rstar - n := by push_cast; ring
      rw [e] at hd hm
      nlinarith
  intro R
  rcases le_or_gt Rstar R with hR | hR
  · have := up (R - Rstar).toNat
    have e : Rstar + (((R - Rstar).toNat : ℕ) : ℤ) = R := by omega
    rwa [e] at this
  · have := down (Rstar - R).toNat
    have e : Rstar - (((Rstar - R).toNat : ℕ) : ℤ) = R := by omega
    rwa [e] at this

/-- The smaller of the two neighbours of the window `{X+1, …, X+Q}`. -/
noncomputable def ic5m (D : DiscreteDemand) (h b1 : ℝ) (Q : ℕ) (X : ℤ) : ℝ :=
  min (sPolicyCost D h b1 X) (sPolicyCost D h b1 (X + Q + 1))

/-- The reorder point of the recursion (6.6). -/
noncomputable def ic5next (D : DiscreteDemand) (h b1 : ℝ) (Q : ℕ) (X : ℤ) : ℤ :=
  if sPolicyCost D h b1 X ≤ sPolicyCost D h b1 (X + Q + 1) then X - 1 else X

section Marginal

variable (D : DiscreteDemand) (h b1 : ℝ) (hpos : 0 ≤ h + b1) (Q : ℕ) (hQ : 0 < Q)
include hpos hQ

lemma ic5_next_opt (X : ℤ) (hX : ∀ R : ℤ, ic5W D h b1 X Q ≤ ic5W D h b1 R Q) :
    ∀ R : ℤ, ic5W D h b1 (ic5next D h b1 Q X) (Q + 1) ≤ ic5W D h b1 R (Q + 1) := by
  intro R
  unfold ic5next; rw [ic5_W_next]
  exact ic5_W_lower D h b1 hpos Q hQ X hX R

lemma ic5_W_value (X Y : ℤ) (hX : ∀ R : ℤ, ic5W D h b1 X Q ≤ ic5W D h b1 R Q)
    (hY : ∀ R : ℤ, ic5W D h b1 Y (Q + 1) ≤ ic5W D h b1 R (Q + 1)) :
    ic5W D h b1 Y (Q + 1) = ic5W D h b1 X Q + ic5m D h b1 Q X := by
  apply le_antisymm
  · have := hY (ic5next D h b1 Q X)
    unfold ic5next at this; rw [ic5_W_next] at this
    exact this
  · exact ic5_W_lower D h b1 hpos Q hQ X hX Y

lemma ic5_m_le (X Y : ℤ) (hX : ∀ R : ℤ, ic5W D h b1 X Q ≤ ic5W D h b1 R Q)
    (hY : ∀ R : ℤ, ic5W D h b1 Y Q ≤ ic5W D h b1 R Q) :
    ic5m D h b1 Q X ≤ ic5m D h b1 Q Y := by
  have h1 := ic5_W_lower D h b1 hpos Q hQ X hX (ic5next D h b1 Q Y)
  have h2 := ic5_W_next D h b1 Q Y
  have h3 := hX Y
  have h4 := hY X
  unfold ic5next at h1
  unfold ic5m
  linarith

lemma ic5_m_step (X : ℤ) (hX : ∀ R : ℤ, ic5W D h b1 X Q ≤ ic5W D h b1 R Q) :
    ic5m D h b1 Q X ≤ ic5m D h b1 (Q + 1) (ic5next D h b1 Q X) := by
  unfold ic5m ic5next
  split_ifs with hc
  · rw [min_eq_left hc]
    have h1 := ic5_g_anti_left D h b1 hpos Q hQ X hX 1
    have e : X - 1 + ((Q + 1 : ℕ) : ℤ) + 1 = X + Q + 1 := by push_cast; ring
    rw [e]; push_cast at h1
    exact le_min h1 hc
  · have hc' := le_of_lt (not_le.mp hc)
    rw [min_eq_right hc']
    have h1 := ic5_g_mono_right D h b1 hpos Q hQ X hX 1
    have e : X + ((Q + 1 : ℕ) : ℤ) + 1 = X + Q + 1 + ((1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact le_min hc' h1

end Marginal

end InventoryControl

open InventoryControl

theorem solution (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar : ℤ)
    (hlo : rqDiscreteReadyRate D Rstar Q ≤ b1 / (h + b1))
    (hhi : b1 / (h + b1) < rqDiscreteReadyRate D (Rstar + 1) Q) :
    ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q :=
  ic5_opt_of_ready D h b1 A μ hh hb Q hQ Rstar hlo hhi
