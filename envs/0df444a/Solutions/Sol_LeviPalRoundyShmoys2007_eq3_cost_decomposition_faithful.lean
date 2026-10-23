-- Prove2me | solution 1 for LeviPalRoundyShmoys2007.eq3_cost_decomposition_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:14:06.413356+00:00
-- url     : https://prove2.me/submissions/c8cbdf73-edc8-444e-a3ea-71afe6eaa9b7

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model

open LeviBalancing.DualBalancing Finset

namespace LV85

theorem pos_step (u q : ℝ) (hq : 0 ≤ q) :
    max (u + q) 0 = max u 0 + max (q - max (-u) 0) 0 := by
  rcases le_total 0 u with hu | hu
  · rw [max_eq_left hu, max_eq_right (by linarith : -u ≤ 0), sub_zero, max_eq_left hq,
      max_eq_left (by linarith)]
  · rw [max_eq_right hu, max_eq_left (by linarith : 0 ≤ -u), zero_add, sub_neg_eq_add, add_comm]

theorem Ico_succ (a b : ℤ) (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) := by
  ext x; simp only [mem_Ico, mem_insert]; omega

theorem tele_pos (f : ℤ → ℝ) (c D : ℝ) (a : ℤ) (n : ℕ)
    (hf : ∀ t ∈ Ico a (a + n), 0 ≤ f t) :
    max (c + ∑ i ∈ Ico a (a + n), f i - D) 0 = max (c - D) 0 +
      ∑ t ∈ Ico a (a + n), max (f t - max (D - (c + ∑ i ∈ Ico a t, f i)) 0) 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have e : a + ((m + 1 : ℕ) : ℤ) = (a + m) + 1 := by push_cast; ring
    rw [e, Ico_succ _ _ (by omega), sum_insert (by simp), sum_insert (by simp)]
    have hm : ∀ t ∈ Ico a (a + m), 0 ≤ f t := fun t ht => hf t (by
      rw [e, Ico_succ _ _ (by omega)]; exact mem_insert_of_mem ht)
    have hlast : 0 ≤ f (a + m) := hf _ (by rw [e, Ico_succ _ _ (by omega)]; exact mem_insert_self _ _)
    have ih' := ih hm
    rw [show c + (f (a + m) + ∑ i ∈ Ico a (a + m), f i) - D =
      c + ∑ i ∈ Ico a (a + m), f i - D + f (a + m) by ring, pos_step _ _ hlast, ih',
      show -(c + ∑ i ∈ Ico a (a + m), f i - D) = D - (c + ∑ i ∈ Ico a (a + m), f i) by ring]
    ring

theorem cum_split (d : ℤ → ℝ) (t j : ℤ) (h : t ≤ j + 1) :
    cumDemand d t j + cumDemand d 1 (t - 1) = cumDemand d 1 j := by
  unfold cumDemand
  rcases le_or_gt t 1 with ht | ht
  · rw [max_eq_right ht, max_self, Finset.Icc_eq_empty (a := (1:ℤ)) (b := t - 1) (by omega),
      sum_empty, add_zero]
  · rw [max_eq_left ht.le, max_self, ← sum_union]
    · congr 1; ext x; simp only [mem_union, mem_Icc]; omega
    · rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc] at h1 h2; omega

end LV85

open LV85 in
theorem solution (I : Instance) (d Q : ℤ → ℝ)
    (hL : I.L ≤ I.T) (hQ : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ Q t) :
    ∑ t ∈ Finset.Icc (1 : ℤ) (I.T : ℤ), periodCost I d Q t =
      ∑ t ∈ Finset.Icc (1 - (I.L : ℤ)) 0, marginalBacklog I d Q t + initialHolding I d +
        marginalCost I d Q := by
  set L : ℤ := (I.L : ℤ) with hLdef
  set T : ℤ := (I.T : ℤ) with hTdef
  have hLT : L ≤ T := by simp only [L, T]; exact_mod_cast hL
  have hL0 : 0 ≤ L := by simp only [L]; positivity
  set ord := order I Q
  set S : ℤ → ℝ := fun t => I.ni0 + ∑ i ∈ Ico (1 - L) t, ord i
  set Dj : ℤ → ℝ := fun j => cumDemand d 1 j
  have hord : ∀ t, 1 - L ≤ t → t ≤ T → 0 ≤ ord t := by
    intro t h1 h2
    simp only [ord, order]
    split_ifs with h
    · exact I.q_nonneg t h1 h
    · exact hQ t (by omega) h2
  -- net inventory
  have hNI : ∀ j, netInventory I d Q j = S (j - L + 1) - Dj j := by
    intro j
    simp only [netInventory, S, Dj]
    congr 2
  let G : ℤ → ℤ → ℝ := fun t j => I.h j * max (ord t - max (Dj j - S t) 0) 0
  -- holding decomposition for each period
  have hhold : ∀ j ∈ Icc 1 T, I.h j * max (netInventory I d Q j) 0 =
      I.h j * max (I.ni0 - Dj j) 0 + ∑ t ∈ Icc (1 - L) (j - L), G t j := by
    intro j hj
    rw [mem_Icc] at hj
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg (by omega)⟩
    have e1 : j - L + 1 = (1 - L) + n := by omega
    have e2 : Icc (1 - L) (j - L) = Ico (1 - L) ((1 - L) + n) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hNI, e1, e2]
    simp only [S, G]
    rw [tele_pos ord I.ni0 (Dj j) (1 - L) n (fun t ht => by
      rw [mem_Ico] at ht; exact hord t ht.1 (by omega)), mul_add, mul_sum]
  -- backlog reindexing
  have hback : ∀ j ∈ Icc 1 T, I.p j * max (-netInventory I d Q j) 0 =
      marginalBacklog I d Q (j - L) := by
    intro j hj
    rw [mem_Icc] at hj
    simp only [marginalBacklog, invPositionAfter, invPosition]
    rw [show j - L + L = j by ring]
    congr 2
    rw [hNI]
    simp only [S, Dj]
    have hc := cum_split d (j - L) j (by omega)
    have hs : ∑ i ∈ Ico (1 - L) (j - L + 1), ord i =
        ∑ j_1 ∈ Ico (1 - L) (j - L), order I Q j_1 + order I Q (j - L) := by
      rw [Ico_succ _ _ (by omega), sum_insert (by simp), add_comm]
    rw [hs]
    linarith
  -- sum over periods
  have hsplit : ∀ F : ℤ → ℝ, ∑ t ∈ Icc (1 - L) (T - L), F t =
      ∑ t ∈ Icc (1 - L) 0, F t + ∑ t ∈ Icc 1 (T - L), F t := by
    intro F
    rw [← sum_union]
    · congr 1; ext x; simp only [mem_union, mem_Icc]; omega
    · rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc] at h1 h2; omega
  have hB : ∑ j ∈ Icc 1 T, I.p j * max (-netInventory I d Q j) 0 =
      ∑ t ∈ Icc (1 - L) (T - L), marginalBacklog I d Q t := by
    rw [sum_congr rfl hback]
    apply sum_nbij' (fun j => j - L) (fun t => t + L)
    · intro j hj; simp only [mem_coe, mem_Icc] at hj ⊢; omega
    · intro t ht; simp only [mem_coe, mem_Icc] at ht ⊢; omega
    · intro j _; simp
    · intro t _; simp
    · intro j _; rfl
  have hH : ∑ j ∈ Icc 1 T, I.h j * max (netInventory I d Q j) 0 =
      ∑ j ∈ Icc 1 T, I.h j * max (I.ni0 - Dj j) 0 +
        ∑ t ∈ Icc (1 - L) (T - L), ∑ j ∈ Icc (t + L) T, G t j := by
    rw [sum_congr rfl hhold, sum_add_distrib]
    congr 1
    apply sum_comm'
    intro j t
    simp only [mem_Icc]; omega
  -- identify the holding terms
  have hG1 : ∀ t ∈ Icc 1 (T - L), ∑ j ∈ Icc (t + L) T, G t j = marginalHolding I d Q t := by
    intro t ht
    rw [mem_Icc] at ht
    simp only [marginalHolding, G]
    apply sum_congr rfl
    intro j hj
    rw [mem_Icc] at hj
    have hc := cum_split d t j (by omega)
    have : cumDemand d t j - invPosition I d Q t = Dj j - S t := by
      simp only [invPosition, S, Dj]; linarith
    rw [this]
  have hG0 : ∀ t ∈ Icc (1 - L) 0, ∑ j ∈ Icc (t + L) T, G t j =
      ∑ j ∈ Icc (t + L) T, I.h j * max (I.q t -
        max (cumDemand d t j - (I.ni0 + ∑ i ∈ Ico (1 - L) t, I.q i)) 0) 0 := by
    intro t ht
    rw [mem_Icc] at ht
    apply sum_congr rfl
    intro j hj
    rw [mem_Icc] at hj
    simp only [G, S, Dj, ord, order, if_pos ht.2]
    have hsq : ∑ i ∈ Ico (1 - L) t, (if i ≤ 0 then I.q i else Q i) = ∑ i ∈ Ico (1 - L) t, I.q i := by
      apply sum_congr rfl; intro i hi; rw [mem_Ico] at hi; rw [if_pos (by omega)]
    have hcd : cumDemand d t j = cumDemand d 1 j := by
      unfold cumDemand; rw [max_eq_right (by omega), max_eq_left (le_refl (1:ℤ))]
    rw [hsq, hcd]
  -- assemble
  have hP : ∑ t ∈ Icc (1 : ℤ) T, periodCost I d Q t =
      ∑ j ∈ Icc 1 T, I.h j * max (netInventory I d Q j) 0 +
        ∑ j ∈ Icc 1 T, I.p j * max (-netInventory I d Q j) 0 := by
    rw [← sum_add_distrib]; rfl
  rw [hP, hH, hB, hsplit, hsplit, sum_congr rfl hG0, sum_congr rfl hG1]
  unfold initialHolding marginalCost
  rw [sum_add_distrib]
  simp only [Dj]
  ring
