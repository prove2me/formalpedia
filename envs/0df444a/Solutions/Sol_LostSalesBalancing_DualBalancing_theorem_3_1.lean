-- Prove2me | solution 1 for LostSalesBalancing.DualBalancing.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T04:09:36.627909+00:00
-- url     : https://prove2.me/submissions/29c55c10-c8c5-4db6-97de-2edae08db016

-- Licensed under Apache 2.0. Complete lost-sales dual-balancing approximation theorem.
import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem onHand_step (I : LSInstance) (d Q : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r) :
    onHand I d Q (r + 1) = max (onHand I d Q r - d r) 0 +
      order I.toInstance Q (r + 1 - I.L) := by
  have hnat : (r + 1 - 1).toNat = (r - 1).toNat + 1 := by omega
  have hcast : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
  simp only [onHand, hnat, onHandNat]
  rw [hcast]
  have h1 : r - 1 + 1 = r := by ring
  have h2 : r - 1 + 2 - (I.L : ℤ) = r + 1 - I.L := by ring
  rw [h1, h2]

theorem order_pos (I : Instance) (Q : ℤ → ℝ) {r : ℤ} (hr : 0 < r) :
    order I Q r = Q r := by simp [order, not_le.mpr hr]

theorem order_nonpos (I : Instance) (Q : ℤ → ℝ) {r : ℤ} (hr : r ≤ 0) :
    order I Q r = I.q r := by simp [order, hr]

theorem onHandNat_mono (I : LSInstance) (d Q R : ℤ → ℝ) (n : ℕ)
    (h : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ (n : ℤ) + 1 - I.L →
      order I.toInstance Q j ≤ order I.toInstance R j) :
    onHandNat I d Q n ≤ onHandNat I d R n := by
  induction n with
  | zero =>
      simp only [onHandNat]
      exact add_le_add_right (h _ le_rfl (by simp)) _
  | succ n ih =>
      simp only [onHandNat]
      apply add_le_add
      · apply max_le_max_right
        exact sub_le_sub_right (ih (fun j hj hjn => h j hj (by push_cast; omega))) _
      · apply h
        · omega
        · push_cast
          omega

def prefixOrders (Q : ℤ → ℝ) (k : ℤ) : ℤ → ℝ :=
  fun j => if j ≤ k then Q j else 0

def prefixStock (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ) : ℝ :=
  onHand I d (prefixOrders Q k) r

theorem order_prefix (I : Instance) (Q : ℤ → ℝ) {k j : ℤ} (hk : 0 ≤ k) :
    order I (prefixOrders Q k) j = if j ≤ k then order I Q j else 0 := by
  by_cases hj : j ≤ 0
  · have hjk : j ≤ k := hj.trans hk
    simp [order, hj, hjk]
  · simp only [order, hj, if_false, prefixOrders]

theorem prefixStock_step (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 0 ≤ k) (hr : 1 ≤ r) :
    prefixStock I d Q k (r + 1) = max (prefixStock I d Q k r - d r) 0 +
      if r + 1 - I.L ≤ k then order I.toInstance Q (r + 1 - I.L) else 0 := by
  unfold prefixStock
  rw [onHand_step I d (prefixOrders Q k) r hr, order_prefix I.toInstance Q hk]

theorem prefixStock_step_after (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 0 ≤ k) (hr : 1 ≤ r) (hkr : k + I.L ≤ r) :
    prefixStock I d Q k (r + 1) = max (prefixStock I d Q k r - d r) 0 := by
  rw [prefixStock_step I d Q k r hk hr, if_neg (by omega), add_zero]

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem onHand_mono (I : LSInstance) (d Q R : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r)
    (h : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ r - I.L →
      order I.toInstance Q j ≤ order I.toInstance R j) :
    onHand I d Q r ≤ onHand I d R r := by
  apply onHandNat_mono
  intro j hj hjr
  apply h j hj
  have hc : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
  rw [hc] at hjr
  omega

theorem onHand_congr (I : LSInstance) (d Q R : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r)
    (h : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ r - I.L →
      order I.toInstance Q j = order I.toInstance R j) :
    onHand I d Q r = onHand I d R r := by
  apply le_antisymm
  · exact onHand_mono I d Q R r hr (fun j hj hjr => (h j hj hjr).le)
  · exact onHand_mono I d R Q r hr (fun j hj hjr => (h j hj hjr).ge)

theorem prefixStock_eq (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 0 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k + I.L) :
    prefixStock I d Q k r = onHand I d Q r := by
  apply onHand_congr I d _ Q r hr
  intro j _ hjr
  rw [order_prefix I.toInstance Q hk, if_pos (by omega)]

theorem prefixStock_mono (I : LSInstance) (d Q : ℤ → ℝ) (k l r : ℤ)
    (hk : 0 ≤ k) (hkl : k ≤ l) (hr : 1 ≤ r)
    (hq : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ r - I.L →
      0 ≤ order I.toInstance Q j) :
    prefixStock I d Q k r ≤ prefixStock I d Q l r := by
  apply onHand_mono I d _ _ r hr
  intro j hj hjr
  rw [order_prefix I.toInstance Q hk, order_prefix I.toInstance Q (hk.trans hkl)]
  split_ifs with hjk hjl hjl
  · exact le_rfl
  · omega
  · exact hq j hj hjr
  · exact le_rfl

theorem prefixStock_zero (I : LSInstance) (d Q R : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r) :
    prefixStock I d Q 0 r = prefixStock I d R 0 r := by
  apply onHand_congr I d _ _ r hr
  intro j _ _
  rw [order_prefix I.toInstance Q le_rfl, order_prefix I.toInstance R le_rfl]
  split_ifs with hj
  · rw [order_nonpos I.toInstance Q hj, order_nonpos I.toInstance R hj]
  · rfl

theorem prefixStock_bound_after (I : LSInstance) (d Q P : ℤ → ℝ) (k : ℤ)
    (hk : 0 ≤ k) (ha : 1 ≤ k + I.L)
    (hstart : prefixStock I d Q k (k + I.L) ≤ onHand I d P (k + I.L))
    (n : ℕ)
    (hp : ∀ j : ℤ, k < j → j ≤ k + n → 0 ≤ order I.toInstance P j) :
    prefixStock I d Q k (k + I.L + n) ≤ onHand I d P (k + I.L + n) := by
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
      have hr : 1 ≤ k + (I.L : ℤ) + n := by omega
      have hh := ih (fun j hj hjn => hp j hj (by push_cast; omega))
      have he : k + (I.L : ℤ) + (n + 1 : ℕ) = (k + I.L + n) + 1 := by push_cast; ring
      rw [he, prefixStock_step_after I d Q k _ hk hr (by omega), onHand_step I d P _ hr]
      have hnonneg : 0 ≤ order I.toInstance P (k + I.L + n + 1 - I.L) := by
        apply hp <;> push_cast <;> omega
      exact le_add_of_le_of_nonneg (max_le_max_right 0 (sub_le_sub_right hh _)) hnonneg

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing

theorem int_sum_step (f : ℤ → ℝ) (a r : ℤ) (h : a ≤ r + 1) :
    (∑ j ∈ Icc a (r + 1), f j) = (∑ j ∈ Icc a r, f j) + f (r + 1) := by
  have he : Icc a (r + 1) = insert (r + 1) (Icc a r) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert (by simp)]
  ring

theorem cumDemand_step (d : ℤ → ℝ) (a r : ℤ) (ha : 1 ≤ a) (har : a ≤ r + 1) :
    cumDemand d a (r + 1) = cumDemand d a r + d (r + 1) := by
  simp only [cumDemand, max_eq_left ha]
  exact int_sum_step d a r har

theorem max_drain_add (x a b : ℝ) (hb : 0 ≤ b) :
    max (max (x - a) 0 - b) 0 = max (x - (a + b)) 0 := by
  by_cases h : x - a ≤ 0
  · rw [max_eq_right h, zero_sub, max_eq_right (neg_nonpos.mpr hb), max_eq_right (by linarith)]
  · rw [max_eq_left (le_of_not_ge h)]
    congr 1
    ring

theorem cohort_difference (a q d : ℝ) (hq : 0 ≤ q) :
    max (a + q - d) 0 - max (a - d) 0 = max (q - max (d - a) 0) 0 := by
  by_cases had : d ≤ a
  · rw [max_eq_left (by linarith : 0 ≤ a + q - d), max_eq_left (by linarith : 0 ≤ a - d),
      max_eq_right (by linarith : d - a ≤ 0), sub_zero, max_eq_left hq]
    ring
  · rw [max_eq_right (by linarith : a - d ≤ 0), sub_zero,
      max_eq_left (by linarith : 0 ≤ d - a)]
    congr 1
    ring

theorem stock_conservation (x d : ℝ) :
    max (x - d) 0 = x - min x d := by
  by_cases h : x ≤ d
  · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]; ring
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)), min_eq_right (le_of_not_ge h)]

theorem lost_conservation (x d : ℝ) :
    max (x - d) 0 = x - d + max (d - x) 0 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)),
      max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]; ring

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem onHandNat_nonneg_of_orders (I : LSInstance) (d Q : ℤ → ℝ) (n : ℕ)
    (hq : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ (n : ℤ) + 1 - I.L →
      0 ≤ order I.toInstance Q j) : 0 ≤ onHandNat I d Q n := by
  cases n with
  | zero => exact add_nonneg I.ni0_nonneg (hq _ le_rfl (by simp))
  | succ n =>
      apply add_nonneg (le_max_right _ _)
      apply hq <;> push_cast <;> omega

theorem prefixStock_nonneg (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 0 ≤ k) (hr : 1 ≤ r)
    (hq : ∀ j : ℤ, 1 - (I.L : ℤ) ≤ j → j ≤ r - I.L →
      0 ≤ order I.toInstance Q j) : 0 ≤ prefixStock I d Q k r := by
  apply onHandNat_nonneg_of_orders
  intro j hj hjr
  rw [order_prefix I.toInstance Q hk]
  split_ifs
  · apply hq j hj
    have hc : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
    rw [hc] at hjr
    omega
  · exact le_rfl

theorem prefixStock_drain (I : LSInstance) (d Q : ℤ → ℝ) (k : ℤ)
    (hk : 0 ≤ k) (ha : 1 ≤ k + I.L)
    (hstart : 0 ≤ prefixStock I d Q k (k + I.L)) (n : ℕ)
    (hd : ∀ j : ℤ, k + I.L ≤ j → j < k + I.L + n → 0 ≤ d j) :
    prefixStock I d Q k (k + I.L + n) =
      max (prefixStock I d Q k (k + I.L) -
        cumDemand d (k + I.L) (k + I.L + n - 1)) 0 := by
  induction n with
  | zero =>
      have he : Icc (max (k + (I.L : ℤ)) 1) (k + I.L - 1) = ∅ := by
        apply Icc_eq_empty_of_lt
        omega
      simp only [Nat.cast_zero, add_zero, cumDemand, he, sum_empty, sub_zero,
        max_eq_left hstart]
  | succ n ih =>
      have hi := ih (fun j hj hjn => hd j hj (by push_cast; omega))
      have hr : 1 ≤ k + (I.L : ℤ) + n := by omega
      have he : k + (I.L : ℤ) + (n + 1 : ℕ) = (k + I.L + n) + 1 := by push_cast; ring
      rw [he, prefixStock_step_after I d Q k _ hk hr (by omega), hi]
      have hdj := hd (k + I.L + n) (by omega) (by push_cast; omega)
      rw [max_drain_add _ _ _ hdj]
      have hc := cumDemand_step d (k + I.L) (k + I.L + n - 1) ha (by omega)
      have hidx : k + (I.L : ℤ) + n - 1 + 1 = k + I.L + n := by ring
      rw [hidx] at hc
      have hidx2 : k + (I.L : ℤ) + n + 1 - 1 = k + I.L + n := by ring
      rw [hidx2, hc]

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem prefixStock_drain_from (I : LSInstance) (d Q : ℤ → ℝ) (k a : ℤ)
    (hk : 0 ≤ k) (ha : 1 ≤ a) (hka : k + I.L ≤ a)
    (hstart : 0 ≤ prefixStock I d Q k a) (n : ℕ)
    (hd : ∀ j : ℤ, a ≤ j → j < a + n → 0 ≤ d j) :
    prefixStock I d Q k (a + n) =
      max (prefixStock I d Q k a - cumDemand d a (a + n - 1)) 0 := by
  induction n with
  | zero =>
      have he : Icc (max a 1) (a - 1) = ∅ := Icc_eq_empty_of_lt (by omega)
      simp only [Nat.cast_zero, add_zero, cumDemand, he, sum_empty, sub_zero,
        max_eq_left hstart]
  | succ n ih =>
      have hi := ih (fun j hj hjn => hd j hj (by push_cast; omega))
      have hr : 1 ≤ a + (n : ℤ) := by omega
      have he : a + (n + 1 : ℕ) = (a + n) + 1 := by push_cast; ring
      rw [he, prefixStock_step_after I d Q k _ hk hr (by omega), hi]
      have hdj := hd (a + n) (by omega) (by push_cast; omega)
      rw [max_drain_add _ _ _ hdj]
      have hc := cumDemand_step d a (a + n - 1) ha (by omega)
      have hidx : a + (n : ℤ) - 1 + 1 = a + n := by ring
      rw [hidx] at hc
      have hidx2 : a + (n : ℤ) + 1 - 1 = a + n := by ring
      rw [hidx2, hc]

theorem prefixStock_previous_arrival (I : LSInstance) (d Q : ℤ → ℝ) (k : ℤ)
    (hk : 1 ≤ k) :
    prefixStock I d Q (k - 1) (k + I.L) =
      max (onHand I d Q (k + I.L - 1) - d (k + I.L - 1)) 0 := by
  have hL := I.L_pos
  have hr : 1 ≤ k + (I.L : ℤ) - 1 := by omega
  have he : k + (I.L : ℤ) = (k + I.L - 1) + 1 := by ring
  conv_lhs => rw [he, prefixStock_step_after I d Q (k - 1) _ (by omega) hr (by omega)]
  rw [prefixStock_eq I d Q (k - 1) _ (by omega) hr (by omega)]

theorem prefixStock_arrival (I : LSInstance) (d Q : ℤ → ℝ) (k : ℤ)
    (hk : 1 ≤ k) :
    prefixStock I d Q k (k + I.L) =
      max (onHand I d Q (k + I.L - 1) - d (k + I.L - 1)) 0 + Q k := by
  have hL := I.L_pos
  have hr : 1 ≤ k + (I.L : ℤ) - 1 := by omega
  rw [prefixStock_eq I d Q k _ (by omega) (by omega) le_rfl]
  have he : k + (I.L : ℤ) = (k + I.L - 1) + 1 := by ring
  conv_lhs => rw [he, onHand_step I d Q _ hr]
  have hidx : k + (I.L : ℤ) - 1 + 1 - I.L = k := by ring
  rw [hidx, order_pos I.toInstance Q (by omega)]

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def endPrefix (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ) : ℝ :=
  max (prefixStock I d Q k r - d r) 0

def cohortRemain (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ) : ℝ :=
  endPrefix I d Q k r - endPrefix I d Q (k - 1) r

theorem endPrefix_after (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 0 ≤ k) (hr : 1 ≤ r) (hkr : k + I.L ≤ r) :
    endPrefix I d Q k r = prefixStock I d Q k (r + 1) :=
  (prefixStock_step_after I d Q k r hk hr hkr).symm

theorem cohortRemain_eq (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 1 ≤ k) (hkr : k + I.L ≤ r) (hq : 0 ≤ Q k)
    (hd : ∀ j : ℤ, k + I.L ≤ j → j ≤ r → 0 ≤ d j) :
    cohortRemain I d Q k r =
      max (Q k - max (cumDemand d (k + I.L) r -
        max (onHand I d Q (k + I.L - 1) - d (k + I.L - 1)) 0) 0) 0 := by
  let a : ℤ := k + I.L
  let n : ℕ := (r + 1 - a).toNat
  have hL := I.L_pos
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : a + (n : ℤ) = r + 1 := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by dsimp [a]; omega)]
    ring
  have hda : ∀ j : ℤ, a ≤ j → j < a + n → 0 ≤ d j := by
    intro j hj hjr
    apply hd j hj
    rw [hn] at hjr
    omega
  have hb : 0 ≤ prefixStock I d Q k a := by
    dsimp [a]
    rw [prefixStock_arrival I d Q k hk]
    exact add_nonneg (le_max_right _ _) hq
  have hc : 0 ≤ prefixStock I d Q (k - 1) a := by
    dsimp [a]
    rw [prefixStock_previous_arrival I d Q k hk]
    exact le_max_right _ _
  have h1 := prefixStock_drain_from I d Q k a (by omega) ha le_rfl hb n hda
  have h2 := prefixStock_drain_from I d Q (k - 1) a (by omega) ha (by dsimp [a]; omega) hc n hda
  rw [hn] at h1 h2
  have hrs : r + 1 - 1 = r := by ring
  rw [hrs] at h1 h2
  dsimp [a] at h1 h2
  rw [prefixStock_arrival I d Q k hk] at h1
  rw [prefixStock_previous_arrival I d Q k hk] at h2
  unfold cohortRemain
  rw [endPrefix_after I d Q k r (by omega) (by omega) hkr,
    endPrefix_after I d Q (k - 1) r (by omega) (by omega) (by omega), h1, h2]
  exact cohort_difference _ _ _ hq

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def PathFeasible (I : LSInstance) (Q : ℤ → ℝ) : Prop :=
  ∀ j : ℤ, 1 ≤ j → j ≤ I.T → 0 ≤ Q j

theorem path_order_nonneg (I : LSInstance) (Q : ℤ → ℝ) (hQ : PathFeasible I Q)
    (j : ℤ) (hj : 1 - (I.L : ℤ) ≤ j) (hjT : j ≤ I.T) :
    0 ≤ order I.toInstance Q j := by
  by_cases h : j ≤ 0
  · rw [order_nonpos I.toInstance Q h]
    exact I.q_nonneg j hj h
  · rw [order_pos I.toInstance Q (by omega)]
    exact hQ j (by omega) hjT

theorem path_onHand_nonneg (I : LSInstance) (d Q : ℤ → ℝ) (hQ : PathFeasible I Q)
    (r : ℤ) (hr : 1 ≤ r) (hrT : r ≤ I.T) : 0 ≤ onHand I d Q r := by
  apply onHandNat_nonneg_of_orders
  intro j hj hjr
  apply path_order_nonneg I Q hQ j hj
  have hc : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
  rw [hc] at hjr
  omega

theorem path_prefix_mono (I : LSInstance) (d Q : ℤ → ℝ) (hQ : PathFeasible I Q)
    (k l r : ℤ) (hk : 0 ≤ k) (hkl : k ≤ l) (hr : 1 ≤ r) (hrT : r ≤ I.T) :
    prefixStock I d Q k r ≤ prefixStock I d Q l r := by
  apply prefixStock_mono I d Q k l r hk hkl hr
  intro j hj hjr
  exact path_order_nonneg I Q hQ j hj (by omega)

theorem path_initial_le (I : LSInstance) (d Q : ℤ → ℝ) (hQ : PathFeasible I Q)
    (r : ℤ) (hr : 1 ≤ r) (hrT : r ≤ I.T) :
    prefixStock I d Q 0 r ≤ onHand I d Q r := by
  apply onHand_mono I d _ Q r hr
  intro j hj hjr
  rw [order_prefix I.toInstance Q le_rfl]
  split_ifs
  · exact le_rfl
  · exact path_order_nonneg I Q hQ j hj (by omega)

theorem truncPos_endpoint (I : LSInstance) (d Q : ℤ → ℝ) (k : ℤ) :
    truncPos I d Q (k + I.L) k = onHand I d Q (k + I.L) := by
  have he : Icc (k + (I.L : ℤ) + 1 - I.L) k = ∅ := Icc_eq_empty_of_lt (by omega)
  simp only [truncPos, he, sum_empty, add_zero]

theorem marked_prefix_cap (I : LSInstance) (d Q P : ℤ → ℝ)
    (hP : PathFeasible I P) (k r : ℤ) (hk : 1 ≤ k)
    (hkr : k + I.L ≤ r) (hrT : r ≤ I.T) (hmark : InTH I d Q P k) :
    prefixStock I d Q k r ≤ onHand I d P r := by
  have hL := I.L_pos
  have hh := hmark (k + I.L) (by simp)
  rw [truncPos_endpoint, truncPos_endpoint] at hh
  have hstart : prefixStock I d Q k (k + I.L) ≤ onHand I d P (k + I.L) := by
    rw [prefixStock_eq I d Q k _ (by omega) (by omega) le_rfl]
    exact hh.le
  let n : ℕ := (r - (k + I.L)).toNat
  have hn : k + (I.L : ℤ) + (n : ℤ) = r := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hb := prefixStock_bound_after I d Q P k (by omega) (by omega) hstart n
    (fun j hj hjn => path_order_nonneg I P hP j (by omega) (by omega))
  rwa [hn] at hb

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset

theorem sum_increments (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, (a (i + 1) - a i)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem selected_increments_le (a : ℕ → ℝ) (S : ℕ → Prop) [DecidablePred S]
    (n : ℕ) (b : ℝ) (h0 : a 0 ≤ b)
    (hmono : ∀ i, i < n → a i ≤ a (i + 1))
    (hcap : ∀ i, i < n → S i → a (i + 1) ≤ b) :
    (∑ i ∈ range n, if S i then a (i + 1) - a i else 0) ≤ b - a 0 := by
  calc
    _ ≤ ∑ i ∈ range n, (min (a (i + 1)) b - min (a i) b) := by
      apply sum_le_sum
      intro i hi
      have hin := mem_range.mp hi
      by_cases hs : S i
      · have h1 := hcap i hin hs
        rw [if_pos hs, min_eq_left h1, min_eq_left ((hmono i hin).trans h1)]
      · rw [if_neg hs]
        exact sub_nonneg.mpr (min_le_min_right b (hmono i hin))
    _ = min (a n) b - min (a 0) b := sum_increments (fun i => min (a i) b) n
    _ ≤ b - a 0 := by rw [min_eq_left h0]; exact sub_le_sub_right (min_le_right _ _) _

theorem weighted_prefix_le (a b : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k, k ≤ n → (∑ i ∈ range k, a i) ≤ ∑ i ∈ range k, b i)
    (w : ℕ → ℝ) (hw : ∀ i, i < n → 0 ≤ w i)
    (hm : ∀ i j, i ≤ j → j < n → w j ≤ w i) :
    (∑ i ∈ range n, w i * a i) ≤ ∑ i ∈ range n, w i * b i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      have hprior := ih (fun k hk => hp k (by omega)) (fun i => w i - w n)
        (fun i hi => sub_nonneg.mpr (hm i n (by omega) (by omega)))
        (fun i j hij hj => sub_le_sub_right (hm i j hij (by omega)) _)
      have hall := mul_le_mul_of_nonneg_left (hp (n + 1) le_rfl) (hw n (by omega))
      have hsplit (v : ℕ → ℝ) :
          (∑ i ∈ range (n + 1), w i * v i) =
            w n * (∑ i ∈ range (n + 1), v i) +
              ∑ i ∈ range n, (w i - w n) * v i := by
        simp only [sum_range_succ, sub_mul, sum_sub_distrib]
        rw [← mul_sum]
        ring
      rw [hsplit a, hsplit b]
      exact add_le_add hall hprior

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem selected_increments_le_or_flat (a : ℕ → ℝ) (S : ℕ → Prop) [DecidablePred S]
    (n : ℕ) (b : ℝ) (h0 : a 0 ≤ b)
    (hmono : ∀ i, i < n → a i ≤ a (i + 1))
    (hcap : ∀ i, i < n → S i → a (i + 1) ≤ b ∨ a i = a (i + 1)) :
    (∑ i ∈ range n, if S i then a (i + 1) - a i else 0) ≤ b - a 0 := by
  calc
    _ ≤ ∑ i ∈ range n, (min (a (i + 1)) b - min (a i) b) := by
      apply sum_le_sum
      intro i hi
      have hin := mem_range.mp hi
      by_cases hs : S i
      · rw [if_pos hs]
        rcases hcap i hin hs with hc | hc
        · rw [min_eq_left hc, min_eq_left ((hmono i hin).trans hc)]
        · simp only [hc, sub_self, le_refl]
      · rw [if_neg hs]
        exact sub_nonneg.mpr (min_le_min_right b (hmono i hin))
    _ = min (a n) b - min (a 0) b := sum_increments (fun i => min (a i) b) n
    _ ≤ b - a 0 := by rw [min_eq_left h0]; exact sub_le_sub_right (min_le_right _ _) _

theorem prefix_future_flat (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hfuture : r < k + I.L) :
    prefixStock I d Q (k - 1) r = prefixStock I d Q k r := by
  rw [prefixStock_eq I d Q (k - 1) r (by omega) hr (by omega),
    prefixStock_eq I d Q k r (by omega) hr (by omega)]

theorem selected_transform_bound (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (r : ℤ)
    (hr : 1 ≤ r) (hrT : r ≤ I.T) (f : ℝ → ℝ) (hf : Monotone f) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then
      f (prefixStock I d Q ((i : ℤ) + 1) r) - f (prefixStock I d Q i r) else 0) ≤
      f (onHand I d P r) - f (prefixStock I d P 0 r) := by
  classical
  have h0 : f (prefixStock I d Q 0 r) ≤ f (onHand I d P r) := by
    rw [prefixStock_zero I d Q P r hr]
    exact hf (path_initial_le I d P hP r hr hrT)
  have hh := selected_increments_le_or_flat
    (fun i : ℕ => f (prefixStock I d Q i r))
    (fun i : ℕ => InTH I d Q P ((i : ℤ) + 1)) N (f (onHand I d P r)) h0
    (by
      intro i _
      apply hf
      simpa only [Nat.cast_add, Nat.cast_one] using
        path_prefix_mono I d Q hQ i (i + 1) r (by omega) (by omega) hr hrT)
    (by
      intro i _ hmark
      simp only [Nat.cast_add, Nat.cast_one]
      by_cases hi : (i : ℤ) + 1 + I.L ≤ r
      · left
        exact hf (marked_prefix_cap I d Q P hP ((i : ℤ) + 1) r (by omega) hi hrT hmark)
      · right
        have he := prefix_future_flat I d Q ((i : ℤ) + 1) r (by omega) hr (by omega)
        simpa only [add_sub_cancel_right] using congrArg f he)
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hh
  rw [prefixStock_zero I d Q P r hr] at hh
  exact hh

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def cohortConsumed (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ) : ℝ :=
  min (prefixStock I d Q k r) (d r) - min (prefixStock I d Q (k - 1) r) (d r)

theorem order_prefix_difference (I : Instance) (Q : ℤ → ℝ) (k j : ℤ) (hk : 1 ≤ k) :
    order I (prefixOrders Q k) j - order I (prefixOrders Q (k - 1)) j =
      if j = k then Q k else 0 := by
  rw [order_prefix I Q (by omega), order_prefix I Q (by omega)]
  by_cases hj : j = k
  · subst j
    rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, sub_zero, order_pos I Q (by omega)]
  · rw [if_neg hj]
    by_cases hle : j ≤ k - 1
    · rw [if_pos (by omega), if_pos hle, sub_self]
    · rw [if_neg (by omega), if_neg hle, sub_self]

theorem cohort_balance (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (prefixStock I d Q k (r + 1) - prefixStock I d Q (k - 1) (r + 1)) -
      (prefixStock I d Q k r - prefixStock I d Q (k - 1) r) =
        -cohortConsumed I d Q k r + if r + 1 - I.L = k then Q k else 0 := by
  unfold prefixStock
  rw [onHand_step I d (prefixOrders Q k) r hr,
    onHand_step I d (prefixOrders Q (k - 1)) r hr]
  rw [stock_conservation, stock_conservation]
  have ho := order_prefix_difference I.toInstance Q k (r + 1 - I.L) hk
  unfold cohortConsumed prefixStock
  linarith

theorem cohort_accounting (I : LSInstance) (d Q : ℤ → ℝ) (k : ℤ) (N : ℕ)
    (hk : 1 ≤ k) (harr : k + I.L ≤ (N : ℤ)) :
    (∑ n ∈ range N, cohortConsumed I d Q k ((n : ℤ) + 1)) +
      cohortRemain I d Q k N = Q k := by
  have hL := I.L_pos
  let z : ℕ := (k + I.L - 2).toNat
  have hz : (z : ℤ) = k + I.L - 2 := Int.toNat_of_nonneg (by omega)
  have hzN : z < N := by omega
  have hs : (∑ n ∈ range N, if (n : ℤ) + 1 + 1 - I.L = k then Q k else 0) = Q k := by
    rw [sum_eq_single z]
    · rw [if_pos (by omega)]
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro h
      exact False.elim (h (mem_range.mpr hzN))
  have he := sum_increments
    (fun n : ℕ => prefixStock I d Q k ((n : ℤ) + 1) -
      prefixStock I d Q (k - 1) ((n : ℤ) + 1)) N
  have hterm : ∀ n : ℕ,
      (prefixStock I d Q k ((n + 1 : ℕ) + 1) - prefixStock I d Q (k - 1) ((n + 1 : ℕ) + 1)) -
        (prefixStock I d Q k ((n : ℤ) + 1) - prefixStock I d Q (k - 1) ((n : ℤ) + 1)) =
      -cohortConsumed I d Q k ((n : ℤ) + 1) + if (n : ℤ) + 1 + 1 - I.L = k then Q k else 0 := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using cohort_balance I d Q k ((n : ℤ) + 1) hk (by omega)
  simp only [hterm, sum_add_distrib, sum_neg_distrib, hs, Nat.cast_zero, zero_add] at he
  have hzero := prefix_future_flat I d Q k 1 hk le_rfl (by omega)
  rw [← hzero, sub_self] at he
  have hend : cohortRemain I d Q k N =
      prefixStock I d Q k ((N : ℤ) + 1) - prefixStock I d Q (k - 1) ((N : ℤ) + 1) := by
    unfold cohortRemain
    rw [endPrefix_after I d Q k N (by omega) (by omega) harr,
      endPrefix_after I d Q (k - 1) N (by omega) (by omega) (by omega)]
  rw [hend]
  linarith

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem selected_cohort_transform_le (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (r : ℤ)
    (hr : 1 ≤ r) (hrT : r ≤ I.T) (hrN : r ≤ (N : ℤ) + I.L)
    (f : ℝ → ℝ) (hf : Monotone f) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then
      f (prefixStock I d Q ((i : ℤ) + 1) r) - f (prefixStock I d Q i r) else 0) ≤
      ∑ i ∈ range N, (f (prefixStock I d P ((i : ℤ) + 1) r) - f (prefixStock I d P i r)) := by
  have hh := selected_transform_bound I d Q P hQ hP N r hr hrT f hf
  have he := sum_increments (fun i : ℕ => f (prefixStock I d P i r)) N
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at he
  rw [he, prefixStock_eq I d P N r (by omega) hr hrN]
  exact hh

theorem selected_remaining_le (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (r : ℤ)
    (hr : 1 ≤ r) (hrT : r ≤ I.T) (hrN : r ≤ (N : ℤ) + I.L) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then
      cohortRemain I d Q ((i : ℤ) + 1) r else 0) ≤
      ∑ i ∈ range N, cohortRemain I d P ((i : ℤ) + 1) r := by
  simpa only [cohortRemain, endPrefix, add_sub_cancel_right] using
    selected_cohort_transform_le I d Q P hQ hP N r hr hrT hrN
      (fun x => max (x - d r) 0) (fun _ _ h => max_le_max_right 0 (sub_le_sub_right h _))

theorem selected_consumed_le (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (r : ℤ)
    (hr : 1 ≤ r) (hrT : r ≤ I.T) (hrN : r ≤ (N : ℤ) + I.L) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then
      cohortConsumed I d Q ((i : ℤ) + 1) r else 0) ≤
      ∑ i ∈ range N, cohortConsumed I d P ((i : ℤ) + 1) r := by
  simpa only [cohortConsumed, add_sub_cancel_right] using
    selected_cohort_transform_le I d Q P hQ hP N r hr hrT hrN
      (fun x => min x (d r)) (fun _ _ h => min_le_min_right _ h)

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem sum_cohort_accounting (I : LSInstance) (d Q : ℤ → ℝ)
    (S : ℕ → Prop) [DecidablePred S] (N M : ℕ) (hNM : N + I.L ≤ M) :
    (∑ i ∈ range N, if S i then Q ((i : ℤ) + 1) else 0) =
      (∑ r ∈ range M, ∑ i ∈ range N,
        if S i then cohortConsumed I d Q ((i : ℤ) + 1) ((r : ℤ) + 1) else 0) +
      ∑ i ∈ range N, if S i then cohortRemain I d Q ((i : ℤ) + 1) M else 0 := by
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  by_cases hs : S i
  · simp only [hs, if_true]
    exact (cohort_accounting I d Q ((i : ℤ) + 1) M (by omega) (by have := mem_range.mp hi; omega)).symm
  · simp only [hs, if_false, sum_const_zero, add_zero]

theorem marked_order_prefix_le (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (hN : N + I.L ≤ I.T) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then Q ((i : ℤ) + 1) else 0) ≤
      ∑ i ∈ range N, P ((i : ℤ) + 1) := by
  let M := N + I.L
  have hL := I.L_pos
  have hq := sum_cohort_accounting I d Q (fun i => InTH I d Q P ((i : ℤ) + 1)) N M le_rfl
  have hp := sum_cohort_accounting I d P (fun _ => True) N M le_rfl
  simp only [if_true] at hp
  rw [hq, hp]
  apply add_le_add
  · apply sum_le_sum
    intro r hr
    apply selected_consumed_le I d Q P hQ hP N ((r : ℤ) + 1)
    · omega
    · have := mem_range.mp hr
      dsimp [M] at this
      omega
    · have := mem_range.mp hr
      dsimp [M] at this
      omega
  · apply selected_remaining_le I d Q P hQ hP N M
    · dsimp [M]; omega
    · dsimp [M]; exact_mod_cast hN
    · dsimp [M]; rfl

theorem marked_ordering_charge (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P) (N : ℕ) (hN : N + I.L ≤ I.T) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then
      I.c ((i : ℤ) + 1) * Q ((i : ℤ) + 1) else 0) ≤
      ∑ i ∈ range N, I.c ((i : ℤ) + 1) * P ((i : ℤ) + 1) := by
  have hh := weighted_prefix_le
    (fun i => if InTH I d Q P ((i : ℤ) + 1) then Q ((i : ℤ) + 1) else 0)
    (fun i => P ((i : ℤ) + 1)) N
    (fun k hk => marked_order_prefix_le I d Q P hQ hP k (by omega))
    (fun i => I.c ((i : ℤ) + 1))
    (fun i hi => I.c_nonneg _ (by omega) (by omega))
    (fun i j hij hj => I.c_anti _ _ (by omega) (by omega) (by omega))
  simpa only [mul_ite, mul_zero] using hh

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset

theorem int_sum_as_range (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    (∑ j ∈ Icc a (a + n - 1), f j) = ∑ i ∈ range n, f (a + i) := by
  induction n with
  | zero =>
      have he : Icc a (a - 1) = ∅ := Icc_eq_empty_of_lt (by omega)
      simp only [Nat.cast_zero, add_zero, he, sum_empty, sum_range_zero]
  | succ n ih =>
      have hidx : a + (n + 1 : ℕ) - 1 = a + n := by push_cast; ring
      rw [hidx, sum_range_succ]
      have hh := int_sum_step f a (a + n - 1) (by omega)
      have he : a + (n : ℤ) - 1 + 1 = a + n := by ring
      rw [he, ih] at hh
      exact hh

theorem int_sum_one (f : ℤ → ℝ) (n : ℕ) :
    (∑ j ∈ Icc 1 (n : ℤ), f j) = ∑ i ∈ range n, f ((i : ℤ) + 1) := by
  have hh := int_sum_as_range f 1 n
  have he : (1 : ℤ) + n - 1 = n := by ring
  rw [he] at hh
  simpa only [add_comm] using hh

theorem nat_interval_to_int (f : ℤ → ℝ) (j N : ℕ) (hj : j ≤ N) :
    (∑ r ∈ Ico j N, f ((r : ℤ) + 1)) = ∑ r ∈ Icc ((j : ℤ) + 1) N, f r := by
  rw [sum_Ico_eq_sum_range]
  have hh := int_sum_as_range f ((j : ℤ) + 1) (N - j)
  have hc : ((N - j : ℕ) : ℤ) = N - j := Int.ofNat_sub hj
  have he : (j : ℤ) + 1 + (N - j : ℕ) - 1 = N := by rw [hc]; ring
  rw [he] at hh
  rw [hh]
  apply sum_congr rfl
  intro i _
  congr 1
  push_cast
  ring

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem cohortRemain_before (I : LSInstance) (d Q : ℤ → ℝ) (k r : ℤ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hfuture : r < k + I.L) :
    cohortRemain I d Q k r = 0 := by
  unfold cohortRemain endPrefix
  rw [prefix_future_flat I d Q k r hk hr hfuture, sub_self]

theorem holding_as_cohorts (I : LSInstance) (d Q : ℤ → ℝ) (hQ : PathFeasible I Q)
    (hd : ∀ r : ℤ, 1 ≤ r → r ≤ I.T → 0 ≤ d r) (k : ℤ)
    (hk : 1 ≤ k) (hkT : k ≤ I.T) :
    holdingLS I d Q k = I.c k * Q k +
      ∑ r ∈ range I.T, I.h ((r : ℤ) + 1) * cohortRemain I d Q k ((r : ℤ) + 1) := by
  rw [holdingLS, order_pos I.toInstance Q (by omega),
    ← int_sum_one (fun r => I.h r * cohortRemain I d Q k r) I.T]
  congr 1
  have hL := I.L_pos
  calc
    _ = ∑ r ∈ Icc (k + I.L) (I.T : ℤ), I.h r * cohortRemain I d Q k r := by
      apply sum_congr rfl
      intro r hr
      rw [cohortRemain_eq I d Q k r hk (mem_Icc.mp hr).1 (hQ k hk hkT)]
      intro j hj hjr
      exact hd j (by omega) (hjr.trans (mem_Icc.mp hr).2)
    _ = _ := sum_subset (by intro r hr; simp only [mem_Icc] at hr ⊢; omega)
      (by
        intro r hr hnot
        have hr1 := (mem_Icc.mp hr).1
        have hrT := (mem_Icc.mp hr).2
        have hbefore : r < k + I.L := by
          simp only [mem_Icc, not_and] at hnot
          by_contra hh
          exact hnot (by omega) hrT
        rw [cohortRemain_before I d Q k r hk hr1 hbefore, mul_zero])

theorem selected_grid_sum (S : ℕ → Prop) [DecidablePred S] (N M : ℕ)
    (c h : ℕ → ℝ) (a : ℕ → ℕ → ℝ) :
    (∑ i ∈ range N, if S i then c i + ∑ r ∈ range M, h r * a i r else 0) =
      (∑ i ∈ range N, if S i then c i else 0) +
        ∑ r ∈ range M, h r * ∑ i ∈ range N, if S i then a i r else 0 := by
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hs : S i
  · simp only [hs, if_true]
  · simp only [hs, if_false, mul_zero, sum_const_zero, add_zero]

theorem marked_holding_charge (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P)
    (hd : ∀ r : ℤ, 1 ≤ r → r ≤ I.T → 0 ≤ d r)
    (N : ℕ) (hN : N + I.L = I.T) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then holdingLS I d Q ((i : ℤ) + 1) else 0) ≤
      ∑ i ∈ range N, holdingLS I d P ((i : ℤ) + 1) := by
  have hsum (R : ℤ → ℝ) (hR : PathFeasible I R) (S : ℕ → Prop) [DecidablePred S] :
      (∑ i ∈ range N, if S i then holdingLS I d R ((i : ℤ) + 1) else 0) =
        (∑ i ∈ range N, if S i then I.c ((i : ℤ) + 1) * R ((i : ℤ) + 1) else 0) +
          ∑ r ∈ range I.T, I.h ((r : ℤ) + 1) *
            ∑ i ∈ range N, if S i then cohortRemain I d R ((i : ℤ) + 1) ((r : ℤ) + 1) else 0 := by
    calc
      _ = ∑ i ∈ range N, if S i then I.c ((i : ℤ) + 1) * R ((i : ℤ) + 1) +
          ∑ r ∈ range I.T, I.h ((r : ℤ) + 1) * cohortRemain I d R ((i : ℤ) + 1) ((r : ℤ) + 1) else 0 := by
        apply sum_congr rfl
        intro i hi
        rw [holding_as_cohorts I d R hR hd _ (by omega) (by have := mem_range.mp hi; omega)]
      _ = _ := selected_grid_sum S N I.T _ _ _
  have hqs := hsum Q hQ (fun i => InTH I d Q P ((i : ℤ) + 1))
  have hps := hsum P hP (fun _ => True)
  simp only [if_true] at hps
  rw [hqs, hps]
  apply add_le_add (marked_ordering_charge I d Q P hQ hP N hN.le)
  apply sum_le_sum
  intro r hr
  have hrT : (r : ℤ) + 1 ≤ I.T := by have := mem_range.mp hr; omega
  apply mul_le_mul_of_nonneg_left
    (selected_remaining_le I d Q P hQ hP N ((r : ℤ) + 1) (by omega) hrT (by omega))
  exact I.h_nonneg _ (by omega) hrT

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem sum_Icc_split_first (f : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    (∑ j ∈ Icc a b, f j) = f a + ∑ j ∈ Icc (a + 1) b, f j := by
  have he : Icc a b = insert a (Icc (a + 1) b) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert]
  simp only [mem_Icc]
  omega

theorem truncPos_step (I : LSInstance) (d Q : ℤ → ℝ) {r t : ℤ}
    (hr : 1 ≤ r) (hrt : r < t + I.L) :
    truncPos I d Q (r + 1) t = max (onHand I d Q r - d r) 0 +
      ∑ a ∈ Icc (r + 1 - I.L) t, order I.toInstance Q a := by
  rw [truncPos, onHand_step I d Q r hr,
    sum_Icc_split_first (order I.toInstance Q) (by omega : r + 1 - (I.L : ℤ) ≤ t)]
  have he : r + 1 + 1 - (I.L : ℤ) = r + 1 - I.L + 1 := by ring
  rw [he]
  ring

theorem crossing_max_zero {b p u v d : ℝ}
    (hbefore : b + u < p + v)
    (hafter : max (p - d) 0 + v ≤ max (b - d) 0 + u) :
    max (b - d) 0 = 0 := by
  apply max_eq_right
  by_contra h
  have hb : 0 ≤ b - d := le_of_lt (lt_of_not_ge h)
  rw [max_eq_left hb] at hafter
  have hp := le_max_left (p - d) (0 : ℝ)
  linarith

theorem crossing_reset (I : LSInstance) (d B P : ℤ → ℝ) {r t : ℤ}
    (hr : 1 ≤ r) (hrt : r < t + I.L)
    (hbefore : truncPos I d B r t < truncPos I d P r t)
    (hafter : truncPos I d P (r + 1) t ≤ truncPos I d B (r + 1) t) :
    onHand I d B (r + 1) = order I.toInstance B (r + 1 - I.L) := by
  rw [truncPos_step I d P hr hrt, truncPos_step I d B hr hrt] at hafter
  have hz := crossing_max_zero hbefore hafter
  rw [onHand_step I d B r hr, hz, zero_add]

end LostSalesProof


noncomputable section
namespace LostSalesProof
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem truncPos_balance_step (I : LSInstance) (d Q : ℤ → ℝ) {r t : ℤ}
    (hr : 1 ≤ r) (hrt : r < t + I.L) :
    truncPos I d Q (r + 1) t = truncPos I d Q r t - d r + lostUnits I d Q r := by
  rw [truncPos_step I d Q hr hrt, lost_conservation]
  unfold truncPos lostUnits
  ring

theorem truncPos_balance (I : LSInstance) (d Q : ℤ → ℝ) (s t : ℤ) (n : ℕ)
    (hs : 1 ≤ s) (hn : s + n ≤ t + I.L) :
    truncPos I d Q (s + n) t = truncPos I d Q s t -
      (∑ r ∈ Icc s (s + n - 1), d r) + ∑ r ∈ Icc s (s + n - 1), lostUnits I d Q r := by
  induction n with
  | zero =>
      have he : Icc s (s - 1) = ∅ := Icc_eq_empty_of_lt (by omega)
      simp only [Nat.cast_zero, add_zero, he, sum_empty, sub_zero]
  | succ n ih =>
      have hi := ih (by push_cast at hn; omega)
      have he : s + (n + 1 : ℕ) = (s + n) + 1 := by push_cast; ring
      rw [he, truncPos_balance_step I d Q (by omega) (by push_cast at hn; omega), hi]
      have hidx : s + (n : ℤ) + 1 - 1 = s + n := by ring
      rw [hidx]
      have h1 := int_sum_step d s (s + n - 1) (by omega)
      have h2 := int_sum_step (lostUnits I d Q) s (s + n - 1) (by omega)
      have hidx2 : s + (n : ℤ) - 1 + 1 = s + n := by ring
      rw [hidx2] at h1 h2
      rw [h1, h2]
      ring

theorem loss_interval_identity (I : LSInstance) (d Q : ℤ → ℝ) (s t : ℤ)
    (hs : 1 ≤ s) (hst : s ≤ t + I.L) :
    (∑ r ∈ Icc s (t + I.L), lostUnits I d Q r) =
      max (onHand I d Q (t + I.L) - d (t + I.L)) 0 - truncPos I d Q s t +
        ∑ r ∈ Icc s (t + I.L), d r := by
  let n : ℕ := (t + I.L - s).toNat
  have hn : s + (n : ℤ) = t + I.L := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hh := truncPos_balance I d Q s t n hs (by omega)
  rw [hn, truncPos_endpoint] at hh
  have h1 := int_sum_step d s (t + I.L - 1) (by omega)
  have h2 := int_sum_step (lostUnits I d Q) s (t + I.L - 1) (by omega)
  have he : t + (I.L : ℤ) - 1 + 1 = t + I.L := by ring
  rw [he] at h1 h2
  rw [h1, h2, lost_conservation]
  unfold lostUnits at *
  linarith

theorem loss_suffix_charge (I : LSInstance) (d Q P : ℤ → ℝ) (s t : ℤ)
    (hs : 1 ≤ s) (hst : s ≤ t + I.L)
    (hy : truncPos I d P s t ≤ truncPos I d Q s t)
    (hloss : 0 < lostUnits I d Q (t + I.L)) :
    (∑ r ∈ Icc s (t + I.L), lostUnits I d Q r) ≤
      ∑ r ∈ Icc s (t + I.L), lostUnits I d P r := by
  have hz : max (onHand I d Q (t + I.L) - d (t + I.L)) 0 = 0 := by
    unfold lostUnits at hloss
    have hp : 0 < d (t + I.L) - onHand I d Q (t + I.L) := by
      simpa only [lt_max_iff, lt_self_iff_false, or_false] using hloss
    exact max_eq_right (by linarith)
  rw [loss_interval_identity I d Q s t hs hst, loss_interval_identity I d P s t hs hst, hz]
  have hh := le_max_right (onHand I d P (t + I.L) - d (t + I.L)) (0 : ℝ)
  linarith

theorem initial_losses_equal (I : LSInstance) (d Q P : ℤ → ℝ) (r : ℤ)
    (hr : 1 ≤ r) (hrL : r ≤ I.L) : lostUnits I d Q r = lostUnits I d P r := by
  have he : onHand I d Q r = onHand I d P r := by
    apply onHand_congr I d Q P r hr
    intro j _ hj
    rw [order_nonpos I.toInstance Q (by omega), order_nonpos I.toInstance P (by omega)]
  unfold lostUnits
  rw [he]

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset

theorem marked_prefix_charge (a b : ℕ → ℝ) (S : ℕ → Prop) [DecidablePred S]
    (n : ℕ) (ha : ∀ i, i < n → 0 ≤ a i) (hb : ∀ i, i < n → 0 ≤ b i)
    (hwitness : ∀ i, i < n → S i → 0 < a i → ∃ j, j ≤ i ∧
      (∑ r ∈ Ico j (i + 1), a r) ≤ ∑ r ∈ Ico j (i + 1), b r) :
    (∑ i ∈ range n, if S i then a i else 0) ≤ ∑ i ∈ range n, b i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ k =>
          have hprev := ih k (by omega) (fun i hi => ha i (by omega))
            (fun i hi => hb i (by omega))
            (fun i hi hs hp => hwitness i (by omega) hs hp)
          by_cases hs : S k
          · by_cases hp : 0 < a k
            · obtain ⟨j, hj, hh⟩ := hwitness k (by omega) hs hp
              have hfirst := ih j (by omega) (fun i hi => ha i (by omega))
                (fun i hi => hb i (by omega))
                (fun i hi hsi hpi => hwitness i (by omega) hsi hpi)
              have hmid : (∑ r ∈ Ico j (k + 1), if S r then a r else 0) ≤
                  ∑ r ∈ Ico j (k + 1), a r := by
                apply sum_le_sum
                intro r hr
                split_ifs
                · exact le_rfl
                · exact ha r (mem_Ico.mp hr).2
              rw [← sum_range_add_sum_Ico _ (by omega : j ≤ k + 1),
                ← sum_range_add_sum_Ico b (by omega : j ≤ k + 1)]
              exact add_le_add hfirst (hmid.trans hh)
            · have hz : a k = 0 := le_antisymm (le_of_not_gt hp) (ha k (by omega))
              rw [sum_range_succ, sum_range_succ, if_pos hs, hz, add_zero]
              exact hprev.trans (le_add_of_nonneg_right (hb k (by omega)))
          · rw [sum_range_succ, sum_range_succ, if_neg hs, add_zero]
            exact hprev.trans (le_add_of_nonneg_right (hb k (by omega)))

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def lossMark (I : LSInstance) (d Q P : ℤ → ℝ) (r : ℤ) : Prop :=
  r ≤ I.L ∨ ¬ InTH I d Q P (r - I.L)

theorem loss_prefix_bound (I : LSInstance) (d Q P : ℤ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, if lossMark I d Q P ((i : ℤ) + 1) then
      lostUnits I d Q ((i : ℤ) + 1) else 0) ≤
      ∑ i ∈ range N, lostUnits I d P ((i : ℤ) + 1) := by
  apply marked_prefix_charge
  · intro i _; exact le_max_right _ _
  · intro i _; exact le_max_right _ _
  · intro i _ hmark hloss
    by_cases hiL : (i : ℤ) + 1 ≤ I.L
    · refine ⟨i, le_rfl, ?_⟩
      simp only [Nat.Ico_succ_singleton, sum_singleton]
      rw [initial_losses_equal I d Q P ((i : ℤ) + 1) (by omega) hiL]
    · have hbad : ¬ InTH I d Q P ((i : ℤ) + 1 - I.L) := hmark.resolve_left hiL
      unfold InTH at hbad
      push Not at hbad
      obtain ⟨s, hs, hy⟩ := hbad
      have hslo := (mem_Icc.mp hs).1
      have hshi := (mem_Icc.mp hs).2
      have hspos : 1 ≤ s := by omega
      let j : ℕ := (s - 1).toNat
      have hj : (j : ℤ) = s - 1 := Int.toNat_of_nonneg (by omega)
      refine ⟨j, by omega, ?_⟩
      rw [nat_interval_to_int _ j (i + 1) (by omega), nat_interval_to_int _ j (i + 1) (by omega)]
      have hje : (j : ℤ) + 1 = s := by rw [hj]; ring
      rw [hje]
      have hh := loss_suffix_charge I d Q P s ((i : ℤ) + 1 - I.L) hspos (by omega) hy
        (by simpa only [sub_add_cancel] using hloss)
      simpa only [sub_add_cancel, Nat.cast_add, Nat.cast_one] using hh

theorem weighted_loss_prefix_bound (I : LSInstance) (d Q P : ℤ → ℝ)
    (N : ℕ) (hN : N ≤ I.T) :
    (∑ i ∈ range N, if lossMark I d Q P ((i : ℤ) + 1) then
      I.p ((i : ℤ) + 1) * lostUnits I d Q ((i : ℤ) + 1) else 0) ≤
      ∑ i ∈ range N, I.p ((i : ℤ) + 1) * lostUnits I d P ((i : ℤ) + 1) := by
  have hh := weighted_prefix_le
    (fun i => if lossMark I d Q P ((i : ℤ) + 1) then lostUnits I d Q ((i : ℤ) + 1) else 0)
    (fun i => lostUnits I d P ((i : ℤ) + 1)) N
    (fun k _ => loss_prefix_bound I d Q P k) (fun i => I.p ((i : ℤ) + 1))
    (fun i hi => I.p_nonneg _ (by omega) (by omega))
    (fun i j hij hj => I.p_anti _ _ (by omega) (by omega) (by omega))
  simpa only [mul_ite, mul_zero] using hh

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem marked_lost_charge (I : LSInstance) (d Q P : ℤ → ℝ)
    (N : ℕ) (hN : N + I.L ≤ I.T) :
    (∑ i ∈ range N, if InTH I d Q P ((i : ℤ) + 1) then 0 else lostLS I d Q ((i : ℤ) + 1)) ≤
      ∑ i ∈ range N, lostLS I d P ((i : ℤ) + 1) := by
  let fQ : ℕ → ℝ := fun i => if lossMark I d Q P ((i : ℤ) + 1) then
    I.p ((i : ℤ) + 1) * lostUnits I d Q ((i : ℤ) + 1) else 0
  let fP : ℕ → ℝ := fun i => I.p ((i : ℤ) + 1) * lostUnits I d P ((i : ℤ) + 1)
  have hall := weighted_loss_prefix_bound I d Q P (N + I.L) hN
  change (∑ i ∈ range (N + I.L), fQ i) ≤ ∑ i ∈ range (N + I.L), fP i at hall
  have hinit : (∑ i ∈ range I.L, fQ i) = ∑ i ∈ range I.L, fP i := by
    apply sum_congr rfl
    intro i hi
    have hiL : (i : ℤ) + 1 ≤ I.L := by have := mem_range.mp hi; omega
    have hm : lossMark I d Q P ((i : ℤ) + 1) := Or.inl hiL
    dsimp [fQ, fP]
    rw [if_pos hm, initial_losses_equal I d Q P ((i : ℤ) + 1) (by omega) hiL]
  rw [← sum_range_add_sum_Ico fQ (by omega : I.L ≤ N + I.L),
    ← sum_range_add_sum_Ico fP (by omega : I.L ≤ N + I.L), hinit] at hall
  have hafter := (add_le_add_iff_left _).mp hall
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, Nat.add_sub_cancel] at hafter
  have hqterm (i : ℕ) : fQ (I.L + i) =
      if InTH I d Q P ((i : ℤ) + 1) then 0 else lostLS I d Q ((i : ℤ) + 1) := by
    have he : ((I.L + i : ℕ) : ℤ) + 1 = (i : ℤ) + 1 + I.L := by push_cast; ring
    change (if lossMark I d Q P (((I.L + i : ℕ) : ℤ) + 1) then
      I.p (((I.L + i : ℕ) : ℤ) + 1) * lostUnits I d Q (((I.L + i : ℕ) : ℤ) + 1) else 0) = _
    rw [he]
    have hh : ¬ ((i : ℤ) + 1 + I.L ≤ I.L) := by omega
    simp only [lossMark, hh, false_or, add_sub_cancel_right, ite_not]
    rfl
  have hpterm (i : ℕ) : fP (I.L + i) = lostLS I d P ((i : ℤ) + 1) := by
    have he : ((I.L + i : ℕ) : ℤ) + 1 = (i : ℤ) + 1 + I.L := by push_cast; ring
    change I.p (((I.L + i : ℕ) : ℤ) + 1) * lostUnits I d P (((I.L + i : ℕ) : ℤ) + 1) = _
    rw [he]
    rfl
  simpa only [hqterm, hpterm] using hafter

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {Q : ℤ → Ω → ℝ}

theorem order_measurable (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    {s r : ℤ} (hsr : s ≤ r) (hrT : r ≤ I.T) :
    Measurable[ℱ r] (fun ω => order I.toInstance (fun j => Q j ω) s) := by
  by_cases hs : s ≤ 0
  · simpa only [order, if_pos hs] using
      (measurable_const : Measurable[ℱ r] (fun _ : Ω => I.q s))
  · simpa only [order, if_neg hs] using
      (hQ.adapted s (by omega) (hsr.trans hrT)).mono (ℱ.mono hsr) le_rfl

theorem onHandNat_measurable (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    (n : ℕ) (hn : (n : ℤ) + 1 ≤ I.T) :
    Measurable[ℱ ((n : ℤ) + 1)]
      (fun ω => onHandNat I (fun j => DP.D j ω) (fun j => Q j ω) n) := by
  induction n with
  | zero =>
    convert measurable_const.add
      (order_measurable hQ (by omega : 1 - (I.L : ℤ) ≤ 1)
        (by simpa using hn)) using 1 <;> rfl
  | succ n ih =>
    have hn' : (n : ℤ) + 2 ≤ I.T := by exact_mod_cast hn
    have hi := (ih (by omega)).mono
      (ℱ.mono (show (n : ℤ) + 1 ≤ (n : ℤ) + 2 by omega)) le_rfl
    have hd := DP.measurable ((n : ℤ) + 1) (by omega) (by omega)
    have hq := order_measurable hQ
      (show (n : ℤ) + 2 - I.L ≤ (n : ℤ) + 2 by omega) hn'
    convert ((hi.sub hd).max measurable_const).add hq using 1
    · congr 1
    · rfl

theorem onHand_measurable (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    {r : ℤ} (hr : 1 ≤ r) (hrT : r ≤ I.T) :
    Measurable[ℱ r] (fun ω => onHand I (fun j => DP.D j ω) (fun j => Q j ω) r) := by
  have he : ((r - 1).toNat : ℤ) + 1 = r := by omega
  have hh := onHandNat_measurable (DP := DP) hQ (r - 1).toNat (by omega)
  rw [he] at hh
  exact hh

theorem truncPos_measurable (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    {s t : ℤ} (hs : 1 ≤ s) (hsT : s ≤ I.T) (hts : t ≤ s) :
    Measurable[ℱ s]
      (fun ω => truncPos I (fun j => DP.D j ω) (fun j => Q j ω) s t) := by
  apply (onHand_measurable hQ hs hsT).add
  apply Finset.measurable_sum
  intro j hj
  exact order_measurable hQ ((Finset.mem_Icc.mp hj).2.trans hts) hsT

theorem feasible_order_nonneg (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    {s : ℤ} (hs : 1 - (I.L : ℤ) ≤ s) (hsT : s ≤ I.T) (ω : Ω) :
    0 ≤ order I.toInstance (fun j => Q j ω) s := by
  by_cases h : s ≤ 0
  · simpa only [order, if_pos h] using I.q_nonneg s hs h
  · simpa only [order, if_neg h] using hQ.nonneg s (by omega) hsT ω

theorem onHandNat_nonneg (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    (d : ℤ → ℝ) (n : ℕ) (hn : (n : ℤ) + 1 ≤ I.T) (ω : Ω) :
    0 ≤ onHandNat I d (fun j => Q j ω) n := by
  cases n with
  | zero =>
    exact add_nonneg I.ni0_nonneg
      (feasible_order_nonneg hQ le_rfl (by omega) ω)
  | succ n =>
    exact add_nonneg (le_max_right _ _)
      (feasible_order_nonneg hQ (by omega) (by omega) ω)

theorem onHand_nonneg (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    (d : ℤ → ℝ) {r : ℤ} (hr : 1 ≤ r) (hrT : r ≤ I.T) (ω : Ω) :
    0 ≤ onHand I d (fun j => Q j ω) r := by
  exact onHandNat_nonneg hQ d (r - 1).toNat (by omega) ω

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B P : ℤ → Ω → ℝ}

def firstCrossing (I : LSInstance) (d B P : ℤ → ℝ) (t j : ℤ) : Prop :=
  truncPos I d P j t ≤ truncPos I d B j t ∧
    ∀ r ∈ Ico t j, truncPos I d B r t < truncPos I d P r t

theorem firstCrossing_measurable
    (hB : IsFeasiblePolicy I.toInstance ℱ B) (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t ≤ j) (hjT : j ≤ I.T) :
    MeasurableSet[ℱ j] {ω | firstCrossing I (fun r => DP.D r ω)
      (fun r => B r ω) (fun r => P r ω) t j} := by
  have hnow := measurableSet_le (truncPos_measurable (DP := DP) hP (ht.trans htj) hjT htj)
    (truncPos_measurable (DP := DP) hB (ht.trans htj) hjT htj)
  have hpast : MeasurableSet[ℱ j] {ω | ∀ r ∈ Ico t j,
      truncPos I (fun a => DP.D a ω) (fun a => B a ω) r t <
      truncPos I (fun a => DP.D a ω) (fun a => P a ω) r t} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    apply MeasurableSet.iInter
    intro hr
    have hr' := mem_Ico.mp hr
    exact measurableSet_lt
      ((truncPos_measurable (DP := DP) hB (ht.trans hr'.1)
        (hr'.2.le.trans hjT) hr'.1).mono (ℱ.mono hr'.2.le) le_rfl)
      ((truncPos_measurable (DP := DP) hP (ht.trans hr'.1)
        (hr'.2.le.trans hjT) hr'.1).mono (ℱ.mono hr'.2.le) le_rfl)
  exact hnow.inter hpast

theorem firstCrossing_unique (I : LSInstance) (d B P : ℤ → ℝ) {t j k : ℤ}
    (htj : t ≤ j) (htk : t ≤ k)
    (hj : firstCrossing I d B P t j) (hk : firstCrossing I d B P t k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim ((not_lt_of_ge hj.1) (hk.2 j (mem_Ico.mpr ⟨htj, h⟩)))
  · exact h
  · exact False.elim ((not_lt_of_ge hk.1) (hj.2 k (mem_Ico.mpr ⟨htk, h⟩)))

theorem not_InTH_iff_firstCrossing (I : LSInstance) (d B P : ℤ → ℝ) (t : ℤ) :
    ¬ InTH I d B P t ↔ ∃ j ∈ Icc t (t + I.L), firstCrossing I d B P t j := by
  classical
  constructor
  · intro h
    have hx : ∃ j ∈ Icc t (t + I.L), truncPos I d P j t ≤ truncPos I d B j t := by
      simpa only [InTH, not_forall, not_lt, exists_prop] using h
    let S := (Icc t (t + I.L)).filter
      (fun j => truncPos I d P j t ≤ truncPos I d B j t)
    have hS : S.Nonempty := by
      rcases hx with ⟨j, hj, hc⟩
      exact ⟨j, mem_filter.mpr ⟨hj, hc⟩⟩
    let j := S.min' hS
    have hj := mem_filter.mp (S.min'_mem hS)
    refine ⟨j, hj.1, hj.2, ?_⟩
    intro r hr
    by_contra hbad
    have hrS : r ∈ S := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨(mem_Ico.mp hr).1,
        (mem_Ico.mp hr).2.le.trans (mem_Icc.mp hj.1).2⟩, le_of_not_gt hbad⟩
    have hle := S.min'_le r hrS
    have hlt := (mem_Ico.mp hr).2
    omega
  · rintro ⟨j, hj, hc⟩ h
    exact (not_lt_of_ge hc.1) (h j hj)

theorem firstCrossing_stock_reset (I : LSInstance) (d B P : ℤ → ℝ)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (hc : firstCrossing I d B P t j) :
    onHand I d B j = order I.toInstance B (j - I.L) := by
  have hh := crossing_reset I d B P (r := j - 1) (t := t) (by omega) (by omega)
    (hc.2 (j - 1) (mem_Ico.mpr ⟨by omega, by omega⟩))
  have he : j - 1 + 1 = j := by omega
  rw [he] at hh
  exact hh hc.1

end LostSalesProof


noncomputable section
namespace LostSalesProof
open scoped Classical
open Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem sum_firstCrossing (I : LSInstance) (d B P : ℤ → ℝ) (t : ℤ) (x : ℝ) :
    (∑ j ∈ Icc t (t + I.L), if firstCrossing I d B P t j then x else 0) =
      if InTH I d B P t then 0 else x := by
  classical
  by_cases h : InTH I d B P t
  · rw [if_pos h]
    apply sum_eq_zero
    intro j hj
    have hn : ¬ firstCrossing I d B P t j := fun hc => (not_lt_of_ge hc.1) (h j hj)
    exact if_neg hn
  · obtain ⟨j, hj, hc⟩ := (not_InTH_iff_firstCrossing I d B P t).mp h
    rw [if_neg h, sum_eq_single j]
    · exact if_pos hc
    · intro k hk hkj
      have hn : ¬ firstCrossing I d B P t k := by
        intro hk'
        exact hkj (firstCrossing_unique I d B P (mem_Icc.mp hk).1 (mem_Icc.mp hj).1 hk' hc)
      exact if_neg hn
    · exact fun hn => False.elim (hn hj)

def markedPeriod (I : LSInstance) (d B P : ℤ → ℝ) (t : ℤ) : ℝ :=
  if InTH I d B P t then holdingLS I d B t else lostLS I d B t

def markedCost (I : LSInstance) (d B P : ℤ → ℝ) : ℝ :=
  ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), markedPeriod I d B P t

theorem markedPeriod_eq_crossing_sum (I : LSInstance) (d B P : ℤ → ℝ) (t : ℤ) :
    markedPeriod I d B P t = holdingLS I d B t +
      ∑ j ∈ Icc t (t + I.L),
        ((if firstCrossing I d B P t j then lostLS I d B t else 0) -
          (if firstCrossing I d B P t j then holdingLS I d B t else 0)) := by
  classical
  rw [sum_sub_distrib, sum_firstCrossing, sum_firstCrossing]
  unfold markedPeriod
  split_ifs <;> ring

end LostSalesProof


noncomputable section
namespace LostSalesProof
open Finset
open scoped Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

theorem pathwise_charge (I : LSInstance) (d Q P : ℤ → ℝ)
    (hQ : PathFeasible I Q) (hP : PathFeasible I P)
    (hd : ∀ r : ℤ, 1 ≤ r → r ≤ I.T → 0 ≤ d r) :
    markedCost I d Q P ≤ costLS I d P := by
  by_cases hLT : I.L ≤ I.T
  · let N := I.T - I.L
    have hN : N + I.L = I.T := Nat.sub_add_cancel hLT
    have he : (I.T : ℤ) - I.L = (N : ℤ) := (Int.ofNat_sub hLT).symm
    unfold markedCost costLS
    rw [he, int_sum_one, int_sum_one]
    have hh := marked_holding_charge I d Q P hQ hP hd N hN
    have hl := marked_lost_charge I d Q P N hN.le
    have hs := add_le_add hh hl
    rw [← sum_add_distrib, ← sum_add_distrib] at hs
    convert hs using 1 <;> try rfl
    apply sum_congr rfl
    intro i _
    unfold markedPeriod
    split_ifs <;> ring
  · have he : Icc (1 : ℤ) ((I.T : ℤ) - I.L) = ∅ := Icc_eq_empty_of_lt (by omega)
    simp only [markedCost, costLS, he, sum_empty, le_refl]

end LostSalesProof
end


noncomputable section
namespace LostSalesProof
open MeasureTheory
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def forwardStock (L : ℕ) (j : ℤ) (Q d : ℤ → ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => max (forwardStock L j Q d a n - d (j + n)) 0 + Q (j + n + 1 - L)

theorem forwardStock_mono (L : ℕ) (j : ℤ) (Q d : ℤ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (n : ℕ) : forwardStock L j Q d a n ≤ forwardStock L j Q d b n := by
  induction n with
  | zero => exact hab
  | succ n ih => exact add_le_add (max_le_max_right 0 (sub_le_sub_right ih _)) le_rfl

theorem forwardStock_native (I : LSInstance) (d Q : ℤ → ℝ) {j : ℤ}
    (hj : 1 ≤ j) (n : ℕ) :
    forwardStock I.L j (order I.toInstance Q) d (onHand I d Q j) n =
      onHand I d Q (j + n) := by
  induction n with
  | zero => simp only [forwardStock, Nat.cast_zero, add_zero]
  | succ n ih =>
    rw [forwardStock, ih]
    have he : j + ((n + 1 : ℕ) : ℤ) = (j + n) + 1 := by push_cast; ring
    rw [he, onHand_step I d Q (j + n) (by omega)]

theorem forwardStock_congr (L : ℕ) (j : ℤ) (Q R d e : ℤ → ℝ) (a : ℝ) (n : ℕ)
    (hQ : ∀ k : ℕ, k < n → Q (j + k + 1 - L) = R (j + k + 1 - L))
    (hd : ∀ k : ℕ, k < n → d (j + k) = e (j + k)) :
    forwardStock L j Q d a n = forwardStock L j R e a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [forwardStock]
    rw [ih (fun k hk => hQ k (by omega)) (fun k hk => hd k (by omega)),
      hQ n (by omega), hd n (by omega)]

theorem forwardStock_measurable {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ) (j : ℤ) {Q d : Ω → ℤ → ℝ} {a : Ω → ℝ}
    (hQ : Measurable Q) (hd : Measurable d) (ha : Measurable a) (n : ℕ) :
    Measurable (fun ω => forwardStock L j (Q ω) (d ω) (a ω) n) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    exact ((ih.sub ((measurable_pi_apply _).comp hd)).max measurable_const).add
      ((measurable_pi_apply _).comp hQ)

def resetStock (L : ℕ) (j e : ℤ) (Q d : ℤ → ℝ) : ℝ :=
  forwardStock L j Q d (Q (j - L)) (e - j).toNat

theorem resetStock_native_le (I : LSInstance) (d Q : ℤ → ℝ) {j e : ℤ}
    (hj : 2 ≤ j) (hje : j ≤ e) :
    resetStock I.L j e (order I.toInstance Q) d ≤ onHand I d Q e := by
  have he : j + ((e - j).toNat : ℤ) = e := by omega
  have ha : order I.toInstance Q (j - I.L) ≤ onHand I d Q j := by
    have hs := onHand_step I d Q (j - 1) (by omega)
    have h1 : j - 1 + 1 = j := by omega
    rw [h1] at hs
    rw [hs]
    exact le_add_of_nonneg_left (le_max_right _ _)
  have hh := forwardStock_mono I.L j (order I.toInstance Q) d ha (e - j).toNat
  rw [forwardStock_native I d Q (by omega), he] at hh
  exact hh

theorem resetStock_native_eq (I : LSInstance) (d Q : ℤ → ℝ) {j e : ℤ}
    (hj : 1 ≤ j) (hje : j ≤ e)
    (hreset : onHand I d Q j = order I.toInstance Q (j - I.L)) :
    resetStock I.L j e (order I.toInstance Q) d = onHand I d Q e := by
  unfold resetStock
  rw [← hreset, forwardStock_native I d Q hj]
  congr 1
  omega

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

def holdingFromStock (I : LSInstance) (t : ℤ) (q : ℝ) (d : ℤ → ℝ) (a : ℝ) : ℝ :=
  I.c t * q + ∑ r ∈ Icc (t + I.L) (I.T : ℤ),
    I.h r * max (q - max (cumDemand d (t + I.L) r - (a - q)) 0) 0

theorem holdingFromStock_mono (I : LSInstance) (t : ℤ) (q : ℝ) (d : ℤ → ℝ)
    (ht : 1 ≤ t) {a b : ℝ} (hab : a ≤ b) :
    holdingFromStock I t q d a ≤ holdingFromStock I t q d b := by
  apply add_le_add le_rfl
  apply sum_le_sum
  intro r hr
  have hr' := mem_Icc.mp hr
  apply mul_le_mul_of_nonneg_left _ (I.h_nonneg r (by omega) hr'.2)
  apply max_le_max_right
  apply sub_le_sub_left
  apply max_le_max_right
  exact sub_le_sub_left (sub_le_sub_right hab q) _

theorem holdingFromStock_nonneg (I : LSInstance) (t : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (d : ℤ → ℝ) (a : ℝ) (ht : 1 ≤ t) (htT : t ≤ I.T) :
    0 ≤ holdingFromStock I t q d a := by
  apply add_nonneg (mul_nonneg (I.c_nonneg t ht htT) hq)
  apply sum_nonneg
  intro r hr
  exact mul_nonneg (I.h_nonneg r (by have := (mem_Icc.mp hr).1; omega)
    (mem_Icc.mp hr).2) (le_max_right _ _)

theorem holdingFromStock_native (I : LSInstance) (d Q : ℤ → ℝ) {t : ℤ}
    (ht : 1 ≤ t) :
    holdingFromStock I t (order I.toInstance Q t) d (onHand I d Q (t + I.L)) =
      holdingLS I d Q t := by
  have hs := onHand_step I d Q (t + I.L - 1) (by have := I.L_pos; omega)
  have he : t + (I.L : ℤ) - 1 + 1 = t + I.L := by omega
  have hq : t + (I.L : ℤ) - I.L = t := by omega
  rw [he, hq] at hs
  simp only [holdingFromStock, holdingLS, hs, add_sub_cancel_right]

theorem resetStock_arrival_le (L : ℕ) (j e : ℤ) (Q d : ℤ → ℝ) (hje : j ≤ e) :
    Q (e - L) ≤ resetStock L j e Q d := by
  have hh : ∀ n : ℕ, Q (j + n - L) ≤ forwardStock L j Q d (Q (j - L)) n := by
    intro n
    cases n with
    | zero => simp only [Nat.cast_zero, add_zero, forwardStock, le_refl]
    | succ n =>
      have he : j + ((n + 1 : ℕ) : ℤ) - L = j + n + 1 - L := by push_cast; ring
      rw [he, forwardStock]
      exact le_add_of_nonneg_left (le_max_right _ _)
  have he : j + ((e - j).toNat : ℤ) = e := by omega
  simpa only [he, resetStock] using hh (e - j).toNat

def resetHolding (I : LSInstance) (d Q : ℤ → ℝ) (t j : ℤ) : ℝ :=
  holdingFromStock I t (order I.toInstance Q t) d
    (resetStock I.L j (t + I.L) (order I.toInstance Q) d)

def resetLost (I : LSInstance) (d Q : ℤ → ℝ) (t j : ℤ) : ℝ :=
  I.p (t + I.L) * max (d (t + I.L) -
    resetStock I.L j (t + I.L) (order I.toInstance Q) d) 0

theorem resetHolding_le (I : LSInstance) (d Q : ℤ → ℝ) {t j : ℤ}
    (ht : 1 ≤ t) (hj : 2 ≤ j) (hje : j ≤ t + I.L) :
    resetHolding I d Q t j ≤ holdingLS I d Q t := by
  rw [← holdingFromStock_native I d Q ht]
  exact holdingFromStock_mono I t _ d ht (resetStock_native_le I d Q hj hje)

theorem lost_le_resetLost (I : LSInstance) (d Q : ℤ → ℝ) {t j : ℤ}
    (_ht : 1 ≤ t) (heT : t + (I.L : ℤ) ≤ I.T) (hj : 2 ≤ j) (hje : j ≤ t + I.L) :
    lostLS I d Q t ≤ resetLost I d Q t j := by
  apply mul_le_mul_of_nonneg_left _ (I.p_nonneg _ (by omega) heT)
  exact max_le_max_right 0 (sub_le_sub_left (resetStock_native_le I d Q hj hje) _)

theorem resetHolding_eq (I : LSInstance) (d Q : ℤ → ℝ) {t j : ℤ}
    (ht : 1 ≤ t) (hj : 1 ≤ j) (hje : j ≤ t + I.L)
    (hs : onHand I d Q j = order I.toInstance Q (j - I.L)) :
    resetHolding I d Q t j = holdingLS I d Q t := by
  unfold resetHolding
  rw [resetStock_native_eq I d Q hj hje hs, holdingFromStock_native I d Q ht]

theorem resetLost_eq (I : LSInstance) (d Q : ℤ → ℝ) {t j : ℤ}
    (hj : 1 ≤ j) (hje : j ≤ t + I.L)
    (hs : onHand I d Q j = order I.toInstance Q (j - I.L)) :
    resetLost I d Q t j = lostLS I d Q t := by
  unfold resetLost
  rw [resetStock_native_eq I d Q hj hje hs]
  rfl

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {Q : ℤ → Ω → ℝ}

def knownOrders (I : LSInstance) (Q : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℤ → ℝ :=
  fun r => if r ≤ t then order I.toInstance (fun a => Q a ω) r else 0

def futureDemands (D : ℤ → Ω → ℝ) (j T : ℤ) (ω : Ω) : ℤ → ℝ :=
  fun r => if j ≤ r ∧ r ≤ T then D r ω else 0

theorem knownOrders_measurable (hQ : IsFeasiblePolicy I.toInstance ℱ Q)
    {t : ℤ} (ht : t ≤ I.T) : Measurable[ℱ t] (knownOrders I Q t) := by
  let : MeasurableSpace Ω := ℱ t
  apply measurable_pi_lambda
  intro r
  by_cases hr : r ≤ t
  · simpa only [knownOrders, if_pos hr] using order_measurable (mΩ := mΩ) hQ hr ht
  · simp only [knownOrders, if_neg hr]
    exact measurable_const

theorem futureDemands_measurable {j : ℤ} (hj : 1 ≤ j) :
    Measurable (futureDemands DP.D j I.T) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : j ≤ r ∧ r ≤ I.T
  · simpa only [futureDemands, if_pos hr] using
      (DP.measurable r (hj.trans hr.1) hr.2).mono (ℱ.le _) le_rfl
  · simp only [futureDemands, if_neg hr]
    exact measurable_const

theorem futureDemands_comap_le (j : ℤ) :
    MeasurableSpace.comap (futureDemands DP.D j I.T) inferInstance ≤
      ⨆ r ∈ {r : ℤ | j ≤ r ∧ r ≤ (I.T : ℤ)},
        MeasurableSpace.comap (DP.D r) inferInstance := by
  let D : ℤ → Ω → ℝ := DP.D
  let : MeasurableSpace Ω := ⨆ r ∈ {r : ℤ | j ≤ r ∧ r ≤ (I.T : ℤ)},
    MeasurableSpace.comap (D r) inferInstance
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro r
  by_cases hr : j ≤ r ∧ r ≤ I.T
  · have hle : MeasurableSpace.comap (D r) inferInstance ≤
        ⨆ k ∈ {k : ℤ | j ≤ k ∧ k ≤ (I.T : ℤ)},
          MeasurableSpace.comap (D k) inferInstance := by
      exact le_iSup_of_le r (le_iSup_of_le
        (show r ∈ {k : ℤ | j ≤ k ∧ k ≤ (I.T : ℤ)} from hr) le_rfl)
    simpa only [futureDemands, if_pos hr] using
      (comap_measurable (D r)).mono hle le_rfl
  · simp only [futureDemands, if_neg hr]
    exact measurable_const

theorem futureDemands_indep (hD : IndependentDemands I ℱ μ DP)
    {j : ℤ} (hj : 1 ≤ j) (hjT : j ≤ I.T) :
    Indep (ℱ j) (MeasurableSpace.comap (futureDemands DP.D j I.T) inferInstance) μ := by
  exact indep_of_indep_of_le_right (hD.indep_future j hj hjT) (futureDemands_comap_le j)

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory Finset
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem holdingFromStock_measurable (I : LSInstance) (t : ℤ)
    {q a : Ω → ℝ} {d : Ω → ℤ → ℝ}
    (hq : Measurable q) (ha : Measurable a) (hd : Measurable d) :
    Measurable (fun ω => holdingFromStock I t (q ω) (d ω) (a ω)) := by
  apply (measurable_const.mul hq).add
  apply Finset.measurable_sum
  intro r _
  apply measurable_const.mul
  apply Measurable.max _ measurable_const
  apply hq.sub
  apply Measurable.max _ measurable_const
  apply Measurable.sub _ (ha.sub hq)
  apply Finset.measurable_sum
  intro k _
  exact (measurable_pi_apply k).comp hd

def resetHoldingKernel (I : LSInstance) (t j : ℤ) (z : (ℤ → ℝ) × (ℤ → ℝ)) : ℝ :=
  holdingFromStock I t (z.1 t) z.2 (resetStock I.L j (t + I.L) z.1 z.2)

def resetLostKernel (I : LSInstance) (t j : ℤ) (z : (ℤ → ℝ) × (ℤ → ℝ)) : ℝ :=
  I.p (t + I.L) * max (z.2 (t + I.L) - resetStock I.L j (t + I.L) z.1 z.2) 0

theorem resetStock_measurable (L : ℕ) (j e : ℤ) :
    Measurable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => resetStock L j e z.1 z.2) := by
  exact forwardStock_measurable L j measurable_fst measurable_snd
    ((measurable_pi_apply _).comp measurable_fst) _

theorem resetHoldingKernel_measurable (I : LSInstance) (t j : ℤ) :
    Measurable (resetHoldingKernel I t j) := by
  exact holdingFromStock_measurable I t ((measurable_pi_apply t).comp measurable_fst)
    (resetStock_measurable I.L j (t + I.L)) measurable_snd

theorem resetLostKernel_measurable (I : LSInstance) (t j : ℤ) :
    Measurable (resetLostKernel I t j) := by
  exact measurable_const.mul ((((measurable_pi_apply _).comp measurable_snd).sub
    (resetStock_measurable I.L j (t + I.L))).max measurable_const)

omit mΩ in
theorem resetStock_frozen (I : LSInstance) (D Q : ℤ → Ω → ℝ) {t j : ℤ}
    (hj : j ≤ t + I.L) (heT : t + (I.L : ℤ) ≤ I.T) (ω : Ω) :
    resetStock I.L j (t + I.L) (knownOrders I Q t ω) (futureDemands D j I.T ω) =
      resetStock I.L j (t + I.L) (order I.toInstance (fun r => Q r ω))
        (fun r => D r ω) := by
  unfold resetStock
  have hbase : knownOrders I Q t ω (j - I.L) =
      order I.toInstance (fun r => Q r ω) (j - I.L) := by
    simp only [knownOrders, if_pos (show j - (I.L : ℤ) ≤ t by omega)]
  rw [hbase]
  apply forwardStock_congr
  · intro k hk
    simp only [knownOrders, if_pos (show j + (k : ℤ) + 1 - I.L ≤ t by omega)]
  · intro k hk
    simp only [futureDemands, if_pos (show j ≤ j + (k : ℤ) ∧ j + k ≤ I.T by omega)]

omit mΩ in
theorem cumDemand_future (D : ℤ → Ω → ℝ) {j a b T : ℤ}
    (hja : j ≤ a) (hbT : b ≤ T) (ω : Ω) :
    cumDemand (futureDemands D j T ω) a b = cumDemand (fun r => D r ω) a b := by
  apply sum_congr rfl
  intro r hr
  have hh := mem_Icc.mp hr
  have h : j ≤ r ∧ r ≤ T := ⟨hja.trans ((le_max_left _ _).trans hh.1), hh.2.trans hbT⟩
  exact if_pos h

omit mΩ in
theorem resetHoldingKernel_eq (I : LSInstance) (D Q : ℤ → Ω → ℝ) {t j : ℤ}
    (hj : j ≤ t + I.L) (heT : t + (I.L : ℤ) ≤ I.T) (ω : Ω) :
    resetHoldingKernel I t j (knownOrders I Q t ω, futureDemands D j I.T ω) =
      resetHolding I (fun r => D r ω) (fun r => Q r ω) t j := by
  unfold resetHoldingKernel resetHolding
  dsimp only
  rw [resetStock_frozen I D Q hj heT ω]
  have hq : knownOrders I Q t ω t = order I.toInstance (fun r => Q r ω) t := by
    simp only [knownOrders, if_pos le_rfl]
  rw [hq]
  unfold holdingFromStock
  congr 1
  apply sum_congr rfl
  intro r hr
  rw [cumDemand_future D hj (mem_Icc.mp hr).2 ω]

omit mΩ in
theorem resetLostKernel_eq (I : LSInstance) (D Q : ℤ → Ω → ℝ) {t j : ℤ}
    (hj : j ≤ t + I.L) (heT : t + (I.L : ℤ) ≤ I.T) (ω : Ω) :
    resetLostKernel I t j (knownOrders I Q t ω, futureDemands D j I.T ω) =
      resetLost I (fun r => D r ω) (fun r => Q r ω) t j := by
  unfold resetLostKernel resetLost
  dsimp only
  rw [resetStock_frozen I D Q hj heT ω]
  simp only [futureDemands, if_pos (show j ≤ t + I.L ∧ t + (I.L : ℤ) ≤ I.T from ⟨hj, heT⟩)]

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Filter
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B : ℤ → Ω → ℝ}

theorem resetHolding_measurable (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    Measurable (fun ω => resetHolding I (fun r => DP.D r ω) (fun r => B r ω) t j) := by
  have hk := (resetHoldingKernel_measurable I t j).comp
    (((knownOrders_measurable (t := t) hB (by omega : t ≤ (I.T : ℤ))).mono (ℱ.le _) le_rfl).prodMk
      (futureDemands_measurable (DP := DP) (by omega : 1 ≤ j)))
  convert hk using 1
  funext ω
  exact (resetHoldingKernel_eq I DP.D B hj heT ω).symm

theorem resetLost_measurable (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    Measurable (fun ω => resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j) := by
  have hk := (resetLostKernel_measurable I t j).comp
    (((knownOrders_measurable (t := t) hB (by omega : t ≤ (I.T : ℤ))).mono (ℱ.le _) le_rfl).prodMk
      (futureDemands_measurable (DP := DP) (by omega : 1 ≤ j)))
  convert hk using 1
  funext ω
  exact (resetLostKernel_eq I DP.D B hj heT ω).symm

theorem resetHolding_integrable (hB : IsDualBalancingLS I ℱ μ DP.D B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    Integrable (fun ω => resetHolding I (fun r => DP.D r ω) (fun r => B r ω) t j) μ := by
  apply (hB.integrable_holding t ht (by omega)).mono_nonneg
    (resetHolding_measurable hB.feasible ht htj hj heT).aestronglyMeasurable
  · exact Eventually.of_forall (fun ω => holdingFromStock_nonneg I t
      (feasible_order_nonneg hB.feasible (by omega) (by omega) ω) _ _ ht (by omega))
  · exact Eventually.of_forall (fun ω => resetHolding_le I _ _ ht (by omega) hj)

theorem resetLost_bound (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t j : ℤ} (ht : 1 ≤ t) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) (ω : Ω) :
    0 ≤ resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j ∧
      resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j ≤
        I.p (t + I.L) * DP.D (t + I.L) ω := by
  have hp := I.p_nonneg (t + I.L) (by omega) heT
  have hd := DP.nonneg (t + I.L) (by omega) heT ω
  have hq := feasible_order_nonneg hB (s := t) (by omega) (by omega) ω
  have ha := resetStock_arrival_le I.L j (t + I.L)
    (order I.toInstance (fun r => B r ω)) (fun r => DP.D r ω) hj
  have he : t + (I.L : ℤ) - I.L = t := by omega
  rw [he] at ha
  constructor
  · exact mul_nonneg hp (le_max_right _ _)
  · apply mul_le_mul_of_nonneg_left _ hp
    exact max_le (sub_le_self _ (hq.trans ha)) hd

theorem resetLost_integrable (hD : IndependentDemands I ℱ μ DP)
    (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    Integrable (fun ω => resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j) μ := by
  apply ((hD.integrable (t + I.L) (by omega) heT).const_mul (I.p (t + I.L))).mono_nonneg
    (resetLost_measurable hB ht htj hj heT).aestronglyMeasurable
  · exact Eventually.of_forall (fun ω => (resetLost_bound hB ht hj heT ω).1)
  · exact Eventually.of_forall (fun ω => (resetLost_bound hB ht hj heT ω).2)

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem independent_integrable {U : Ω → A} {V : Ω → B}
    (hU : Measurable U) (hV : Measurable V) (hi : IndepFun U V μ)
    {f : A × B → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (U ω, V ω)) μ) :
    Integrable f ((μ.map U).prod (μ.map V)) := by
  rw [← hi.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (hU.prodMk hV).aemeasurable).2 hint

theorem independent_integral {U : Ω → A} {V : Ω → B}
    (hU : Measurable U) (hV : Measurable V) (hi : IndepFun U V μ)
    {f : A × B → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (U ω, V ω)) μ) :
    (∫ ω, f (U ω, V ω) ∂μ) =
      ∫ ω, ∫ v, f (U ω, v) ∂μ.map V ∂μ := by
  have hp := independent_integrable hU hV hi hf hint
  calc
    _ = ∫ z, f z ∂μ.map (fun ω => (U ω, V ω)) :=
      (integral_map (hU.prodMk hV).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(μ.map U).prod (μ.map V) := by
      rw [hi.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
    _ = ∫ u, ∫ v, f (u, v) ∂μ.map V ∂μ.map U := integral_prod f hp
    _ = _ := integral_map hU.aemeasurable
      hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

theorem independent_kernel_integrable {U : Ω → A} {V : Ω → B}
    (hU : Measurable U) (hV : Measurable V) (hi : IndepFun U V μ)
    {f : A × B → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (U ω, V ω)) μ) :
    Integrable (fun ω => ∫ v, f (U ω, v) ∂μ.map V) μ := by
  exact (independent_integrable hU hV hi hf hint).integral_prod_left.comp_measurable hU

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory

variable {Ω A B : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem indep_parameter {m : MeasurableSpace Ω} {U : Ω → A} {V : Ω → B}
    (hU : Measurable[m] U)
    (hi : Indep m (MeasurableSpace.comap V inferInstance) μ) : IndepFun U V μ := by
  exact indep_of_indep_of_le_left hi hU.comap_le

theorem independent_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {U : Ω → A} {V : Ω → B} (hU : Measurable[m] U) (hV : Measurable[mΩ] V)
    (hi : Indep m (MeasurableSpace.comap V inferInstance) μ)
    {f : A × B → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (U ω, V ω)) μ) :
    μ[fun ω => f (U ω, V ω) | m] =ᵐ[μ]
      fun ω => ∫ v, f (U ω, v) ∂(@Measure.map Ω B mΩ inferInstance V μ) := by
  let : MeasurableSpace Ω := mΩ
  have hUa : Measurable U := hU.mono hm le_rfl
  have hiU := indep_parameter hU hi
  have hk := independent_kernel_integrable hUa hV hiU hf hint
  have hkm : StronglyMeasurable[m] (fun ω => ∫ v, f (U ω, v) ∂μ.map V) :=
    hf.stronglyMeasurable.integral_prod_right'.comp_measurable hU
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun _ _ _ => hk.integrableOn) _ hkm.aestronglyMeasurable
  intro s hs _
  have hsa : MeasurableSet s := hm s hs
  let W : Ω → A × ℝ := fun ω => (U ω, s.indicator (fun _ => 1) ω)
  have hW : Measurable[m] W := hU.prodMk (measurable_const.indicator hs)
  let F : (A × ℝ) × B → ℝ := fun z => z.1.2 * f (z.1.1, z.2)
  have hF : Measurable F := measurable_fst.snd.mul
    (hf.comp (measurable_fst.fst.prodMk measurable_snd))
  have hEq : (fun ω => F (W ω, V ω)) = s.indicator (fun ω => f (U ω, V ω)) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [F, W, hω]
  have hIF : Integrable (fun ω => F (W ω, V ω)) μ := by
    rw [hEq]
    exact hint.indicator hsa
  have he := independent_integral (hW.mono hm le_rfl) hV
    (indep_parameter hW hi) hF hIF
  have hK : (fun ω => ∫ v, F (W ω, v) ∂μ.map V) =
      s.indicator (fun ω => ∫ v, f (U ω, v) ∂μ.map V) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [F, W, hω]
  rw [hEq, hK, integral_indicator hsa, integral_indicator hsa] at he
  exact he.symm

theorem conditional_future_invariance {g m : MeasurableSpace Ω}
    (hgm : g ≤ m) (hm : m ≤ mΩ)
    {U : Ω → A} {V : Ω → B} (hU : Measurable[g] U) (hV : Measurable[mΩ] V)
    (hi : Indep m (MeasurableSpace.comap V inferInstance) μ)
    {f : A × B → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (U ω, V ω)) μ) :
    μ[fun ω => f (U ω, V ω) | m] =ᵐ[μ]
      μ[fun ω => f (U ω, V ω) | g] := by
  let : MeasurableSpace Ω := mΩ
  exact (independent_condExp hm (hU.mono hgm le_rfl) hV hi hf hint).trans
    (independent_condExp (hgm.trans hm) hU hV
      (indep_of_indep_of_le_left hi hgm) hf hint).symm

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B : ℤ → Ω → ℝ}

theorem resetHolding_condExp (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    μ[(fun ω => resetHolding I (fun r => DP.D r ω) (fun r => B r ω) t j) | ℱ j] =ᵐ[μ]
      μ[(fun ω => resetHolding I (fun r => DP.D r ω) (fun r => B r ω) t j) | ℱ t] := by
  have heq : (fun ω => resetHoldingKernel I t j
      (knownOrders I B t ω, futureDemands DP.D j I.T ω)) =
      (fun ω => resetHolding I (fun r => DP.D r ω) (fun r => B r ω) t j) :=
    funext (resetHoldingKernel_eq I DP.D B hj heT)
  have hint : Integrable (fun ω => resetHoldingKernel I t j
      (knownOrders I B t ω, futureDemands DP.D j I.T ω)) μ := by
    rw [heq]
    exact resetHolding_integrable hB ht htj hj heT
  have hh := conditional_future_invariance (ℱ.mono htj.le) (ℱ.le j)
    (knownOrders_measurable hB.feasible (by omega : t ≤ (I.T : ℤ)))
    (futureDemands_measurable (DP := DP) (by omega : 1 ≤ j))
    (futureDemands_indep hD (by omega) (hj.trans heT))
    (resetHoldingKernel_measurable I t j) hint
  rw [heq] at hh
  exact hh

theorem resetLost_condExp (hD : IndependentDemands I ℱ μ DP)
    (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t < j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    μ[(fun ω => resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j) | ℱ j] =ᵐ[μ]
      μ[(fun ω => resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j) | ℱ t] := by
  have heq : (fun ω => resetLostKernel I t j
      (knownOrders I B t ω, futureDemands DP.D j I.T ω)) =
      (fun ω => resetLost I (fun r => DP.D r ω) (fun r => B r ω) t j) :=
    funext (resetLostKernel_eq I DP.D B hj heT)
  have hint : Integrable (fun ω => resetLostKernel I t j
      (knownOrders I B t ω, futureDemands DP.D j I.T ω)) μ := by
    rw [heq]
    exact resetLost_integrable hD hB ht htj hj heT
  have hh := conditional_future_invariance (ℱ.mono htj.le) (ℱ.le j)
    (knownOrders_measurable hB (by omega : t ≤ (I.T : ℤ)))
    (futureDemands_measurable (DP := DP) (by omega : 1 ≤ j))
    (futureDemands_indep hD (by omega) (hj.trans heT))
    (resetLostKernel_measurable I t j) hint
  rw [heq] at hh
  exact hh

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem reset_indicator_factor {g m : MeasurableSpace Ω}
    (hgm : g ≤ m) (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m] E)
    {X R : Ω → ℝ} (hR : Integrable R μ)
    (heq : ∀ ω ∈ E, X ω = R ω)
    (hinv : μ[R | m] =ᵐ[μ] μ[R | g]) :
    μ[E.indicator X | g] =ᵐ[μ]
      (fun ω => μ[E.indicator (fun _ => (1 : ℝ)) | g] ω * μ[R | g] ω) := by
  let : MeasurableSpace Ω := mΩ
  have hEa : MeasurableSet E := hm E hE
  have hind : E.indicator X = E.indicator R := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω, heq ω hω]
    · simp only [Set.indicator_of_notMem hω]
  rw [hind]
  have hmid : μ[E.indicator R | m] =ᵐ[μ] E.indicator (μ[R | g]) := by
    filter_upwards [condExp_indicator hR hE, hinv] with ω hω hr
    by_cases he : ω ∈ E <;> simpa [he, hr] using hω
  have htower : μ[E.indicator R | g] =ᵐ[μ] μ[E.indicator (μ[R | g]) | g] :=
    (condExp_condExp_of_le hgm hm).symm.trans (condExp_congr_ae hmid)
  have hfun : E.indicator (μ[R | g]) =
      E.indicator (fun _ => (1 : ℝ)) * μ[R | g] := by
    funext ω
    by_cases he : ω ∈ E <;> simp [he]
  have hint : Integrable (E.indicator (fun _ => (1 : ℝ)) * μ[R | g]) μ := by
    rw [← hfun]
    exact integrable_condExp.indicator hEa
  have hp := condExp_mul_of_stronglyMeasurable_right
    (stronglyMeasurable_condExp (m := g) (f := R)) hint
    ((integrable_const (1 : ℝ)).indicator hEa)
  rw [hfun] at htower
  exact htower.trans hp

theorem reset_indicator_le {g m : MeasurableSpace Ω}
    (hgm : g ≤ m) (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m] E)
    {X R : Ω → ℝ} (hX : Integrable X μ) (hR : Integrable R μ)
    (heq : ∀ ω ∈ E, X ω = R ω) (hRX : R ≤ᵐ[μ] X)
    (hinv : μ[R | m] =ᵐ[μ] μ[R | g]) :
    μ[E.indicator X | g] ≤ᵐ[μ]
      (fun ω => μ[E.indicator (fun _ => (1 : ℝ)) | g] ω * μ[X | g] ω) := by
  let : MeasurableSpace Ω := mΩ
  have hn : 0 ≤ᵐ[μ] E.indicator (fun _ : Ω => (1 : ℝ)) :=
    Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [reset_indicator_factor hgm hm hE hR heq hinv,
    condExp_mono (m := g) hR hX hRX, condExp_nonneg (m := g) hn] with ω he hc ha
  rw [he]
  exact mul_le_mul_of_nonneg_left hc ha

theorem reset_indicator_ge {g m : MeasurableSpace Ω}
    (hgm : g ≤ m) (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m] E)
    {X R : Ω → ℝ} (hX : Integrable X μ) (hR : Integrable R μ)
    (heq : ∀ ω ∈ E, X ω = R ω) (hXR : X ≤ᵐ[μ] R)
    (hinv : μ[R | m] =ᵐ[μ] μ[R | g]) :
    (fun ω => μ[E.indicator (fun _ => (1 : ℝ)) | g] ω * μ[X | g] ω) ≤ᵐ[μ]
      μ[E.indicator X | g] := by
  let : MeasurableSpace Ω := mΩ
  have hn : 0 ≤ᵐ[μ] E.indicator (fun _ : Ω => (1 : ℝ)) :=
    Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [reset_indicator_factor hgm hm hE hR heq hinv,
    condExp_mono (m := g) hX hR hXR, condExp_nonneg (m := g) hn] with ω he hc ha
  rw [he]
  exact mul_le_mul_of_nonneg_left hc ha

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Filter
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B P : ℤ → Ω → ℝ}

def crossingSet (I : LSInstance) (D B P : ℤ → Ω → ℝ) (t j : ℤ) : Set Ω :=
  {ω | firstCrossing I (fun r => D r ω) (fun r => B r ω) (fun r => P r ω) t j}

theorem crossing_holding_correlation (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t ≤ j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    μ[(crossingSet I DP.D B P t j).indicator (randHoldingLS I DP.D B t) | ℱ t] ≤ᵐ[μ]
      (fun ω => μ[(crossingSet I DP.D B P t j).indicator (fun _ => (1 : ℝ)) | ℱ t] ω *
        μ[randHoldingLS I DP.D B t | ℱ t] ω) := by
  have hE := firstCrossing_measurable (DP := DP) hB.feasible hP ht htj (hj.trans heT)
  have hH := hB.integrable_holding t ht (by omega)
  rcases eq_or_lt_of_le htj with rfl | hlt
  · exact reset_indicator_le le_rfl (ℱ.le t) hE hH hH (fun _ _ => rfl)
      (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ => rfl)
  · apply reset_indicator_le (ℱ.mono hlt.le) (ℱ.le j) hE hH
      (resetHolding_integrable hB ht hlt hj heT)
    · intro ω hω
      exact (resetHolding_eq I (fun r => DP.D r ω) (fun r => B r ω)
        ht (by omega) hj (firstCrossing_stock_reset I _ _ _ ht hlt hj hω)).symm
    · exact Eventually.of_forall (fun ω => resetHolding_le I _ _ ht (by omega) hj)
    · exact resetHolding_condExp hD hB ht hlt hj heT

theorem crossing_lost_correlation (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t ≤ j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    (fun ω => μ[(crossingSet I DP.D B P t j).indicator (fun _ => (1 : ℝ)) | ℱ t] ω *
      μ[randLostLS I DP.D B t | ℱ t] ω) ≤ᵐ[μ]
      μ[(crossingSet I DP.D B P t j).indicator (randLostLS I DP.D B t) | ℱ t] := by
  have hE := firstCrossing_measurable (DP := DP) hB.feasible hP ht htj (hj.trans heT)
  have hL := hB.integrable_lost t ht (by omega)
  rcases eq_or_lt_of_le htj with rfl | hlt
  · exact reset_indicator_ge le_rfl (ℱ.le t) hE hL hL (fun _ _ => rfl)
      (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ => rfl)
  · apply reset_indicator_ge (ℱ.mono hlt.le) (ℱ.le j) hE hL
      (resetLost_integrable hD hB.feasible ht hlt hj heT)
    · intro ω hω
      exact (resetLost_eq I (fun r => DP.D r ω) (fun r => B r ω)
        (by omega) hj (firstCrossing_stock_reset I _ _ _ ht hlt hj hω)).symm
    · exact Eventually.of_forall (fun ω => lost_le_resetLost I _ _ ht heT (by omega) hj)
    · exact resetLost_condExp hD hB.feasible ht hlt hj heT

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Classical ENNReal
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B P : ℤ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem crossingSet_measurable
    (hB : IsFeasiblePolicy I.toInstance ℱ B) (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t ≤ j) (hjT : j ≤ I.T) :
    MeasurableSet (crossingSet I DP.D B P t j) :=
  (ℱ.le j) _ (firstCrossing_measurable (DP := DP) hB hP ht htj hjT)

theorem crossing_integral_le (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t j : ℤ} (ht : 1 ≤ t) (htj : t ≤ j) (hj : j ≤ t + I.L)
    (heT : t + (I.L : ℤ) ≤ I.T) :
    (∫ ω, (crossingSet I DP.D B P t j).indicator (randHoldingLS I DP.D B t) ω ∂μ) ≤
      ∫ ω, (crossingSet I DP.D B P t j).indicator (randLostLS I DP.D B t) ω ∂μ := by
  have hh := crossing_holding_correlation hD hB hP ht htj hj heT
  have hl := crossing_lost_correlation hD hB hP ht htj hj heT
  have hb := hB.balance t ht (by omega)
  have he : μ[(crossingSet I DP.D B P t j).indicator (randHoldingLS I DP.D B t) | ℱ t] ≤ᵐ[μ]
      μ[(crossingSet I DP.D B P t j).indicator (randLostLS I DP.D B t) | ℱ t] := by
    filter_upwards [hh, hl, hb] with ω hhω hlω hbω
    rw [hbω] at hhω
    exact hhω.trans hlω
  have hi := integral_mono_ae integrable_condExp integrable_condExp he
  simpa only [integral_condExp (ℱ.le t)] using hi

omit [IsProbabilityMeasure μ] in
theorem markedPeriod_random_eq (t : ℤ) :
    (fun ω => markedPeriod I (fun r => DP.D r ω) (fun r => B r ω) (fun r => P r ω) t) =
      (fun ω => randHoldingLS I DP.D B t ω +
        ∑ j ∈ Icc t (t + I.L),
          ((crossingSet I DP.D B P t j).indicator (randLostLS I DP.D B t) ω -
            (crossingSet I DP.D B P t j).indicator (randHoldingLS I DP.D B t) ω)) := by
  funext ω
  exact markedPeriod_eq_crossing_sum I _ _ _ t

omit [IsProbabilityMeasure μ] in
theorem markedPeriod_integrable (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t : ℤ} (ht : 1 ≤ t) (heT : t + (I.L : ℤ) ≤ I.T) :
    Integrable (fun ω => markedPeriod I (fun r => DP.D r ω)
      (fun r => B r ω) (fun r => P r ω) t) μ := by
  rw [markedPeriod_random_eq]
  apply (hB.integrable_holding t ht (by omega)).add
  apply integrable_finsetSum
  intro j hj
  have hj' := mem_Icc.mp hj
  have hE := crossingSet_measurable (DP := DP) hB.feasible hP ht hj'.1 (hj'.2.trans heT)
  exact ((hB.integrable_lost t ht (by omega)).indicator hE).sub
    ((hB.integrable_holding t ht (by omega)).indicator hE)

theorem holding_integral_le_markedPeriod (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    {t : ℤ} (ht : 1 ≤ t) (heT : t + (I.L : ℤ) ≤ I.T) :
    (∫ ω, randHoldingLS I DP.D B t ω ∂μ) ≤
      ∫ ω, markedPeriod I (fun r => DP.D r ω) (fun r => B r ω) (fun r => P r ω) t ∂μ := by
  have hH := hB.integrable_holding t ht (by omega)
  have hL := hB.integrable_lost t ht (by omega)
  have hE : ∀ j ∈ Icc t (t + I.L), MeasurableSet (crossingSet I DP.D B P t j) := by
    intro j hj
    exact crossingSet_measurable (DP := DP) hB.feasible hP ht (mem_Icc.mp hj).1
      ((mem_Icc.mp hj).2.trans heT)
  have hInt : ∀ j ∈ Icc t (t + I.L), Integrable (fun ω =>
      (crossingSet I DP.D B P t j).indicator (randLostLS I DP.D B t) ω -
      (crossingSet I DP.D B P t j).indicator (randHoldingLS I DP.D B t) ω) μ :=
    fun j hj => (hL.indicator (hE j hj)).sub (hH.indicator (hE j hj))
  rw [markedPeriod_random_eq, integral_add hH (integrable_finsetSum _ hInt),
    integral_finsetSum _ hInt]
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro j hj
  rw [integral_sub (hL.indicator (hE j hj)) (hH.indicator (hE j hj))]
  exact sub_nonneg.mpr (crossing_integral_le hD hB hP ht
    (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 heT)

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Classical
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℤ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {I : LSInstance}
  {DP : DemandProcess ℱ μ I.T} {B P : ℤ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem stochastic_holding_nonneg (hB : IsFeasiblePolicy I.toInstance ℱ B)
    {t : ℤ} (ht : 1 ≤ t) (htT : t ≤ I.T) (ω : Ω) :
    0 ≤ randHoldingLS I DP.D B t ω := by
  rw [randHoldingLS, ← holdingFromStock_native I _ _ ht]
  exact holdingFromStock_nonneg I t
    (feasible_order_nonneg hB (by omega) htT ω) _ _ ht htT

omit [IsProbabilityMeasure μ] in
theorem stochastic_lost_nonneg {t : ℤ} (ht : 1 ≤ t)
    (heT : t + (I.L : ℤ) ≤ I.T) (ω : Ω) :
    0 ≤ randLostLS I DP.D B t ω := by
  exact mul_nonneg (I.p_nonneg _ (by omega) heT) (le_max_right _ _)

omit [IsProbabilityMeasure μ] in
theorem costLS_integrable (hB : IsDualBalancingLS I ℱ μ DP.D B) :
    Integrable (fun ω => costLS I (fun r => DP.D r ω) (fun r => B r ω)) μ := by
  apply integrable_finsetSum
  intro t ht
  exact (hB.integrable_holding t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2).add
    (hB.integrable_lost t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2)

omit [IsProbabilityMeasure μ] in
theorem markedCost_integrable (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    Integrable (fun ω => markedCost I (fun r => DP.D r ω)
      (fun r => B r ω) (fun r => P r ω)) μ := by
  apply integrable_finsetSum
  intro t ht
  exact markedPeriod_integrable hB hP (mem_Icc.mp ht).1 (by have := (mem_Icc.mp ht).2; omega)

omit [IsProbabilityMeasure μ] in
theorem costLS_nonneg_stochastic (hB : IsFeasiblePolicy I.toInstance ℱ B) (ω : Ω) :
    0 ≤ costLS I (fun r => DP.D r ω) (fun r => B r ω) := by
  apply sum_nonneg
  intro t ht
  have h := mem_Icc.mp ht
  exact add_nonneg (stochastic_holding_nonneg hB h.1 (by omega) ω)
    (stochastic_lost_nonneg h.1 (by omega) ω)

omit [IsProbabilityMeasure μ] in
theorem markedCost_nonneg_stochastic (hB : IsFeasiblePolicy I.toInstance ℱ B) (ω : Ω) :
    0 ≤ markedCost I (fun r => DP.D r ω) (fun r => B r ω) (fun r => P r ω) := by
  apply sum_nonneg
  intro t ht
  have h := mem_Icc.mp ht
  unfold markedPeriod
  split_ifs
  · exact stochastic_holding_nonneg hB h.1 (by omega) ω
  · exact stochastic_lost_nonneg h.1 (by omega) ω

theorem cost_integral_le_twice_marked (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    (∫ ω, costLS I (fun r => DP.D r ω) (fun r => B r ω) ∂μ) ≤
      2 * ∫ ω, markedCost I (fun r => DP.D r ω) (fun r => B r ω) (fun r => P r ω) ∂μ := by
  have hsum : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
      Integrable (fun ω => holdingLS I (fun r => DP.D r ω) (fun r => B r ω) t +
        lostLS I (fun r => DP.D r ω) (fun r => B r ω) t) μ := by
    intro t ht
    exact (hB.integrable_holding t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2).add
      (hB.integrable_lost t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2)
  have hm : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
      Integrable (fun ω => markedPeriod I (fun r => DP.D r ω)
        (fun r => B r ω) (fun r => P r ω) t) μ := by
    intro t ht
    exact markedPeriod_integrable hB hP (mem_Icc.mp ht).1 (by have := (mem_Icc.mp ht).2; omega)
  unfold costLS markedCost
  rw [integral_finsetSum _ hsum, integral_finsetSum _ hm, Finset.mul_sum]
  apply sum_le_sum
  intro t ht
  have h := mem_Icc.mp ht
  have hH := hB.integrable_holding t h.1 h.2
  have hL := hB.integrable_lost t h.1 h.2
  have he : (∫ ω, randHoldingLS I DP.D B t ω ∂μ) =
      ∫ ω, randLostLS I DP.D B t ω ∂μ := by
    rw [← integral_condExp (ℱ.le t) (f := randHoldingLS I DP.D B t),
      ← integral_condExp (ℱ.le t) (f := randLostLS I DP.D B t)]
    exact integral_congr_ae (hB.balance t h.1 h.2)
  change (∫ ω, randHoldingLS I DP.D B t ω + randLostLS I DP.D B t ω ∂μ) ≤ _
  rw [integral_add hH hL]
  have hb := holding_integral_le_markedPeriod hD hB hP h.1 (by omega)
  change (∫ ω, randHoldingLS I DP.D B t ω ∂μ) +
    (∫ ω, randLostLS I DP.D B t ω ∂μ) ≤ _
  linarith

theorem expectedCost_le_twice_marked (hD : IndependentDemands I ℱ μ DP)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    expectedCostLS I μ DP.D B ≤
      2 * ∫⁻ ω, ENNReal.ofReal (markedCost I (fun r => DP.D r ω)
        (fun r => B r ω) (fun r => P r ω)) ∂μ := by
  unfold expectedCostLS
  rw [← ofReal_integral_eq_lintegral_ofReal (costLS_integrable hB)
      (Eventually.of_forall (costLS_nonneg_stochastic hB.feasible)),
    ← ofReal_integral_eq_lintegral_ofReal (markedCost_integrable hB hP)
      (Eventually.of_forall (markedCost_nonneg_stochastic hB.feasible))]
  have hh := ENNReal.ofReal_le_ofReal (cost_integral_le_twice_marked hD hB hP)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hh

end LostSalesProof


noncomputable section
namespace LostSalesProof
open MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing
open scoped ENNReal

theorem full_native_result {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (DP : DemandProcess ℱ μ I.T)
    (hD : IndependentDemands I ℱ μ DP) (B P : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    expectedCostLS I μ DP.D B ≤ 2 * expectedCostLS I μ DP.D P := by
  have hc : (∫⁻ ω, ENNReal.ofReal (markedCost I (fun r => DP.D r ω)
      (fun r => B r ω) (fun r => P r ω)) ∂μ) ≤ expectedCostLS I μ DP.D P := by
    apply lintegral_mono
    intro ω
    apply ENNReal.ofReal_le_ofReal
    apply pathwise_charge
    · exact fun r hr hrT => hB.feasible.nonneg r hr hrT ω
    · exact fun r hr hrT => hP.nonneg r hr hrT ω
    · exact fun r hr hrT => DP.nonneg r hr hrT ω
  exact (expectedCost_le_twice_marked hD hB hP).trans (by gcongr)

end LostSalesProof
end


open LostSalesBalancing.DualBalancing

namespace LostSalesBalancing.DualBalancing

open MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing
open scoped ENNReal

/-- Theorem 3.1: the dual-balancing policy costs at most twice every feasible
nonanticipatory policy, including any optimum when one exists. -/
theorem theorem_3_1 {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (DP : DemandProcess ℱ μ I.T)
    (hD : IndependentDemands I ℱ μ DP) (B P : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    expectedCostLS I μ DP.D B ≤ 2 * expectedCostLS I μ DP.D P := by
  exact LostSalesProof.full_native_result ℱ μ I DP hD B P hB hP

end LostSalesBalancing.DualBalancing

open MeasureTheory ProbabilityTheory LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing
open scoped ENNReal

theorem solution {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (DP : DemandProcess ℱ μ I.T)
    (hD : IndependentDemands I ℱ μ DP) (B P : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P) :
    expectedCostLS I μ DP.D B ≤ 2 * expectedCostLS I μ DP.D P := LostSalesBalancing.DualBalancing.theorem_3_1 ℱ μ I DP hD B P hB hP
