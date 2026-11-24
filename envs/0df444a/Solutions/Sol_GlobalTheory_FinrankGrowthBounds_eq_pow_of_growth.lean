-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.eq_pow_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:27.635851+00:00
-- url     : https://prove2.me/submissions/30cea793-1af6-4f82-a571-cca207cd866a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_le_of_pow_le_mul_pow
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_le_of_frequently

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution (h : ℕ → ℕ) (g : ℕ) (G : ℕ → Prop) (hG : ∀ m, G m ∨ G (m + 1))
    (hG0 : ¬ G 0) (h1 : h 1 = 1)
    (hmono : Monotone h) (hrel : ∀ n j, G n → 1 ≤ j → h (n ^ 2 * j) = h (n ^ 2) * h j)
    (N c C : ℕ) (hN : 1 ≤ N)
    (hgr : ∀ t, 1 ≤ t → t ^ g ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ g) (j : ℕ) (hj : 1 ≤ j) :
    h j = j ^ g := by
  have hpos : ∀ n, G n → 1 ≤ n := fun n hn => Nat.pos_of_ne_zero fun e => hG0 (e ▸ hn)
  have hit : ∀ n, G n → ∀ i, 1 ≤ i → ∀ k, h ((n ^ 2) ^ k * i) = h (n ^ 2) ^ k * h i := by
    intro n hn i hi k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hpos n hn
      rw [pow_succ' (n ^ 2), Nat.mul_assoc, hrel n _ hn (Nat.mul_pos (by positivity) hi), ih]
      ring
  have hsq : ∀ n, G n → h (n ^ 2) = (n ^ 2) ^ g := by
    intro n hn
    have hn1 := hpos n hn
    apply le_antisymm
    · refine le_of_pow_le_mul_pow (C := C) (Nat.pos_of_ne_zero (by positivity)) fun k => ?_
      have e := hit n hn 1 le_rfl k
      rw [h1, Nat.mul_one, Nat.mul_one] at e
      rw [← e, ← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      refine le_trans (hmono (Nat.le_mul_of_pos_left _ hN)) (hgr _ (Nat.pos_of_ne_zero (by positivity))).2
    · have hd : 1 ≤ h (n ^ 2) := h1 ▸ hmono (Nat.pos_of_ne_zero (by positivity))
      refine le_of_pow_le_mul_pow (C := c * h N) hd fun k => ?_
      have e := hit n hn N hN k
      have := (hgr ((n ^ 2) ^ k) (Nat.pos_of_ne_zero (by positivity))).1
      rw [mul_comm N, e] at this
      rw [← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      calc _ ≤ _ := this
        _ = _ := by ring
  have hbig : ∀ M, ∃ n, M ≤ n ∧ G n := fun M => (hG M).elim (fun x => ⟨M, le_rfl, x⟩)
    fun x => ⟨M + 1, by omega, x⟩
  apply le_antisymm
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig M
    have hn1 := hpos n hn
    refine ⟨n, hMn, ?_⟩
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m + 1 ≤ m' ∧ m' ≤ m + 2 ∧ G m' :=
      (hG (m + 1)).elim (fun x => ⟨_, le_rfl, by omega, x⟩) fun x => ⟨_, by omega, le_rfl, x⟩
    have hnj : 1 ≤ n * j := Nat.mul_pos hn1 hj
    have l3 : m ≤ n * j := by
      by_contra hc
      push Not at hc
      have : n ^ 2 * j ≤ (n * j) * (n * j) := by nlinarith [Nat.mul_le_mul_left (n ^ 2 * j) hj]
      nlinarith
    have l4 : m' ^ 2 ≤ n * (j * (n + 8)) := by nlinarith
    have l5 : h (n ^ 2 * j) ≤ h (m' ^ 2) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := l5.trans (Nat.pow_le_pow_left l4 g)
    rw [pow_two, mul_pow, mul_pow, mul_pow, Nat.mul_assoc] at l6
    rw [mul_comm]
    exact Nat.le_of_mul_le_mul_left l6 (by positivity)
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig (M + 2)
    have hn1 := hpos n hn
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    have l3 : n ≤ m := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left (n ^ 2) hj]
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m' ≤ m ∧ m ≤ m' + 1 ∧ G m' :=
      (hG (m - 1)).elim (fun x => ⟨_, by omega, by omega, x⟩) fun x => ⟨_, by omega, by omega, x⟩
    have hm1 := hpos m' hm'
    refine ⟨m', by omega, ?_⟩
    have l4 : n ^ 2 * j ≤ m' * (m' + 8) := by nlinarith
    have l5 : h (m' ^ 2) ≤ h (n ^ 2 * j) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := Nat.pow_le_pow_left l4 g
    rw [mul_pow, mul_pow] at l6
    rw [pow_two m', mul_pow] at l5
    have l7 : (n ^ 2) ^ g * (j ^ g * m' ^ g) ≤ (n ^ 2) ^ g * (h j * (m' + 8) ^ g) :=
      calc _ = ((n ^ 2) ^ g * j ^ g) * m' ^ g := by ring
        _ ≤ (m' ^ g * (m' + 8) ^ g) * m' ^ g := Nat.mul_le_mul_right _ l6
        _ = (m' ^ g * m' ^ g) * (m' + 8) ^ g := by ring
        _ ≤ ((n ^ 2) ^ g * h j) * (m' + 8) ^ g := Nat.mul_le_mul_right _ l5
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left l7 (by positivity)
end GlobalTheory.FinrankGrowthBounds
