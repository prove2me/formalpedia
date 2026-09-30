-- Prove2me | solution 1 for InventoryControl.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T20:14:08.139568+00:00
-- url     : https://prove2.me/submissions/78d56559-c866-451f-8afb-fe4486c4881a

import Mathlib
import Definitions.Def_InventoryControl_rqPolicy

set_option autoImplicit false

lemma p2e7_S (p : ℕ → ℝ) (k : ℤ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j : ℝ) * p (k + 1 - j).toNat
      = ∑ j ∈ Finset.Icc (1 : ℤ) k, (j : ℝ) * p (k - j).toNat
        + ∑ i ∈ Finset.Icc (0 : ℤ) k, p i.toNat := by
  have e1 : ∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j : ℝ) * p (k + 1 - j).toNat
      = ∑ j ∈ Finset.Icc (1 : ℤ) (k + 1),
          (((j - 1 : ℤ) : ℝ) * p (k + 1 - j).toNat + p (k + 1 - j).toNat) := by
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [e1, Finset.sum_add_distrib]
  congr 1
  · have e2 : ∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), ((j - 1 : ℤ) : ℝ) * p (k + 1 - j).toNat
        = ∑ j ∈ Finset.Icc (0 : ℤ) k, (j : ℝ) * p (k - j).toNat := by
      apply Finset.sum_nbij' (fun j => j - 1) (fun j => j + 1)
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a _
        simp
      · intro a _
        simp
      · intro a _
        have : k + 1 - a = k - (a - 1) := by ring
        rw [this]
    rw [e2]
    symm
    apply Finset.sum_subset
    · exact Finset.Icc_subset_Icc_left (by norm_num)
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      have : x = 0 := by omega
      subst this
      simp
  · apply Finset.sum_nbij' (fun j => k + 1 - j) (fun j => k + 1 - j)
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      rfl

open InventoryControl in
lemma p2e7_step (D : DiscreteDemand) (h b1 : ℝ) (k : ℤ) :
    sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k
      = -b1 + (h + b1) * ∑ i ∈ Finset.Icc (0 : ℤ) k, D.p i.toNat := by
  unfold sPolicyCost
  rw [p2e7_S]
  push_cast
  ring

open InventoryControl in
lemma p2e7_mono (D : DiscreteDemand) (h b1 : ℝ) (hh : 0 < h) (hb : 0 < b1) (a b : ℤ)
    (hab : a ≤ b) :
    sPolicyCost D h b1 (a + 1) - sPolicyCost D h b1 a
      ≤ sPolicyCost D h b1 (b + 1) - sPolicyCost D h b1 b := by
  rw [p2e7_step, p2e7_step]
  have hC : ∑ i ∈ Finset.Icc (0 : ℤ) a, D.p i.toNat ≤ ∑ i ∈ Finset.Icc (0 : ℤ) b, D.p i.toNat :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hab)
      (fun i _ _ => D.nonneg _)
  have hpos : 0 ≤ h + b1 := by linarith
  have := mul_le_mul_of_nonneg_left hC hpos
  linarith

lemma p2e7_tele (g : ℤ → ℝ) (y : ℤ) (n : ℕ) :
    g (y + n) - g y = ∑ j ∈ Finset.range n, (g (y + j + 1) - g (y + j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    have : y + ((n : ℤ) + 1) = y + n + 1 := by ring
    rw [this]
    ring

lemma p2e7_Tmono (g : ℤ → ℝ) (hd : ∀ a b : ℤ, a ≤ b → g (a + 1) - g a ≤ g (b + 1) - g b)
    (Q : ℕ) (a b : ℤ) (hab : a ≤ b) : g (a + Q) - g a ≤ g (b + Q) - g b := by
  rw [p2e7_tele g a Q, p2e7_tele g b Q]
  apply Finset.sum_le_sum
  intro j _
  apply hd
  omega

lemma p2e7_W (g : ℤ → ℝ) (Q : ℕ) (y : ℤ) :
    ∑ j ∈ Finset.range Q, g (y + 1 + j) - ∑ j ∈ Finset.range Q, g (y + j)
      = g (y + Q) - g y := by
  rw [← Finset.sum_sub_distrib, p2e7_tele g y Q]
  apply Finset.sum_congr rfl
  intro j _
  have : y + 1 + (j : ℤ) = y + j + 1 := by ring
  rw [this]

lemma p2e7_band_min (g : ℤ → ℝ)
    (hd : ∀ a b : ℤ, a ≤ b → g (a + 1) - g a ≤ g (b + 1) - g b)
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ)
    (hR : ∀ y : ℤ, ∑ j ∈ Finset.range Q, g (R + 1 + j) ≤ ∑ j ∈ Finset.range Q, g (y + 1 + j))
    (w : ℤ) (hw1 : R + 1 ≤ w) (hw2 : w ≤ R + Q) (x : ℤ) : g w ≤ g (w + x * Q) := by
  have hT1 : 0 ≤ g (R + 1 + Q) - g (R + 1) := by
    have h1 := hR (R + 1)
    have h2 := p2e7_W g Q (R + 1)
    linarith
  have hT0 : g (R + Q) - g R ≤ 0 := by
    have h1 := hR (R - 1)
    have h2 := p2e7_W g Q R
    simp only [sub_add_cancel] at h1
    linarith
  have hQ0 : (0 : ℤ) ≤ Q := by positivity
  have up : ∀ n : ℕ, g w ≤ g (w + (n : ℤ) * Q) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hT := p2e7_Tmono g hd Q (R + 1) (w + (n : ℤ) * Q) (by nlinarith)
      have e : w + ((n + 1 : ℕ) : ℤ) * Q = w + (n : ℤ) * Q + Q := by push_cast; ring
      rw [e]
      linarith
  have down : ∀ n : ℕ, g w ≤ g (w - (n : ℤ) * Q) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hT := p2e7_Tmono g hd Q (w - ((n + 1 : ℕ) : ℤ) * Q) R (by push_cast; nlinarith)
      have e : w - ((n + 1 : ℕ) : ℤ) * Q + Q = w - (n : ℤ) * Q := by push_cast; ring
      rw [e] at hT
      linarith
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg x
  · rw [hn]
    exact up n
  · rw [hn]
    have e : w + -(n : ℤ) * Q = w - (n : ℤ) * Q := by ring
    rw [e]
    exact down n

open InventoryControl in
lemma p2e7_band (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : ℤ) :
    R + 1 ≤ reduceToBand R Q z ∧ reduceToBand R Q z ≤ R + Q ∧
      (Q : ℤ) ∣ reduceToBand R Q z - z := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  unfold reduceToBand
  refine ⟨?_, ?_, ?_⟩
  · have := Int.emod_nonneg (z - (R + 1)) hQ'.ne'
    linarith
  · have := Int.emod_lt_of_pos (z - (R + 1)) hQ'
    linarith
  · have h := Int.emod_add_mul_ediv (z - (R + 1)) (Q : ℤ)
    exact ⟨-((z - (R + 1)) / (Q : ℤ)), by linear_combination h⟩

open InventoryControl in
theorem solution (D : DiscreteDemand) (h b1 : ℝ) (hh : 0 < h) (hb : 0 < b1) (Q : ℕ) (hQ : 0 < Q)
    (R : ℤ) (hR : ∀ y : ℤ, windowCost D h b1 Q R ≤ windowCost D h b1 Q y) (z : ℤ) :
    (∀ x : ℤ, sPolicyCost D h b1 (z + (x + 1) * Q) - sPolicyCost D h b1 (z + x * Q)
        ≤ sPolicyCost D h b1 (z + (x + 2) * Q) - sPolicyCost D h b1 (z + (x + 1) * Q))
      ∧ (R + 1 ≤ reduceToBand R Q z ∧ reduceToBand R Q z ≤ R + Q
          ∧ ∃ x : ℤ, reduceToBand R Q z = z + x * Q)
      ∧ ∀ x : ℤ, sPolicyCost D h b1 (reduceToBand R Q z) ≤ sPolicyCost D h b1 (z + x * Q) := by
  have hd := p2e7_mono D h b1 hh hb
  obtain ⟨b1', b2', b3'⟩ := p2e7_band R Q hQ z
  obtain ⟨c, hc⟩ := b3'
  have hx0 : reduceToBand R Q z = z + c * Q := by linear_combination hc
  refine ⟨?_, ⟨b1', b2', c, hx0⟩, ?_⟩
  · intro x
    have hT := p2e7_Tmono (sPolicyCost D h b1) hd Q (z + x * Q) (z + (x + 1) * Q) (by nlinarith)
    have e1 : z + (x + 1) * (Q : ℤ) = z + x * Q + Q := by ring
    have e2 : z + (x + 2) * (Q : ℤ) = z + (x + 1) * Q + Q := by ring
    rw [e2, e1]
    rw [e1] at hT
    exact hT
  · intro x
    have hR' : ∀ y : ℤ, ∑ j ∈ Finset.range Q, sPolicyCost D h b1 (R + 1 + j)
        ≤ ∑ j ∈ Finset.range Q, sPolicyCost D h b1 (y + 1 + j) := by
      intro y
      exact hR y
    have key := p2e7_band_min (sPolicyCost D h b1) hd Q hQ R hR' (reduceToBand R Q z) b1' b2'
      (x - c)
    have e : z + x * (Q : ℤ) = reduceToBand R Q z + (x - c) * Q := by rw [hx0]; ring
    rw [e]
    exact key
