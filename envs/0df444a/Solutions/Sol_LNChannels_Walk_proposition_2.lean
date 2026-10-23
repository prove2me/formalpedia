-- Prove2me | solution 1 for LNChannels.Walk.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:08:00.594776+00:00
-- url     : https://prove2.me/submissions/2d57537a-8b12-49a8-8a54-bddc9b0fe8c2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

set_option autoImplicit false

namespace LNChWalkP2

open MarkovMixing LNChannels.Walk Matrix

/-- geometric sum `1 + q + ... + q^(n-1)` -/
noncomputable def G (q : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, q ^ i

lemma G_zero (q : ℝ) : G q 0 = 0 := by simp [G]

lemma G_succ (q : ℝ) (n : ℕ) : G q (n + 1) = 1 + q * G q n := by
  unfold G
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma G_succ' (q : ℝ) (n : ℕ) : G q (n + 1) = G q n + q ^ n := by
  unfold G
  rw [Finset.sum_range_succ]

lemma G_pos (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 1 ≤ n) : 0 < G q n := by
  unfold G
  apply Finset.sum_pos (fun i _ => pow_pos hq i)
  exact ⟨0, by simp; omega⟩

/-- the row of the reset walk applied to a vector -/
lemma row (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (φ : Fin (l₁ + l₂ - 1) → ℝ) (i : Fin (l₁ + l₂ - 1)) :
    (resetWalk lam₁ lam₂ l₁ l₂ *ᵥ φ) i =
      lam₂ / (lam₁ + lam₂) * φ ⟨upTarget l₁ l₂ i, by unfold upTarget; split_ifs <;> omega⟩ +
      lam₁ / (lam₁ + lam₂) * φ ⟨downTarget l₁ i, by unfold downTarget; split_ifs <;> omega⟩ := by
  have key : ∀ (a : ℕ) (ha : a < l₁ + l₂ - 1) (c : ℝ),
      ∑ k : Fin (l₁ + l₂ - 1), (if (k : ℕ) = a then c else 0) * φ k = c * φ ⟨a, ha⟩ := by
    intro a ha c
    rw [Finset.sum_eq_single ⟨a, ha⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      · simp
      · intro h; exact hb (Fin.ext h)
    · simp
  simp only [Matrix.mulVec, dotProduct, resetWalk, add_mul, Finset.sum_add_distrib]
  rw [key, key]

/-- sum over the up-preimage -/
lemma up_sum (l₁ l₂ n : ℕ) (hn : l₁ + l₂ - 1 = n + 1) (g : ℕ → ℝ) (k : ℕ) (hk : k < n + 1) :
    ∑ i ∈ Finset.range (l₁ + l₂ - 1), (if k = upTarget l₁ l₂ i then g i else 0) =
      (if 1 ≤ k then g (k - 1) else 0) + (if k = l₁ - 1 then g n else 0) := by
  rw [hn, Finset.sum_range_succ]
  have h1 : upTarget l₁ l₂ n = l₁ - 1 := by unfold upTarget; rw [if_pos (by omega)]
  rw [h1]
  congr 1
  have h2 : ∀ i ∈ Finset.range n, (if k = upTarget l₁ l₂ i then g i else 0) =
      (if k = i + 1 then g i else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : upTarget l₁ l₂ i = i + 1 := by unfold upTarget; rw [if_neg (by omega)]
    rw [this]
  rw [Finset.sum_congr rfl h2]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h3 : ∀ i ∈ Finset.range n, (if k' + 1 = i + 1 then g i else 0) =
        (if k' = i then g i else 0) := by
      intro i _
      simp only [Nat.add_right_cancel_iff]
    rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    rw [if_pos (by omega), if_pos (by omega)]
    simp

/-- sum over the down-preimage -/
lemma down_sum (l₁ l₂ n : ℕ) (hn : l₁ + l₂ - 1 = n + 1) (g : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (l₁ + l₂ - 1), (if k = downTarget l₁ i then g i else 0) =
      (if k < n then g (k + 1) else 0) + (if k = l₁ - 1 then g 0 else 0) := by
  rw [hn, Finset.sum_range_succ']
  have h1 : downTarget l₁ 0 = l₁ - 1 := by unfold downTarget; simp
  rw [h1]
  congr 1
  have h2 : ∀ i ∈ Finset.range n, (if k = downTarget l₁ (i + 1) then g (i + 1) else 0) =
      (if k = i then g (i + 1) else 0) := by
    intro i _
    have : downTarget l₁ (i + 1) = i := by unfold downTarget; simp
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- the column formula for `vecMul` -/
lemma col (lam₁ lam₂ : ℝ) (l₁ l₂ n : ℕ) (hn : l₁ + l₂ - 1 = n + 1) (g : ℕ → ℝ) (hgN : g (n + 1) = 0)
    (k : Fin (l₁ + l₂ - 1)) :
    Matrix.vecMul (fun i : Fin (l₁ + l₂ - 1) => g i) (resetWalk lam₁ lam₂ l₁ l₂) k =
      lam₂ / (lam₁ + lam₂) * ((if 1 ≤ (k : ℕ) then g (k - 1) else 0) +
          (if (k : ℕ) = l₁ - 1 then g n else 0)) +
      lam₁ / (lam₁ + lam₂) * (g (k + 1) + (if (k : ℕ) = l₁ - 1 then g 0 else 0)) := by
  have hk := k.isLt
  have e1 : Matrix.vecMul (fun i : Fin (l₁ + l₂ - 1) => g i) (resetWalk lam₁ lam₂ l₁ l₂) k =
      lam₂ / (lam₁ + lam₂) * ∑ i : Fin (l₁ + l₂ - 1),
          (if (k : ℕ) = upTarget l₁ l₂ i then g i else 0) +
      lam₁ / (lam₁ + lam₂) * ∑ i : Fin (l₁ + l₂ - 1),
          (if (k : ℕ) = downTarget l₁ i then g i else 0) := by
    simp only [Matrix.vecMul, dotProduct, resetWalk, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [e1]
  have s1 := Fin.sum_univ_eq_sum_range
    (fun i => if (k : ℕ) = upTarget l₁ l₂ i then g i else 0) (l₁ + l₂ - 1)
  have s2 := Fin.sum_univ_eq_sum_range
    (fun i => if (k : ℕ) = downTarget l₁ i then g i else 0) (l₁ + l₂ - 1)
  rw [s1, s2, up_sum l₁ l₂ n hn g k (by omega), down_sum l₁ l₂ n hn g k]
  have : (if (k : ℕ) < n then g (k + 1) else 0) = g (k + 1) := by
    split_ifs with h
    · rfl
    · have : (k : ℕ) = n := by omega
      rw [this, hgN]
  rw [this]

/-- the unnormalised stationary vector -/
noncomputable def gv (q : ℝ) (l₁ l₂ : ℕ) (j : ℕ) : ℝ :=
  if j ≤ l₁ - 1 then G q (j + 1) * G q l₂ else q ^ (j - (l₁ - 1)) * G q (l₂ - (j - (l₁ - 1))) * G q l₁

lemma gv_low (q : ℝ) (l₁ l₂ j : ℕ) (h : j ≤ l₁ - 1) : gv q l₁ l₂ j = G q (j + 1) * G q l₂ := by
  simp [gv, h]

lemma gv_up (q : ℝ) (l₁ l₂ j : ℕ) (hl₁ : 1 ≤ l₁) (h : l₁ - 1 ≤ j) :
    gv q l₁ l₂ j = q ^ (j - (l₁ - 1)) * G q (l₂ - (j - (l₁ - 1))) * G q l₁ := by
  unfold gv
  split_ifs with h'
  · have hj : j = l₁ - 1 := by omega
    subst hj
    simp only [Nat.sub_self, pow_zero, Nat.sub_zero, one_mul]
    rw [Nat.sub_add_cancel hl₁]
    ring
  · rfl

lemma stat_g (p r q : ℝ) (hr : r * (1 + q) = 1) (l₁ l₂ n : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hn : l₁ + l₂ - 1 = n + 1) (hp : p = q * r) (k : ℕ) (hk : k < n + 1) :
    p * ((if 1 ≤ k then gv q l₁ l₂ (k - 1) else 0) + (if k = l₁ - 1 then gv q l₁ l₂ n else 0)) +
      r * (gv q l₁ l₂ (k + 1) + (if k = l₁ - 1 then gv q l₁ l₂ 0 else 0)) = gv q l₁ l₂ k := by
  subst hp
  rcases lt_trichotomy k (l₁ - 1) with hlt | heq | hgt
  · -- lower region
    have hne' : k ≠ l₁ - 1 := by omega
    rw [if_neg hne', if_neg hne', gv_low q l₁ l₂ k (by omega),
      gv_low q l₁ l₂ (k + 1) (by omega)]
    have hprev : (if 1 ≤ k then gv q l₁ l₂ (k - 1) else 0) = G q k * G q l₂ := by
      split_ifs with h1
      · rw [gv_low q l₁ l₂ (k - 1) (by omega), Nat.sub_add_cancel h1]
      · have : k = 0 := by omega
        subst this; rw [G_zero]; ring
    rw [hprev, G_succ q (k + 1), G_succ q k]
    linear_combination (G q l₂ * (1 + q * G q k)) * hr
  · -- the reset state
    subst heq
    rw [if_pos rfl, if_pos rfl]
    obtain ⟨a, ha⟩ : ∃ a, l₁ = a + 1 := ⟨l₁ - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, l₂ = b + 1 := ⟨l₂ - 1, by omega⟩
    have hprev : (if 1 ≤ l₁ - 1 then gv q l₁ l₂ (l₁ - 1 - 1) else 0) = G q a * G q l₂ := by
      split_ifs with h1
      · rw [gv_low q l₁ l₂ _ (by omega)]
        congr 2; omega
      · have : a = 0 := by omega
        rw [this, G_zero]; ring
    rw [hprev, gv_up q l₁ l₂ n hl₁ (by omega), gv_up q l₁ l₂ (l₁ - 1 + 1) hl₁ (by omega),
      gv_low q l₁ l₂ 0 (by omega), gv_low q l₁ l₂ (l₁ - 1) le_rfl]
    have e1 : n - (l₁ - 1) = b := by omega
    have e2 : l₁ - 1 + 1 - (l₁ - 1) = 1 := by omega
    have e3 : l₂ - b = 1 := by omega
    have e4 : l₁ - 1 + 1 = l₁ := by omega
    rw [e1, e2, e3, e4, hb, ha]
    simp only [Nat.add_sub_cancel, zero_add]
    have hW : q ^ b = 1 + q * G q b - G q b := by
      have h1 := G_succ q b
      have h2 := G_succ' q b
      linarith
    rw [G_succ q a, G_succ q b, G_succ q 0, G_zero, hW]
    linear_combination ((1 + q * G q b) * (1 + q * G q a)) * hr
  · -- upper region
    have hne' : k ≠ l₁ - 1 := by omega
    have h1k : 1 ≤ k := by omega
    rw [if_pos h1k, if_neg hne', if_neg hne', add_zero, add_zero,
      gv_up q l₁ l₂ (k - 1) hl₁ (by omega), gv_up q l₁ l₂ (k + 1) hl₁ (by omega),
      gv_up q l₁ l₂ k hl₁ (by omega)]
    obtain ⟨s, hs⟩ : ∃ s, k - (l₁ - 1) = s + 1 := ⟨k - (l₁ - 1) - 1, by omega⟩
    obtain ⟨u, hu⟩ : ∃ u, l₂ - (s + 1) = u + 1 := ⟨l₂ - (s + 1) - 1, by omega⟩
    have e1 : k - 1 - (l₁ - 1) = s := by omega
    have e2 : k + 1 - (l₁ - 1) = s + 2 := by omega
    have e3 : l₂ - s = u + 2 := by omega
    have e4 : l₂ - (s + 2) = u := by omega
    rw [e1, e2, hs, e3, e4, hu, G_succ q (u + 1), G_succ q u]
    linear_combination (q ^ (s + 1) * G q l₁ * (1 + q * G q u)) * hr

/-- the hitting-time function (scaled) -/
noncomputable def Kf (q : ℝ) (M : ℕ) (s : ℕ) : ℝ :=
  (s : ℝ) * (q ^ M - 1) + (M : ℝ) * (q ^ (M - s) - q ^ M)

lemma Kf_zero (q : ℝ) (M : ℕ) : Kf q M 0 = 0 := by simp [Kf]

lemma Kf_M (q : ℝ) (M : ℕ) : Kf q M M = 0 := by simp [Kf]; ring

lemma Kf_rec (p r q : ℝ) (hr : r * (1 + q) = 1) (hp : p = q * r) (M i : ℕ) (hi : i + 2 ≤ M) :
    Kf q M (i + 1) = (r - p) * (q ^ M - 1) + p * Kf q M (i + 2) + r * Kf q M i := by
  subst hp
  obtain ⟨t, rfl⟩ : ∃ t, M = i + 2 + t := ⟨M - (i + 2), by omega⟩
  unfold Kf
  have e1 : i + 2 + t - (i + 1) = t + 1 := by omega
  have e2 : i + 2 + t - (i + 2) = t := by omega
  have e3 : i + 2 + t - i = t + 2 := by omega
  rw [e1, e2, e3]
  push_cast
  linear_combination (-(q ^ (i + 2 + t) - 1) * ((i : ℝ) + 1) - ((i : ℝ) + 2 + t) * q ^ (t + 1)
    + ((i : ℝ) + 2 + t) * q ^ (i + 2 + t)) * hr

theorem main (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁) :
    (∃ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) ∧
    ∀ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m →
      1 / resetFraction lam₁ lam₂ l₁ l₂ m =
        (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
          ((q - 1) * (q ^ (l₁ + l₂) - 1)) := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hq1 : q ≠ 1 := by
    intro h; rw [hq, div_eq_one_iff_eq hlam₁.ne'] at h; exact hne h.symm
  have hlam2 : lam₂ = q * lam₁ := by rw [hq]; field_simp
  have hs : lam₁ + lam₂ ≠ 0 := by positivity
  set p := lam₂ / (lam₁ + lam₂) with hp_def
  set r := lam₁ / (lam₁ + lam₂) with hr_def
  have hr : r * (1 + q) = 1 := by
    rw [hr_def, hlam2]; field_simp; try ring
  have hp : p = q * r := by
    rw [hp_def, hr_def, hlam2]; field_simp
  obtain ⟨n, hn⟩ : ∃ n, l₁ + l₂ - 1 = n + 1 := ⟨l₁ + l₂ - 2, by omega⟩
  constructor
  · -- existence
    have hgN : gv q l₁ l₂ (n + 1) = 0 := by
      rw [gv_up q l₁ l₂ (n + 1) hl₁ (by omega)]
      rw [show l₂ - (n + 1 - (l₁ - 1)) = 0 by omega, G_zero]; ring
    have hgpos : ∀ j, j < n + 1 → 0 < gv q l₁ l₂ j := by
      intro j hj
      rcases le_or_gt j (l₁ - 1) with h | h
      · rw [gv_low q l₁ l₂ j h]
        exact mul_pos (G_pos q hqpos _ (by omega)) (G_pos q hqpos _ hl₂)
      · rw [gv_up q l₁ l₂ j hl₁ h.le]
        exact mul_pos (mul_pos (pow_pos hqpos _) (G_pos q hqpos _ (by omega)))
          (G_pos q hqpos _ hl₁)
    set S := ∑ i : Fin (l₁ + l₂ - 1), gv q l₁ l₂ i with hS
    have hSpos : 0 < S := by
      rw [hS]
      exact Finset.sum_pos (f := fun i : Fin (l₁ + l₂ - 1) => gv q l₁ l₂ i)
        (fun i _ => hgpos i (by have := i.isLt; omega)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    refine ⟨fun i => gv q l₁ l₂ i / S, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (hgpos i (by have := i.isLt; omega)).le hSpos.le
    · rw [← Finset.sum_div, ← hS, div_self hSpos.ne']
    · funext k
      have hc := col lam₁ lam₂ l₁ l₂ n hn (gv q l₁ l₂) hgN k
      have hst := stat_g p r q hr l₁ l₂ n hl₁ hl₂ hn hp k (by have := k.isLt; omega)
      have e : Matrix.vecMul (fun i : Fin (l₁ + l₂ - 1) => gv q l₁ l₂ i / S)
          (resetWalk lam₁ lam₂ l₁ l₂) k =
          Matrix.vecMul (fun i : Fin (l₁ + l₂ - 1) => gv q l₁ l₂ i)
          (resetWalk lam₁ lam₂ l₁ l₂) k / S := by
        simp only [Matrix.vecMul, dotProduct, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [e, hc, hst]
  · -- the ratio
    intro m hm
    obtain ⟨⟨_, hsum⟩, hfix⟩ := hm
    obtain ⟨M, hM⟩ : ∃ M, M = l₁ + l₂ := ⟨_, rfl⟩
    have hMn : M = n + 2 := by omega
    set φ : Fin (l₁ + l₂ - 1) → ℝ := fun k => Kf q M (k + 1) with hφ
    set c := (r - p) * (q ^ M - 1) with hc
    have hrowφ : ∀ i : Fin (l₁ + l₂ - 1), (resetWalk lam₁ lam₂ l₁ l₂ *ᵥ φ) i =
        φ i - c + (if (i : ℕ) = n then p * Kf q M l₁ else 0) +
          (if (i : ℕ) = 0 then r * Kf q M l₁ else 0) := by
      intro i
      have hi := i.isLt
      rw [row lam₁ lam₂ l₁ l₂ hl₁ hl₂ φ i]
      rw [← hp_def, ← hr_def]
      have hrec := Kf_rec p r q hr hp M i (by omega)
      rw [← hc] at hrec
      have hu : Kf q M (upTarget l₁ l₂ i + 1) =
          Kf q M (i + 2) + (if (i : ℕ) = n then Kf q M l₁ else 0) := by
        unfold upTarget
        by_cases h1 : (i : ℕ) + 1 = l₁ + l₂ - 1
        · rw [if_pos h1, if_pos (by omega), show l₁ - 1 + 1 = l₁ by omega,
            show (i : ℕ) + 2 = M by omega, Kf_M]
          ring
        · rw [if_neg h1, if_neg (by omega)]
          ring
      have hd : Kf q M (downTarget l₁ i + 1) =
          Kf q M i + (if (i : ℕ) = 0 then Kf q M l₁ else 0) := by
        unfold downTarget
        by_cases h1 : (i : ℕ) = 0
        · rw [if_pos h1, if_pos h1, show l₁ - 1 + 1 = l₁ by omega, h1, Kf_zero]
          ring
        · rw [if_neg h1, if_neg h1, show (i : ℕ) - 1 + 1 = i by omega]
          ring
      show p * Kf q M (upTarget l₁ l₂ i + 1) + r * Kf q M (downTarget l₁ i + 1) =
        Kf q M (i + 1) - c + (if (i : ℕ) = n then p * Kf q M l₁ else 0) +
          (if (i : ℕ) = 0 then r * Kf q M l₁ else 0)
      rw [hu, hd, hrec]
      split_ifs <;> ring
    have hfin : ∀ (F : Fin (l₁ + l₂ - 1) → ℝ) (a : ℕ) (ha : a < l₁ + l₂ - 1),
        ∑ k : Fin (l₁ + l₂ - 1), (if (k : ℕ) = a then F k else 0) = F ⟨a, ha⟩ := by
      intro F a ha
      rw [Finset.sum_eq_single ⟨a, ha⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h; exact hb (Fin.ext h)
      · simp
    have hdot : m ⬝ᵥ φ = m ⬝ᵥ (resetWalk lam₁ lam₂ l₁ l₂ *ᵥ φ) := by
      rw [Matrix.dotProduct_mulVec, hfix]
    have hexp : m ⬝ᵥ (resetWalk lam₁ lam₂ l₁ l₂ *ᵥ φ) =
        ∑ i : Fin (l₁ + l₂ - 1), (m i * φ i - c * m i +
          (if (i : ℕ) = n then m i * (p * Kf q M l₁) else 0) +
          (if (i : ℕ) = 0 then m i * (r * Kf q M l₁) else 0)) := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i _
      rw [hrowφ i]
      split_ifs <;> ring
    rw [hexp, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hfin _ n (by omega), hfin _ 0 (by omega), ← Finset.mul_sum, hsum] at hdot
    unfold dotProduct at hdot
    have hkey : c = Kf q M l₁ * (p * m ⟨n, by omega⟩ + r * m ⟨0, by omega⟩) := by
      linarith
    have hRF : resetFraction lam₁ lam₂ l₁ l₂ m = p * m ⟨n, by omega⟩ + r * m ⟨0, by omega⟩ := by
      unfold resetFraction massAt
      rw [dif_pos (by omega), dif_pos (by omega), ← hp_def, ← hr_def]
      have a1 : (⟨((l₂ : ℤ) - 1 + l₁ - 1).toNat, by omega⟩ : Fin (l₁ + l₂ - 1)) = ⟨n, by omega⟩ := by
        ext; simp only; omega
      have a2 : (⟨(-(l₁ : ℤ) + 1 + l₁ - 1).toNat, by omega⟩ : Fin (l₁ + l₂ - 1)) = ⟨0, by omega⟩ := by
        ext; simp only; omega
      rw [a1, a2]; ring
    rw [hRF]
    have hQ : q ^ M - 1 ≠ 0 := by
      intro h
      have : q ^ M = 1 := by linarith
      rw [pow_eq_one_iff_of_nonneg hqpos.le (by omega)] at this
      exact hq1 this
    have hrp : r - p ≠ 0 := by
      rw [hp]; intro h
      have : r * (1 - q) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · rw [h'] at hr; simp at hr
      · exact hq1 (by linarith)
    have hc0 : c ≠ 0 := mul_ne_zero hrp hQ
    have hRne : p * m ⟨n, by omega⟩ + r * m ⟨0, by omega⟩ ≠ 0 := by
      intro h; rw [h, mul_zero] at hkey; exact hc0 hkey
    have hK : Kf q M l₁ ≠ 0 := by
      intro h; rw [h, zero_mul] at hkey; exact hc0 hkey
    rw [show p * m ⟨n, by omega⟩ + r * m ⟨0, by omega⟩ = c / Kf q M l₁ by
      rw [hkey]; field_simp]
    rw [one_div_div]
    have hr' : r = 1 / (1 + q) := by
      have : (1 + q) ≠ 0 := by linarith
      field_simp; linarith
    have hq1' : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
    have hq1'' : 1 + q ≠ 0 := by linarith
    rw [hc, hp, hr']
    unfold Kf
    rw [show M - l₁ = l₂ by omega]
    subst hM
    push_cast
    rw [div_eq_div_iff]
    · rw [pow_add]; field_simp; ring
    · intro h
      have : (1 / (1 + q) - q * (1 / (1 + q))) = (1 - q) / (1 + q) := by field_simp
      rw [this] at h
      rcases mul_eq_zero.mp h with h' | h'
      · rcases div_eq_zero_iff.mp h' with h'' | h''
        · exact hq1' (by linarith)
        · exact hq1'' h''
      · exact hQ h'
    · exact mul_ne_zero hq1' hQ

end LNChWalkP2

open LNChannels.Walk in
theorem solution (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁) :
    (∃ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) ∧
    ∀ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m →
      1 / resetFraction lam₁ lam₂ l₁ l₂ m =
        (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
          ((q - 1) * (q ^ (l₁ + l₂) - 1)) := by
  exact LNChWalkP2.main lam₁ lam₂ l₁ l₂ hlam₁ hlam₂ hne hl₁ hl₂ q hq
