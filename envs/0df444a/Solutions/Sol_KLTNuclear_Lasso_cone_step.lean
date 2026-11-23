-- Prove2me | solution 1 for KLTNuclear.Lasso.cone_step
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:51:48.544335+00:00
-- url     : https://prove2.me/submissions/8d4a0198-8c2a-4d56-aab2-a4c3e2b32295

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

set_option autoImplicit false

open KLTNuclear.Lasso

namespace KLTNuclear.Lasso.ConeProof

theorem key_ineq {n p : ℕ} (hn : 0 < n) (x : Fin n → Fin p → ℝ) (βstar : Fin p → ℝ)
    (ξ Y : Fin n → ℝ) (hY : ∀ i, Y i = ∑ j, x i j * βstar j + ξ i)
    {lam : ℝ} (hlam : 0 < lam) (hM : ∀ j, 3 * |noiseVec x ξ j| ≤ lam)
    {βhat : Fin p → ℝ} (hβhat : IsLasso x Y lam βhat) (β : Fin p → ℝ) :
    2 * ((1 / (n : ℝ)) * ∑ i, design x (βhat - βstar) i * design x (βhat - β) i) +
        (1 / 3) * lam * l1On (βhat - β) (supp β)ᶜ ≤
      (5 / 3) * lam * l1On (βhat - β) (supp β) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set Δ : Fin p → ℝ := βhat - β
  set IP : ℝ := (1 / (n : ℝ)) * ∑ i, design x (βhat - βstar) i * design x Δ i
  set Nterm : ℝ := ∑ j, noiseVec x ξ j * Δ j
  set Q : ℝ := (1 / (n : ℝ)) * ∑ i, (design x Δ i) ^ 2
  have hQ : 0 ≤ Q := by
    unfold Q
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hN_eq : (1 / (n : ℝ)) * ∑ i, ξ i * design x Δ i = Nterm := by
    simp only [Nterm, noiseVec, design]
    rw [Finset.mul_sum]
    have h1 : ∑ i, (1 / (n : ℝ)) * (ξ i * ∑ j, x i j * Δ j) =
        ∑ i, ∑ j, (1 / (n : ℝ)) * (ξ i * x i j) * Δ j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hdir : 2 * IP + lam * l1On Δ (supp β)ᶜ ≤ 2 * Nterm + lam * l1On Δ (supp β) := by
    by_contra hlt
    push Not at hlt
    set G := 2 * IP + lam * l1On Δ (supp β)ᶜ - (2 * Nterm + lam * l1On Δ (supp β))
    have hG : 0 < G := by linarith
    set t := min (1 : ℝ) (G / (2 * (Q + 1)))
    have ht0 : 0 < t := lt_min one_pos (div_pos hG (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ G / (2 * (Q + 1)) := min_le_right _ _
    have htQ : t * Q < G := by
      have h1 : t * (2 * (Q + 1)) ≤ G := (le_div_iff₀ (by positivity)).mp ht2
      nlinarith
    let βt : Fin p → ℝ := fun j => βhat j - t * Δ j
    have hopt := hβhat βt
    have hq_i : ∀ i : Fin n,
        (Y i - ∑ j, x i j * βt j) ^ 2 - (Y i - ∑ j, x i j * βhat j) ^ 2 =
          2 * t * (ξ i * design x Δ i - design x (βhat - βstar) i * design x Δ i) +
            t ^ 2 * (design x Δ i) ^ 2 := by
      intro i
      have hbt : ∑ j, x i j * βt j = design x βhat i - t * design x Δ i := by
        simp only [βt, design]
        have : ∀ j, x i j * (βhat j - t * Δ j) = x i j * βhat j - t * (x i j * Δ j) :=
          fun j => by ring
        simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hbh : Y i - ∑ j, x i j * βhat j = ξ i - design x (βhat - βstar) i := by
        rw [hY i]
        simp only [design, Pi.sub_apply]
        have : ∀ j, x i j * (βhat j - βstar j) = x i j * βhat j - x i j * βstar j :=
          fun j => by ring
        simp only [this, Finset.sum_sub_distrib]
        ring
      have hbh' : Y i - design x βhat i = ξ i - design x (βhat - βstar) i := hbh
      rw [hbt, show Y i - (design x βhat i - t * design x Δ i) =
        (Y i - design x βhat i) + t * design x Δ i by ring, hbh', hbh]
      ring
    have hq_sum : (1 / (n : ℝ)) * ∑ i, (Y i - ∑ j, x i j * βt j) ^ 2 -
        (1 / (n : ℝ)) * ∑ i, (Y i - ∑ j, x i j * βhat j) ^ 2 =
        2 * t * (Nterm - IP) + t ^ 2 * Q := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hq_i i),
        Finset.sum_add_distrib]
      have hlin : ∑ i, 2 * t * (ξ i * design x Δ i - design x (βhat - βstar) i * design x Δ i) =
          2 * t * (∑ i, ξ i * design x Δ i - ∑ i, design x (βhat - βstar) i * design x Δ i) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      have hsq : ∑ i, t ^ 2 * (design x Δ i) ^ 2 = t ^ 2 * ∑ i, (design x Δ i) ^ 2 := by
        rw [← Finset.mul_sum]
      rw [hlin, hsq, mul_add]
      have eN : (1 / (n : ℝ)) * (2 * t * (∑ i, ξ i * design x Δ i -
          ∑ i, design x (βhat - βstar) i * design x Δ i)) =
          2 * t * ((1 / (n : ℝ)) * ∑ i, ξ i * design x Δ i - IP) := by
        simp only [IP]; ring
      have eQ : (1 / (n : ℝ)) * (t ^ 2 * ∑ i, (design x Δ i) ^ 2) = t ^ 2 * Q := by
        simp only [Q]; ring
      rw [eN, hN_eq, eQ]
    have hl1 : l1Norm βt - l1Norm βhat ≤ t * (l1On Δ (supp β) - l1On Δ (supp β)ᶜ) := by
      unfold l1Norm l1On
      rw [← Finset.sum_add_sum_compl (supp β) (fun j => |βt j|),
        ← Finset.sum_add_sum_compl (supp β) (fun j => |βhat j|)]
      have h_on : ∑ j ∈ supp β, |βt j| - ∑ j ∈ supp β, |βhat j| ≤
          t * ∑ j ∈ supp β, |Δ j| := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        simp only [βt]
        have := abs_add_le (βhat j) (-t * Δ j)
        rw [show βhat j + -t * Δ j = βhat j - t * Δ j by ring,
          abs_mul, abs_neg, abs_of_pos ht0] at this
        linarith
      have h_off : ∑ j ∈ (supp β)ᶜ, |βt j| - ∑ j ∈ (supp β)ᶜ, |βhat j| =
          -(t * ∑ j ∈ (supp β)ᶜ, |Δ j|) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hβ0 : β j = 0 := by
          simp only [supp, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
            not_not] at hj
          exact hj
        have hΔj : Δ j = βhat j := by simp [Δ, hβ0]
        have hbtj : βt j = (1 - t) * βhat j := by simp only [βt, hΔj]; ring
        rw [hbtj, hΔj, abs_mul, abs_of_nonneg (by linarith)]
        ring
      linarith
    have hl1_lam : lam * l1Norm βt - lam * l1Norm βhat ≤
        t * lam * (l1On Δ (supp β) - l1On Δ (supp β)ᶜ) := by
      have := mul_le_mul_of_nonneg_left hl1 hlam.le
      linarith
    unfold lassoObj at hopt
    have hcomb : 0 ≤ t * (-G + t * Q) := by
      have : 0 ≤ ((1 / (n : ℝ)) * ∑ i, (Y i - ∑ j, x i j * βt j) ^ 2 -
          (1 / (n : ℝ)) * ∑ i, (Y i - ∑ j, x i j * βhat j) ^ 2) +
          (lam * l1Norm βt - lam * l1Norm βhat) := by linarith
      rw [hq_sum] at this
      have hG_exp : 2 * t * (Nterm - IP) + t ^ 2 * Q +
          t * lam * (l1On Δ (supp β) - l1On Δ (supp β)ᶜ) = t * (-G + t * Q) := by
        simp only [G]; ring
      linarith
    nlinarith
  have hN_bound : 2 * Nterm ≤
      (2 / 3) * lam * (l1On Δ (supp β) + l1On Δ (supp β)ᶜ) := by
    unfold Nterm l1On
    rw [Finset.sum_add_sum_compl (supp β) (fun j => |Δ j|)]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h1 : noiseVec x ξ j * Δ j ≤ |noiseVec x ξ j| * |Δ j| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 := hM j
    have h3 : 0 ≤ |Δ j| := abs_nonneg _
    nlinarith
  linarith

end KLTNuclear.Lasso.ConeProof

open KLTNuclear.Lasso.ConeProof in
theorem solution {n p : ℕ} (hn : 0 < n) (x : Fin n → Fin p → ℝ) (βstar : Fin p → ℝ)
    (ξ Y : Fin n → ℝ) (hY : ∀ i, Y i = ∑ j, x i j * βstar j + ξ i)
    {lam : ℝ} (hlam : 0 < lam) (hM : ∀ j, 3 * |noiseVec x ξ j| ≤ lam)
    {βhat : Fin p → ℝ} (hβhat : IsLasso x Y lam βhat) (β : Fin p → ℝ)
    (hcase : 0 < (1 / (n : ℝ)) * ∑ i, design x (βhat - βstar) i * design x (βhat - β) i) :
    l1On (βhat - β) (supp β)ᶜ ≤ 5 * l1On (βhat - β) (supp β) := by
  have hk := key_ineq hn x βstar ξ Y hY hlam hM hβhat β
  have hle : (1 / 3) * lam * l1On (βhat - β) (supp β)ᶜ ≤
      ((1 / 3) * lam) * (5 * l1On (βhat - β) (supp β)) := by linarith
  exact (mul_le_mul_iff_of_pos_left (by positivity)).mp hle
