-- Prove2me | solution 1 for L0BnB.Duality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T07:56:05.56323+00:00
-- url     : https://prove2.me/submissions/525f8512-5b20-4f70-9380-ea079840d969

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace Accepted45

set_option autoImplicit false
open L0BnB.Duality

namespace SparseDualitySupport

lemma sqrt_scaling (l0 l2 : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) = 1 ∧
    l0 * Real.sqrt (l2 / l0) = Real.sqrt (l0 * l2) := by
  constructor
  · rw [← Real.sqrt_mul (div_pos h0 h2).le]
    have : l0 / l2 * (l2 / l0) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  · have hs := Real.sq_sqrt (div_pos h2 h0).le
    have hw := Real.sq_sqrt (mul_pos h0 h2).le
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hx : l0 * Real.sqrt (l2 / l0) ^ 2 = l2 := by
      rw [hs]; field_simp
    nlinarith

lemma psi1_linear (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2)
    (hb : |b| ≤ Real.sqrt (l0 / l2)) :
    L0BnB.Reduced.psi1 l0 l2 b = 2 * Real.sqrt (l0 * l2) * |b| := by
  obtain ⟨ht, hw⟩ := sqrt_scaling l0 l2 h0 h2
  have hs := Real.sqrt_nonneg (l2 / l0)
  have hbound : |b * Real.sqrt (l2 / l0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc |b| * Real.sqrt (l2 / l0) ≤ Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) :=
      mul_le_mul_of_nonneg_right hb hs
      _ = 1 := ht
  unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
  rw [if_pos hbound, abs_mul, abs_of_nonneg hs]
  calc 2 * l0 * (|b| * Real.sqrt (l2 / l0)) = 2 * (l0 * Real.sqrt (l2 / l0)) * |b| := by ring
    _ = _ := by rw [hw]

lemma interval_linear_minimum (c a t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    let u := if 0 ≤ c - |a| then 0 else -t * Real.sign a
    u ∈ Set.Icc (-t) t ∧ ∀ b ∈ Set.Icc (-t) t,
      c * |u| + a * u ≤ c * |b| + a * b := by
  dsimp
  by_cases h : 0 ≤ c - |a|
  · rw [if_pos h]
    refine ⟨⟨by linarith, ht⟩, ?_⟩
    intro b hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hz := mul_nonneg h (abs_nonneg b)
    simp only [abs_zero, mul_zero, zero_add]
    nlinarith
  · rw [if_neg h]
    have hane : a ≠ 0 := by intro hz; subst a; simp at h; linarith
    have habs : |-t * Real.sign a| = t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha]; simp [abs_of_nonneg ht]
      · rw [Real.sign_of_pos ha]; simp [abs_of_nonneg ht]
    have hau : a * (-t * Real.sign a) = -|a| * t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha, abs_of_neg ha]; ring
      · rw [Real.sign_of_pos ha, abs_of_pos ha]; ring
    refine ⟨abs_le.mp (by rw [habs]), ?_⟩
    intro b hb
    have hbt : |b| ≤ t := abs_le.mpr hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonpos_left hbt (le_of_lt (not_le.mp h))
    rw [habs, hau]
    nlinarith

end SparseDualitySupport

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η) :
    betaTilde45 lam0 lam2 a η ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)) ∧
      ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
        D lam0 lam2 a η (betaTilde45 lam0 lam2 a η) ≤ D lam0 lam2 a η b := by
  have hc : 0 ≤ 2 * Real.sqrt (lam0 * lam2) + η := by positivity
  obtain ⟨hu, hmin⟩ := SparseDualitySupport.interval_linear_minimum
    (2 * Real.sqrt (lam0 * lam2) + η) a (Real.sqrt (lam0 / lam2)) hc (Real.sqrt_nonneg _)
  change betaTilde45 lam0 lam2 a η ∈ _ at hu
  change ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
    (2 * Real.sqrt (lam0 * lam2) + η) * |betaTilde45 lam0 lam2 a η| + a * betaTilde45 lam0 lam2 a η ≤
      (2 * Real.sqrt (lam0 * lam2) + η) * |b| + a * b at hmin
  refine ⟨hu, ?_⟩
  intro b hb
  unfold D
  rw [SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hu),
    SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hb)]
  nlinarith [hmin b hb]

end Accepted45

namespace Accepted47

set_option autoImplicit false
open L0BnB.Duality

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η)
    (hcase : |a| - η ≥ 2 * Real.sqrt (lam0 * lam2)) :
    IsLeast (Set.range (D lam0 lam2 a η)) (-(1 / (4 * lam2)) * (|a| - η) ^ 2 + lam0) := by
  have hD : ∀ b, D lam0 lam2 a η b = 2 * lam0 * (if |b * Real.sqrt (lam2 / lam0)| ≤ 1 then |b * Real.sqrt (lam2 / lam0)| else ((b * Real.sqrt (lam2 / lam0)) ^ 2 + 1) / 2)
      + a * b + η * |b| := by
    intro b
    unfold D L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
    rfl
  have hw0 : 0 < Real.sqrt (lam0 * lam2) := Real.sqrt_pos.mpr (mul_pos hlam0 hlam2)
  have hw2 : Real.sqrt (lam0 * lam2) ^ 2 = lam0 * lam2 := Real.sq_sqrt (mul_pos hlam0 hlam2).le
  have hs0 : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.mpr (div_pos hlam2 hlam0)
  have hs2 : Real.sqrt (lam2 / lam0) ^ 2 = lam2 / lam0 := Real.sq_sqrt (div_pos hlam2 hlam0).le
  generalize Real.sqrt (lam0 * lam2) = w at hw0 hw2 hcase
  generalize Real.sqrt (lam2 / lam0) = s at hs0 hs2 hD
  generalize hcdef : |a| - η = c at hcase
  have hls2 : lam0 * s ^ 2 = lam2 := by rw [hs2]; field_simp
  have hws : lam0 * s = w := by
    have h1 : (lam0 * s) ^ 2 = w ^ 2 := by
      rw [mul_pow, hw2]; nlinarith [hls2]
    exact (sq_eq_sq₀ (by positivity) hw0.le).mp h1
  have hws2 : w * s = lam2 := by rw [← hws]; nlinarith [hls2]
  have hc2 : 2 * w ≤ c := hcase
  have hcpos : 0 < c := by linarith
  constructor
  · -- attained
    let b0 : ℝ := if 0 ≤ a then -(c / (2 * lam2)) else c / (2 * lam2)
    have hb0abs : |b0| = c / (2 * lam2) := by
      unfold b0
      split_ifs
      · rw [abs_neg, abs_of_pos (by positivity)]
      · rw [abs_of_pos (by positivity)]
    have hab0 : a * b0 = -|a| * (c / (2 * lam2)) := by
      unfold b0
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hbs : 1 ≤ |b0 * s| := by
      rw [abs_mul, hb0abs, abs_of_pos hs0]
      rw [← sub_nonneg]
      have : c / (2 * lam2) * s - 1 = (c * s - 2 * lam2) / (2 * lam2) := by field_simp
      rw [this]
      apply div_nonneg _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hc2 hs0.le]
    refine ⟨b0, ?_⟩
    rw [hD]
    have hRH : (if |b0 * s| ≤ 1 then |b0 * s| else ((b0 * s) ^ 2 + 1) / 2) = ((b0 * s) ^ 2 + 1) / 2 := by
      split_ifs with h
      · have h1 : |b0 * s| = 1 := le_antisymm h hbs
        have h2 : (b0 * s) ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
        rw [h1, h2]; norm_num
      · rfl
    rw [hRH, hab0, hb0abs]
    have hb2 : (b0 * s) ^ 2 = (c / (2 * lam2)) ^ 2 * s ^ 2 := by
      rw [mul_pow, ← sq_abs b0, hb0abs]
    rw [hb2]
    have hη' : η = |a| - c := by linarith [hcdef]
    rw [hη']
    field_simp
    nlinarith [hls2]
  · rintro _ ⟨b, rfl⟩
    rw [hD]
    have hab : -|a| * |b| ≤ a * b := by
      have := neg_abs_le (a * b)
      rw [abs_mul] at this
      linarith
    have hη' : η = |a| - c := by linarith [hcdef]
    have hb0 : 0 ≤ |b| := abs_nonneg b
    by_cases hcs : |b * s| ≤ 1
    · rw [if_pos hcs]
      have h1 : |b * s| = |b| * s := by rw [abs_mul, abs_of_pos hs0]
      rw [h1] at hcs ⊢
      have h2 : |b| * w ≤ lam0 := by
        have := mul_le_mul_of_nonneg_left hcs hlam0.le
        nlinarith [hws]
      have h3 : lam2 * |b| ≤ w := by
        have h4 : lam2 * |b| * w ≤ w * w := by nlinarith [hw2]
        exact le_of_mul_le_mul_right h4 hw0
      have h5 : 2 * lam0 * (|b| * s) = 2 * w * |b| := by
        rw [← hws]; ring
      rw [h5]
      have : 0 ≤ (c - 2 * w) * (2 * w + c - 4 * lam2 * |b|) :=
        mul_nonneg (by linarith) (by linarith)
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = (4 * lam0 * lam2 - c ^ 2) / (4 * lam2) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have hlam : lam0 * lam2 = w ^ 2 := hw2.symm
      nlinarith [hab, this]
    · rw [if_neg hcs]
      have h1 : (b * s) ^ 2 = |b| ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
      rw [h1]
      have h6 : 2 * lam0 * ((|b| ^ 2 * s ^ 2 + 1) / 2) = lam2 * |b| ^ 2 + lam0 := by
        have : lam0 * (|b| ^ 2 * s ^ 2) = lam2 * |b| ^ 2 := by
          calc lam0 * (|b| ^ 2 * s ^ 2) = |b| ^ 2 * (lam0 * s ^ 2) := by ring
            _ = lam2 * |b| ^ 2 := by rw [hls2]; ring
        nlinarith [this]
      rw [h6]
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = lam0 - c ^ 2 / (4 * lam2) := by ring
      rw [e]
      have h7 : 0 ≤ (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) := by positivity
      have h8 : (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) = lam2 * |b| ^ 2 - c * |b| + c ^ 2 / (4 * lam2) := by
        field_simp; ring
      rw [hη']
      nlinarith [hab, h7, h8]

end Accepted47
set_option autoImplicit false
open L0BnB.Duality L0BnB.Reduced

namespace WeakDualitySupport

lemma psi1_lower (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    2 * Real.sqrt (l0 * l2) * |b| ≤ psi1 l0 l2 b := by
  have hw := (Accepted45.SparseDualitySupport.sqrt_scaling l0 l2 h0 h2).2
  have hr : |b * Real.sqrt (l2 / l0)| ≤ reverseHuber (b * Real.sqrt (l2 / l0)) := by
    unfold reverseHuber
    split_ifs with h
    · exact le_rfl
    · nlinarith [sq_nonneg (|b * Real.sqrt (l2/l0)| - 1), sq_abs (b * Real.sqrt (l2/l0))]
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*l0)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hm
  unfold psi1
  calc 2 * Real.sqrt (l0 * l2) * |b| = 2*l0*(|b| *Real.sqrt (l2/l0)) := by rw [← hw]; ring
    _ ≤ _ := hm

lemma conjugate_bound (l0 l2 a b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    -(max (a^2/(4*l2)-l0) 0) ≤ psi1 l0 l2 b + a*b := by
  have hw := Real.sq_sqrt (mul_pos h0 h2).le
  have hw0 := Real.sqrt_nonneg (l0*l2)
  by_cases ha : 2 * Real.sqrt (l0*l2) ≤ |a|
  · have hh := (Accepted47.solution l0 l2 a 0 h0 h2 (le_refl _) (by simpa using ha)).2
    have hb := hh (Set.mem_range_self b)
    have hq : 0 ≤ a^2/(4*l2)-l0 := by
      have hsq : 4*l0*l2 ≤ a^2 := by nlinarith [sq_abs a]
      rw [sub_nonneg, le_div_iff₀ (by positivity)]
      nlinarith
    rw [max_eq_left hq]
    simp only [D, zero_mul, add_zero, sub_zero, sq_abs] at hb
    convert hb using 1 <;> ring
  · have ha' : |a| ≤ 2 * Real.sqrt (l0*l2) := le_of_lt (not_le.mp ha)
    have hq : a^2/(4*l2)-l0 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      nlinarith [sq_abs a, abs_nonneg a]
    rw [max_eq_right hq, neg_zero]
    have hp := psi1_lower l0 l2 b h0 h2
    have hab : -(|a| * |b|) ≤ a*b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonneg_right ha' (abs_nonneg b)
    linarith

lemma loss_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y α : Fin n → ℝ) (β : Fin p → ℝ) :
    -(1/2) * ∑ r, α r ^ 2 - ∑ r, α r * y r + ∑ i, colDot X α i * β i ≤
      lsLoss X y β := by
  have hs : ∑ i, colDot X α i * β i = ∑ r, α r * Matrix.mulVec X β r := by
    simp only [colDot, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro i hi; ring
  rw [hs]
  have hb : ∑ r, (-(1/2)*α r^2 - α r*y r + α r*Matrix.mulVec X β r) ≤
      ∑ r, (1/2)*(y r-Matrix.mulVec X β r)^2 := by
    apply Finset.sum_le_sum; intro r hr
    nlinarith [sq_nonneg (α r+y r-Matrix.mulVec X β r)]
  simpa only [lsLoss, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using hb

end WeakDualitySupport

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      ∀ (α : Fin n → ℝ) (γ : Fin p → ℝ), ∀ β ∈ L0BnB.Reduced.box p M,
        h1 X y lam0 lam2 M α γ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
    (M < Real.sqrt (lam0 / lam2) →
      ∀ (ρ : Fin n → ℝ) (μ : Fin p → ℝ), Feas22 X lam0 lam2 M ρ μ → ∀ β ∈ L0BnB.Reduced.box p M,
        h2 y M ρ μ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) := by
  constructor
  · intro hcase α γ β hβ
    have hcoord : ∀ i, -v X lam0 lam2 M α i (γ i) ≤
        psi1 lam0 lam2 (β i) + colDot X α i * β i := by
      intro i
      have hcon := WeakDualitySupport.conjugate_bound lam0 lam2 (colDot X α i-γ i) (β i) hlam0 hlam2
      have hg : -(|γ i| * |β i|) ≤ γ i*β i := by simpa only [abs_mul] using neg_abs_le (γ i*β i)
      have hm := mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg (γ i))
      unfold v
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
    have hls := WeakDualitySupport.loss_bound X y α β
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
    have hF : F X y lam0 lam2 M β = lsLoss X y β + ∑ i, psi1 lam0 lam2 (β i) := by
      simp only [F, psi, if_pos hcase]
    rw [hF]; unfold h1; linarith
  · intro hcase ρ μ hfeas β hβ
    have hcoord : ∀ i, -M* |μ i| ≤ psi2 lam0 lam2 M (β i) + colDot X ρ i * β i := by
      intro i
      have hf := mul_le_mul_of_nonneg_right (hfeas i) (abs_nonneg (β i))
      have ha : -(|colDot X ρ i| * |β i|) ≤ colDot X ρ i * β i := by
        simpa only [abs_mul] using neg_abs_le (colDot X ρ i * β i)
      have hmu := mul_le_mul_of_nonneg_right (le_abs_self (μ i)) (abs_nonneg (β i))
      have hm := mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg (μ i))
      unfold psi2
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
    have hls := WeakDualitySupport.loss_bound X y ρ β
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hF : F X y lam0 lam2 M β = lsLoss X y β + ∑ i, psi2 lam0 lam2 M (β i) := by
      simp only [F, psi, if_neg (not_le.mpr hcase)]
    rw [hF]; unfold h2; linarith
