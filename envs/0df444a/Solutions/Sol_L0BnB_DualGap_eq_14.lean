-- Prove2me | solution 1 for L0BnB.DualGap.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:52:44.334122+00:00
-- url     : https://prove2.me/submissions/2f299f7b-d473-4815-bbd7-cdc4f8782026

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup

set_option autoImplicit false

namespace L0BnB.DualGap.Aux13

open L0BnB.DualGap

/-- Subgradient certificate for the unique minimizer of `½(t − bt)² + φ(t)` on `[-M, M]`. -/
lemma isSol_of_subgrad (lam0 lam2 M bt b g : ℝ)
    (hb : b ∈ Set.Icc (-M) M)
    (hsub : ∀ t, L0BnB.Reduced.psi lam0 lam2 M b + g * (t - b) ≤ L0BnB.Reduced.psi lam0 lam2 M t)
    (hopt : ∀ t ∈ Set.Icc (-M) M, 0 ≤ (t - b) * (b - bt + g)) :
    IsSolution13 lam0 lam2 M bt b := by
  refine ⟨hb, fun t ht hne => ?_⟩
  unfold obj13
  have h1 := hsub t
  have h2 := hopt t ht
  have h3 : 0 < (t - b) ^ 2 := by
    have : t - b ≠ 0 := sub_ne_zero.2 hne
    positivity
  nlinarith

lemma sign_pos' {x : ℝ} (h : 0 < x) : Real.sign x = 1 := Real.sign_of_pos h
lemma sign_neg' {x : ℝ} (h : x < 0) : Real.sign x = -1 := Real.sign_of_neg h

theorem eq15 (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (bt : ℝ) :
    IsSolution13 lam0 lam2 M bt (boxedSoftThreshold bt (lam0 / M + lam2 * M) M) := by
  set κ := lam0 / M + lam2 * M with hκ
  have hκ0 : 0 < κ := by positivity
  have hpsi : ∀ t, L0BnB.Reduced.psi lam0 lam2 M t = κ * |t| := by
    intro t
    unfold L0BnB.Reduced.psi L0BnB.Reduced.psi2
    rw [if_neg (not_le.2 hreg)]
  unfold boxedSoftThreshold
  split_ifs with h1 h2
  · -- |bt| ≤ κ : solution 0, subgradient bt
    apply isSol_of_subgrad lam0 lam2 M bt 0 bt ⟨by linarith, hM.le⟩
    · intro t
      rw [hpsi, hpsi, abs_zero, mul_zero, zero_add, sub_zero]
      have := abs_le.1 h1
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]; nlinarith
      · rw [abs_of_neg ht]; nlinarith
    · intro t _; simp
  · rcases le_or_gt 0 bt with hbt | hbt
    · rw [abs_of_nonneg hbt] at h1 h2 ⊢
      rw [sign_pos' (by linarith)]
      apply isSol_of_subgrad lam0 lam2 M bt ((bt - κ) * 1) κ ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, abs_of_nonneg (by linarith : 0 ≤ (bt - κ) * 1)]
        nlinarith [le_abs_self t]
      · intro t _; nlinarith
    · rw [abs_of_neg hbt] at h1 h2 ⊢
      rw [sign_neg' hbt]
      apply isSol_of_subgrad lam0 lam2 M bt ((-bt - κ) * -1) (-κ) ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, abs_of_nonpos (by linarith : (-bt - κ) * -1 ≤ 0)]
        nlinarith [neg_abs_le t]
      · intro t _; nlinarith
  · rcases le_or_gt 0 bt with hbt | hbt
    · rw [abs_of_nonneg hbt] at h1 h2
      rw [sign_pos' (by linarith)]
      apply isSol_of_subgrad lam0 lam2 M bt (M * 1) κ ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, abs_of_nonneg (by linarith : 0 ≤ M * 1)]
        nlinarith [le_abs_self t]
      · intro t ht
        have := ht.2
        nlinarith
    · rw [abs_of_neg hbt] at h1 h2
      rw [sign_neg' hbt]
      apply isSol_of_subgrad lam0 lam2 M bt (M * -1) (-κ) ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, abs_of_nonpos (by linarith : M * -1 ≤ 0)]
        nlinarith [neg_abs_le t]
      · intro t ht
        have := ht.1
        nlinarith

/-- Facts about `ψ₁` in terms of `s = √(λ₀/λ₂)`. -/
lemma psi1_facts {lam0 lam2 : ℝ} (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) :
    let s := Real.sqrt (lam0 / lam2)
    0 < s ∧ lam0 = lam2 * s ^ 2 ∧ 2 * Real.sqrt (lam0 * lam2) = 2 * lam2 * s ∧
    (∀ t, |t| ≤ s → L0BnB.Reduced.psi1 lam0 lam2 t = 2 * lam2 * s * |t|) ∧
    (∀ t, s ≤ |t| → L0BnB.Reduced.psi1 lam0 lam2 t = lam2 * t ^ 2 + lam0) := by
  intro s
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hlam0 hlam2)
  have hs2 : s ^ 2 = lam0 / lam2 := Real.sq_sqrt (div_pos hlam0 hlam2).le
  have hl0 : lam0 = lam2 * s ^ 2 := by rw [hs2]; field_simp
  have hr : Real.sqrt (lam2 / lam0) = 1 / s := by
    rw [show lam2 / lam0 = (1 / s) ^ 2 by rw [div_pow, hs2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have ha : Real.sqrt (lam0 * lam2) = lam2 * s := by
    rw [show lam0 * lam2 = (lam2 * s) ^ 2 by rw [mul_pow, hs2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  refine ⟨hs, hl0, by rw [ha]; ring, ?_, ?_⟩
  · intro t ht
    unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
    rw [hr]
    have : |t * (1 / s)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / s)]
      rw [mul_one_div, div_le_one hs]; exact ht
    rw [if_pos this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / s), hl0]
    field_simp
  · intro t ht
    unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
    rw [hr]
    split_ifs with h
    · have h' : |t| ≤ s := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / s), mul_one_div, div_le_one hs] at h
        exact h
      have hts : |t| = s := le_antisymm h' ht
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / s), hts, hl0]
      have : t ^ 2 = s ^ 2 := by rw [← sq_abs, hts]
      rw [this]; field_simp; norm_num
    · rw [hl0]; field_simp

theorem eq14 (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M) (bt : ℝ) :
    IsSolution13 lam0 lam2 M bt
      (if |bt| ≤ 2 * Real.sqrt (lam0 * lam2) + Real.sqrt (lam0 / lam2) then
        boxedSoftThreshold bt (2 * Real.sqrt (lam0 * lam2)) M
      else boxedSoftThreshold (bt * (1 + 2 * lam2)⁻¹) 0 M) := by
  obtain ⟨hs, hl0, ha, hsmall, hlarge⟩ := psi1_facts hlam0 hlam2
  set s := Real.sqrt (lam0 / lam2)
  have hapos : 0 < 2 * lam2 * s := by positivity
  have hopl : 0 < 1 + 2 * lam2 := by positivity
  have hpsi : ∀ t, L0BnB.Reduced.psi lam0 lam2 M t = L0BnB.Reduced.psi1 lam0 lam2 t := by
    intro t; unfold L0BnB.Reduced.psi; rw [if_pos hreg]
  -- global lower bound ψ₁(t) ≥ 2λ₂ s |t|
  have hlow : ∀ t, 2 * lam2 * s * |t| ≤ L0BnB.Reduced.psi1 lam0 lam2 t := by
    intro t
    rcases le_or_gt (|t|) s with h | h
    · rw [hsmall t h]
    · rw [hlarge t h.le, hl0]
      nlinarith [sq_abs t, sq_nonneg (|t| - s)]
  -- tangent lower bound at |u| ≥ s
  have htan : ∀ u, s ≤ |u| → ∀ t,
      lam2 * u ^ 2 + lam0 + 2 * lam2 * u * (t - u) ≤ L0BnB.Reduced.psi1 lam0 lam2 t := by
    intro u hu t
    rcases le_or_gt (|t|) s with h | h
    · rw [hsmall t h, hl0]
      have key : s ^ 2 - u ^ 2 + 2 * u * t ≤ 2 * s * |t| := by
        rcases le_or_gt 0 u with hu0 | hu0
        · rw [abs_of_nonneg hu0] at hu
          rcases le_or_gt 0 t with ht0 | ht0
          · rw [abs_of_nonneg ht0] at h ⊢; nlinarith
          · rw [abs_of_neg ht0] at h ⊢; nlinarith
        · rw [abs_of_neg hu0] at hu
          rcases le_or_gt 0 t with ht0 | ht0
          · rw [abs_of_nonneg ht0] at h ⊢; nlinarith
          · rw [abs_of_neg ht0] at h ⊢; nlinarith
      nlinarith
    · rw [hlarge t h.le]
      nlinarith [sq_nonneg (t - u)]
  rw [ha]
  unfold boxedSoftThreshold
  split_ifs with hA hB hC hD hE
  · -- |bt| ≤ a: solution 0
    apply isSol_of_subgrad lam0 lam2 M bt 0 bt ⟨by linarith, hM.le⟩
    · intro t
      rw [hpsi, hpsi, hsmall 0 (by simp; exact hs.le), abs_zero, mul_zero, zero_add, sub_zero]
      have := hlow t
      have h1 := abs_le.1 hB
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht] at this; nlinarith
      · rw [abs_of_neg ht] at this; nlinarith
    · intro t _; simp
  · -- a < |bt| ≤ a + s
    rcases le_or_gt 0 bt with hbt | hbt
    · rw [abs_of_nonneg hbt] at hA hB hC ⊢
      rw [sign_pos' (by linarith)]
      apply isSol_of_subgrad lam0 lam2 M bt ((bt - 2 * lam2 * s) * 1) (2 * lam2 * s)
        ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, hsmall _ (by rw [abs_of_nonneg (by linarith)]; linarith),
          abs_of_nonneg (by linarith : 0 ≤ (bt - 2 * lam2 * s) * 1)]
        have := hlow t
        nlinarith [le_abs_self t]
      · intro t _; nlinarith
    · rw [abs_of_neg hbt] at hA hB hC ⊢
      rw [sign_neg' hbt]
      apply isSol_of_subgrad lam0 lam2 M bt ((-bt - 2 * lam2 * s) * -1) (-(2 * lam2 * s))
        ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, hsmall _ (by rw [abs_of_nonpos (by linarith)]; linarith),
          abs_of_nonpos (by linarith : (-bt - 2 * lam2 * s) * -1 ≤ 0)]
        have := hlow t
        nlinarith [neg_abs_le t]
      · intro t _; nlinarith
  · exfalso; linarith
  · -- large branch, |u| ≤ 0 impossible
    exfalso
    have hu : 0 < |bt * (1 + 2 * lam2)⁻¹| := by
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0:ℝ) < 1 + 2 * lam2)]
      have : 0 < |bt| := by linarith
      positivity
    linarith
  · -- u inside the box: solution u, gradient 2λ₂u
    set u := bt * (1 + 2 * lam2)⁻¹ with hu
    have hbtu : bt = u * (1 + 2 * lam2) := by rw [hu]; field_simp
    have hus : s ≤ |u| := by
      rw [hbtu, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 + 2 * lam2)] at hA
      by_contra hcon; push Not at hcon
      nlinarith
    have hb : (|u| - 0) * Real.sign u = u := by
      rcases lt_trichotomy u 0 with h | h | h
      · rw [abs_of_neg h, sign_neg' h]; ring
      · rw [h]; simp
      · rw [abs_of_pos h, sign_pos' h]; ring
    rw [hb]
    have hE' : |u| ≤ M := by linarith
    apply isSol_of_subgrad lam0 lam2 M bt u (2 * lam2 * u) (abs_le.1 hE')
    · intro t
      rw [hpsi, hpsi, hlarge u hus]
      exact htan u hus t
    · intro t _; rw [hbtu]; nlinarith
  · -- u outside the box: solution M sign u
    set u := bt * (1 + 2 * lam2)⁻¹ with hu
    have hbtu : bt = u * (1 + 2 * lam2) := by rw [hu]; field_simp
    have hE' : M < |u| := by linarith
    rcases le_or_gt 0 u with hu0 | hu0
    · rw [abs_of_nonneg hu0] at hE'
      rw [sign_pos' (by linarith)]
      have hMs : s ≤ |M * 1| := by rw [mul_one, abs_of_pos hM]; exact hreg
      apply isSol_of_subgrad lam0 lam2 M bt (M * 1) (2 * lam2 * (M * 1)) ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, hlarge _ hMs]
        exact htan _ hMs t
      · intro t ht
        have := ht.2
        rw [hbtu]
        have e : (t - M * 1) * (M * 1 - u * (1 + 2 * lam2) + 2 * lam2 * (M * 1)) =
            (M - t) * (u - M) * (1 + 2 * lam2) := by ring
        rw [e]; exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hopl.le
    · rw [abs_of_neg hu0] at hE'
      rw [sign_neg' hu0]
      have hMs : s ≤ |M * -1| := by rw [abs_mul, abs_neg, abs_one, mul_one, abs_of_pos hM]; exact hreg
      apply isSol_of_subgrad lam0 lam2 M bt (M * -1) (2 * lam2 * (M * -1)) ⟨by linarith, by linarith⟩
      · intro t
        rw [hpsi, hpsi, hlarge _ hMs]
        exact htan _ hMs t
      · intro t ht
        have := ht.1
        rw [hbtu]
        have e : (t - M * -1) * (M * -1 - u * (1 + 2 * lam2) + 2 * lam2 * (M * -1)) =
            (t + M) * (-u - M) * (1 + 2 * lam2) := by ring
        rw [e]; exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hopl.le

end L0BnB.DualGap.Aux13

open L0BnB.DualGap

theorem solution (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M) (bt : ℝ) :
    IsSolution13 lam0 lam2 M bt
      (if |bt| ≤ 2 * Real.sqrt (lam0 * lam2) + Real.sqrt (lam0 / lam2) then
        boxedSoftThreshold bt (2 * Real.sqrt (lam0 * lam2)) M
      else boxedSoftThreshold (bt * (1 + 2 * lam2)⁻¹) 0 M) :=
  L0BnB.DualGap.Aux13.eq14 lam0 lam2 M hlam0 hlam2 hM hreg bt
