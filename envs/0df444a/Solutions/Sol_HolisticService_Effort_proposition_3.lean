-- Prove2me | solution 1 for HolisticService.Effort.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:44:55.123347+00:00
-- url     : https://prove2.me/submissions/938cb9a2-e7fb-4d14-b471-3c4c35113185

import Mathlib
import Definitions.Def_HolisticService_Effort_Model
import Theorems.Thm_HolisticService_Effort_partials_own
import Theorems.Thm_HolisticService_Effort_partials_cross
import Theorems.Thm_HolisticService_Effort_proposition_1

open HolisticService.Effort

namespace HSProp3

lemma sign_eq_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    SignType.sign a = SignType.sign b ↔ 0 < a * b := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · rw [sign_neg ha, sign_neg hb]; simp only [true_iff]; exact mul_pos_of_neg_of_neg ha hb
  · rw [sign_neg ha, sign_pos hb]
    simp only [reduceCtorEq, false_iff, not_lt]; exact (mul_neg_of_neg_of_pos ha hb).le
  · rw [sign_pos ha, sign_neg hb]
    simp only [reduceCtorEq, false_iff, not_lt]; exact (mul_neg_of_pos_of_neg ha hb).le
  · rw [sign_pos ha, sign_pos hb]; simp only [true_iff]; exact mul_pos ha hb

/-- The sign bookkeeping of Proposition 3 for a pair of distinct steps. -/
lemma cross_arith (p a b x y r : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : 0 < x) (hy : 0 < y)
    (hr : 0 < r) :
    ((-x / (r * b * a) * p < 0 ∧ 0 < y / (r * b * a) * p ∧
        (a < 0 → 0 < -(y * x) / (r * b * a ^ 2) * p) ∧
        (0 < a → -(y * x) / (r * b * a ^ 2) * p < 0)) ↔
      ((SignType.sign a = SignType.sign b ∧ 0 < p) ∨
        (SignType.sign a ≠ SignType.sign b ∧ p < 0))) ∧
    (¬ ((SignType.sign a = SignType.sign b ∧ 0 < p) ∨
        (SignType.sign a ≠ SignType.sign b ∧ p < 0)) → p ≠ 0 →
      (0 < -x / (r * b * a) * p ∧ y / (r * b * a) * p < 0 ∧
        (a < 0 → -(y * x) / (r * b * a ^ 2) * p < 0) ∧
        (0 < a → 0 < -(y * x) / (r * b * a ^ 2) * p))) := by
  set q := p / (a * b) with hq
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have e1 : -x / (r * b * a) * p = -(x / r) * q := by rw [hq]; ring
  have e2 : y / (r * b * a) * p = (y / r) * q := by rw [hq]; ring
  have e3 : -(y * x) / (r * b * a ^ 2) * p = -(y * x / r) * (q * a⁻¹) := by
    rw [hq]; field_simp
  have hxr : 0 < x / r := div_pos hx hr
  have hyr : 0 < y / r := div_pos hy hr
  have hyxr : 0 < y * x / r := div_pos (mul_pos hy hx) hr
  have hcond : ((SignType.sign a = SignType.sign b ∧ 0 < p) ∨
        (SignType.sign a ≠ SignType.sign b ∧ p < 0)) ↔ 0 < q := by
    rw [ne_eq, sign_eq_iff a b ha hb, hq, div_pos_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, lt_of_le_of_ne (not_lt.mp h1) hab⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨not_lt.mpr h2.le, h1⟩
  rw [e1, e2, e3, hcond]
  constructor
  · constructor
    · rintro ⟨h1, -, -, -⟩
      by_contra h
      have h' : q ≤ 0 := not_lt.mp h
      nlinarith
    · intro hq0
      refine ⟨by nlinarith, by positivity, fun ha0 => ?_, fun ha0 => ?_⟩
      · have : a⁻¹ < 0 := inv_lt_zero.mpr ha0
        have : q * a⁻¹ < 0 := mul_neg_of_pos_of_neg hq0 this
        nlinarith
      · have : 0 < q * a⁻¹ := mul_pos hq0 (inv_pos.mpr ha0)
        nlinarith
  · intro hnq hp
    have hq0 : q < 0 := by
      rcases lt_trichotomy q 0 with h | h | h
      · exact h
      · exfalso; rw [hq, div_eq_zero_iff] at h
        rcases h with h | h
        · exact hp h
        · exact hab h
      · exact absurd h hnq
    refine ⟨by nlinarith, by nlinarith, fun ha0 => ?_, fun ha0 => ?_⟩
    · have : 0 < q * a⁻¹ := mul_pos_of_neg_of_neg hq0 (inv_lt_zero.mpr ha0)
      nlinarith
    · have : q * a⁻¹ < 0 := mul_neg_of_neg_of_pos hq0 (inv_pos.mpr ha0)
      nlinarith

end HSProp3

theorem solution {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i : Fin n) :
    (deriv (fun t => optEffort (withC M i t) i) (M.c i) < 0 ∧
      0 < deriv (fun t => optEffort (withVH M i t) i) (M.VH i) ∧
      (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) i) (M.sH i)) ∧
      (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) i) (M.sH i) < 0)) ∧
    ∀ j : Fin n, j ≠ i →
      let Cross :=
        deriv (fun t => optEffort (withC M i t) j) (M.c i) < 0 ∧
        0 < deriv (fun t => optEffort (withVH M i t) j) (M.VH i) ∧
        (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) j) (M.sH i)) ∧
        (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) j) (M.sH i) < 0)
      let Rev :=
        0 < deriv (fun t => optEffort (withC M i t) j) (M.c i) ∧
        deriv (fun t => optEffort (withVH M i t) j) (M.VH i) < 0 ∧
        (M.sH i - M.sL i < 0 → deriv (fun t => optEffort (withSH M i t) j) (M.sH i) < 0) ∧
        (0 < M.sH i - M.sL i → 0 < deriv (fun t => optEffort (withSH M i t) j) (M.sH i))
      let Cond :=
        (SignType.sign (M.sH i - M.sL i) = SignType.sign (M.sH j - M.sL j) ∧ 0 < M.P⁻¹ i j) ∨
        (SignType.sign (M.sH i - M.sL i) ≠ SignType.sign (M.sH j - M.sL j) ∧ M.P⁻¹ i j < 0)
      (Cross ↔ Cond) ∧ (¬ Cond → M.P⁻¹ i j ≠ 0 → Rev) := by
  have hS' := hS
  obtain ⟨hV, -, -, -, hcS, -, hr, -, hne, -, -, -, hP⟩ := hS'
  have hd : ∀ k, M.sH k - M.sL k ≠ 0 := fun k => sub_ne_zero.mpr (hne k)
  have hsym : ∀ a b, M.P⁻¹ a b = M.P⁻¹ b a := by
    intro a b
    have := hP.inv.isHermitian.apply a b
    simp only [star_trivial] at this
    exact this.symm
  refine ⟨?_, ?_⟩
  · -- own step
    obtain ⟨hc, hcneg, hv, hvpos, hA, hδeq, hsh⟩ := partials_own M hS hβ hI i
    have hex : ∃ δ, IsOptimalEffort M δ := ⟨δhat M, _, (proposition_1 M hS hI).1⟩
    have hδ0 : 0 ≤ optEffort M i := by
      unfold optEffort
      rw [dif_pos hex]
      obtain ⟨π, hπ⟩ := Classical.choose_spec hex
      exact (hπ.1.1 i).1
    have hdi := hd i
    refine ⟨by rw [hc.deriv]; exact hcneg, by rw [hv.deriv]; exact hvpos, ?_, ?_⟩
    · intro hneg
      rw [hsh.deriv]
      generalize M.sH i - M.sL i = d at *
      have hX : 2 * ((1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i)
          + (∑ j ∈ Finset.univ.erase i,
              (1 - M.c j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ j i - M.sL i) * d
          = (1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i + d ^ 2 * optEffort M i := by
        rw [hδeq]; field_simp; ring
      rw [hX]
      have h3 : d ^ 3 < 0 := Odd.pow_neg (by decide) hneg
      exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) h3
    · intro hpos
      rw [hsh.deriv]
      generalize M.sH i - M.sL i = d at *
      have hX : 2 * ((1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i)
          + (∑ j ∈ Finset.univ.erase i,
              (1 - M.c j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ j i - M.sL i) * d
          = (1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i + d ^ 2 * optEffort M i := by
        rw [hδeq]; field_simp; ring
      rw [hX]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)
  · -- other steps
    intro j hji
    obtain ⟨hVc, hCc, hSc⟩ := partials_cross M hS hβ hI j i hji
    simp only []
    rw [hCc.deriv, hVc.deriv, hSc.deriv, hsym j i]
    have hx : 0 < M.VH i - M.VL i := by linarith [(hV i).2]
    have hy : 0 < 1 - M.c i := by linarith [(hcS i).2]
    exact HSProp3.cross_arith (M.P⁻¹ i j) (M.sH i - M.sL i) (M.sH j - M.sL j) _ _ M.r
      (hd i) (hd j) hx hy hr
