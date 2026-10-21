-- Prove2me | solution 1 for MultitierCSR.Strategy.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:38:57.453136+00:00
-- url     : https://prove2.me/submissions/a37bafd1-89d3-44a2-8f9c-8375a9afc97f

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model
import Theorems.Thm_MultitierCSR_Strategy_lemma_1
import Theorems.Thm_MultitierCSR_Strategy_lemma_2
import Theorems.Thm_MultitierCSR_Strategy_buyer_reduced_profit
import Theorems.Thm_MultitierCSR_Strategy_domination
import Theorems.Thm_MultitierCSR_Strategy_control_delegation_comparison

namespace MTCSRRed
open MultitierCSR.Strategy


variable (P : Params)

lemma st_pos (hS : P.Standing) :
    0 < P.d ∧ 0 < P.k0 ∧ 0 < P.k1 ∧ 0 < P.k2 ∧ 0 < P.ell0 ∧ 0 < P.ell1 ∧ 0 < P.ell2 ∧
    0 < P.β ∧ 0 < P.b ∧ P.tau2 / P.β < P.b := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, h2, h3, h4, h5, h6, h7, h8, -, h9, h10⟩ := hS
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

lemma tau0_pos (hS : P.Standing) : 0 < P.tau0 := by
  obtain ⟨-, h, -, -, h', -⟩ := st_pos P hS; exact div_pos h h'
lemma tau1_pos (hS : P.Standing) : 0 < P.tau1 := by
  obtain ⟨-, -, h, -, -, h', -⟩ := st_pos P hS; exact div_pos h h'
lemma tau2_pos (hS : P.Standing) : 0 < P.tau2 := by
  obtain ⟨-, -, -, h, -, -, h', -⟩ := st_pos P hS; exact div_pos h h'

lemma k2_eq (hS : P.Standing) : P.k2 = P.tau2 * P.ell2 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := st_pos P hS
  unfold Params.tau2; field_simp
lemma k1_eq (hS : P.Standing) : P.k1 = P.tau1 * P.ell1 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := st_pos P hS
  unfold Params.tau1; field_simp
lemma k0_eq (hS : P.Standing) : P.k0 = P.tau0 * P.ell0 := by
  obtain ⟨-, -, -, -, h, -⟩ := st_pos P hS
  unfold Params.tau0; field_simp

/-- b ≥ τ₂/β, so β s ≥ τ₂ for s ≥ b. -/
lemma beta_s_ge (hS : P.Standing) {s : ℝ} (hs : P.b ≤ s) : P.tau2 < P.β * s := by
  obtain ⟨-, -, -, -, -, -, -, hβ, hb, hlt⟩ := st_pos P hS
  rw [div_lt_iff₀ hβ] at hlt
  nlinarith

/-! ### Tier 2 -/

lemma exp_cand2 (hS : P.Standing) (x0 x1 : ℝ) (hs : P.b ≤ x0 + x1 + P.b) :
    Real.exp (-(tier2Candidate P x0 x1 * (x0 + x1 + P.b))) =
      P.tau2 / (P.β * (x0 + x1 + P.b)) := by
  have hb := (st_pos P hS).2.2.2.2.2.2.2.2.1
  have h2 := tau2_pos P hS
  have hlt := beta_s_ge P hS hs
  have hspos : 0 < x0 + x1 + P.b := by linarith
  unfold tier2Candidate
  rw [div_mul_cancel₀ _ hspos.ne', Real.exp_neg, Real.exp_log (div_pos (by linarith) h2)]
  rw [inv_div]


/-- Lemma 1 (uniqueness clause) identifies Tier 2's strategy. -/
lemma sigma2_eq (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (h2 : IsBestResponse2 P σ2)
    (x0 x1 : ℝ) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) : σ2 x0 x1 = tier2Candidate P x0 x1 := by
  obtain ⟨hnn, hmax⟩ := h2 x0 x1 hx0 hx1
  have L := (MultitierCSR.Strategy.lemma_1 P hS).1 x0 x1 hx0 hx1
  exact L.2.2.2.1 _ hnn hmax

/-- Lemma 2 (uniqueness clause) identifies Tier 1's strategy. -/
lemma sigma1_eq (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (x0 : ℝ) (hx0 : 0 ≤ x0) : σ1 x0 = tier1Candidate P x0 := by
  obtain ⟨hnn, hmax⟩ := h1 x0 hx0
  have L := (MultitierCSR.Strategy.lemma_2 P hS σ2 h2).1 x0 hx0
  exact L.2.2.2.1 _ hnn hmax

lemma cand1_nonneg (x0 : ℝ) : 0 ≤ tier1Candidate P x0 := le_max_right _ _

/-! ### Abstract cost analysis -/

noncomputable def cst (s0 s1 s2 b x : ℝ) : ℝ := s0 ^ 2 * x + s2 ^ 2 / max (s2 / s1) (x + b)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
section Abs
variable {s0 s1 s2 b : ℝ} (h0 : 0 < s0) (h1 : 0 < s1) (h2 : 0 < s2) (hb : 0 < b)
include h0 h1 h2 hb

lemma F1 {x : ℝ} (hx : x ≤ s2 / s1 - b) : cst s0 s1 s2 b x = s0 ^ 2 * x + s1 * s2 := by
  unfold cst
  rw [max_eq_left (by linarith)]
  field_simp

lemma F2 {x : ℝ} (hx0 : 0 ≤ x) (hx : s2 / s1 - b ≤ x) :
    cst s0 s1 s2 b x = s0 ^ 2 * (x + b) + s2 ^ 2 / (x + b) - s0 ^ 2 * b := by
  unfold cst
  rw [max_eq_right (by linarith)]
  ring

lemma F3 {u : ℝ} (hu : 0 < u) (hne : u ≠ s2 / s0) : 2 * s0 * s2 < s0 ^ 2 * u + s2 ^ 2 / u := by
  have : s0 ^ 2 * u + s2 ^ 2 / u - 2 * s0 * s2 = (s0 * u - s2) ^ 2 / u := by
    field_simp; ring
  have hne' : s0 * u - s2 ≠ 0 := by
    intro h; apply hne; field_simp; linarith
  have : 0 < (s0 * u - s2) ^ 2 / u := by positivity
  linarith

lemma F3' {u : ℝ} (hu : 0 < u) : 2 * s0 * s2 ≤ s0 ^ 2 * u + s2 ^ 2 / u := by
  have : s0 ^ 2 * u + s2 ^ 2 / u - 2 * s0 * s2 = (s0 * u - s2) ^ 2 / u := by
    field_simp; ring
  have : 0 ≤ (s0 * u - s2) ^ 2 / u := by positivity
  linarith

lemma F3eq : s0 ^ 2 * (s2 / s0) + s2 ^ 2 / (s2 / s0) = 2 * s0 * s2 := by
  field_simp; ring

lemma F4 {u v : ℝ} (hwv : s2 / s0 ≤ v) (hvu : v < u) :
    s0 ^ 2 * v + s2 ^ 2 / v < s0 ^ 2 * u + s2 ^ 2 / u := by
  have hw : 0 < s2 / s0 := by positivity
  have hv : 0 < v := by linarith
  have hu : 0 < u := by linarith
  have hsv : s2 ≤ s0 * v := by rw [div_le_iff₀ h0] at hwv; linarith
  have : s0 ^ 2 * u + s2 ^ 2 / u - (s0 ^ 2 * v + s2 ^ 2 / v) =
      (u - v) * (s0 ^ 2 * u * v - s2 ^ 2) / (u * v) := by
    field_simp; ring
  have h3 : s2 ^ 2 ≤ (s0 * v) ^ 2 := by nlinarith
  have h5 := mul_pos (mul_pos (pow_pos h0 2) hv) (sub_pos.mpr hvu)
  have h4 : 0 < s0 ^ 2 * u * v - s2 ^ 2 := by nlinarith
  have : 0 < (u - v) * (s0 ^ 2 * u * v - s2 ^ 2) / (u * v) := by
    apply div_pos (mul_pos (by linarith) h4) (by positivity)
  linarith

lemma cA (hA : b * s1 < s2) : 0 < s2 / s1 - b := by
  rw [sub_pos, lt_div_iff₀ h1]; linarith

lemma C0A (hA : b * s1 < s2) : cst s0 s1 s2 b 0 = s1 * s2 := by
  rw [F1 h0 h1 h2 hb (cA h0 h1 h2 hb hA).le]; ring

lemma R0 (hA : b * s1 < s2) {x : ℝ} (hx : 0 < x) (hxc : x ≤ s2 / s1 - b) :
    cst s0 s1 s2 b 0 < cst s0 s1 s2 b x := by
  rw [C0A h0 h1 h2 hb hA, F1 h0 h1 h2 hb hxc]
  have := mul_pos (pow_pos h0 2) hx; linarith

/-- In regime A with `s1 < s0`, zero is the strict cost minimizer. -/
lemma Rdel1 (hA : b * s1 < s2) (h10 : s1 < s0) {y : ℝ} (hy : 0 ≤ y) (hne : y ≠ 0) :
    cst s0 s1 s2 b 0 < cst s0 s1 s2 b y := by
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
  rcases le_or_gt y (s2 / s1 - b) with hyc | hyc
  · exact R0 h0 h1 h2 hb hA hy' hyc
  · rw [F2 h0 h1 h2 hb hy hyc.le, C0A h0 h1 h2 hb hA]
    have hwr : s2 / s0 ≤ s2 / s1 := div_le_div_of_nonneg_left h2.le h1 h10.le
    have := F4 h0 h1 h2 hb hwr (show s2 / s1 < y + b by linarith)
    have e : s0 ^ 2 * (s2 / s1) + s2 ^ 2 / (s2 / s1) = s0 ^ 2 * (s2 / s1) + s1 * s2 := by
      field_simp
    have hc := cA h0 h1 h2 hb hA
    nlinarith [mul_pos (mul_pos h0 h0) hc]

/-- In regime A with `K < 0`, zero is the strict cost minimizer. -/
lemma Rdel2 (hA : b * s1 < s2) (hK : b * s0 ^ 2 - 2 * s0 * s2 + s1 * s2 < 0)
    {y : ℝ} (hy : 0 ≤ y) (hne : y ≠ 0) :
    cst s0 s1 s2 b 0 < cst s0 s1 s2 b y := by
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
  rcases le_or_gt y (s2 / s1 - b) with hyc | hyc
  · exact R0 h0 h1 h2 hb hA hy' hyc
  · rw [F2 h0 h1 h2 hb hy hyc.le, C0A h0 h1 h2 hb hA]
    have := F3' h0 h1 h2 hb (show 0 < y + b by linarith)
    linarith

lemma Cctrl {e0 : ℝ} (he : e0 = s2 / s0 - b) (hc : s2 / s1 - b ≤ e0) (he0 : 0 ≤ e0) :
    cst s0 s1 s2 b e0 = 2 * s0 * s2 - s0 ^ 2 * b := by
  rw [F2 h0 h1 h2 hb he0 hc, he, sub_add_cancel, F3eq h0 h1 h2 hb]

/-- Regime A control. -/
lemma RctrlA (hA : b * s1 < s2) (h01 : s0 < s1) (hK : 0 ≤ b * s0 ^ 2 - 2 * s0 * s2 + s1 * s2)
    (hstrict : 0 < b * s0 ^ 2 - 2 * s0 * s2 + s1 * s2 →
      cst s0 s1 s2 b (s2 / s0 - b) < cst s0 s1 s2 b 0)
    {y : ℝ} (hy : 0 ≤ y) (hne : y ≠ s2 / s0 - b) :
    cst s0 s1 s2 b (s2 / s0 - b) < cst s0 s1 s2 b y ∨
      (y = 0 ∧ 0 < s2 / s0 - b ∧ cst s0 s1 s2 b (s2 / s0 - b) = cst s0 s1 s2 b 0) := by
  have hrw : s2 / s1 < s2 / s0 := div_lt_div_of_pos_left h2 h0 h01
  have hc := cA h0 h1 h2 hb hA
  have hCe := Cctrl h0 h1 h2 hb rfl (by linarith) (by linarith)
  have hC0 := C0A h0 h1 h2 hb hA
  rcases le_or_gt y (s2 / s1 - b) with hyc | hyc
  · rcases eq_or_lt_of_le hy with hy0 | hy0
    · subst hy0
      rcases eq_or_lt_of_le hK with hK0 | hK0
      · right; refine ⟨rfl, by linarith, ?_⟩; rw [hCe, hC0]; linarith
      · left; exact hstrict hK0
    · left
      have := R0 h0 h1 h2 hb hA hy0 hyc
      rw [hCe]; rw [hC0] at this; linarith
  · left
    rw [hCe, F2 h0 h1 h2 hb hy hyc.le]
    have := F3 h0 h1 h2 hb (show 0 < y + b by linarith) (by intro h; apply hne; linarith)
    linarith

/-- Regime B control. -/
lemma RctrlB (hB : s2 ≤ b * s1) (hw : b * s0 ≤ s2)
    {y : ℝ} (hy : 0 ≤ y) (hne : y ≠ s2 / s0 - b) :
    cst s0 s1 s2 b (s2 / s0 - b) < cst s0 s1 s2 b y := by
  have hc : s2 / s1 - b ≤ 0 := by rw [sub_nonpos, div_le_iff₀ h1]; linarith
  have he0 : 0 ≤ s2 / s0 - b := by rw [sub_nonneg, le_div_iff₀ h0]; linarith
  rw [Cctrl h0 h1 h2 hb rfl (by linarith) he0, F2 h0 h1 h2 hb hy (by linarith)]
  have := F3 h0 h1 h2 hb (show 0 < y + b by linarith) (by intro h; apply hne; linarith)
  linarith

/-- Regime B no effort. -/
lemma RnoB (hB : s2 ≤ b * s1) (hw : s2 < b * s0) {y : ℝ} (hy : 0 ≤ y) (hne : y ≠ 0) :
    cst s0 s1 s2 b 0 < cst s0 s1 s2 b y := by
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
  have hc : s2 / s1 - b ≤ 0 := by rw [sub_nonpos, div_le_iff₀ h1]; linarith
  rw [F2 h0 h1 h2 hb le_rfl (by linarith), F2 h0 h1 h2 hb hy (by linarith)]
  have hwb : s2 / s0 ≤ 0 + b := by rw [div_le_iff₀ h0]; linarith
  have := F4 h0 h1 h2 hb hwb (show 0 + b < y + b by linarith)
  linarith

end Abs

/-! ### Back to the model -/

lemma sq_sqrt_tau {t : ℝ} (ht : 0 < t) : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le

lemma sqrt_ratio {t t' : ℝ} (ht : 0 < t) : Real.sqrt (t / t') = Real.sqrt t / Real.sqrt t' :=
  Real.sqrt_div ht.le _

lemma sqrt_prod {t t' : ℝ} (ht : 0 < t) : Real.sqrt (t * t') = Real.sqrt t * Real.sqrt t' :=
  Real.sqrt_mul ht.le _


lemma cost_eq (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (x0 : ℝ) (hx0 : 0 ≤ x0) :
    buyerProfit P σ2 σ1 x0 = P.m0 * P.d - P.ell0 *
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b x0 := by
  have t0 := tau0_pos P hS
  have t1 := tau1_pos P hS
  have t2 := tau2_pos P hS
  have q1 : 0 < Real.sqrt P.tau1 := Real.sqrt_pos.mpr t1
  have q2 : 0 < Real.sqrt P.tau2 := Real.sqrt_pos.mpr t2
  obtain ⟨hA, hB⟩ :=
    MultitierCSR.Strategy.buyer_reduced_profit P hS σ2 σ1 h2 h1 x0 hx0
  rw [sqrt_ratio t2] at hA hB
  unfold cst
  rw [sq_sqrt_tau t0, sq_sqrt_tau t2]
  rcases le_or_gt x0 (Real.sqrt P.tau2 / Real.sqrt P.tau1 - P.b) with h | h
  · rw [hA h, max_eq_left (by linarith), sqrt_prod t1, k0_eq P hS]
    have hq := sq_sqrt_tau t2
    set q := Real.sqrt P.tau2
    rw [← hq]
    field_simp
    ring
  · rw [hB h, max_eq_right (by linarith), k0_eq P hS]
    ring

/-- Generic selection: a cost minimizer (with ties only against zero) is the unique selected
buyer optimum. -/
lemma select (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) (e0 : ℝ) (he0 : 0 ≤ e0)
    (H : ∀ y, 0 ≤ y → y ≠ e0 →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b e0 <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b y ∨
      (y = 0 ∧ 0 < e0 ∧
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b e0 =
          cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0)) :
    IsBuyerOptimal P σ2 σ1 e0 ∧ ∀ x0, IsBuyerOptimal P σ2 σ1 x0 → x0 = e0 := by
  have hl0 := (st_pos P hS).2.2.2.2.1
  set C := cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b
  have hP : ∀ x, 0 ≤ x → P.game.buyerProfit σ2 σ1 x = P.m0 * P.d - P.ell0 * C x :=
    fun x hx => cost_eq P hS σ2 σ1 h2 h1 x hx
  have hle : ∀ y, 0 ≤ y → C e0 ≤ C y := by
    intro y hy
    by_cases hye : y = e0
    · rw [hye]
    · rcases H y hy hye with h | ⟨rfl, -, h⟩
      · exact h.le
      · exact h.le
  refine ⟨⟨he0, ?_, ?_⟩, ?_⟩
  · intro y hy
    rw [hP y hy, hP e0 he0]
    have := hle y hy
    nlinarith
  · intro hz y hy
    rw [hP y hy.le, hP 0 le_rfl]
    have hne : y ≠ e0 := by rw [hz]; exact hy.ne'
    rcases H y hy.le hne with h | ⟨h, -, -⟩
    · rw [hz] at h; nlinarith
    · exact absurd h hy.ne'
  · intro x0 ⟨hx0, hopt, htie⟩
    by_contra hne
    have h' := hopt e0 he0
    rw [hP e0 he0, hP x0 hx0] at h'
    rcases H x0 hx0 hne with h | ⟨hx, he, h⟩
    · nlinarith
    · have := htie hx e0 he
      rw [hP e0 he0, hP 0 le_rfl] at this
      rw [h] at this
      linarith

/-- Generic row lemma. -/
lemma row (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) (e0 e1 e2 lam : ℝ)
    (he0 : 0 ≤ e0) (he1 : tier1Candidate P e0 = e1)
    (he2 : tier2Candidate P e0 e1 = e2) (hlam : P.tau2 / (P.β * (e0 + e1 + P.b)) = lam)
    (H : ∀ y, 0 ≤ y → y ≠ e0 →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b e0 <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b y ∨
      (y = 0 ∧ 0 < e0 ∧
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b e0 =
          cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0)) :
    ChoiceIs P σ2 σ1 e0 e1 e2 lam := by
  obtain ⟨hopt, huniq⟩ := select P hS σ2 σ1 h2 h1 e0 he0 H
  have he1' : 0 ≤ e1 := he1 ▸ cand1_nonneg P e0
  refine ⟨hopt, huniq, ?_, ?_, ?_⟩
  · rw [sigma1_eq P hS σ2 σ1 h2 h1 e0 he0, he1]
  · rw [sigma2_eq P hS σ2 h2 e0 e1 he0 he1', he2]
  · unfold violationProb
    rw [← he2, exp_cand2 P hS e0 e1 (by linarith), hlam]

lemma ctrl_row (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (hrw : Real.sqrt P.tau2 / Real.sqrt P.tau1 ≤ Real.sqrt P.tau2 / Real.sqrt P.tau0)
    (he0 : 0 ≤ Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b)
    (H : ∀ y, 0 ≤ y → y ≠ Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b
          (Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b) <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b y ∨
      (y = 0 ∧ 0 < Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b ∧
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b
            (Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b) =
          cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0)) :
    ChoiceRow P σ2 σ1 (controlRow P) := by
  have t0 := tau0_pos P hS
  have t2 := tau2_pos P hS
  have hβ := (st_pos P hS).2.2.2.2.2.2.2.1
  have q0 : 0 < Real.sqrt P.tau0 := Real.sqrt_pos.mpr t0
  have q2 : 0 < Real.sqrt P.tau2 := Real.sqrt_pos.mpr t2
  unfold ChoiceRow controlRow
  simp only
  rw [sqrt_ratio t2, sqrt_ratio t0, sqrt_prod t0]
  apply row P hS σ2 σ1 h2 h1 _ _ _ _ he0
  · unfold tier1Candidate
    rw [sqrt_ratio t2]
    apply max_eq_right; linarith
  · unfold tier2Candidate
    have e : Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b + 0 + P.b =
        Real.sqrt P.tau2 / Real.sqrt P.tau0 := by ring
    rw [e]
    have e2 : P.β * (Real.sqrt P.tau2 / Real.sqrt P.tau0) / P.tau2 =
        P.β / (Real.sqrt P.tau0 * Real.sqrt P.tau2) := by
      have hq := sq_sqrt_tau t2
      set q := Real.sqrt P.tau2
      rw [← hq]; field_simp
    rw [e2]; field_simp
  · have e : Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b + 0 + P.b =
        Real.sqrt P.tau2 / Real.sqrt P.tau0 := by ring
    have hq := sq_sqrt_tau t2
    rw [e]
    set q := Real.sqrt P.tau2
    rw [← hq]; field_simp
  · exact H

lemma del_row (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (hA : P.b < Real.sqrt P.tau2 / Real.sqrt P.tau1)
    (H : ∀ y, 0 ≤ y → y ≠ 0 →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0 <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b y) :
    ChoiceRow P σ2 σ1 (delegationRow P) := by
  have t1 := tau1_pos P hS
  have t2 := tau2_pos P hS
  have hβ := (st_pos P hS).2.2.2.2.2.2.2.1
  have q1 : 0 < Real.sqrt P.tau1 := Real.sqrt_pos.mpr t1
  have q2 : 0 < Real.sqrt P.tau2 := Real.sqrt_pos.mpr t2
  unfold ChoiceRow delegationRow
  simp only
  rw [sqrt_ratio t2, sqrt_ratio t1, sqrt_prod t1]
  apply row P hS σ2 σ1 h2 h1 _ _ _ _ le_rfl
  · unfold tier1Candidate
    rw [sqrt_ratio t2, sub_zero]
    apply max_eq_left; linarith
  · unfold tier2Candidate
    have e : 0 + (Real.sqrt P.tau2 / Real.sqrt P.tau1 - P.b) + P.b =
        Real.sqrt P.tau2 / Real.sqrt P.tau1 := by ring
    rw [e]
    have e2 : P.β * (Real.sqrt P.tau2 / Real.sqrt P.tau1) / P.tau2 =
        P.β / (Real.sqrt P.tau1 * Real.sqrt P.tau2) := by
      have hq := sq_sqrt_tau t2
      set q := Real.sqrt P.tau2
      rw [← hq]; field_simp
    rw [e2]; field_simp
  · have e : 0 + (Real.sqrt P.tau2 / Real.sqrt P.tau1 - P.b) + P.b =
        Real.sqrt P.tau2 / Real.sqrt P.tau1 := by ring
    have hq := sq_sqrt_tau t2
    rw [e]
    set q := Real.sqrt P.tau2
    rw [← hq]; field_simp
  · intro y hy hne; left; exact H y hy hne

lemma no_row (hS : P.Standing) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (hB : Real.sqrt P.tau2 / Real.sqrt P.tau1 ≤ P.b)
    (H : ∀ y, 0 ≤ y → y ≠ 0 →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0 <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b y) :
    ChoiceRow P σ2 σ1 (noEffortRow P) := by
  have t2 := tau2_pos P hS
  unfold ChoiceRow noEffortRow
  simp only
  apply row P hS σ2 σ1 h2 h1 _ _ _ _ le_rfl
  · unfold tier1Candidate
    rw [sqrt_ratio t2]
    apply max_eq_right; linarith
  · unfold tier2Candidate; congr 1 <;> ring_nf
  · ring_nf
  · intro y hy hne; left; exact H y hy hne

theorem main' (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) :
    (∀ x0 : ℝ, IsBuyerOptimal P σ2 σ1 x0 → ¬ (0 < x0 ∧ 0 < σ1 x0)) ∧
    (P.tau1 < P.tau2 / P.b ^ 2 →
      (P.tau0 ≤ P.tau1 / 4 → ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau1 / 4 < P.tau0 → P.tau0 ≤ P.tau1 →
        (P.tau2 ≤ g P → ChoiceRow P σ2 σ1 (controlRow P)) ∧
        (g P < P.tau2 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
      (P.tau1 < P.tau0 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
    (P.tau2 / P.b ^ 2 ≤ P.tau1 →
      (P.tau0 ≤ P.tau2 / P.b ^ 2 →
        ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau2 / P.b ^ 2 < P.tau0 →
        ChoiceRow P σ2 σ1 (noEffortRow P))) := by
  have t0 := tau0_pos P hS
  have t1 := tau1_pos P hS
  have t2 := tau2_pos P hS
  have hb := (st_pos P hS).2.2.2.2.2.2.2.2.1
  have hl0 := (st_pos P hS).2.2.2.2.1
  have q0 : 0 < Real.sqrt P.tau0 := Real.sqrt_pos.mpr t0
  have q1 : 0 < Real.sqrt P.tau1 := Real.sqrt_pos.mpr t1
  have q2 : 0 < Real.sqrt P.tau2 := Real.sqrt_pos.mpr t2
  have e0 := sq_sqrt_tau t0
  have e1 := sq_sqrt_tau t1
  have e2 := sq_sqrt_tau t2
  have hg : g P = (P.b * Real.sqrt P.tau0 ^ 2 / (2 * Real.sqrt P.tau0 - Real.sqrt P.tau1)) ^ 2 := by
    unfold g; rw [e0]
  rw [hg]
  have hcmpS : P.tau1 < P.tau2 / P.b ^ 2 → P.tau0 ≤ P.tau1 →
      0 ≤ Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b →
      0 < P.b * Real.sqrt P.tau0 ^ 2 - 2 * Real.sqrt P.tau0 * Real.sqrt P.tau2 +
        Real.sqrt P.tau1 * Real.sqrt P.tau2 →
      cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b
          (Real.sqrt P.tau2 / Real.sqrt P.tau0 - P.b) <
        cst (Real.sqrt P.tau0) (Real.sqrt P.tau1) (Real.sqrt P.tau2) P.b 0 := by
    intro a c hx hK
    have hc := (MultitierCSR.Strategy.control_delegation_comparison P hS σ2 σ1 h2 h1 a c).mpr
      (by
        have : P.b * Real.sqrt P.tau0 ^ 2 = P.b * P.tau0 := by rw [e0]
        rw [sqrt_prod t0, sqrt_prod t1]; linarith)
    rw [sqrt_ratio t2, cost_eq P hS σ2 σ1 h2 h1 0 le_rfl, cost_eq P hS σ2 σ1 h2 h1 _ hx] at hc
    nlinarith
  set s0 := Real.sqrt P.tau0
  set s1 := Real.sqrt P.tau1
  set s2 := Real.sqrt P.tau2
  rw [← e0, ← e1, ← e2]
  rw [← e0, ← e1, ← e2] at hcmpS
  have hb2 : 0 < P.b ^ 2 := by positivity
  -- regime translations
  have trA : s1 ^ 2 < s2 ^ 2 / P.b ^ 2 → P.b * s1 < s2 := by
    intro h; rw [lt_div_iff₀ hb2] at h; nlinarith
  have trB : s2 ^ 2 / P.b ^ 2 ≤ s1 ^ 2 → s2 ≤ P.b * s1 := by
    intro h; rw [div_le_iff₀ hb2] at h; nlinarith [mul_pos hb q1]
  have hrA : P.b * s1 < s2 → P.b < s2 / s1 := fun h => by rw [lt_div_iff₀ q1]; linarith
  have hrB : s2 ≤ P.b * s1 → s2 / s1 ≤ P.b := fun h => by rw [div_le_iff₀ q1]; linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1 (via the domination milestone)
    rintro x0 ⟨hx0, hopt, -⟩ ⟨hxpos, hσ⟩
    rw [sigma1_eq P hS σ2 σ1 h2 h1 x0 hx0] at hσ
    unfold tier1Candidate at hσ
    have hlt : 0 < Real.sqrt (P.tau2 / P.tau1) - P.b - x0 := by
      by_contra h; push Not at h; rw [max_eq_right h] at hσ; exact lt_irrefl _ hσ
    have hdom := MultitierCSR.Strategy.domination P hS σ2 σ1 h2 h1 (by linarith) x0 hxpos
      (by linarith)
    have h' := hopt 0 le_rfl
    change buyerProfit P σ2 σ1 0 ≤ buyerProfit P σ2 σ1 x0 at h'
    linarith
  · intro hA'
    have hA := trA hA'
    have hc := cA q0 q1 q2 hb hA
    have ctrlA : s0 < s1 → 0 ≤ P.b * s0 ^ 2 - 2 * s0 * s2 + s1 * s2 →
        ChoiceRow P σ2 σ1 (controlRow P) := by
      intro h01 hK
      have hrw : s2 / s1 < s2 / s0 := div_lt_div_of_pos_left q2 q0 h01
      have hx : 0 ≤ s2 / s0 - P.b := by linarith [hrA hA]
      apply ctrl_row P hS σ2 σ1 h2 h1 hrw.le hx
      intro y hy hne
      exact RctrlA q0 q1 q2 hb hA h01 hK (hcmpS hA' (by nlinarith) hx) hy hne
    refine ⟨?_, ?_, ?_⟩
    · intro h4
      have h01 : 2 * s0 ≤ s1 := by nlinarith
      apply ctrlA (by linarith)
      nlinarith [mul_pos q0 q0]
    · intro h4 h01
      have h4' : s1 < 2 * s0 := by nlinarith
      have h01' : s0 ≤ s1 := by nlinarith
      have hd : 0 < 2 * s0 - s1 := by linarith
      have hgnn : 0 ≤ P.b * s0 ^ 2 / (2 * s0 - s1) := by positivity
      constructor
      · intro hgle
        have h3 : s2 ≤ P.b * s0 ^ 2 / (2 * s0 - s1) := (sq_le_sq₀ q2.le hgnn).mp hgle
        rw [le_div_iff₀ hd] at h3
        have hK : 0 ≤ P.b * s0 ^ 2 - 2 * s0 * s2 + s1 * s2 := by nlinarith
        apply ctrlA _ hK
        rcases eq_or_lt_of_le h01' with h | h
        · exfalso
          rw [← h] at hK hA
          nlinarith
        · exact h
      · intro hglt
        have h3 : P.b * s0 ^ 2 / (2 * s0 - s1) < s2 := by
          by_contra hh; push Not at hh
          have := (sq_le_sq₀ q2.le hgnn).mpr hh; linarith
        rw [div_lt_iff₀ hd] at h3
        apply del_row P hS σ2 σ1 h2 h1 (hrA hA)
        intro y hy hne
        exact Rdel2 q0 q1 q2 hb hA (by nlinarith) hy hne
    · intro h10
      have h10' : s1 < s0 := by nlinarith
      apply del_row P hS σ2 σ1 h2 h1 (hrA hA)
      intro y hy hne
      exact Rdel1 q0 q1 q2 hb hA h10' hy hne
  · intro hB'
    have hB := trB hB'
    constructor
    · intro hw'
      have hw : P.b * s0 ≤ s2 := by rw [le_div_iff₀ hb2] at hw'; nlinarith
      have hw2 : P.b ≤ s2 / s0 := by rw [le_div_iff₀ q0]; linarith
      apply ctrl_row P hS σ2 σ1 h2 h1 (by linarith [hrB hB]) (by linarith)
      intro y hy hne
      left; exact RctrlB q0 q1 q2 hb hB hw hy hne
    · intro hw'
      have hw : s2 < P.b * s0 := by rw [div_lt_iff₀ hb2] at hw'; nlinarith [mul_pos hb q0]
      apply no_row P hS σ2 σ1 h2 h1 (hrB hB)
      intro y hy hne
      exact RnoB q0 q1 q2 hb hB hw hy hne

end MTCSRRed

open MultitierCSR.Strategy in
theorem solution (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) :
    (∀ x0 : ℝ, IsBuyerOptimal P σ2 σ1 x0 → ¬ (0 < x0 ∧ 0 < σ1 x0)) ∧
    (P.tau1 < P.tau2 / P.b ^ 2 →
      (P.tau0 ≤ P.tau1 / 4 → ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau1 / 4 < P.tau0 → P.tau0 ≤ P.tau1 →
        (P.tau2 ≤ g P → ChoiceRow P σ2 σ1 (controlRow P)) ∧
        (g P < P.tau2 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
      (P.tau1 < P.tau0 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
    (P.tau2 / P.b ^ 2 ≤ P.tau1 →
      (P.tau0 ≤ P.tau2 / P.b ^ 2 →
        ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau2 / P.b ^ 2 < P.tau0 →
        ChoiceRow P σ2 σ1 (noEffortRow P))) :=
  MTCSRRed.main' P hS σ2 σ1 h2 h1
