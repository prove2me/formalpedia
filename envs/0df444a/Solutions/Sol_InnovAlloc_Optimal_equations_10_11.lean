-- Prove2me | solution 1 for InnovAlloc.Optimal.equations_10_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:07:21.867854+00:00
-- url     : https://prove2.me/submissions/3bb6b1a0-5b83-4fed-a2eb-98cb8b14d868

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model
import Theorems.Thm_InnovAlloc_Optimal_equations_2_3

open InnovAlloc.Optimal

namespace IASolT1

noncomputable def F (g b : ℝ) : ℝ := if g * b ≤ 1 then 0 else 1 - 1 / (g * b)
noncomputable def gp (α γ p : ℝ) : ℝ := γ * (α * p + (1 - p))

lemma succ_zero (x : ℝ) : succ 0 x = 0 := by simp [succ]

lemma succ_bounds {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) : 0 ≤ succ b x ∧ succ b x < 1 := by
  unfold succ
  constructor
  · have : Real.exp (-(b * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  · have := Real.exp_pos (-(b * x)); linarith

lemma gp_bounds {α γ p : ℝ} (hs : Standing α γ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    0 < gp α γ p ∧ gp α γ p < 1 ∧ gp α γ p ≤ γ := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold gp
  have : 0 < α * p + (1 - p) := by nlinarith
  have : α * p + (1 - p) ≤ 1 := by nlinarith
  refine ⟨by positivity, by nlinarith, by nlinarith⟩

lemma payoff_eq (α γ bi xi bj xj : ℝ) :
    agentPayoff α γ bi xi bj xj = gp α γ (succ bj xj) * succ bi xi - xi := by
  unfold agentPayoff gp; ring

lemma effortStar_nonneg {g b : ℝ} (hb : 0 < b) : 0 ≤ effortStar g b := by
  unfold effortStar
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (Real.log_nonneg (by linarith)) hb.le

lemma br_succ {g b x : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : ∀ z : ℝ, 0 ≤ z → g * succ b z - z ≤ g * succ b x - x) :
    succ b x = F g b := by
  rcases hb.lt_or_eq with hb | hb
  · have H := equations_2_3 g b hg0 hg1 hb
    have hx' : x = effortStar g b := (H.1 x hx).1 h
    rw [hx', H.2.1]; rfl
  · subst hb; simp [succ_zero, F]

lemma br_exists {g b : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hb : 0 ≤ b) :
    ∃ x, 0 ≤ x ∧ ∀ z : ℝ, 0 ≤ z → g * succ b z - z ≤ g * succ b x - x := by
  rcases hb.lt_or_eq with hb | hb
  · have H := equations_2_3 g b hg0 hg1 hb
    exact ⟨effortStar g b, effortStar_nonneg hb, (H.1 _ (effortStar_nonneg hb)).2 rfl⟩
  · subst hb; exact ⟨0, le_rfl, fun z hz => by simp [succ_zero]; linarith⟩

lemma eq_succ {α γ b1 b2 x1 x2 : ℝ} (hs : Standing α γ) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h : IsEquilibrium α γ b1 b2 x1 x2) :
    0 ≤ x1 ∧ 0 ≤ x2 ∧ succ b1 x1 = F (gp α γ (succ b2 x2)) b1 ∧
      succ b2 x2 = F (gp α γ (succ b1 x1)) b2 := by
  obtain ⟨v1, v2, rfl, rfl, h1, h2⟩ := h
  have hx1 := v1.2
  have hx2 := v2.2
  obtain ⟨p20, p21⟩ := succ_bounds hb2 hx2
  obtain ⟨p10, p11⟩ := succ_bounds hb1 hx1
  obtain ⟨g1a, g1b, -⟩ := gp_bounds hs p20 p21
  obtain ⟨g2a, g2b, -⟩ := gp_bounds hs p10 p11
  refine ⟨hx1, hx2, br_succ g1a g1b hb1 hx1 ?_, br_succ g2a g2b hb2 hx2 ?_⟩
  · intro z hz
    have := h1 ⟨z, hz⟩
    simpa [payoff_eq] using this
  · intro z hz
    have := h2 ⟨z, hz⟩
    simpa [payoff_eq] using this

lemma mk_eq {α γ b1 b2 x1 x2 : ℝ} (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (h1 : ∀ z, 0 ≤ z → gp α γ (succ b2 x2) * succ b1 z - z ≤
      gp α γ (succ b2 x2) * succ b1 x1 - x1)
    (h2 : ∀ z, 0 ≤ z → gp α γ (succ b1 x1) * succ b2 z - z ≤
      gp α γ (succ b1 x1) * succ b2 x2 - x2) :
    IsEquilibrium α γ b1 b2 x1 x2 :=
  ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩, rfl, rfl, fun y => by simpa [payoff_eq] using h1 y.1 y.2,
    fun y => by simpa [payoff_eq] using h2 y.1 y.2⟩

lemma profitMono_F (γ B : ℝ) : profitMono γ B = (1 - γ) * F γ B := by
  unfold profitMono F; split_ifs <;> ring

lemma gp_zero (α γ : ℝ) : gp α γ 0 = γ := by unfold gp; ring

end IASolT1

namespace IASolT1

lemma ystar_facts {α γ B : ℝ} (hs : Standing α γ) (hB : 2 < γ * B) :
    0 < yStar α γ B ∧ yStar α γ B < 1 ∧
    γ * (B / 2) * (α + (1 - α) * yStar α γ B) * yStar α γ B = 1 ∧
    1 / yStar α γ B = (γ * B * α + Real.sqrt ((γ * B) ^ 2 * α ^ 2 + 8 * (γ * B) * (1 - α))) / 4 := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  set T := γ * B with hT
  have hT0 : 0 < T := by linarith
  have hBpos : 0 < B := by
    by_contra hc; push_neg at hc; nlinarith
  have harg : 0 ≤ 8 - 8 * α + α ^ 2 * B * γ := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hBpos.le) hγ0.le]
  have hRdef : Real.sqrt (B * γ) * Real.sqrt (8 - 8 * α + α ^ 2 * B * γ) =
      Real.sqrt (T ^ 2 * α ^ 2 + 8 * T * (1 - α)) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; rw [hT]; ring
  have hR2arg : 0 ≤ T ^ 2 * α ^ 2 + 8 * T * (1 - α) := by
    have : 0 ≤ 8 * T * (1 - α) := by have := mul_nonneg hT0.le (by linarith : (0:ℝ) ≤ 1 - α); linarith
    positivity
  have hR2 := Real.sq_sqrt hR2arg
  have hR0 := Real.sqrt_nonneg (T ^ 2 * α ^ 2 + 8 * T * (1 - α))
  set R := Real.sqrt (T ^ 2 * α ^ 2 + 8 * T * (1 - α))
  have hy : yStar α γ B = 4 / (T * α + R) := by
    unfold yStar; rw [hRdef, hT]; ring_nf
  have hD : 4 < T * α + R := by
    by_contra hc; push_neg at hc
    have h1 : R ≤ 4 - T * α := by linarith
    nlinarith [mul_le_mul h1 h1 hR0 (by linarith)]
  have hDpos : 0 < T * α + R := by linarith
  rw [hy]
  refine ⟨by positivity, by rw [div_lt_one hDpos]; exact hD, ?_, ?_⟩
  · have : γ * (B / 2) = T / 2 := by rw [hT]; ring
    rw [this]
    have hD2 : (T * α + R) ^ 2 = 2 * T * (α * (T * α + R) + 4 * (1 - α)) := by
      linear_combination hR2
    calc T / 2 * (α + (1 - α) * (4 / (T * α + R))) * (4 / (T * α + R))
        = 2 * T * (α * (T * α + R) + 4 * (1 - α)) / (T * α + R) ^ 2 := by
          field_simp; ring
      _ = 1 := by rw [← hD2, div_self (pow_ne_zero 2 hDpos.ne')]
  · field_simp

lemma profit_sym {α γ B c x1 x2 y : ℝ} (hs : Standing α γ) (hB : 2 < γ * B) (hc : c = B / 2)
    (hy : y = yStar α γ B) (h1 : succ c x1 = 1 - y) (h2 : succ c x2 = 1 - y) :
    principalProfit α γ c c x1 x2 = profitDuo α γ B := by
  obtain ⟨y0, y1, ykey, yinv⟩ := ystar_facts hs hB
  rw [← hy] at y0 y1 ykey yinv
  have hT0 : 0 < γ * B := by linarith
  unfold principalProfit profitDuo
  rw [if_neg (by linarith), h1, h2]
  have harg : (γ * α ^ 2 * B - 8 * α + 8) / (γ * B) =
      ((γ * B) ^ 2 * α ^ 2 + 8 * (γ * B) * (1 - α)) / (γ * B) ^ 2 := by
    field_simp; ring
  rw [harg, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hT0.le]
  have hS : Real.sqrt ((γ * B) ^ 2 * α ^ 2 + 8 * (γ * B) * (1 - α)) = 4 / y - γ * B * α := by
    rw [one_div] at yinv
    have : 4 / y = 4 * y⁻¹ := by ring
    rw [this, yinv]; ring
  have hy0 : y ≠ 0 := y0.ne'
  have hk : γ * B * (α + (1 - α) * y) * y = 2 := by
    have : γ * (B / 2) = γ * B / 2 := by ring
    rw [this] at ykey; linarith
  have h4y : 4 / y = 2 * (γ * B) * (α + (1 - α) * y) := by
    field_simp; linear_combination (-2) * hk
  rw [hS, h4y]
  have hTn : γ * B ≠ 0 := hT0.ne'
  have hγn : γ ≠ 0 := left_ne_zero_of_mul hTn
  have hBn : B ≠ 0 := right_ne_zero_of_mul hTn
  congr 1
  field_simp
  linear_combination (-2) * hk

lemma eq1011 (α γ B : ℝ) (hs : Standing α γ) (hB : 2 < γ * B) :
    (∃ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 ∧
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) ∧
    (0 < α → ∀ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 →
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) := by
  obtain ⟨y0, y1, ykey, -⟩ := ystar_facts hs hB
  have hs' := hs
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs'
  have hBpos : 0 < B := by
    by_contra hc; push_neg at hc; nlinarith
  set y := yStar α γ B with hydef
  set c := B / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hsucc_exp : ∀ x, succ c x = 1 - Real.exp (-(c * x)) := fun x => rfl
  constructor
  · set x := -Real.log y / c with hx
    have hex : Real.exp (-(c * x)) = y := by
      have : -(c * x) = Real.log y := by rw [hx]; field_simp
      rw [this, Real.exp_log y0]
    have hsx : succ c x = 1 - y := by rw [hsucc_exp, hex]
    have hx0 : 0 ≤ x := by
      rw [hx]; apply div_nonneg _ hc0.le
      have := Real.log_neg y0 y1; linarith
    have hgp : gp α γ (succ c x) = γ * (α + (1 - α) * y) := by rw [hsx]; unfold gp; ring
    obtain ⟨g0, g1, -⟩ := gp_bounds hs (succ_bounds hc0.le hx0).1 (succ_bounds hc0.le hx0).2
    have hbr : ∀ z, 0 ≤ z → gp α γ (succ c x) * succ c z - z ≤ gp α γ (succ c x) * succ c x - x := by
      have H := equations_2_3 (gp α γ (succ c x)) c g0 g1 hc0
      apply (H.1 x hx0).2
      have hgc : gp α γ (succ c x) * c = 1 / y := by
        rw [hgp]; field_simp; linarith
      unfold effortStar
      rw [if_neg (by rw [hgc]; exact not_lt.2 (by rw [le_div_iff₀ y0]; linarith)), hgc, hx, Real.log_div one_ne_zero y0.ne', Real.log_one]
      ring
    refine ⟨x, x, mk_eq hx0 hx0 hbr hbr, hex, hex, ?_⟩
    exact profit_sym hs hB rfl rfl hsx hsx
  · intro hα x1 x2 h
    obtain ⟨hx1, hx2, e1, e2⟩ := eq_succ hs hc0.le hc0.le h
    have hgp : ∀ p, gp α γ p = γ * (α + (1 - α) * (1 - p)) := fun p => by unfold gp; ring
    rw [hgp] at e1 e2
    set q1 := Real.exp (-(c * x1)) with hq1
    set q2 := Real.exp (-(c * x2)) with hq2
    have hp1 : succ c x1 = 1 - q1 := rfl
    have hp2 : succ c x2 = 1 - q2 := rfl
    rw [hp1, hp2] at e1 e2
    have q10 : 0 < q1 := Real.exp_pos _
    have q20 : 0 < q2 := Real.exp_pos _
    have q11 : q1 ≤ 1 := by have := (succ_bounds hc0.le hx1).1; rw [hp1] at this; linarith
    have q21 : q2 ≤ 1 := by have := (succ_bounds hc0.le hx2).1; rw [hp2] at this; linarith
    simp only [sub_sub_cancel] at e1 e2
    have hγc : 1 < γ * c := by rw [hcdef]; linarith
    unfold F at e1 e2
    have hq : q1 = q2 := by
      split_ifs at e1 with A1 <;> split_ifs at e2 with A2
      · exfalso; have : q1 = 1 := by linarith
        rw [this] at A2; nlinarith
      · exfalso
        have : q1 = 1 := by linarith
        rw [this] at A2 e2
        push_neg at A2
        have e2' : q2 = 1 / (γ * (α + (1 - α) * 1) * c) := by linarith
        rw [show γ * (α + (1 - α) * 1) * c = γ * c by ring] at e2'
        have hq2v : q2 * (γ * c) = 1 := by rw [e2', one_div, inv_mul_cancel₀ (by positivity)]
        nlinarith [mul_pos hα (by linarith : (0:ℝ) < γ * c - 1), congrArg (· * α) hq2v]
      · exfalso
        have : q2 = 1 := by linarith
        rw [this] at A1 e1
        push_neg at A1
        have e1' : q1 = 1 / (γ * (α + (1 - α) * 1) * c) := by linarith
        rw [show γ * (α + (1 - α) * 1) * c = γ * c by ring] at e1'
        have hq1v : q1 * (γ * c) = 1 := by rw [e1', one_div, inv_mul_cancel₀ (by positivity)]
        nlinarith [mul_pos hα (by linarith : (0:ℝ) < γ * c - 1), congrArg (· * α) hq1v]
      · push_neg at A1 A2
        have k1 : q1 * (γ * (α + (1 - α) * q2) * c) = 1 := by
          have hne : γ * (α + (1 - α) * q2) * c ≠ 0 := by intro h0; linarith
          have : q1 = 1 / (γ * (α + (1 - α) * q2) * c) := by linarith
          rw [eq_div_iff hne] at this; exact this
        have k2 : q2 * (γ * (α + (1 - α) * q1) * c) = 1 := by
          have hne : γ * (α + (1 - α) * q1) * c ≠ 0 := by intro h0; linarith
          have : q2 = 1 / (γ * (α + (1 - α) * q1) * c) := by linarith
          rw [eq_div_iff hne] at this; exact this
        have : γ * c * α * (q1 - q2) = 0 := by linear_combination k1 - k2
        have hpos : γ * c * α ≠ 0 := by positivity
        have := (mul_eq_zero.1 this).resolve_left hpos
        linarith
    -- now q1 = q2 =: q, show q = y
    rw [← hq] at e1
    have hact : 1 < γ * (α + (1 - α) * q1) * c := by
      by_contra hc; push_neg at hc
      rw [if_pos hc] at e1
      have : q1 = 1 := by linarith
      rw [this] at hc; nlinarith
    rw [if_neg (not_le.2 hact)] at e1
    have k : q1 * (γ * (α + (1 - α) * q1) * c) = 1 := by
      have hne : γ * (α + (1 - α) * q1) * c ≠ 0 := by intro h0; linarith
      have : q1 = 1 / (γ * (α + (1 - α) * q1) * c) := by linarith
      rw [eq_div_iff hne] at this; exact this
    have ky : γ * c * (α + (1 - α) * y) * y = 1 := ykey
    have hqy : q1 = y := by
      have : (q1 - y) * (γ * c * (1 - α) * (q1 + y) + γ * c * α) = 0 := by
        linear_combination k - ky
      have hpos : 0 < γ * c * (1 - α) * (q1 + y) + γ * c * α := by
        have : 0 ≤ γ * c * (1 - α) * (q1 + y) := by
          have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ γ * c) (by linarith : (0:ℝ) ≤ 1 - α)) (by linarith : (0:ℝ) ≤ q1 + y)
          linarith
        have : 0 < γ * c * α := by positivity
        linarith
      have := (mul_eq_zero.1 this).resolve_right hpos.ne'
      linarith
    refine ⟨hqy, by rw [← hq]; exact hqy, ?_⟩
    exact profit_sym hs hB rfl rfl (by rw [hp1, hqy]) (by rw [hp2, ← hq, hqy])

end IASolT1

open InnovAlloc.Optimal in
theorem solution (α γ B : ℝ) (hs : Standing α γ) (hB : 2 < γ * B) :
    (∃ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 ∧
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) ∧
    (0 < α → ∀ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 →
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) :=
  IASolT1.eq1011 α γ B hs hB
