-- Prove2me | solution 1 for InnovAlloc.Optimal.equation_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:57:47.63896+00:00
-- url     : https://prove2.me/submissions/09d132ac-56f1-4b72-b171-6f73a5263066

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

theorem eq8 (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B) :
    (∃ x1 x2, IsEquilibrium α γ B 0 x1 x2) ∧
    ∀ x1 x2, IsEquilibrium α γ B 0 x1 x2 →
      principalProfit α γ B 0 x1 x2 = profitMono γ B := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  constructor
  · obtain ⟨x, hx, hbr⟩ := br_exists h1 h2 hB.le
    refine ⟨x, 0, mk_eq hx le_rfl ?_ ?_⟩
    · simpa [succ_zero, gp_zero] using hbr
    · intro z hz; simp [succ_zero]; linarith
  · intro x1 x2 h
    obtain ⟨-, -, e1, -⟩ := eq_succ ⟨h1, h2, h3, h4⟩ hB.le le_rfl h
    rw [succ_zero, gp_zero] at e1
    rw [profitMono_F]
    unfold principalProfit
    rw [succ_zero, e1]; ring

end IASolT1

open InnovAlloc.Optimal in
theorem solution (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B) :
    (∃ x1 x2, IsEquilibrium α γ B 0 x1 x2) ∧
    ∀ x1 x2, IsEquilibrium α γ B 0 x1 x2 →
      principalProfit α γ B 0 x1 x2 = profitMono γ B :=
  IASolT1.eq8 α γ B hs hB
