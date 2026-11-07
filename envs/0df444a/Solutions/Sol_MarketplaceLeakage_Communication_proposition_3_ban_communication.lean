-- Prove2me | solution 1 for MarketplaceLeakage.Communication.proposition_3_ban_communication
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:02:43.225066+00:00
-- url     : https://prove2.me/submissions/44993a98-54aa-42db-9de5-1e6304d24c49

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piL
import Definitions.Def_MarketplaceLeakage_Communication_piStarUniform
import Definitions.Def_MarketplaceLeakage_Communication_PrefersBan
import Definitions.Def_MarketplaceLeakage_Communication_PrefersAllow

set_option autoImplicit false

namespace MLP3Ban

open MarketplaceLeakage.Communication

/-- `Π_L` in the variable `t = 1 - η`: `K + α t - β / t`. -/
lemma piL_t (q v c η : ℝ) (h : η < 1) :
    piL q v c η = (q * ((2 - q) * q * v - c) - (1 - q) * ((1 - q) * q * v))
      + (1 - q) * ((2 - q) * q * v - c) * (1 - η) - q * ((1 - q) * q * v) / (1 - η) := by
  have h1 : (1 - η) ≠ 0 := by linarith
  unfold piL
  field_simp
  ring

/-- `Π_L = (1 - (1-q)η) (qv - c - (1-q) q v · η/(1-η))`. -/
lemma piL_s (q v c η : ℝ) (h : η < 1) :
    piL q v c η = (1 - (1 - q) * η) * (q * v - c - (1 - q) * q * v * (η / (1 - η))) := by
  have h1 : (1 - η) ≠ 0 := by linarith
  unfold piL
  field_simp
  ring

/-- `Π_L · (1 - η)` is a polynomial. -/
lemma piL_mul (q v c η : ℝ) (h : η < 1) :
    piL q v c η * (1 - η) = (1 - η + η * q) * ((1 - (2 - q) * η) * q * v - c * (1 - η)) := by
  have h1 : (1 - η) ≠ 0 := by linarith
  unfold piL
  field_simp

lemma piL_zero (q v c : ℝ) : piL q v c 0 = q * v - c := by
  unfold piL; simp

/-- `Π_L` is strictly decreasing on `[0,1)` when `α ≥ 0`, `β > 0`. -/
lemma piL_anti (q v c a b : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hv : 0 < v)
    (hA : 0 ≤ (2 - q) * q * v - c) (hab : a < b) (hb : b < 1) :
    piL q v c b < piL q v c a := by
  rw [piL_t q v c a (by linarith), piL_t q v c b hb]
  have ht2 : 0 < 1 - b := by linarith
  have hβ : 0 < q * ((1 - q) * q * v) := by
    have : 0 < 1 - q := by linarith
    positivity
  have hα : 0 ≤ (1 - q) * ((2 - q) * q * v - c) := mul_nonneg (by linarith) hA
  have e1 : q * ((1 - q) * q * v) / (1 - a) < q * ((1 - q) * q * v) / (1 - b) :=
    div_lt_div_of_pos_left hβ ht2 (by linarith)
  have e2 : (1 - q) * ((2 - q) * q * v - c) * (1 - b) ≤ (1 - q) * ((2 - q) * q * v - c) * (1 - a) :=
    mul_le_mul_of_nonneg_left (by linarith) hα
  linarith

lemma part_i {v c : ℝ} (hcv : c < v) (P q η : ℝ) (hq0 : 0 < q) (hη : P / (v - c) < η) :
    PrefersBan q v c η P := by
  unfold PrefersBan banProfit piH
  have h1 : P < η * (v - c) := by rwa [div_lt_iff₀ (by linarith)] at hη
  have h2 := mul_lt_mul_of_pos_left h1 hq0
  exact lt_max_of_lt_left (by linarith)

lemma part_ii {v c : ℝ} (hc : 0 < c) (hcv : c < v) (P : ℝ) (hP0 : 0 < P) (hPv : P < v - c)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hqc : c / (v - P) < q) :
    ∃ ηL : ℝ, 0 < ηL ∧ ηL < 1 ∧ piL q v c ηL = q * P ∧
      (∀ η : ℝ, 0 ≤ η → η < 1 → piL q v c η = q * P → η = ηL) ∧
      ∀ η : ℝ, 0 ≤ η → η < ηL → PrefersBan q v c η P := by
  have hvP : 0 < v - P := by linarith
  have hqv : c < q * (v - P) := by rwa [div_lt_iff₀ hvP] at hqc
  have hv : 0 < v := by linarith
  have hqP : 0 < q * P := mul_pos hq0 hP0
  have hA : 0 ≤ (2 - q) * q * v - c := by
    have : 0 ≤ (1 - q) * q * v := by
      have : 0 ≤ 1 - q := by linarith
      positivity
    nlinarith
  let hp : ℝ → ℝ := fun η => (1 - η + η * q) * ((1 - (2 - q) * η) * q * v - c * (1 - η)) - q * P * (1 - η)
  have h0 : 0 < hp 0 := by
    simp only [hp]; nlinarith
  have h1 : hp 1 < 0 := by
    simp only [hp]
    have : 0 < q * q * v * (1 - q) := by
      have : 0 < 1 - q := by linarith
      positivity
    nlinarith
  have hcont : ContinuousOn hp (Set.Icc 0 1) := by
    simp only [hp]; fun_prop
  obtain ⟨ηL, ⟨hL0, hL1⟩, hLeq⟩ := intermediate_value_Ioo' zero_le_one hcont ⟨h1, h0⟩
  have hroot : piL q v c ηL = q * P := by
    have hm := piL_mul q v c ηL hL1
    have hne : (1 - ηL) ≠ 0 := by linarith
    simp only [hp] at hLeq
    have : (piL q v c ηL - q * P) * (1 - ηL) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hne
  refine ⟨ηL, hL0, hL1, hroot, ?_, ?_⟩
  · intro η hη0 hη1 heq
    rcases lt_trichotomy η ηL with h | h | h
    · have := piL_anti q v c η ηL hq0 hq1 hv hA h hL1
      linarith
    · exact h
    · have := piL_anti q v c ηL η hq0 hq1 hv hA h hη1
      linarith
  · intro η hη0 hlt
    unfold PrefersBan banProfit
    have := piL_anti q v c η ηL hq0 hq1 hv hA hlt hL1
    exact lt_max_of_lt_right (by linarith)

lemma part_iii {v c : ℝ} (hc : 0 < c) (hcv : c < v) (P : ℝ) (hP0 : 0 < P) (hPv : P < v - c) :
    ∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q < 1 →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1 → PrefersBan q v c η P := by
  have hv : 0 < v := by linarith
  have hvc : 0 < v - c := by linarith
  set r := P / (v - c) with hr
  have hr0 : 0 < r := div_pos hP0 hvc
  have hr1 : r < 1 := (div_lt_one hvc).mpr hPv
  have hpos : 0 < (v - c - P) * (1 - r) / v := div_pos (mul_pos (by linarith) (by linarith)) hv
  refine ⟨max 0 (1 - (v - c - P) * (1 - r) / v), max_lt (by norm_num) (by linarith), ?_⟩
  intro q hq hq1 η hη0 hη1
  have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hq' : 1 - (v - c - P) * (1 - r) / v < q := lt_of_le_of_lt (le_max_right _ _) hq
  by_cases hrη : r < η
  · exact part_i hcv P q η hq0 hrη
  · rw [not_lt] at hrη
    have hη1' : η < 1 := lt_of_le_of_lt hrη hr1
    have hs1 : (0 : ℝ) < 1 - η := by linarith
    have hR1 : (0 : ℝ) < 1 - r := by linarith
    set s := η / (1 - η) with hs
    set R := r / (1 - r) with hRdef
    have hs0 : 0 ≤ s := div_nonneg hη0 hs1.le
    have hsR : s ≤ R := by
      rw [hs, hRdef, div_le_div_iff₀ hs1 hR1]; nlinarith
    have hR : R * (1 - r) = r := by rw [hRdef]; field_simp
    have hq2 : (1 - q) * v < (v - c - P) * (1 - r) := by
      have : 1 - q < (v - c - P) * (1 - r) / v := by linarith
      rwa [lt_div_iff₀ hv] at this
    have e : ((1 - q) * v * (1 + R)) * (1 - r) = (1 - q) * v := by
      rw [show ((1 - q) * v * (1 + R)) * (1 - r) = (1 - q) * v * (1 - r) + (1 - q) * v * (R * (1 - r))
        by ring, hR]
      ring
    have hkey : (1 - q) * v * (1 + R) < v - c - P := by
      have : ((1 - q) * v * (1 + R)) * (1 - r) < (v - c - P) * (1 - r) := by rw [e]; exact hq2
      exact lt_of_mul_lt_mul_right this hR1.le
    have hqs : q * s ≤ R := by nlinarith
    have hm : (1 - q) * v * (q * s) ≤ (1 - q) * v * R :=
      mul_le_mul_of_nonneg_left hqs (mul_nonneg (by linarith) hv.le)
    set I := q * v - c - (1 - q) * q * v * s with hI
    have hIP : P < I := by
      rw [hI]
      have : (1 - q) * q * v * s = (1 - q) * v * (q * s) := by ring
      nlinarith
    have hF : q ≤ 1 - (1 - q) * η := by nlinarith
    have hpl : piL q v c η = (1 - (1 - q) * η) * I := piL_s q v c η hη1'
    have h3 : q * P < q * I := mul_lt_mul_of_pos_left hIP hq0
    have h4 : q * I ≤ (1 - (1 - q) * η) * I := mul_le_mul_of_nonneg_right hF (by linarith)
    unfold PrefersBan banProfit
    exact lt_max_of_lt_right (by rw [hpl]; linarith)

lemma part_iv {v c : ℝ} (hc : 0 < c) (hcv : c < v) (q η : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ((0 < η ∨ c < q * v) →
        ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
          PrefersBan q v c η (piStarUniform v c μ)) ∧
      (η < 1 →
        ∃ μ₁ : ℝ, ∀ μ : ℝ, μ₁ < μ → PrefersAllow q v c η (piStarUniform v c μ)) := by
  have hvc : 0 < v - c := by linarith
  have hv : 0 < v := by linarith
  constructor
  · intro hor
    have hb : 0 < banProfit q v c η := by
      unfold banProfit
      by_cases hη : 0 < η
      · exact lt_max_of_lt_left (by unfold piH; positivity)
      · have : η = 0 := le_antisymm (not_lt.mp hη) hη0
        subst this
        have hcq : c < q * v := by
          rcases hor with h | h
          · exact absurd h (lt_irrefl 0)
          · exact h
        exact lt_max_of_lt_right (by rw [piL_zero]; linarith)
    set b := banProfit q v c η with hbdef
    refine ⟨min (v - c) (b / q), lt_min hvc (div_pos hb hq0), ?_⟩
    intro μ hμ0 hμ
    have hμ1 : μ ≤ v - c := le_of_lt (lt_of_lt_of_le hμ (min_le_left _ _))
    have hμ2 : μ < b / q := lt_of_lt_of_le hμ (min_le_right _ _)
    have hμq : μ * q < b := (lt_div_iff₀ hq0).mp hμ2
    unfold PrefersBan piStarUniform
    rw [if_pos hμ1, ← hbdef]
    have : 0 < μ * q := mul_pos hμ0 hq0
    nlinarith
  · intro hη1'
    have hs1 : (0 : ℝ) < 1 - η := by linarith
    have hqvc : 0 < q * (v - c) := mul_pos hq0 hvc
    have hH : piH q v c η < q * (v - c) := by
      unfold piH
      nlinarith
    have hL : piL q v c η < q * (v - c) := by
      rw [piL_s q v c η hη1']
      set s := η / (1 - η) with hs
      have hs0 : 0 ≤ s := div_nonneg hη0 hs1.le
      have hn : 0 ≤ (1 - q) * q * v * s := by
        have : 0 ≤ 1 - q := by linarith
        positivity
      have hF0 : 0 < 1 - (1 - q) * η := by nlinarith
      have hF1 : 1 - (1 - q) * η ≤ 1 := by nlinarith
      have hcq : q * v - c < q * (v - c) := by nlinarith
      set I := q * v - c - (1 - q) * q * v * s with hI
      rcases le_or_gt 0 I with hI0 | hI0
      · have : (1 - (1 - q) * η) * I ≤ I := by nlinarith
        linarith
      · have : (1 - (1 - q) * η) * I < 0 := mul_neg_of_pos_of_neg hF0 hI0
        linarith
    have hb : banProfit q v c η < q * (v - c) := by
      unfold banProfit; exact max_lt hH hL
    set b := banProfit q v c η with hbdef
    set g := q * (v - c) - b with hg
    have hg0 : 0 < g := by linarith
    refine ⟨max (v - c) (q * (v - c) ^ 2 / (2 * g)), ?_⟩
    intro μ hμ
    have h1 : v - c < μ := lt_of_le_of_lt (le_max_left _ _) hμ
    have h2 : q * (v - c) ^ 2 / (2 * g) < μ := lt_of_le_of_lt (le_max_right _ _) hμ
    have hμ0 : 0 < μ := by linarith
    have h3 : q * (v - c) ^ 2 < μ * (2 * g) := (div_lt_iff₀ (by linarith)).mp h2
    have h4 : q * (v - c) ^ 2 / (2 * μ) < g := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    unfold PrefersAllow piStarUniform
    rw [if_neg (not_le.mpr h1), ← hbdef]
    have e : q * ((v - c) * (1 - (v - c) / (2 * μ))) = q * (v - c) - q * (v - c) ^ 2 / (2 * μ) := by
      ring
    rw [e]; linarith

theorem main {v c : ℝ} (hc : 0 < c) (hcv : c < v) :
    (∀ P : ℝ, 0 < P → P < v - c →
      (∀ q η : ℝ, 0 < q → q < 1 → P / (v - c) < η → η ≤ 1 → PrefersBan q v c η P) ∧
      (∀ q : ℝ, 0 < q → q < 1 → c / (v - P) < q →
        ∃ ηL : ℝ, 0 < ηL ∧ ηL < 1 ∧ piL q v c ηL = q * P ∧
          (∀ η : ℝ, 0 ≤ η → η < 1 → piL q v c η = q * P → η = ηL) ∧
          ∀ η : ℝ, 0 ≤ η → η < ηL → PrefersBan q v c η P) ∧
      (∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q < 1 →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 → PrefersBan q v c η P)) ∧
    (∀ q η : ℝ, 0 < q → q < 1 → 0 ≤ η → η ≤ 1 →
      ((0 < η ∨ c < q * v) →
        ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
          PrefersBan q v c η (piStarUniform v c μ)) ∧
      (η < 1 →
        ∃ μ₁ : ℝ, ∀ μ : ℝ, μ₁ < μ → PrefersAllow q v c η (piStarUniform v c μ))) := by
  refine ⟨fun P hP0 hPv => ⟨?_, ?_, part_iii hc hcv P hP0 hPv⟩, ?_⟩
  · intro q η hq0 _ hη _
    exact part_i hcv P q η hq0 hη
  · intro q hq0 hq1 hqc
    exact part_ii hc hcv P hP0 hPv q hq0 hq1 hqc
  · intro q η hq0 hq1 hη0 hη1
    exact part_iv hc hcv q η hq0 hq1 hη0 hη1

end MLP3Ban

open MarketplaceLeakage.Communication in
theorem solution {v c : ℝ} (hc : 0 < c) (hcv : c < v) :
    (∀ P : ℝ, 0 < P → P < v - c →
      -- (i)
      (∀ q η : ℝ, 0 < q → q < 1 → P / (v - c) < η → η ≤ 1 → PrefersBan q v c η P) ∧
      -- (ii)
      (∀ q : ℝ, 0 < q → q < 1 → c / (v - P) < q →
        ∃ ηL : ℝ, 0 < ηL ∧ ηL < 1 ∧ piL q v c ηL = q * P ∧
          (∀ η : ℝ, 0 ≤ η → η < 1 → piL q v c η = q * P → η = ηL) ∧
          ∀ η : ℝ, 0 ≤ η → η < ηL → PrefersBan q v c η P) ∧
      -- (iii)
      (∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q < 1 →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 → PrefersBan q v c η P)) ∧
    -- (iv): uniform G, Π* = Π*(µ) of (6)
    (∀ q η : ℝ, 0 < q → q < 1 → 0 ≤ η → η ≤ 1 →
      ((0 < η ∨ c < q * v) →
        ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
          PrefersBan q v c η (piStarUniform v c μ)) ∧
      (η < 1 →
        ∃ μ₁ : ℝ, ∀ μ : ℝ, μ₁ < μ → PrefersAllow q v c η (piStarUniform v c μ))) := by
  exact MLP3Ban.main hc hcv
