-- Prove2me | solution 1 for InterimTesting.NotProficient.lemma_A12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:27:48.964037+00:00
-- url     : https://prove2.me/submissions/4512ee30-cc89-46b6-a54b-0744353f4c1e

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

open InterimTesting.NotProficient

theorem solution (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) :
    ∃ μ1 : ℝ,
      (∀ μ ∈ Set.Ioo (0 : ℝ) 1,
        (H1 { θ with μ := μ } ≤ HI1 { θ with μ := μ } ↔ μ1 ≤ μ)) ∧
      (μ1 ≤ 1 → mu0 θ ≤ μ1) := by
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  set A := θ.A with hAdef
  set B := θ.B with hBdef
  set a := θ.φPP with hadef
  set b := θ.φPN with hbdef
  -- the polynomial whose sign is that of H1 - HI1
  set P : ℝ → ℝ := fun x => (A * (B * a + b * (1 - x * B)) + B * (1 + (1 - x) * B)) *
      (a * x * B + b * (1 - x * B)) - (B * a + b * (1 - x * B)) * (x * B) * (A + (1 + (1 - x) * B))
    with hPdef
  have hB1 : B ≤ 1 := by linarith
  have hD1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < B * a + b * (1 - x * B) := by
    intro x hx
    have : x * B < 1 := by nlinarith [hx.1, hx.2]
    have : 0 < b * (1 - x * B) := mul_pos hb0 (by linarith)
    have : 0 ≤ B * a := mul_nonneg hB0 (by linarith)
    linarith
  have key1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      (H1 { θ with μ := x } ≤ HI1 { θ with μ := x } ↔ P x ≤ 0) := by
    intro x hx
    have hd := hD1 x hx
    have e : H1 { θ with μ := x } - HI1 { θ with μ := x } = P x / (A * (B * a + b * (1 - x * B))) := by
      simp only [H1, HI1, hPdef]
      rw [← hAdef, ← hBdef, ← hadef, ← hbdef]
      generalize B * a + b * (1 - x * B) = D at hd ⊢
      field_simp
      ring
    rw [← sub_nonpos, e, div_le_iff₀ (by positivity), zero_mul]
  -- decomposition P = D1 * L + Q
  have hdec : ∀ x, P x = (B * a + b * (1 - x * B)) * (A * (b * (1 - x * B) - x * B * (1 - a)))
      + B * b * ((1 + (1 - x) * B) * (1 - x)) * (1 - x * B) := by
    intro x; simp only [hPdef]; ring
  have key2 : ∀ x y, 0 < x → x < y → y < 1 → P x ≤ 0 → P y < 0 := by
    intro x y hx hxy hy hPx
    have hdx := hD1 x ⟨hx, by linarith⟩
    have hdy := hD1 y ⟨by linarith, hy⟩
    have hxB : x * B < 1 := by nlinarith
    have hyB : y * B < 1 := by nlinarith
    -- L strictly decreasing
    have hL : A * (b * (1 - y * B) - y * B * (1 - a)) < A * (b * (1 - x * B) - x * B * (1 - a)) := by
      have : 0 < (y - x) * B * (b + (1 - a)) := by
        have : 0 < b + (1 - a) := by linarith
        have : 0 < y - x := by linarith
        positivity
      nlinarith
    -- Q / D1 nonincreasing
    have hC : (1 + (1 - y) * B) * (1 - y) ≤ (1 + (1 - x) * B) * (1 - x) := by
      have h1 : 0 ≤ 1 - y := by linarith
      have h2 : (1 + (1 - y) * B) ≤ (1 + (1 - x) * B) := by nlinarith
      have h3 : 0 ≤ 1 + (1 - y) * B := by nlinarith
      nlinarith [mul_le_mul h2 (by linarith : 1 - y ≤ 1 - x) h1 (by nlinarith)]
    have hr : (1 - y * B) / (B * a + b * (1 - y * B)) ≤ (1 - x * B) / (B * a + b * (1 - x * B)) := by
      rw [div_le_div_iff₀ hdy hdx]
      have e : (1 - x * B) * (B * a + b * (1 - y * B)) - (1 - y * B) * (B * a + b * (1 - x * B))
          = (y - x) * B * (B * a) := by ring
      have : 0 ≤ (y - x) * B * (B * a) := by
        have : 0 ≤ y - x := by linarith
        have : 0 ≤ B * a := mul_nonneg hB0 (by linarith)
        positivity
      linarith
    have hCx0 : 0 ≤ (1 + (1 - x) * B) * (1 - x) := by
      have : 0 ≤ 1 + (1 - x) * B := by nlinarith
      exact mul_nonneg this (by linarith)
    have hCy0 : 0 ≤ (1 + (1 - y) * B) * (1 - y) := by
      have : 0 ≤ 1 + (1 - y) * B := by nlinarith
      exact mul_nonneg this (by linarith)
    have hBb : 0 ≤ B * b := mul_nonneg hB0 hb0.le
    have hq : B * b * ((1 + (1 - y) * B) * (1 - y)) * ((1 - y * B) / (B * a + b * (1 - y * B)))
        ≤ B * b * ((1 + (1 - x) * B) * (1 - x)) * ((1 - x * B) / (B * a + b * (1 - x * B))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hC hBb) hr
        (div_nonneg (by linarith) hdy.le) (mul_nonneg hBb hCx0)
    have ex : P x / (B * a + b * (1 - x * B)) = A * (b * (1 - x * B) - x * B * (1 - a))
        + B * b * ((1 + (1 - x) * B) * (1 - x)) * ((1 - x * B) / (B * a + b * (1 - x * B))) := by
      rw [hdec x, add_div, mul_div_cancel_left₀ _ hdx.ne', mul_div_assoc]
    have ey : P y / (B * a + b * (1 - y * B)) = A * (b * (1 - y * B) - y * B * (1 - a))
        + B * b * ((1 + (1 - y) * B) * (1 - y)) * ((1 - y * B) / (B * a + b * (1 - y * B))) := by
      rw [hdec y, add_div, mul_div_cancel_left₀ _ hdy.ne', mul_div_assoc]
    have hx0 : P x / (B * a + b * (1 - x * B)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hPx hdx.le
    have hy0 : P y / (B * a + b * (1 - y * B)) < 0 := by rw [ey]; rw [ex] at hx0; linarith
    have := (div_neg_iff.mp hy0)
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h1
  -- small μ: P > 0 when μ ≤ μ0(B)
  have key3 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≤ mu0 θ → 0 < P x := by
    intro x hx hxm
    have e2 : mu0 θ = (b - B * (1 - a)) / (B * b) := by
      unfold mu0; rw [← hBdef, ← hadef, ← hbdef]; field_simp
    rw [e2, le_div_iff₀ (by positivity)] at hxm
    have hd := hD1 x hx
    have hxB : x * B < 1 := by nlinarith [hx.1, hx.2]
    rw [hdec x]
    have hL : 0 ≤ A * (b * (1 - x * B) - x * B * (1 - a)) := by
      have : 0 ≤ b * (1 - x * B) - x * B * (1 - a) := by
        have : B * (1 - a) * (1 - x) ≥ 0 :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) (by linarith [hx.2])
        nlinarith
      exact mul_nonneg hA.le this
    have hQ : 0 < B * b * ((1 + (1 - x) * B) * (1 - x)) * (1 - x * B) := by
      have : 0 < 1 + (1 - x) * B := by nlinarith [hx.2]
      have : 0 < 1 - x := by linarith [hx.2]
      have : 0 < 1 - x * B := by linarith
      positivity
    have := mul_nonneg hd.le hL
    linarith
  have hPc : Continuous P := by simp only [hPdef]; fun_prop
  set S := {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ P x ≤ 0} with hSdef
  have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.1.le⟩
  by_cases hS : S.Nonempty
  · refine ⟨sInf S, fun μ hμ => ?_, fun _ => ?_⟩
    · rw [key1 μ hμ]
      constructor
      · intro h
        exact csInf_le hSbdd ⟨hμ, h⟩
      · intro h
        rcases eq_or_lt_of_le h with heq | hlt
        · by_contra hpos
          push Not at hpos
          have hev : ∀ᶠ y in nhds μ, 0 < P y := hPc.continuousAt.eventually (lt_mem_nhds hpos)
          obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
          obtain ⟨s, hs, hsl⟩ := exists_lt_of_csInf_lt hS (show sInf S < μ + δ by linarith)
          have hsge : μ ≤ s := heq ▸ csInf_le hSbdd hs
          have : 0 < P s := hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
          linarith [hs.2]
        · obtain ⟨s, hs, hsμ⟩ := exists_lt_of_csInf_lt hS hlt
          exact (key2 s μ hs.1.1 hsμ hμ.2 hs.2).le
    · apply le_csInf hS
      intro s hs
      by_contra hlt
      push Not at hlt
      have := key3 s hs.1 hlt.le
      linarith [hs.2]
  · refine ⟨2, fun μ hμ => ?_, fun h => by norm_num at h⟩
    rw [key1 μ hμ]
    constructor
    · intro h
      exact absurd ⟨μ, hμ, h⟩ hS
    · intro h
      linarith [hμ.2]
