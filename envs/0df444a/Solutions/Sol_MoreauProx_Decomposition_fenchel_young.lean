-- Prove2me | solution 1 for MoreauProx.Decomposition.fenchel_young
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:18:21.806755+00:00
-- url     : https://prove2.me/submissions/025cfd6a-afd6-475f-8451-c3e75c28285d

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

open MoreauProx.Decomposition
open scoped InnerProductSpace

/-- `conj f y` is never `-∞` when `f` is somewhere finite. -/
private theorem conj_ne_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (y : H) : conj f y ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hf.exists_ne_top
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℝ, f x₀ = (r : EReal) :=
    ⟨(f x₀).toReal, (EReal.coe_toReal hx₀ (hf.ne_bot x₀)).symm⟩
  have h0 : ((⟪x₀, y⟫_ℝ : ℝ) : EReal) - f x₀ ≤ conj f y :=
    le_iSup (fun x => ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x) x₀
  rw [hr₀, ← EReal.coe_sub] at h0
  intro h
  rw [h, le_bot_iff] at h0
  exact EReal.coe_ne_bot _ h0

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (x y : H) :
    ((⟪x, y⟫_ℝ : ℝ) : EReal) ≤ f x + conj f y := by
  have hgb : conj f y ≠ ⊥ := conj_ne_bot f hf y
  rcases eq_or_ne (f x) ⊤ with hx | hx
  · rw [hx, EReal.top_add_of_ne_bot hgb]; exact le_top
  rcases eq_or_ne (conj f y) ⊤ with hgt | hgt
  · rw [hgt, EReal.add_top_of_ne_bot (hf.ne_bot x)]; exact le_top
  obtain ⟨a, ha⟩ : ∃ r : ℝ, f x = (r : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal hx (hf.ne_bot x)).symm⟩
  obtain ⟨b, hb⟩ : ∃ r : ℝ, conj f y = (r : EReal) :=
    ⟨(conj f y).toReal, (EReal.coe_toReal hgt hgb).symm⟩
  have hle : ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x ≤ conj f y :=
    le_iSup (fun u => ((⟪u, y⟫_ℝ : ℝ) : EReal) - f u) x
  rw [ha, hb, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hle
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith
