-- Prove2me | solution 1 for MoreauProx.Characterization.conjugate_points_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:18:22.414684+00:00
-- url     : https://prove2.me/submissions/97e97ba7-b10e-463b-b7a1-8c6cedc83ca5

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero

open MoreauProx.Characterization
open scoped InnerProductSpace

private theorem conj_ne_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (y : H) : conj f y ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hf.2.1
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℝ, f x₀ = (r : EReal) :=
    ⟨(f x₀).toReal, (EReal.coe_toReal hx₀ (hf.1 x₀)).symm⟩
  have h0 : ((⟪x₀, y⟫_ℝ : ℝ) : EReal) - f x₀ ≤ conj f y :=
    le_iSup (fun x => ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x) x₀
  rw [hr₀, ← EReal.coe_sub] at h0
  intro h
  rw [h, le_bot_iff] at h0
  exact EReal.coe_ne_bot _ h0

/-- Fenchel–Young. -/
private theorem fy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (x y : H) :
    ((⟪x, y⟫_ℝ : ℝ) : EReal) ≤ f x + conj f y := by
  have hgb : conj f y ≠ ⊥ := conj_ne_bot f hf y
  rcases eq_or_ne (f x) ⊤ with hx | hx
  · rw [hx, EReal.top_add_of_ne_bot hgb]; exact le_top
  rcases eq_or_ne (conj f y) ⊤ with hgt | hgt
  · rw [hgt, EReal.add_top_of_ne_bot (hf.1 x)]; exact le_top
  obtain ⟨a, ha⟩ : ∃ r : ℝ, f x = (r : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal hx (hf.1 x)).symm⟩
  obtain ⟨b, hb⟩ : ∃ r : ℝ, conj f y = (r : EReal) :=
    ⟨(conj f y).toReal, (EReal.coe_toReal hgt hgb).symm⟩
  have hle : ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x ≤ conj f y :=
    le_iSup (fun u => ((⟪u, y⟫_ℝ : ℝ) : EReal) - f u) x
  rw [ha, hb, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hle
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- From a Fenchel equality both values are finite, with real parts summing to the pairing. -/
private theorem split {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y : H)
    (h : f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal)) :
    ∃ a b : ℝ, f x = (a : EReal) ∧ g y = (b : EReal) ∧ a + b = ⟪x, y⟫_ℝ := by
  have hgb : g y ≠ ⊥ := by rw [hg]; exact conj_ne_bot f hf y
  have hfb : f x ≠ ⊥ := hf.1 x
  have hxt : f x ≠ ⊤ := by
    intro hx
    rw [hx, EReal.top_add_of_ne_bot hgb] at h
    exact EReal.coe_ne_top _ h.symm
  have hyt : g y ≠ ⊤ := by
    intro hy
    rw [hy, EReal.add_top_of_ne_bot hfb] at h
    exact EReal.coe_ne_top _ h.symm
  obtain ⟨a, ha⟩ : ∃ r : ℝ, f x = (r : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal hxt hfb).symm⟩
  obtain ⟨b, hb⟩ : ∃ r : ℝ, g y = (r : EReal) :=
    ⟨(g y).toReal, (EReal.coe_toReal hyt hgb).symm⟩
  refine ⟨a, b, ha, hb, ?_⟩
  rw [ha, hb, ← EReal.coe_add] at h
  exact_mod_cast h

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y x' y' : H)
    (hxy : f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal))
    (hxy' : f x' + g y' = ((⟪x', y'⟫_ℝ : ℝ) : EReal)) :
    0 ≤ ⟪x - x', y - y'⟫_ℝ := by
  obtain ⟨a, b, ha, hb, hab⟩ := split f g hf hg x y hxy
  obtain ⟨a', b', ha', hb', hab'⟩ := split f g hf hg x' y' hxy'
  -- cross Fenchel–Young inequalities
  have h1 : ⟪x, y'⟫_ℝ ≤ a + b' := by
    have := fy f hf x y'
    rw [← hg, ha, hb', ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have h2 : ⟪x', y⟫_ℝ ≤ a' + b := by
    have := fy f hf x' y
    rw [← hg, ha', hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have hexp : ⟪x - x', y - y'⟫_ℝ
      = ⟪x, y⟫_ℝ - ⟪x, y'⟫_ℝ - ⟪x', y⟫_ℝ + ⟪x', y'⟫_ℝ := by
    simp [inner_sub_left, inner_sub_right]
    ring
  rw [hexp]
  linarith
