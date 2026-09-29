-- Prove2me | solution 1 for GoldenRatioVI.Fixed.prox_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:23:30.260887+00:00
-- url     : https://prove2.me/submissions/a428f23e-df16-4f10-9186-88c8a1b7e538

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

open Filter Topology

namespace GoldenRatioVI.Fixed

lemma coe_toReal_of {x : EReal} (h1 : x ≠ ⊤) (h2 : x ≠ ⊥) : ((x.toReal : ℝ) : EReal) = x :=
  EReal.coe_toReal h1 h2

lemma real_limit_le {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

theorem prox_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (z xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g z xbar ↔
      ∀ x : E, ((inner ℝ (xbar - z) (x - xbar) : ℝ) : EReal) ≥ g xbar - g x := by
  obtain ⟨hbot, ⟨x0, hx0⟩, hconv, _⟩ := hg
  constructor
  · intro hprox
    -- g xbar is finite
    have hxbar : g xbar ≠ ⊤ := by
      intro htop
      have h := hprox x0
      rw [htop, EReal.top_add_coe] at h
      rw [← coe_toReal_of hx0 (hbot x0), ← EReal.coe_add] at h
      exact absurd h (not_le.2 (EReal.coe_lt_top _))
    set Gb := (g xbar).toReal with hGb
    have hgb : g xbar = (Gb : EReal) := (coe_toReal_of hxbar (hbot xbar)).symm
    intro x
    by_cases hx : g x = ⊤
    · rw [hx, hgb, EReal.sub_top]; exact bot_le
    set G := (g x).toReal with hG
    have hgx : g x = (G : EReal) := (coe_toReal_of hx (hbot x)).symm
    rw [hgb, hgx, ← EReal.coe_sub, ge_iff_le, EReal.coe_le_coe_iff]
    apply real_limit_le (C := ‖x - xbar‖ ^ 2 / 2)
    intro t ht0 ht1
    set xt := (1 - t) • xbar + t • x with hxt
    -- convexity
    have hmem1 : (xbar, Gb) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq]; rw [hgb]
    have hmem2 : (x, G) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq]; rw [hgx]
    have hc := hconv hmem1 hmem2 (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul] at hc
    -- prox at xt
    have hp := hprox xt
    rw [hgb] at hp
    have hp2 : ((Gb + ‖xbar - z‖ ^ 2 / 2 : ℝ) : EReal) ≤
        (((1 - t) * Gb + t * G + ‖xt - z‖ ^ 2 / 2 : ℝ) : EReal) := by
      rw [EReal.coe_add, EReal.coe_add]
      exact hp.trans (add_le_add hc le_rfl)
    rw [EReal.coe_le_coe_iff] at hp2
    have hexp : xt - z = (xbar - z) + t • (x - xbar) := by
      rw [hxt]; module
    rw [hexp, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
      abs_of_pos ht0] at hp2
    have key : t * (Gb - G) ≤ t * (inner ℝ (xbar - z) (x - xbar) + t * (‖x - xbar‖ ^ 2 / 2)) := by
      nlinarith
    exact le_of_mul_le_mul_left key ht0
  · intro h x
    have hxbar : g xbar ≠ ⊤ := by
      intro htop
      have h0 := h x0
      rw [htop, ← coe_toReal_of hx0 (hbot x0), EReal.top_sub_coe] at h0
      exact absurd h0 (not_le.2 (EReal.coe_lt_top _))
    set Gb := (g xbar).toReal with hGb
    have hgb : g xbar = (Gb : EReal) := (coe_toReal_of hxbar (hbot xbar)).symm
    by_cases hx : g x = ⊤
    · rw [hx, EReal.top_add_coe]; exact le_top
    set G := (g x).toReal with hG
    have hgx : g x = (G : EReal) := (coe_toReal_of hx (hbot x)).symm
    have hx' := h x
    rw [hgb, hgx, ← EReal.coe_sub, ge_iff_le, EReal.coe_le_coe_iff] at hx'
    rw [hgb, hgx, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hexp : x - z = (xbar - z) + (x - xbar) := by abel
    rw [hexp, norm_add_sq_real]
    nlinarith [sq_nonneg ‖x - xbar‖]

end GoldenRatioVI.Fixed

open GoldenRatioVI.Fixed

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (z xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g z xbar ↔
      ∀ x : E, ((inner ℝ (xbar - z) (x - xbar) : ℝ) : EReal) ≥ g xbar - g x := by
  exact prox_inequality g hg z xbar
