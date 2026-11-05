-- Prove2me | solution 1 for GraphonMF.DenseLLN.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:51:32.134195+00:00
-- url     : https://prove2.me/submissions/ff798b8c-d29a-48aa-87dd-abc17488b718
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting
import Theorems.Thm_GraphonMF_DenseLLN_theorem_3_1_eq_3_3
import Theorems.Thm_GraphonMF_DenseLLN_lemma_6_1
import Theorems.Thm_GraphonMF_DenseLLN_remark_2_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open GraphonMF.DenseLLN

theorem solution {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (h31a : ∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n))
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (hξ : ∀ n, Measurable (ξ n))
    (h31b : Cond31b P X0 B ξ Gs)
    (h31c : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0))
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution noise b σ n (ξ n) (hξ n) (Xn n)) :
    TendstoInProb P (fun n ω => empiricalPM (fun i => Xn n i ω)) (mixturePM P X) ∧
      (Cond22b G J → Tendsto (fun n : ℕ => (1 / (n : ℝ≥0∞)) *
          ∑ i : Fin n, ∫⁻ ω, ‖Xn n i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) := by
  refine ⟨theorem_3_1_eq_3_3 noise hT b σ ε h21 J h22a G hG Gs h31a ξ hξ h31b h31c X hX Xn hXn,
    fun h22b => ?_⟩
  have hε : 0 < ε := h21.1
  obtain ⟨κ, hκ⟩ := lemma_6_1 noise hT b σ ε h21 J h22a G hG h22b X hX
  -- operator-norm convergence from cut-norm convergence (Remark 2.1)
  set Gs' : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ :=
    fun n => if n = 0 then G else Gs n with hGs'
  have hGs'g : ∀ n, GraphonMF.Stability.IsGraphon (Gs' n) := by
    intro n
    by_cases hn : n = 0
    · simp only [Gs', hn, if_true]; exact hG
    · simp only [Gs', hn, if_false]; exact (h31a n (Nat.pos_of_ne_zero hn)).1
  have hev : ∀ᶠ n in atTop, (fun u v => Gs' n u v - G u v) = (fun u v => Gs n u v - G u v) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : n ≠ 0 := by omega
    simp [Gs', this]
  have hcut' : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs' n u v - G u v))
      atTop (𝓝 0) := by
    refine h31c.congr' ?_
    filter_upwards [hev] with n hn
    rw [hn]
  have hop' := remark_2_1 G Gs' hG hGs'g hcut'
  have hop : Tendsto (fun n => GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v))
      atTop (𝓝 0) := by
    refine hop'.congr' ?_
    filter_upwards [hev] with n hn
    rw [hn]
  have hlimop : limsup (fun n => ENNReal.ofReal
      (GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v))) atTop = 0 := by
    have := (ENNReal.tendsto_ofReal hop)
    rw [ENNReal.ofReal_zero] at this
    exact this.limsup_eq
  set L : ℕ → ℝ≥0∞ := fun n : ℕ => (1 / (n : ℝ≥0∞)) *
      ∑ i : Fin n, ∫⁻ ω, ‖Xn n i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ 2 ∂P with hL
  have hM : ∀ M : ℝ, 0 < M → limsup L atTop ≤ ENNReal.ofReal (κ / M ^ ε) := by
    intro M hM
    obtain ⟨κM, hκM⟩ := hκ M hM
    have := hκM Gs ξ hξ Xn h31a h31b hXn
    rw [hlimop, mul_zero, zero_add] at this
    exact this
  have htend : Tendsto (fun M : ℝ => ENNReal.ofReal (κ / M ^ ε)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => κ * M ^ (-ε)) atTop (𝓝 (κ * 0)) :=
      (tendsto_rpow_neg_atTop hε).const_mul κ
    rw [mul_zero] at h1
    have h2 : Tendsto (fun M : ℝ => κ / M ^ ε) atTop (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with M hM
      rw [Real.rpow_neg hM.le, div_eq_mul_inv]
    have := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at this
  have hle : limsup L atTop ≤ 0 :=
    ge_of_tendsto htend ((eventually_gt_atTop 0).mono fun M hM0 => hM M hM0)
  refine tendsto_order.2 ⟨fun a ha => absurd ha (ENNReal.not_lt_zero), fun a ha => ?_⟩
  exact eventually_lt_of_limsup_lt (hle.trans_lt ha)
