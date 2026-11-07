-- Prove2me | solution 1 for GlynnSTS.Length.proposition_4_1_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:36:29.994681+00:00
-- url     : https://prove2.me/submissions/ec6c458b-217f-4ff2-8465-327bf1b60470

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Theorems.Thm_GlynnSTS_Length_display_4_2

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (hg0 : ∀ x, 0 ≤ g x)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : GlynnSTS.Length.Assumption21 P Y Ybar μ σ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (α β : ℝ) (hαβ : GlynnSTS.Length.H P B g β - GlynnSTS.Length.H P B g α = 1 - δ) :
    ENNReal.ofReal (σ * (β - α)) *
      (∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P) ≤
        liminf (fun n : ℕ => ENNReal.ofReal (Real.sqrt n) *
          ∫⁻ ω, ENNReal.ofReal (GlynnSTS.Length.Ln g Ybar α β n ω) ∂P) atTop := by
  have hσ : 0 < σ := h21.sigma_pos
  set c := β - α with hc
  rcases le_or_gt c 0 with hc0 | hc0
  · have : ENNReal.ofReal (σ * c) = 0 :=
      ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos hσ.le hc0)
    rw [this, zero_mul]; exact bot_le
  have h42 := GlynnSTS.Length.display_4_2 P B hB g hg Y Ybar μ σ h21
  -- the continuous nonnegative test function
  let f : ℝ → ℝ := fun x => max (c * x) 0
  have hf_cont : Continuous f := (continuous_const.mul continuous_id).max continuous_const
  have hf_nn : 0 ≤ f := fun x => le_max_right _ _
  have hofmax : ∀ t : ℝ, ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
    intro t
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right ht, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos ht]
    · rw [max_eq_left ht]
  have key := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := P.map (fun ω => σ * g (B ω)))
    (μs := fun n => P.map (fun ω => g (GlynnSTS.Limit.Xn Ybar μ n ω))) hf_cont hf_nn
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto h42.tendsto hG)
  have hfm : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf_cont.measurable
  rw [lintegral_map' hfm.aemeasurable h42.aemeasurable_limit] at key
  have hL : ∫⁻ ω, ENNReal.ofReal (f (σ * g (B ω))) ∂P =
      ENNReal.ofReal (σ * c) * ∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun ω => ?_)
    simp only [f]
    rw [hofmax, ← ENNReal.ofReal_mul (by positivity)]; ring_nf
  rw [hL] at key
  refine key.trans (le_of_eq ?_)
  apply liminf_congr
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lintegral_map' hfm.aemeasurable (h42.forall_aemeasurable n),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun ω => ?_)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hX : g (GlynnSTS.Limit.Xn Ybar μ n ω) = Real.sqrt n * g (Ybar n ω) := by
    simp only [GlynnSTS.Limit.Xn]
    rw [hg.2.1 _ hsq, hg.2.2.1]
  simp only [f, GlynnSTS.Length.Ln]
  rw [hofmax, hX, ← ENNReal.ofReal_mul hsq.le, hc]; congr 1; ring
