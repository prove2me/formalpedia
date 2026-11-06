-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:48:35.706393+00:00
-- url     : https://prove2.me/submissions/c741e7f4-998e-4f33-bf1a-ea36399a94f9

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit
import Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion
open MartingaleHT.InfiniteServer

theorem solution (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    UocInProb P (fun n ω t (_ : Fin 1) => phiS n μ (Q n) ω t) (fun t _ => μ * t) := by
  have h43 := MartingaleHT.InfiniteServer.lemma_4_3 μ hμ P A S Q hsys ν h0
  intro T hT ε hε
  set ε' : ℝ := ε / (2 * (μ * T + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hlim := h43 T hT ε' hε'pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push_neg at hcon
  -- |Q/n - 1| < ε' on [0, T]
  have hb : ∀ s ∈ Set.Icc (0:ℝ) T, |(Q n ω s : ℝ) / n - 1| ≤ ε' := by
    intro s hs
    have h1 : ENNReal.ofReal (∑ i : Fin 1, |psiS n (Q n) ω s - (1 : ℝ)|)
        ≤ supDist (fun t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) T := by
      unfold supDist
      exact le_iSup₂_of_le (f := fun (s : ℝ) (_ : s ∈ Set.Icc 0 T) =>
        ENNReal.ofReal (∑ i : Fin 1, |psiS n (Q n) ω s - (1 : ℝ)|)) s hs le_rfl
    have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 (lt_of_le_of_lt h1 hcon)).1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, psiS] at h2
    exact h2.le
  have hbound : supDist (fun t (_ : Fin 1) => phiS n μ (Q n) ω t) (fun t _ => μ * t) T
      ≤ ENNReal.ofReal (μ * (ε' * T)) := by
    unfold supDist
    refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, phiS]
    have hI : IntervalIntegrable (fun s => (Q n ω s : ℝ)) volume 0 t :=
      (hsys n hn).integrable ω t ht.1
    have heq : (μ / n * ∫ s in (0:ℝ)..t, (Q n ω s : ℝ)) - μ * t =
        μ * ∫ s in (0:ℝ)..t, ((Q n ω s : ℝ) / n - 1) := by
      rw [intervalIntegral.integral_sub (hI.div_const _) intervalIntegrable_const,
        intervalIntegral.integral_div]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      field_simp
    rw [heq, abs_mul, abs_of_pos hμ]
    refine mul_le_mul_of_nonneg_left ?_ hμ.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => (Q n ω s : ℝ) / n - 1) (a := 0) (b := t) (C := ε') (fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        rw [Real.norm_eq_abs]
        exact hb s ⟨hs.1.le, le_trans hs.2 ht.2⟩)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
    exact le_trans this (mul_le_mul_of_nonneg_left ht.2 hε'pos.le)
  have hlt : ENNReal.ofReal (μ * (ε' * T)) < ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_lt_ofReal_iff hε, hε']
    rw [show μ * (ε / (2 * (μ * T + 1)) * T) = ε * (μ * T) / (2 * (μ * T + 1)) by ring,
      div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hμ.le hT]
  exact absurd hω (not_le.2 (lt_of_le_of_lt hbound hlt))
