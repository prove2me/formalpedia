-- Prove2me | solution 1 for MarkovChainCLT.rhoMixingCoef_comp_nonneg_le_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T16:00:33.294561+00:00
-- url     : https://prove2.me/submissions/008f09fa-2dcb-4736-8128-9e0697917478

import Theorems.Thm_MarkovChainCLT_processSigma_comp_le
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

/-- Cauchy–Schwarz for the covariance: `|cov[U,V]| ≤ √Var[U] · √Var[V]`. -/
private theorem abs_cov_le_sqrt_mul_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (U V : Ω → ℝ)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) :
    |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by
  have hUc : MemLp (fun ω => U ω - P[U]) 2 P := hU.sub (memLp_const _)
  have hVc : MemLp (fun ω => V ω - P[V]) 2 P := hV.sub (memLp_const _)
  have h2 : ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) := by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; rfl
  have hUc' : MemLp (fun ω => U ω - P[U]) (ENNReal.ofReal (2:ℝ)) P := by rwa [h2]
  have hVc' : MemLp (fun ω => V ω - P[V]) (ENNReal.ofReal (2:ℝ)) P := by rwa [h2]
  -- Hölder with p = q = 2
  have hhol := integral_mul_norm_le_Lp_mul_Lq (μ := P)
    (Real.HolderConjugate.two_two) hUc' hVc'
  have hVarU : Var[U; P] = ∫ ω, (U ω - P[U]) ^ 2 ∂P :=
    variance_eq_integral hU.aestronglyMeasurable.aemeasurable
  have hVarV : Var[V; P] = ∫ ω, (V ω - P[V]) ^ 2 ∂P :=
    variance_eq_integral hV.aestronglyMeasurable.aemeasurable
  have habs : |cov[U, V; P]| ≤ ∫ ω, ‖U ω - P[U]‖ * ‖V ω - P[V]‖ ∂P := by
    rw [covariance]
    refine le_trans abs_integral_le_integral_abs (le_of_eq (integral_congr_ae ?_))
    filter_upwards with ω
    rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine le_trans habs (le_trans hhol (le_of_eq ?_))
  have hrw : ∀ W : Ω → ℝ, (∫ ω, ‖W ω‖ ^ (2:ℝ) ∂P) ^ (1 / (2:ℝ))
      = Real.sqrt (∫ ω, (W ω) ^ 2 ∂P) := by
    intro W
    have hpt : (fun ω => ‖W ω‖ ^ (2:ℝ)) = fun ω => (W ω) ^ 2 := by
      funext ω
      rw [Real.norm_eq_abs]
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    rw [hpt, Real.sqrt_eq_rpow]
  rw [hrw (fun ω => U ω - P[U]), hrw (fun ω => V ω - P[V]), hVarU, hVarV]

theorem solution {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (n : ℕ) :
    0 ≤ rhoMixingCoef P (fun i ω => g (Y i ω)) n ∧
      rhoMixingCoef P (fun i ω => g (Y i ω)) n ≤ rhoMixingCoef P Y n := by
  set Sg := {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma (fun i ω => g (Y i ω)) (Set.Iic k)] U ∧
      Measurable[processSigma (fun i ω => g (Y i ω)) (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} with hSg
  set SY := {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} with hSY
  have hsub : Sg ⊆ SY := by
    rintro r ⟨k, U, V, hU, hV, hUp, hVp, rfl⟩
    exact ⟨k, U, V, fun s hs => processSigma_comp_le Y g hg _ _ (hU hs),
      fun s hs => processSigma_comp_le Y g hg _ _ (hV hs), hUp, hVp, rfl⟩
  -- every candidate value lies in [0, 1] by Cauchy–Schwarz
  have hmem : ∀ r ∈ SY, (0:ℝ) ≤ r ∧ r ≤ 1 := by
    rintro r ⟨k, U, V, hU, hV, hUp, hVp, rfl⟩
    refine ⟨div_nonneg (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ?_⟩
    rcases eq_or_lt_of_le (mul_nonneg (Real.sqrt_nonneg (Var[U; P]))
      (Real.sqrt_nonneg (Var[V; P]))) with h | h
    · rw [← h, div_zero]; norm_num
    · rw [div_le_one h]
      exact abs_cov_le_sqrt_mul_sqrt P U V hUp hVp
  have hmemg : ∀ r ∈ Sg, (0:ℝ) ≤ r ∧ r ≤ 1 := fun r hr => hmem r (hsub hr)
  have hbddY : BddAbove SY := ⟨1, fun r hr => (hmem r hr).2⟩
  have hnonneg : ∀ S : Set ℝ, BddAbove S → (∀ r ∈ S, (0:ℝ) ≤ r) → (0:ℝ) ≤ sSup S := by
    intro S hb hpos
    rcases S.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
    · simp
    · exact le_trans (hpos r hr) (le_csSup hb hr)
  have hbddg : BddAbove Sg := hbddY.mono hsub
  refine ⟨hnonneg Sg hbddg (fun r hr => (hmemg r hr).1), ?_⟩
  rcases Sg.eq_empty_or_nonempty with h | hne
  · rw [show rhoMixingCoef P (fun i ω => g (Y i ω)) n = sSup Sg from rfl, h]
    rw [Real.sSup_empty]
    exact hnonneg SY hbddY (fun r hr => (hmem r hr).1)
  · exact csSup_le_csSup hbddY hne hsub
