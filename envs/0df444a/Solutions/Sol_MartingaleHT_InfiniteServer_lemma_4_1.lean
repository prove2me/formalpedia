-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:33:14.294159+00:00
-- url     : https://prove2.me/submissions/a39c268b-3bd7-4d2a-b7d9-dd2314010676

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

theorem solution (g : ℝ → ℝ) (T ε M : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hg_meas : Measurable g) (hg_int : IntegrableOn g (Set.Icc 0 T))
    (hg : ∀ t ∈ Set.Icc 0 T, 0 ≤ g t ∧ g t ≤ ε + M * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Set.Icc 0 T, g t ≤ ε * Real.exp (M * t) := by
  intro t ht
  have hgt_int : Integrable (Set.indicator (Set.Icc 0 T) g) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg_int
  obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ → ℝ,
      Gt = fun t => ∫ s in (0 : ℝ)..t, Set.indicator (Set.Icc 0 T) g s := ⟨_, rfl⟩
  have hGc : Continuous Gt := by rw [hGt]; exact hgt_int.continuous_primitive 0
  have hind : ∀ x ∈ Set.Icc 0 T, Set.indicator (Set.Icc 0 T) g x = g x :=
    fun x hx => Set.indicator_of_mem hx g
  have hGeq : ∀ x ∈ Set.Icc 0 T, ∫ s in (0 : ℝ)..x, g s = Gt x := by
    intro x hx
    rw [hGt]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx.1] at hy
    exact (hind y ⟨hy.1, hy.2.trans hx.2⟩).symm
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, A = fun t => ε * t + M * ∫ s in (0 : ℝ)..t, Gt s := ⟨_, rfl⟩
  have hAd : ∀ x, HasDerivAt A (ε + M * Gt x) x := by
    intro x
    rw [hA]
    have h := ((hasDerivAt_id x).const_mul ε).add
      ((hGc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul M)
    exact h.congr_deriv (by ring)
  have hGA : ∀ x ∈ Set.Icc 0 T, Gt x ≤ A x := by
    intro x hx
    have hc : Continuous (fun s => ε + M * Gt s) := continuous_const.add (continuous_const.mul hGc)
    have h1 : Gt x ≤ ∫ s in (0 : ℝ)..x, (ε + M * Gt s) := by
      have e : Gt x = ∫ s in (0 : ℝ)..x, Set.indicator (Set.Icc 0 T) g s := by rw [hGt]
      rw [e]
      refine intervalIntegral.integral_mono_on (f := fun s => Set.indicator (Set.Icc 0 T) g s)
        (g := fun s => ε + M * Gt s) hx.1 (hgt_int.intervalIntegrable)
        (hc.intervalIntegrable _ _) ?_
      intro y hy
      have hyT : y ∈ Set.Icc 0 T := ⟨hy.1, hy.2.trans hx.2⟩
      show Set.indicator (Set.Icc 0 T) g y ≤ ε + M * Gt y
      rw [hind y hyT, ← hGeq y hyT]
      exact (hg y hyT).2
    have h2 : ∫ s in (0 : ℝ)..x, (ε + M * Gt s) = A x := by
      have hc0 : Continuous (fun _ : ℝ => ε) := continuous_const
      have hc2 : Continuous (fun s => M * Gt s) := continuous_const.mul hGc
      rw [intervalIntegral.integral_add (hc0.intervalIntegrable 0 x)
        (hc2.intervalIntegrable 0 x), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero, hA, mul_comm x ε]
    linarith
  have hgb := le_gronwallBound_of_liminf_deriv_right_le (f := A)
    (f' := fun x => ε + M * Gt x) (δ := 0) (K := M) (ε := ε) (a := 0) (b := T)
    (fun x _ => (hAd x).continuousAt.continuousWithinAt)
    (fun x _ r hr => ((hAd x).hasDerivWithinAt.liminf_right_slope_le hr).mono
      (fun z hz => by simpa only [slope_def_module, smul_eq_mul] using hz))
    (by rw [hA]; simp)
    (fun x hx => by
      have := mul_le_mul_of_nonneg_left (hGA x (Set.Ico_subset_Icc_self hx)) hM.le
      linarith) t ht
  rw [gronwallBound_of_K_ne_0 hM.ne'] at hgb
  simp only [sub_zero, zero_mul, zero_add] at hgb
  have h3 := mul_le_mul_of_nonneg_left hgb hM.le
  have h4 : M * (ε / M * (Real.exp (M * t) - 1)) = ε * Real.exp (M * t) - ε := by
    rw [← mul_assoc, mul_div_cancel₀ ε hM.ne']; ring
  have h5 := (hg t ht).2
  rw [hGeq t ht] at h5
  have h6 := mul_le_mul_of_nonneg_left (hGA t ht) hM.le
  linarith
