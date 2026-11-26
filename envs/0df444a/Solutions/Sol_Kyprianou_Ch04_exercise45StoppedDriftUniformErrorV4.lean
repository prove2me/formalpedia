-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedDriftUniformErrorV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:35:18.944468+00:00
-- url     : https://prove2.me/submissions/f1f0d65a-8a85-4e0c-bdbc-d112fb1b5788

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45GridL1StepErrorV4
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedDriftSumIntegralV4
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, t ≤ T →
      |(∑ i ∈ Finset.range (n+1),
        H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
          ((min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)) : NNReal).toReal -
           (min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) : NNReal).toReal)) -
        (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal)| < δ := by
  intro δ hδ
  obtain ⟨hi,hH,hlim⟩ := Kyprianou.Ch04.exercise45GridL1StepErrorV4 T H C hb hl
  let u (n i : ℕ) := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
  let G (n : ℕ) (s : ℝ) := ∑ i ∈ Finset.range (n+1),
    (Ioc (u n i : ℝ) (u n (i+1) : ℝ)).indicator (fun _ => H (u n i)) s
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hlim δ hδ
  refine ⟨N,fun n hn t ht => ?_⟩
  rw [← Kyprianou.Ch04.exercise45StoppedDriftSumIntegralV4 T t n H,
    integral_Icc_eq_integral_Ioc]
  change |(∫ s in Ioc (0 : ℝ) (t : ℝ), G n s) -
    ∫ s in Ioc (0 : ℝ) (t : ℝ), H s.toNNReal| < δ
  have hsub : Ioc (0 : ℝ) (t : ℝ) ⊆ Ioc (0 : ℝ) (T : ℝ) :=
    Ioc_subset_Ioc_right (by exact_mod_cast ht)
  have hm := Measure.restrict_mono hsub le_rfl (μ := (volume : Measure ℝ))
  have hi' := (hi n).mono_measure hm
  have hH' := hH.mono_measure hm
  rw [← integral_sub hi' hH']
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) (t : ℝ), |G n s-H s.toNNReal| := abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioc (0 : ℝ) (T : ℝ), |G n s-H s.toNNReal| :=
      setIntegral_mono_set ((hi n).sub hH).abs
        (Eventually.of_forall fun _ => abs_nonneg _) (ae_of_all _ hsub)
    _ < δ := by
      have h := hN n hn
      rw [Real.dist_eq,sub_zero] at h
      exact (le_abs_self _).trans_lt h