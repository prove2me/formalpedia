-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_of_tendsto_eLpNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:03:32.509294+00:00
-- url     : https://prove2.me/submissions/e9cfd1c9-d87d-47ea-aae5-c8a378741cdd

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u}

theorem solution
    {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {ℱ : MeasureTheory.Filtration ℝ m0}
    {M : ℕ → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ}
    (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
    (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
    (hadapt : MeasureTheory.StronglyAdapted ℱ F)
    (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
    (htend : ∀ t, Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
    MeasureTheory.Martingale F ℱ μ := by
  have hlim (t : ℝ) (s : Set Ω) :=
    tendsto_setIntegral_of_L1' (F t) (hint t).aestronglyMeasurable
      (Eventually.of_forall (fun n => hMint n t)) (htend t) s
  refine ⟨hadapt, fun i j hij => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_of_ae_eq_trim
  apply ((hint i).trim (ℱ.le i) (hadapt i)).ae_eq_of_forall_setIntegral_eq _ _
    (integrable_condExp.trim (ℱ.le i) stronglyMeasurable_condExp)
  intro s hs _
  rw [← setIntegral_trim (ℱ.le i) (hadapt i) hs,
    ← setIntegral_trim (ℱ.le i) stronglyMeasurable_condExp hs,
    setIntegral_condExp (ℱ.le i) (hint j) hs]
  exact tendsto_nhds_unique (hlim i s)
    ((hlim j s).congr (fun n => ((hM n).setIntegral_eq hij hs).symm))

#print axioms solution
