-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovFiniteVectorLawLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:56:11.383183+00:00
-- url     : https://prove2.me/submissions/3f192974-751c-4b5a-b4f7-837a0c4fabe0

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Probability.ConditionalProbability
import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_compactTest_lintegral
import Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega I : Type} [MeasurableSpace Omega] [Fintype I]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : ℕ → Omega → (I → Real)) (Z : Omega → (I → Real))
    (hMeas : ∀ n, Measurable (Y n)) (hZ : Measurable Z)
    (hLaw : ∀ n, Measure.map (Y n) mu = Measure.map (Y 0) mu)
    (hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => Y n w) atTop (nhds (Z w))) :
    Measure.map Z mu = Measure.map (Y 0) mu := by
  classical
  apply AvramDividend.Classical.measure_eq_of_compactTest_lintegral
  intro f
  let k : (I → ℝ) → ℝ≥0∞ := fun z => (f z : ℝ≥0)
  have hk : Continuous k := ENNReal.continuous_coe.comp f.continuous
  let C : ℝ≥0∞ := ((nndist (0 : BoundedContinuousFunction (I → ℝ) ℝ≥0)
    f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞)
  obtain ⟨hb, hf⟩ := AvramDividend.Classical.compactTest_nnreal_uniformBound_finiteLintegral
    mu (measure_ne_top mu Set.univ) f
  have hlim : ∀ᵐ w ∂mu, Tendsto (fun n => k (Y n w)) atTop (nhds (k (Z w))) := by
    filter_upwards [hLimit] with w hw
    exact hk.continuousAt.tendsto.comp hw
  have ht := tendsto_lintegral_of_dominated_convergence (fun _ => C)
    (fun n => hk.measurable.comp (hMeas n))
    (fun n => Eventually.of_forall (fun w => hb (Y n w))) hf hlim
  have hconst : (fun n => ∫⁻ w, k (Y n w) ∂mu) =
      (fun _ : ℕ => ∫⁻ z, k z ∂Measure.map (Y 0) mu) := by
    funext n
    rw [← lintegral_map hk.measurable (hMeas n), hLaw n]
  change Tendsto (fun n => ∫⁻ w, k (Y n w) ∂mu) atTop (nhds (∫⁻ w, k (Z w) ∂mu)) at ht
  rw [hconst] at ht
  change (∫⁻ z, k z ∂Measure.map Z mu) = _
  rw [lintegral_map hk.measurable hZ]
  exact tendsto_nhds_unique ht tendsto_const_nhds
