-- Prove2me | solution 1 for OAI.InvariantIsing.spectral_clip_empirical_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:18:05.345205+00:00
-- url     : https://prove2.me/submissions/dcbfcec3-e545-4a35-ba11-03544025c7f0

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258002

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_EmpiricalSpectralLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The empirical spectral probability measure and its finite-set masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace InvariantIsing

lemma empiricalSpectralLaw_map {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map f (empiricalSpectralLaw hN eig : Measure ℝ)=
      (empiricalSpectralLaw hN (fun i => f (eig i)) : Measure ℝ) := by
  change Measure.map f (finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) eig)=
    finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) (fun i => f (eig i))
  unfold finiteSpectralMeasure
  rw [Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul,Measure.map_dirac]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping the finite spectra to the limiting support interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma spectralClip_eq {a b x : ℝ} (hx : x∈Icc a b) : spectralClip a b x=x := by
  simp only [spectralClip,min_eq_right hx.2,max_eq_right hx.1]

lemma spectral_clip_empirical_tendsto_oai
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k)
      (fun i => spectralClip a b (eig (k+1) i))) atTop (𝓝 ν) := by
  have he : ν.map (f := (spectralClip a b)) (by first | (apply Continuous.aemeasurable; apply continuous_spectralClip <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)=ν := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    have h : spectralClip a b =ᵐ[(ν : Measure ℝ)] id := by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact spectralClip_eq (hbound hx)
    rw [Measure.map_congr h,Measure.map_id]
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hweak
    (continuous_spectralClip a b)
  rw [he] at hh
  apply hh.congr
  intro k
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map _ _ _ (continuous_spectralClip a b).measurable

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spectral_clip_empirical_tendsto_oai := @OAI.InvariantIsing.spectral_clip_empirical_tendsto_oai
