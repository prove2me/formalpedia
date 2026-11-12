-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_finite_compact_block
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:05.464399+00:00
-- url     : https://prove2.me/submissions/d61e554d-cf0b-49e4-8ffe-2067f45b48c8

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
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_spin

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCascadeBlock
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite spectral cascade block is the pushforward of the actual
labeled-tree replica law. This identifies bounded block averages without
adding a limiting-law assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_finite_compact_block_oai {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (σ : ℕ → LabeledLeaf n) :
    cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p)
      (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1
        (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ)))) =
      cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i) := by
  have ha : Monotone (fun i => q (cavityFiniteLevel n i)) :=
    hq.comp (cavityFiniteLevel_monotone n)
  have ha0 : 0 ≤ q (cavityFiniteLevel n 0) := by simpa [cavityFiniteLevel] using hq0
  have ha1 : q (cavityFiniteLevel n n) ≤ 1 := by
    simpa only [cavityFiniteLevel_last] using hq1
  ext i j a
  simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, arrayBlock,
    cascadeCompact_spin n ha ha0 ha1 σ, diagonalPatch, cascadeScalarArray, Fin.val_inj]
  split_ifs <;> rfl

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_finite_compact_block_oai := @OAI.InvariantIsing.cavity_finite_compact_block_oai
