-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_finite_cascade_block_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:32.213363+00:00
-- url     : https://prove2.me/submissions/549eefd3-971d-49c0-af5b-2f7c0e3c0eab

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
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_compact_block
import Theorems.Thm_OAI_InvariantIsing_continuous_cavityCanonicalLabel
import Theorems.Thm_OAI_InvariantIsing_continuous_cavitySynchronizedBlock
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_integral
import Theorems.Thm_OAI_IsingPerceptron_replicaLaw_integral_prefix

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCascadeBlock
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

theorem cavity_finite_cascade_block_average_oai {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (H : SpectralBlock m r →ᵇ ℝ) :
    (∫ x, H (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n,
        H (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hm : Measurable (fun x : JointArray => H
      (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))) :=
    H.continuous.measurable.comp
    ((continuous_cavitySynchronizedBlock _ _
      (continuous_cavityCanonicalLabel rho lam hrho hsum p)).measurable.comp
      (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block rho lam hrho hsum p q hq hq0 hq1]
  exact replicaLaw_integral_prefix (labeledCascadeLaw n b : Measure (LabeledTree n))
    (labeledLeafLaw n) (measurable_labeledLeafLaw n)
    (fun σ => H (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))
    (fun σ => by simpa only [Real.norm_eq_abs] using
      (H.norm_coe_le_norm (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)))

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_finite_cascade_block_average_oai := @OAI.InvariantIsing.cavity_finite_cascade_block_average_oai
