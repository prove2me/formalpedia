-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_original_overlap_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:38.138662+00:00
-- url     : https://prove2.me/submissions/b8529302-29fa-4261-bc06-6a4c6a0493c8

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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_full_tree_cutoff_sequence
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_finite_cutoff_comparison
import Theorems.Thm_OAI_InvariantIsing_cavity_original_restricted_haar_limit_family
import Theorems.Thm_OAI_InvariantIsing_cavity_strict_finite_overlap_test

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma referenceReplicaMean_eq_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D =
      (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
      (∫ σ, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν)) := by
  rw [reference_replica_partition]; rfl

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron



lemma abs_bounded_gibbs_test_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H D : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ x, |D x| ≤ c) :
    |(∫ x, Real.exp (H x)*D x ∂ν)/(∫ x, Real.exp (H x) ∂ν)| ≤ c := by
  have hi := he.mul_bdd hmD.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hD x))
  have hb : |∫ x, Real.exp (H x)*D x ∂ν| ≤ c*(∫ x, Real.exp (H x) ∂ν) := by
    calc
      _ ≤ ∫ x, |Real.exp (H x)*D x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, c*Real.exp (H x) ∂ν := by
        apply integral_mono hi.abs (he.const_mul c)
        intro x
        dsimp only
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        nlinarith [mul_le_mul_of_nonneg_left (hD x) (Real.exp_pos (H x)).le]
      _ = _ := integral_const_mul _ _
  have hz : 0 ≤ ∫ x, Real.exp (H x) ∂ν := integral_nonneg (fun _ => (Real.exp_pos _).le)
  rcases hz.eq_or_lt with hz | hz
  · simp only [← hz,div_zero,abs_zero]
    exact hc
  · rw [abs_div,abs_of_pos hz]
    exact (div_le_iff₀ hz).mpr hb



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma measurable_countable_measure_pi {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] (r : ℕ) :
    Measurable (fun ω => Measure.pi (fun _ : Fin r => ν ω)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : Measure.pi (fun _ : Fin r => ν ω) s =
      ∑' σ : Fin r → X, (∏ i : Fin r, ν ω {σ i}) * Measure.dirac σ s := by
    rw [← Measure.sum_smul_dirac (Measure.pi (fun _ : Fin r => ν ω)),Measure.sum_apply _ hs]
    simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_singleton]
  simp_rw [he]
  apply Measurable.tsum
  intro σ
  exact (Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (measurableSet_singleton _)).comp hν)).mul_const _

lemma measurable_random_referenceReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) {r : ℕ}
    {D : Ω × (Fin r → X) → ℝ} (hD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  let κ : Kernel Ω (Fin r → X) := ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω),
    measurable_countable_measure_pi hν r⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω))
    infer_instance⟩
  have hm : Measurable (fun z : Ω × (Fin r → X) => Real.exp (∑ i, H (z.1,z.2 i))*D z) := by
    apply Measurable.mul _ hD
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun i _ => hH.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((measurable_random_referencePartition hν hH).pow_const r)

lemma referenceReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    |referenceReplicaMean ν H D| ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))) (Measure.pi (fun _ => ν))
  · exact abs_bounded_gibbs_test_le he hmD hc hD
  · rw [integral_undef he,div_zero,abs_zero]
    exact hc

lemma abs_integral_le_const_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : |∫ ω, F ω ∂μ| ≤ c := by
  calc
    _ ≤ ∫ ω, |F ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂μ := integral_mono ((integrable_of_measurable_abs_le hF hbound).abs)
      (integrable_const _) hbound
    _ = c := by simp

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := _root_.MeasureTheory.integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma referenceReplicaMean_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) (c : ℝ) :
    referenceReplicaMean ν H (fun σ => c*D σ) = c*referenceReplicaMean ν H D := by
  unfold referenceReplicaMean
  rw [show (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*(c*D σ)) =
    (fun σ => c*(Real.exp (∑ i, H (σ i))*D σ)) from by funext σ; ring,
    integral_const_mul]
  ring

end IsingPerceptron

namespace IsingPerceptron

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true, if_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_Overlaps
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap geometry

The finite projected overlaps are Gram matrices. Panchenko's ultrametricity
theorem applies to their limit arrays satisfying the Ghirlanda–Guerra identities.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Each spectral overlap component is a positive semidefinite Gram kernel. -/
lemma projectedOverlap_posSemidef {N m : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Fin m → Spin N) :
    Matrix.PosSemidef (fun i j => projectedOverlap U I (σ i) (σ j)) := by
  classical
  let A : Matrix (Fin m) (Fin N) ℝ := fun i k =>
    if k ∈ I then U (spinVector (σ i)) k else 0
  have hp := (Matrix.posSemidef_self_mul_conjTranspose A).smul
    (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
  have he : (fun i j : Fin m => projectedOverlap U I (σ i) (σ j)) =
      (N : ℝ)⁻¹ • (A * Aᴴ) := by
    ext i j
    change (N : ℝ)⁻¹ * (∑ k ∈ I, U (spinVector (σ i)) k * U (spinVector (σ j)) k) =
      (N : ℝ)⁻¹ * ∑ k, (if k ∈ I then U (spinVector (σ i)) k else 0) *
        (if k ∈ I then U (spinVector (σ j)) k else 0)
    congr 1
    simp only [ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self]
  rw [he]
  exact hp

/-- Full spectral overlap agrees with the ordinary spin overlap, because an
orthogonal rotation preserves the inner product. -/
lemma projectedOverlap_univ {N : ℕ} (U : Rotation N) (σ τ : Spin N) :
    projectedOverlap U Finset.univ σ τ =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  simp only [projectedOverlap]
  congr 1
  have h := U.inner_map_map (spinVector σ) (spinVector τ)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    spinVector_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma labeledCommonDepth_sum (n : ℕ) (x y : LabeledLeaf n) :
    (∑ d ∈ Finset.range n, if (labeledAddress n x).take (d+1) =
      (labeledAddress n y).take (d+1) then (1:ℝ) else 0) = labeledCommonDepth n x y := by
  have hc := labeledCommonDepth_le n x y
  calc
    _ = ∑ d ∈ Finset.range n, if d < labeledCommonDepth n x y then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [labeled_prefix_eq_iff n x y (d := d+1) (by have := Finset.mem_range.mp hd; omega), Nat.add_one_le_iff]
    _ = labeledCommonDepth n x y := by
      simp only [Finset.sum_boole]
      congr 1
      have he : (Finset.range n).filter (fun d => d < labeledCommonDepth n x y) =
          Finset.range (labeledCommonDepth n x y) := by
        ext d
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
      rw [he,Finset.card_range]

lemma treeOverlap_posSemidef (n : ℕ) {m : ℕ} (x : Fin m → LabeledLeaf n) :
    Matrix.PosSemidef (fun i j => treeOverlap n (x i) (x j)) := by
  classical
  let A : ℕ → Matrix (Fin m) (Fin m) ℝ := fun d =>
    Matrix.submatrix (1 : Matrix (List ChildLabel) (List ChildLabel) ℝ)
      (fun i => (labeledAddress n (x i)).take (d+1)) (fun i => (labeledAddress n (x i)).take (d+1))
  have hp (d : ℕ) : (A d).PosSemidef := Matrix.PosSemidef.one.submatrix _
  have hs := (Matrix.posSemidef_sum (Finset.range n) (fun d _ => hp d)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
  have he : (fun i j => treeOverlap n (x i) (x j)) =
      ((n+1:ℕ):ℝ)⁻¹ • (∑ d ∈ Finset.range n, A d) := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,A,Matrix.submatrix_apply,Matrix.one_apply]
    rw [labeledCommonDepth_sum]
    simp only [treeOverlap,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hs

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma measurable_cavityWeightNormalizer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) :
    Measurable (fun ω => cavityWeightNormalizer (ν ω) (fun x => w (ω, x))) := by
  let κ : Kernel Ω X := ⟨ν, hν⟩
  let : IsMarkovKernel κ := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  exact (hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma measurable_cavityWeightNumerator {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityWeightNumerator (ν ω) (fun x => w (ω, x)) (fun σ => F (ω, σ))) := by
  let κ : Kernel Ω (Fin r → X) :=
    ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω), measurable_probability_pi hν⟩
  let : IsMarkovKernel κ := ⟨fun ω =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω)))⟩
  have hm : Measurable (fun p : Ω × (Fin r → X) => (∏ i, w (p.1, p.2 i)) * F p) :=
    (Finset.measurable_prod _ fun i _ => hw.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul hF
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityWeightNormalizer_mem {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {a b : ℝ} (ha : 0 ≤ a) (hwb : ∀ x, w x ∈ Icc a b) :
    cavityWeightNormalizer ν w ∈ Icc a b := by
  have hi : Integrable w ν := Integrable.of_bound hw.aestronglyMeasurable b
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hwb x).1)]
      exact (hwb x).2)
  constructor
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const a) hi (fun x => (hwb x).1)
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const b) (fun x => (hwb x).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityNormalizerRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a denominator regularizer for bounded replica tests. Small
normalizers are isolated as a measurable exceptional event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityWeightNumerator_abs_le_normalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F) {M B : ℝ}
    (_hM : 0 ≤ M) (_hB : 0 ≤ B) (hwb : ∀ x, w x ∈ Icc 0 M)
    (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * cavityWeightNormalizer ν w ^ r := by
  let W := fun σ : Fin r → X => ∏ i, w (σ i)
  have hWM : Measurable W := Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)
  have hW0 σ : 0 ≤ W σ := Finset.prod_nonneg fun i _ => (hwb (σ i)).1
  have hWb σ : |W σ| ≤ M ^ r := by
    rw [abs_of_nonneg (hW0 σ)]
    exact (Finset.prod_le_prod (fun i _ => (hwb (σ i)).1)
      (fun i _ => (hwb (σ i)).2)).trans_eq (by simp)
  have hWI : Integrable W (Measure.pi (fun _ : Fin r => ν)) :=
    integrable_of_measurable_abs_le hWM hWb
  have hWFI : Integrable (fun σ => W σ * F σ) (Measure.pi (fun _ : Fin r => ν)) :=
    hWI.mul_bdd hF.aestronglyMeasurable (ae_of_all _ fun σ => by
      simpa only [Real.norm_eq_abs] using hFb σ)
  change |∫ σ, W σ * F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤ _
  calc
    _ ≤ ∫ σ, |W σ * F σ| ∂Measure.pi (fun _ : Fin r => ν) := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * W σ ∂Measure.pi (fun _ : Fin r => ν) := by
      apply integral_mono hWFI.abs (hWI.const_mul B)
      intro σ
      change |W σ * F σ| ≤ B * W σ
      rw [abs_mul, abs_of_nonneg (hW0 σ)]
      exact (mul_le_mul_of_nonneg_left (hFb σ) (hW0 σ)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [W, cavityWeightNormalizer, Fintype.card_fin] using
        integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) w

lemma cavity_normalized_numerator_bound {A Z B : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / Z ^ r| ≤ B := by
  rw [abs_div, abs_of_nonneg (pow_nonneg hZ r)]
  exact div_le_of_le_mul₀ (pow_nonneg hZ r) hB hA

lemma cavity_regularized_numerator_bound {A Z B δ : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / (Z + δ) ^ r| ≤ B := by
  apply cavity_normalized_numerator_bound (add_nonneg hZ hδ) hB r
  exact hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ (by linarith) r) hB)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eventual nondegeneracy of the Gaussian Gram matrix used to construct
fresh orthonormal directions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma cavity_posDef_of_posSemidef_det_ne_zero {q : ℕ}
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef) (hdet : G.det ≠ 0) :
    G.PosDef := by
  apply hG.1.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hprod : (∏ j, hG.1.eigenvalues j) ≠ 0 := by
    rw [hG.1.det_eq_prod_eigenvalues] at hdet
    exact hdet
  have hi : hG.1.eigenvalues i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hG.eigenvalues_nonneg i) hi.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_det_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : G.PosDef) : IsUnit (CFC.sqrt G).det := by
  apply isUnit_iff_ne_zero.mpr
  have he : (CFC.sqrt G).det * (CFC.sqrt G).det = G.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  intro hz
  rw [hz, zero_mul] at he
  exact hG.det_pos.ne' he.symm

theorem cavityNormalizeFrame_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hG : (A.transpose * A).PosDef) :
    (cavityNormalizeFrame A).transpose * cavityNormalizeFrame A = 1 := by
  let G : Matrix (Fin q) (Fin q) ℝ := A.transpose * A
  let S : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hs : S.transpose = S :=
    Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hss : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hu : IsUnit S.det := cavity_sqrt_det_isUnit G hG
  change (A * S⁻¹).transpose * (A * S⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs]
  calc
    S⁻¹ * A.transpose * (A * S⁻¹) = S⁻¹ * G * S⁻¹ := by
      simp only [G, Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hss]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv S hu]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameTransitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

lemma spectralJointEntry_spectral {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) (a : Fin m) :
    (spectralJointEntry U I n x y a.castSucc : ℝ) = projectedOverlap U (I a) x.1 y.1 := by
  simp only [spectralJointEntry, Fin.lastCases_castSucc]

lemma spectralJointEntry_tree {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) :
    (spectralJointEntry U I n x y (Fin.last m) : ℝ) = treeOverlap n x.2 y.2 := by
  simp only [spectralJointEntry, Fin.lastCases_last]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameMeasurable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the finite Gram normalization, including its
arbitrary singular-matrix values. -/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_matrix_inverse_measurable {q : ℕ} :
    Measurable (Inv.inv : Matrix (Fin q) (Fin q) ℝ → Matrix (Fin q) (Fin q) ℝ) := by
  have he (A : Matrix (Fin q) (Fin q) ℝ) : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp_rw [show (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) =
    (fun A => A.det⁻¹ • A.adjugate) from funext he]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

lemma measurable_cavityNormalizeFrame (n q : ℕ) :
    Measurable (cavityNormalizeFrame : Matrix (Fin n) (Fin q) ℝ → Matrix (Fin n) (Fin q) ℝ) := by
  have hg : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => A.transpose * A) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => ∑ k, A k i * A k j)
    exact Finset.measurable_sum _ (fun k _ =>
      (Matrix.measurable_apply (i := k) (j := i)).mul
        (Matrix.measurable_apply (i := k) (j := j)))
  have hs : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => CFC.sqrt (A.transpose * A)) :=
    CFC.measurable_sqrt.comp hg
  have hi : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
      (CFC.sqrt (A.transpose * A))⁻¹) := cavity_matrix_inverse_measurable.comp hs
  unfold cavityNormalizeFrame
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
    ∑ k, A i k * ((CFC.sqrt (A.transpose * A))⁻¹) k j)
  exact Finset.measurable_sum _ (fun k _ =>
    (Matrix.measurable_apply (i := i) (j := k)).mul (hi.eval_matrix))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous local choice of the special complement in the cavity
block: project a limiting frame and orthonormalize its columns. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityRawComplement_eq {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hEB : E.transpose * B₀ = 0) :
    cavityRawComplement E B₀ = B₀ := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hEB, Matrix.mul_zero, sub_zero]

lemma cavityComplement_gram {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ)
    (hG : ((cavityRawComplement E B₀).transpose * cavityRawComplement E B₀).PosDef) :
    (cavityComplement E B₀).transpose * cavityComplement E B₀ = 1 :=
  cavityNormalizeFrame_gram _ hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_scalar_identity {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) :
    CFC.sqrt (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) = Real.sqrt ρ • 1 := by
  apply CFC.sqrt_unique
    (hb := (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg ρ)).nonneg)
  rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt hρ]

theorem cavitySpectralStack_gram {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (cavitySpectralStack M).transpose * cavitySpectralStack M = ∑ a, M a := by
  ext i j
  change (∑ k : Fin (m * n),
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 i *
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (CFC.sqrt (M a)).transpose = CFC.sqrt (M a) :=
    Matrix.isHermitian_iff_isSymm.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M a))).isHermitian
  have he := CFC.sqrt_mul_sqrt_self (M a) (hM a).nonneg
  have he' : (CFC.sqrt (M a)).transpose * CFC.sqrt (M a) = M a := by
    rw [hs, he]
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) he'
  exact hentry

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special/cavity block matrix and its continuous limit. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

theorem cavityLimitingStack_gram {m n : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityLimitingStack (n := n) ρ =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have he : cavityLimitingStack (n := n) ρ =
      cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    ext i j
    simp only [cavityLimitingStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [he, cavitySpectralStack_gram _ (fun a => Matrix.PosSemidef.one.smul (hρ a)),
    ← Finset.sum_smul, hsum, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the limiting cavity columns by a fixed orthonormal special
frame. This is the reference frame for the continuous complement rule. -/

noncomputable section
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_frame_completion {d n : ℕ}
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ B : Matrix (Fin (d + n)) (Fin d) ℝ,
      B.transpose * B = 1 ∧ E.transpose * B = 0 := by
  let e := EuclideanSpace.basisFun (Fin (d + n)) ℝ
  have hr : Orthonormal ℝ (fun j : Fin n => e (Fin.natAdd d j)) :=
    e.orthonormal.comp _ (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive
    (fun j : Fin n => e (Fin.natAdd d j))
    (fun j : Fin n => WithLp.toLp 2 (fun i => E i j)) hr (cavity_orthonormal_of_gram E hE)
  let B : Matrix (Fin (d + n)) (Fin d) ℝ := fun i j => U (e (Fin.castAdd n j)) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    change (∑ k, U (e (Fin.castAdd n i)) k * U (e (Fin.castAdd n j)) k) =
      if i = j then 1 else 0
    have hh := U.inner_map_map (e (Fin.castAdd n i)) (e (Fin.castAdd n j))
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n i) (Fin.castAdd n j)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fin.castAdd_inj, mul_comm] using hh.trans he
  · ext i j
    change (∑ k, E k i * U (e (Fin.castAdd n j)) k) = 0
    have hh := U.inner_map_map (e (Fin.castAdd n j)) (e (Fin.natAdd d i))
    rw [hU i] at hh
    have hne : Fin.castAdd n j ≠ Fin.natAdd d i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n j) (Fin.natAdd d i)
    rw [ite_eq_right hne] at he
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply] using hh.trans he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global measurable completion of the cavity columns. The rule first
tries the prescribed limiting frame and otherwise uses a fixed dense
sequence. Near the limit it agrees with the continuous local rule. -/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Matrix Topology MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma continuous_cavityRawComplement {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) :
    Continuous (fun E : Matrix (Fin r) (Fin n) ℝ => cavityRawComplement E B) :=
  (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose)).matrix_mul
    continuous_const

lemma measurableSet_cavityGoodCandidate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (k : ℕ) :
    MeasurableSet {E | cavityGoodCandidate B₀ E k} := by
  have h := continuous_cavityRawComplement (n := n) (cavityComplementCandidate B₀ k)
  exact isOpen_lt continuous_const ((h.matrix_transpose.matrix_mul h).matrix_det) |>.measurableSet

lemma cavityGoodCandidate_exists {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ k, cavityGoodCandidate B₀ E k := by
  obtain ⟨B, hB, hEB⟩ := cavity_frame_completion E hE
  let s : Set (Matrix (Fin (d + n)) (Fin d) ℝ) :=
    {A | 0 < ((cavityRawComplement E A).transpose * cavityRawComplement E A).det}
  have hraw : Continuous (fun A : Matrix (Fin (d + n)) (Fin d) ℝ => cavityRawComplement E A) :=
    continuous_const.matrix_mul continuous_id
  have hs : IsOpen s := isOpen_lt continuous_const ((hraw.matrix_transpose.matrix_mul hraw).matrix_det)
  have hBmem : B ∈ s := by
    change 0 < ((cavityRawComplement E B).transpose * cavityRawComplement E B).det
    rw [cavityRawComplement_eq E B hEB, hB, Matrix.det_one]
    norm_num
  obtain ⟨k, hk⟩ := (denseRange_denseSeq (Fin (d + n) → Fin d → ℝ)).exists_mem_open hs ⟨B, hBmem⟩
  exact ⟨k + 1, hk⟩

lemma measurable_cavitySelectedComplement {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) : Measurable (cavitySelectedComplement B₀) := by
  classical
  refine Measurable.find (p := fun k E => cavityComplementChoicePredicate B₀ E k)
    (f := fun k E => cavityComplement E (cavityComplementCandidate B₀ (k - 1)))
    ?_ ?_ (cavityComplementChoice_exists B₀)
  · intro k
    exact (measurable_cavityNormalizeFrame _ _).comp
      (continuous_cavityRawComplement (cavityComplementCandidate B₀ (k - 1))).measurable
  · intro k
    by_cases hk : k = 0
    · subst k
      have he : {E | cavityComplementChoicePredicate B₀ E 0} =
          (⋃ j, {E | cavityGoodCandidate B₀ E j})ᶜ := by
        ext E
        simp [cavityComplementChoicePredicate]
      rw [he]
      exact (MeasurableSet.iUnion (fun j => measurableSet_cavityGoodCandidate B₀ j)).compl
    · simpa only [cavityComplementChoicePredicate, ite_eq_right hk] using
        measurableSet_cavityGoodCandidate B₀ (k - 1)

lemma cavitySelectedComplement_gram {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    (cavitySelectedComplement B₀ E).transpose * cavitySelectedComplement B₀ E = 1 := by
  classical
  have he := cavityGoodCandidate_exists B₀ E hE
  have hs := Nat.find_spec (cavityComplementChoice_exists B₀ E)
  have hn : Nat.find (cavityComplementChoice_exists B₀ E) ≠ 0 := by
    intro h
    simp only [cavityComplementChoicePredicate, h, ite_true, if_true] at hs
    exact hs he
  have hg : cavityGoodCandidate B₀ E (Nat.find (cavityComplementChoice_exists B₀ E) - 1) := by
    simpa only [cavityComplementChoicePredicate, ite_eq_right hn] using hs
  apply cavityComplement_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self
      (cavityRawComplement E (cavityComplementCandidate B₀
        (Nat.find (cavityComplementChoice_exists B₀ E) - 1)))
  · exact hg.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityEigenspaceFrame (r m n : ℕ) :
    Measurable (cavityEigenspaceFrame :
      (Fin m → Matrix (Fin r) (Fin n) ℝ) → Matrix (Fin r) (Fin (m * n)) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_cavityNormalizeFrame r n).comp
    (measurable_pi_apply (finProdFinEquiv.symm j).1)).eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralImage_gram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A a =
      A.transpose * Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) * A := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = a then A k j else 0)) =
    ∑ k : Fin r, (∑ t : Fin r,
      A t i * (if t = k then (if g t = a then (1 : ℝ) else 0) else 0)) * A k j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma measurable_cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m) (a : Fin m) :
    Measurable (fun A : Matrix (Fin r) (Fin n) ℝ => cavitySpectralImage g A a) := by
  apply Measurable.of_eval_matrix
  intro i j
  by_cases h : g i = a
  · simpa only [cavitySpectralImage, h, ite_true, if_true] using
      (Matrix.measurable_apply (i := i) (j := j))
  · simpa only [cavitySpectralImage, h, ite_false, if_false] using
      (measurable_const : Measurable (fun _ : Matrix (Fin r) (Fin n) ℝ => (0 : ℝ)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the cavity directions inside each spectral group. The added
columns are retained eigenvectors supported in the same group. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralProjectors_sum {r m : ℕ} (g : Fin r → Fin m) :
    (∑ a, Matrix.diagonal (fun i : Fin r => if g i = a then (1 : ℝ) else 0)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true, Matrix.one_apply_eq]
  · simp only [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij,
      Finset.sum_const_zero, Matrix.one_apply_ne hij]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalBase
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable base interaction built from the actual cavity columns. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityColumns (N n : ℕ) :
    Measurable (cavityColumns : Orthogonal (N + n) → Matrix (Fin (N + n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_apply (i := i) (j := Fin.natAdd N j)).comp measurable_subtype_coe

lemma measurable_cavityCompressionGrams {N n m : ℕ} (g : Fin (N + n) → Fin m) :
    Measurable (cavityCompressionGrams g) := by
  apply measurable_pi_iff.mpr
  intro a
  have hX := (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n)
  exact ((continuous_id.matrix_transpose.matrix_mul continuous_id).measurable).comp hX

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Haar compression limits for the actual measurable cavity block
construction. Only continuity at the prescribed limiting stack is used;
the completion rule need not be continuous on every frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n)) :
    Measurable (cavityReindexedStack e) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm (e.symm i)).1)
      (finProdFinEquiv.symm (e.symm i)).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm (e.symm i)).1)).eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full rank of the actual spectral compressions, with the eigenvalue
groups arranged in their given consecutive coordinate windows. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityColumns_gram {N n : ℕ} (U : Orthogonal (N + n)) :
    (cavityColumns U).transpose * cavityColumns U = 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin (N + n)) ℝ).mp U.property
  ext i j
  have h := congrArg (fun M : Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
    M (Fin.natAdd N i) (Fin.natAdd N j)) hU
  change (∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    k (Fin.natAdd N i) * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (Fin.natAdd N j)) = if i = j then 1 else 0
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.natAdd_inj] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable special frame used in the actual base interaction.
Its Gram and cavity-orthogonality identities hold for every input frame. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityCompressionGrams_sum {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : ∑ a, cavityCompressionGrams g U a = 1 := by
  unfold cavityCompressionGrams
  simp_rw [cavitySpectralImage_gram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, cavitySpectralProjectors_sum, Matrix.mul_one]
  exact cavityColumns_gram U

lemma measurable_cavityConcreteComplement {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n)) (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityConcreteComplement e B₀) := by
  have h := (measurable_cavitySelectedComplement B₀).comp (measurable_cavityReindexedStack e)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityReindexedStack_compression_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : Orthogonal (N + n)) :
    (cavityReindexedStack e (cavityCompressionGrams g U)).transpose *
      cavityReindexedStack e (cavityCompressionGrams g U) = 1 := by
  have hM : ∀ a, (cavityCompressionGrams g U a).PosSemidef := by
    intro a
    simpa only [cavityCompressionGrams, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (cavitySpectralImage g (cavityColumns U) a)
  have hs := cavitySpectralStack_gram (cavityCompressionGrams g U) hM
  rw [cavityCompressionGrams_sum g U] at hs
  ext i j
  change (∑ k : Fin (d + n),
    cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) i *
      cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) j) =
    (1 : Matrix (Fin n) (Fin n) ℝ) i j
  exact (Equiv.sum_comp e.symm (fun k =>
    cavitySpectralStack (cavityCompressionGrams g U) k i *
      cavitySpectralStack (cavityCompressionGrams g U) k j)).trans
        (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hs)

lemma cavityConcreteComplement_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    (cavityConcreteComplement e B₀ (cavityCompressionGrams g U)).transpose *
      cavityConcreteComplement e B₀ (cavityCompressionGrams g U) = 1 := by
  have h := cavitySelectedComplement_gram B₀ _ (cavityReindexedStack_compression_gram g e U)
  ext i j
  change (∑ k : Fin (m * n),
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) j) = _
  exact (Equiv.sum_comp e (fun k =>
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k j)).trans
        (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite Ising model with its actual spectral/tree tensor
perturbation has signed site-permutation symmetry after Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavityPerturbationField {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2) := by
  simp only [cavityPerturbationCoefficients, tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavityFullDisorderInner {N m depth : ℕ}
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2)
      (F p.1)) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
  let H : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) → ℝ :=
    fun z => rotatedEnergy eig (specialRotation z.1.1) z.2.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation z.1.1) I u depth z.2) z.1.2
  have hmH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
    exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) (F p.1))
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.1.1 z.2)
    hmH (hFm.comp (measurable_fst.fst.prodMk measurable_snd))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear combinations of bounded replica tests commute with
the normalized Gibbs average, including a zero denominator. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_referenceReplicaMean_sum {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ}
    (F : ι → (Fin r → X) → ℝ) (hF : ∀ i, Measurable (F i))
    (B : ι → ℝ) (hB : ∀ i σ, |F i σ| ≤ B i) :
    referenceReplicaMean ν H (fun σ => ∑ i, F i σ) =
      ∑ i, referenceReplicaMean ν H (F i) := by
  simp only [referenceReplicaMean_eq_ratio]
  by_cases hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ => ν))
  · have hip (i : ι) : Integrable
        (fun σ : Fin r → X => Real.exp (∑ j, H (σ j)) * F i σ)
        (Measure.pi (fun _ => ν)) := by
      apply (hi.mul_const (B i)).mono'
        ((hi.aestronglyMeasurable.mul (hF i).aestronglyMeasurable))
      exact ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hB i σ) (Real.exp_pos _).le
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => hip i), Finset.sum_div]
  · simp only [integral_undef hi, div_zero, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded disorder-dependent replica averages and finite sums. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_nested_disorder_replica_sum {Ω Ω' X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : ι → Ω → (Fin r → X) → ℝ) (hmF : ∀ i ω, Measurable (F i ω))
    (hmeas : ∀ i, Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F i z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i ω σ, |F i ω σ| ≤ B) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i ω σ) ∂P ∂μ) =
      ∑ i, ∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P ∂μ := by
  have hiG (ω : Ω) (i : ι) :
      Integrable (fun g => referenceReplicaMean ν (H ω g) (F i ω)) P :=
    integrable_of_measurable_abs_le ((hmeas i).comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i ω) (hmF i ω) hB (hF i ω))
  have he (ω : Ω) :
      (∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i ω σ) ∂P) =
        ∑ i, ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P := by
    simp_rw [cavity_referenceReplicaMean_sum ν _ (fun i => F i ω)
      (fun i => hmF i ω) (fun _ => B) (fun i => hF i ω)]
    exact integral_finsetSum _ (fun i _ => hiG ω i)
  have hiU (i : ι) : Integrable
      (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P) μ :=
    integrable_of_measurable_abs_le
      ((hmeas i).stronglyMeasurable.integral_prod_right'.measurable)
      (fun ω => abs_integral_le_const_of_bound ((hmeas i).comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i ω) (hmF i ω) hB (hF i ω)))
  simp_rw [he]
  exact integral_finsetSum _ (fun i _ => hiU i)

lemma cavity_nested_disorder_abs_le {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : Ω → (Fin r → X) → ℝ) (hmF : ∀ ω, Measurable (F ω))
    (hmeas : Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω σ, |F ω σ| ≤ B) :
    |∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P ∂μ| ≤ B := by
  apply abs_integral_le_const_of_bound hmeas.stronglyMeasurable.integral_prod_right'.measurable
  intro ω
  apply abs_integral_le_const_of_bound (hmeas.comp measurable_prodMk_left)
  intro g
  exact referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω)

lemma cavityFullDisorderTest_abs_le {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    |cavityFullDisorderTest μ T eig I u F| ≤ B := by
  exact cavity_nested_disorder_abs_le μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_cavityFullDisorderInner T eig I u F hFm) hB hF

lemma cavityFullDisorderTest_sum {N m depth : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : ∀ i, Measurable (Function.uncurry (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i U σ, |F i U σ| ≤ B) :
    cavityFullDisorderTest μ T eig I u (fun U σ => ∑ i, F i U σ) =
      ∑ i, cavityFullDisorderTest μ T eig I u (F i) := by
  exact cavity_nested_disorder_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ _ => measurable_of_countable _)
    (fun i => measurable_cavityFullDisorderInner T eig I u (F i) (hmF i)) hB hF

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω)
      (fun σ => F (ω, σ))) := by
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (measurable_referenceReplicaMean ν (H := H) hH
    (Measurable.ite hS hF measurable_const)).div
      (measurable_referenceReplicaMean ν (H := H) hH
        (Measurable.ite hS measurable_const measurable_const))

lemma cavity_cutoff_replica_eq_cond {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      ∫ σ, F σ ∂cond (Measure.pi (fun _ : Fin 2 => ν.tilted H))
        (univ.pi (fun _ => s)) := by
  let P := Measure.pi (fun _ : Fin 2 => ν.tilted H)
  let S := univ.pi (fun _ : Fin 2 => s)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hnum : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then F σ else 0) = S.indicator F := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  have hden : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then (1 : ℝ) else 0) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  rw [cavityCutoffReplicaMean, referenceReplicaMean_eq_tilted ν H hH,
    referenceReplicaMean_eq_tilted ν H hH, hnum, hden]
  change (∫ σ, S.indicator F σ ∂P) / (∫ σ, S.indicator (fun _ => (1 : ℝ)) σ ∂P) = _
  rw [integral_indicator hS, integral_indicator hS, integral_const]
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_inv, Measure.real, Measure.restrict_apply_univ, mul_one, div_eq_inv_mul]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A random cutoff changes bounded replica tests by its discarded
one-replica probability, after averaging over the common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F]
  have h := norm_integral_le_of_norm_le_const
    (μ := cond (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)))
    (f := F) (C := M) (ae_of_all _ (fun σ => by
      simpa only [Real.norm_eq_abs] using hF σ))
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hM measureReal_le_one)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTotalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cutoff is bounded also when its partition integral
is undefined: the existing zero convention then gives zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (s : Set X) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  by_cases hi : Integrable (fun x => Real.exp (H x)) ν
  · exact cavity_cutoff_replica_abs_le ν H hi s (Set.to_countable s).measurableSet F hM hF
  · have hz : referencePartition ν H = 0 := integral_undef hi
    simp only [cavityCutoffReplicaMean, referenceReplicaMean, hz, zero_pow (by decide : 2 ≠ 0),
      div_zero, abs_zero]
    exact hM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff control in the full perturbed model. The bad compression
event is paid for only by its probability, never by an inverse moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityFullDisorderTest_const_mul {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    cavityFullDisorderTest μ T eig I u (fun U σ => c * F U σ) =
      c * cavityFullDisorderTest μ T eig I u F := by
  simp only [cavityFullDisorderTest, referenceReplicaMean_const_mul, integral_const_mul]

lemma cavityFullDisorderTest_sub {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F G : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) (hmG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) (hG : ∀ U σ, |G U σ| ≤ B) :
    cavityFullDisorderTest μ T eig I u (fun U σ => F U σ - G U σ) =
      cavityFullDisorderTest μ T eig I u F - cavityFullDisorderTest μ T eig I u G := by
  let H : Fin 2 → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ :=
    ![F, fun U σ => (-1 : ℝ) * G U σ]
  have hmH : ∀ i, Measurable (Function.uncurry (H i)) := by
    intro i
    fin_cases i
    · exact hmF
    · exact hmG.const_mul (-1)
  have hH : ∀ i U σ, |H i U σ| ≤ B := by
    intro i U σ
    fin_cases i
    · exact hF U σ
    · change |(-1 : ℝ) * G U σ| ≤ B
      simpa only [neg_one_mul, abs_neg] using hG U σ
  have hs := cavityFullDisorderTest_sum μ T eig I u H hmH hB hH
  simp only [Fin.sum_univ_two] at hs
  change cavityFullDisorderTest μ T eig I u (fun U σ => F U σ + (-1 : ℝ) * G U σ) =
    cavityFullDisorderTest μ T eig I u F +
      cavityFullDisorderTest μ T eig I u (fun U σ => (-1 : ℝ) * G U σ) at hs
  rw [cavityFullDisorderTest_const_mul] at hs
  simpa only [neg_one_mul, sub_eq_add_neg] using hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-model cutoff estimate for the actual normalized spectral
image construction, with no inverse-Gram estimate on the bad event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityFullSpecialCoordinates {N n m d : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (σ : Spin (N + n)) :
    Measurable (fun U => cavityFullSpecialCoordinates g (B U) U σ) := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hA : Measurable (fun U : SpecialOrthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) :=
    measurable_pi_iff.mpr fun a => ((measurable_cavitySpectralImage g a).comp
      (measurable_cavityColumns N n)).comp hO
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hA
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hV := hmul.measurable.comp (hW.prodMk hB)
  have hz : Measurable (fun U : SpecialOrthogonal (N + n) =>
      ((cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun U : SpecialOrthogonal (N + n) => ∑ i : Fin (N + n),
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U) i j * specialRotation U (spinVector σ) i)
    apply Finset.measurable_sum
    intro i _
    exact hV.eval_matrix.mul (measurable_specialRotation_eval (spinVector σ) i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.measurable).comp hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded cutoff tests for the actual perturbed Ising law, with the
same Haar and Gaussian disorder in the full and restricted models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialPythagoras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special coordinates and the physical cavity spins exhaust the
normalized spectral-image coordinates. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_complement_projection_reindex {s d n : ℕ}
    (e : Fin s ≃ Fin (d + n))
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1)
    (hBT : B.transpose * T = 0) :
    B * B.transpose + T * T.transpose = 1 := by
  have hTB : T.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBT
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B T).transpose * Matrix.fromCols B T = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBT, hTB, hT,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    ((finSumFinEquiv : Fin d ⊕ Fin n ≃ Fin (d + n)).trans e.symm)).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalGroupAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical cavity frame admits the fresh-group Gibbs
representation. No new independent-frame assumption is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalGroupFrame_gram {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (a : Fin m) :
    (cavityCanonicalGroupFrame k e g hk a).transpose*cavityCanonicalGroupFrame k e g hk a=1 :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).1 a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionLimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The limiting frame extracted from the concrete compression has the
orthogonality and completeness used in the finite spectral cavity model. -/

noncomputable section
open Filter
open scoped Matrix Topology

namespace InvariantIsing

lemma cavitySpectralStack_scalar_eq {m n : ℕ} (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) :
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      cavityLimitingStack (n := n) ρ := by
  ext i j
  simp only [cavitySpectralStack, cavityLimitingStack,
    cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

lemma cavityCompressionLimitFrame_gram {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityCompressionLimitFrame e B₀ = 1 := by
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i * B₀ k j)
  exact he.trans (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB₀)

lemma cavityCompressionLimitFrame_perp {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityLimitingStack (n := n) ρ = 0 := by
  have ht := congrArg Matrix.transpose hEB
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
  rw [← cavitySpectralStack_scalar_eq ρ hρ]
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i *
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) (e.symm k) j)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, cavityCompressionLimitFrame,
    Equiv.symm_apply_apply, cavityReindexedStack, Matrix.zero_apply] using
      he.trans (congrArg (fun A : Matrix (Fin d) (Fin n) ℝ => A i j) ht)

theorem cavityCompressionLimitFrame_complete {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    cavityCompressionLimitFrame e B₀ * (cavityCompressionLimitFrame e B₀).transpose +
      cavityLimitingStack (n := n) ρ * (cavityLimitingStack (n := n) ρ).transpose = 1 :=
  cavity_complement_projection_reindex e _ _ (cavityCompressionLimitFrame_gram e B₀ hB₀)
    (cavityLimitingStack_gram ρ hρ hsum) (cavityCompressionLimitFrame_perp e B₀ ρ hρ hEB)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sequence of increasing cutoff radii can avoid every boundary
atom of a countable family of limiting replica laws. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace InvariantIsing

lemma cavity_radius_atoms_countable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (R : X → ℝ) (hR : Measurable R) :
    Set.Countable {B : ℝ | μ {x | R x=B} ≠ 0} := by
  have hm B : MeasurableSet {x | R x=B} := measurableSet_eq_fun hR measurable_const
  have hd : Pairwise (fun B C : ℝ => Disjoint {x | R x=B} {x | R x=C}) := by
    intro B C hBC
    exact Set.disjoint_left.mpr (fun x hx hy => hBC (hx.symm.trans hy))
  simpa only [pos_iff_ne_zero] using Measure.countable_meas_pos_of_disjoint_iUnion hm hd

theorem cavity_common_null_cutoff_radii {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, SFinite (μ n)]
    (R : (n : ℕ) → X n → ℝ) (hR : ∀ n, Measurable (R n)) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, (j : ℝ)+1 < B j ∧ B j < (j : ℝ)+2 ∧
        ∀ n, μ n {x | R n x=B j}=0 := by
  let S : Set ℝ := ⋃ n, {B : ℝ | μ n {x | R n x=B} ≠ 0}
  have hS : S.Countable := Set.countable_iUnion (fun n => cavity_radius_atoms_countable (μ n) (R n) (hR n))
  have hex (j : ℕ) : ∃ B ∈ Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2), B ∉ S := by
    have he := measure_sdiff_null (s := Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2)) (hS.measure_zero volume)
    have hp : 0 < volume (Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2) \ S) := by
      rw [he,Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨B,hB⟩ := nonempty_of_measure_ne_zero hp.ne'
    exact ⟨B,hB.1,hB.2⟩
  choose B hB hBS using hex
  refine ⟨B, ?_, fun j => ⟨(hB j).1,(hB j).2,?_⟩⟩
  · apply tendsto_atTop.mpr
    intro b
    obtain ⟨n,hn⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop n] with j hj
    have hnj : (n : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith [(hB j).1]
  · intro n
    by_contra hn
    exact hBS j (Set.mem_iUnion_of_mem n hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTightness
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the actual special-coordinate cutoff from bounded tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurableSet_cavitySpecialCutoff {N n m d depth : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (R : ℝ) :
    MeasurableSet {p : SpecialOrthogonal (N + n) × (Spin (N + n) × LabeledLeaf depth) |
      p.2 ∈ cavitySpecialCutoff g B R p.1} := by
  have hm : Measurable (fun p : SpecialOrthogonal (N + n) ×
      (Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B p.1) p.1 p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    exact measurable_cavityFullSpecialCoordinates g B hB x.1
  exact measurableSet_le hm.norm measurable_const

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary fourth moment bound after averaging over the original
Gibbs prior and the independent fresh Haar frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × X =>
      cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  dsimp only [cavitySelectedSiteProjection]
  apply Finset.measurable_sum
  intro l _
  exact (((measurable_pi_apply l).comp ((measurable_pi_apply (e j).1).comp
    ((hv x).comp measurable_fst))).mul
      (((measurable_pi_apply (e j).2).comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply (e j).1).comp
          ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRegularizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and boundedness of the regularized replica mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma measurable_cavityRegularizedReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) (δ : ℝ) :
    Measurable (fun ω => cavityRegularizedReplicaMean (ν ω)
      (fun x => w (ω,x)) (fun σ => F (ω,σ)) δ) :=
  (measurable_cavityWeightNumerator ν hν w hw F hF).div
    (((measurable_cavityWeightNormalizer ν hν w hw).add_const δ).pow_const r)

lemma cavityRegularizedReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F)
    {M B δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hwb : ∀ x, w x ∈ Icc 0 M) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityRegularizedReplicaMean ν w F δ| ≤ B :=
  cavity_regularized_numerator_bound
    (cavityWeightNormalizer_mem ν w hw le_rfl hwb).1 hB hδ r
    (cavityWeightNumerator_abs_le_normalizer ν w hw F hF hM hB hwb hFb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProductDisorderWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-disorder integration for normalized restricted weights and
the Gaussian/fresh-frame permutation used by the canonical cavity law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_bounded_disorder_shuffle {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (R : Measure C) [IsProbabilityMeasure R]
    (f : (A × B) × C → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂(P.prod Q).prod R) = ∫ a, ∫ c, ∫ b, f ((a,b),c) ∂Q ∂ R ∂P := by
  have hi := integrable_of_measurable_abs_le (μ := (P.prod Q).prod R) hf hb
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with a
  have hm : Measurable (fun p : B × C => f ((a,p.1),p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact integral_integral_swap (integrable_of_measurable_abs_le (μ := Q.prod R) hm
    (fun p => hb ((a,p.1),p.2)))

lemma cavity_bounded_disorder_dirac_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (b : B)
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R) =
      ∫ a, ∫ d, ∫ c, f (((a,b),c),d) ∂Q ∂ R ∂P := by
  rw [cavity_bounded_disorder_shuffle (P.prod (Measure.dirac b)) Q R f hf hb,
    Measure.prod_dirac]
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  exact integral_map_of_stronglyMeasurable measurable_prodMk_right
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiracAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the original random tree after proving an identity for
each fixed tree, while retaining the rotation and Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_bounded_dirac_average {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (S : Measure B) [IsProbabilityMeasure S]
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    (∫ b, ∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R ∂S) =
      ∫ p, f p ∂((P.prod S).prod Q).prod R := by
  let g := fun x : A × B => ∫ d, ∫ c, f ((x,c),d) ∂Q ∂ R
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hg : Measurable g :=
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  have hgb x : |g x| ≤ M := by
    apply abs_integral_le_const_of_bound
      ((hm.stronglyMeasurable.integral_prod_right'.measurable).comp measurable_prodMk_left)
    intro d
    exact abs_integral_le_const_of_bound (hm.comp measurable_prodMk_left)
      (fun c => hb ((x,c),d))
  have hgi := integrable_of_measurable_abs_le (μ := P.prod S) hg hgb
  simp_rw [cavity_bounded_disorder_dirac_shuffle P _ Q R f hf hb]
  rw [cavity_bounded_disorder_shuffle (P.prod S) Q R f hf hb, integral_prod _ hgi]
  exact (integral_integral_swap hgi).symm

lemma measurable_cavity_bounded_dirac_integral {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P]
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    Measurable (fun b => ∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R) := by
  simp_rw [cavity_bounded_disorder_dirac_shuffle P _ Q R f hf hb]
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hg : Measurable (fun x : A × B => ∫ d, ∫ c, f ((x,c),d) ∂Q ∂ R) :=
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  exact (hg.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature scaling of the actual quadratic cavity factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_radial_square_cutoff {α : Type*} (Y : α → ℝ) (hY : ∀ x, 0 ≤ Y x)
    {R : ℝ} (hR : 0 ≤ R) :
    {x | Y x ≤ R} = {x | 1+(Y x)^2 ≤ 1+R^2} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have hy := hY x
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hR hy)]
  · intro h
    nlinarith [hY x]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-spin geometric cutoff as a measurable bounded
function of its orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityOriginalGeometricMean {N n m d depth : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (T : LabeledTree depth) (eig : Fin (N+n) → ℝ)
    (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    Measurable (cavityOriginalGeometricMean g B T eig u D F) := by
  let X := Spin (N+n) × LabeledLeaf depth
  let I := cavitySpectralGroup g
  have hO : Measurable (cavitySpecialOrthogonal (N := N+n)) :=
    measurable_subtype_coe.subtype_mk
  have hBc := hB.comp ((measurable_cavityCompressionGrams g).comp hO)
  have hs : MeasurableSet {q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × X |
      cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1.1)))
        q.1.1 (cavitySpinSplit N n q.2.1) ≤ D} := by
    apply measurableSet_le _ measurable_const
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityFullSpecialCoordinates g _ hBc
      (cavityJoinedSpin (cavitySpinSplit N n x.1))).norm.pow_const 2).const_add 1 |>.comp
        measurable_fst
  have hH := measurable_cavityFullHamiltonian (N := N+n) (m := m) (depth := depth) eig I u
  have hF : Measurable (fun q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × (Fin 2 → X) =>
      F (fun i => (cavitySpinSplit N n (q.2 i).1,(q.2 i).2))) := by
    have hf : Measurable (fun σ : Fin 2 → X =>
        F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) := measurable_of_countable _
    exact hf.comp measurable_snd
  have hc := measurable_cavityCutoffReplicaMean
    (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
    (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) hH
    (fun q => {x | cavityGeometricWeight g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1))) q.1
        (cavitySpinSplit N n x.1) ≤ D}) hs _ hF
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

lemma cavityOriginalGeometricMean_bound {N n m d depth : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (U : SpecialOrthogonal (N+n)) :
    ‖cavityOriginalGeometricMean g B T eig u D F U‖ ≤ M := by
  have hb := fun z => cavity_cutoff_replica_abs_le_all
    (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) hM (fun σ => hF _)
  have ht := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
    (f := fun z => cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
      {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavitySpinSplit N n x.1) ≤ D}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))))
    (C := M) (ae_of_all gaussianCoordinates (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  simpa only [cavityOriginalGeometricMean, probReal_univ, mul_one] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame covariance is the physical projected overlap divided
by the finite spectral-group mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityPhysicalReplicaVectors_gram {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j =
      projectedOverlap U (I a) (σ i) (σ j) / ((d a : ℝ) / N) := by
  have hs : (∑ k, U (spinVector (σ i)) (e a k) * U (spinVector (σ j)) (e a k)) =
      ∑ k ∈ I a, U (spinVector (σ i)) k * U (spinVector (σ j)) k := by
    exact ((e a).sum_comp (fun k : ↥(I a) =>
      U (spinVector (σ i)) k * U (spinVector (σ j)) k)).trans
        ((I a).sum_coe_sort (fun k : Fin N => U (spinVector (σ i)) k * U (spinVector (σ j)) k))
  simp only [cavityGroupReplicaGram, cavityPhysicalReplicaVectors, hs, projectedOverlap]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  by_cases hd : d a = 0
  · simp [hd]
  · have hd' : (d a : ℝ) ≠ 0 := by exact_mod_cast hd
    field_simp

lemma cavityPhysicalReplicaVectors_gram_bound {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (c : ℝ) (hc : 0 < c) (hd : ∀ a, c ≤ (d a : ℝ) / N) :
    ∀ a i j, |cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j| ≤ 1 / c := by
  intro a i j
  rw [cavityPhysicalReplicaVectors_gram hN, abs_div,
    abs_of_pos (lt_of_lt_of_le hc (hd a))]
  exact div_le_div₀ (by positivity) (projectedOverlap_abs_le_one U (I a) (σ i) (σ j))
    hc (hd a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vectors used by the fresh group frames have exactly the
physical projected-overlap covariance divided by the group density. -/

noncomputable section
open IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityGroupSetEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupSetEquiv k e a) j : Fin N)=e ⟨a,j⟩ := rfl

lemma cavityGroupSpinCoordinates_physical {N m r : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N) (σ : Fin r → Spin N) :
    (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) =
    cavityPhysicalReplicaVectors (matrixRotation V⁻¹)
      (cavitySpectralGroup (fun i => (e.symm i).1)) k (cavityGroupSetEquiv k e) σ := by
  funext a i j
  rw [cavityPhysicalReplicaVectors, cavityGroupSetEquiv_apply]
  rfl

lemma cavityGroupSpinCoordinates_gram {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j =
      projectedOverlap (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1) a) (σ i) (σ j) / ((k a : ℝ)/N) := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram hN _ _ _ _ _ a i j

lemma cavityGroupSpinCoordinates_covariance {N m r depth : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N × LabeledLeaf depth) (q : ℕ) :
    cavityGroupReplicaCovariance q
      (cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i).1)) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (fun i j => spectralJointEntry (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) depth (σ i) (σ j)) := by
  unfold cavitySpectralBlockCovariance
  congr 1
  funext a i j
  rw [cavityGroupSpinCoordinates_gram hN, spectralJointEntry_spectral]

lemma cavityGroupSpinCoordinates_gram_bound {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) {c : ℝ} (hc : 0 < c)
    (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j|
      ≤ 1/c := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram_bound hN _ _ _ _ _ c hc hk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximum selected-coordinate norm gives exactly the simultaneous
spatial restriction of every replica. A common divergent sequence of
radii avoids the boundaries of all the limiting replica laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavityReplicaRadius {m r q d : ℕ} {L : Type*} [TopologicalSpace L]
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    Continuous (cavityReplicaRadius (L := L) J) :=
  (J.continuous.comp continuous_snd).norm

theorem cavity_replica_common_null_radii {m q d : ℕ}
    (L : ℕ → Type*) [∀ r, TopologicalSpace (L r)]
    [∀ r, MeasurableSpace (L r)] [∀ r, BorelSpace (L r)]
    (Q : (r : ℕ) → ProbabilityMeasure
      (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (J : (r : ℕ) → EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, 0 < B j ∧ ∀ r,
        (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
          {p | cavityReplicaRadius (J r) p = B j} = 0 := by
  obtain ⟨B,hlim,hB⟩ := cavity_common_null_cutoff_radii
    (fun r => (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))))
    (fun r => cavityReplicaRadius (J r))
    (fun r => (continuous_cavityReplicaRadius (J r)).measurable)
  refine ⟨B,hlim,fun j => ⟨?_,(hB j).2.2⟩⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith [(hB j).1]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary boundedness and product identities for the restricted
finite-spin factor used in the actual cavity Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityRestrictedFactor_mem {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    cavityRestrictedFactor K L C T B y ε ∈ Icc 0 (Real.exp T) := by
  unfold cavityRestrictedFactor
  split_ifs
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr (min_le_right _ _)⟩
  · exact ⟨le_rfl,(Real.exp_pos _).le⟩

lemma measurable_cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityRestrictedFactor K L C T B p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro ε
  apply Measurable.ite _ _ measurable_const
  · apply measurableSet_le _ measurable_const
    fun_prop
  · exact (((continuous_cavityLogFactor K L C ε).measurable).min measurable_const).exp

lemma measurable_cavityRestrictedFactor_comp {d k : ℕ} {E : Type*} [MeasurableSpace E]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (Y : E → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (ε : E → Spin k) (hε : Measurable ε) :
    Measurable (fun x => cavityRestrictedFactor K L C T B (Y x) (ε x)) := by
  have hp : Measurable (fun x => (Y x,ε x)) := hY.prodMk hε
  change Measurable ((fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ (fun x => (Y x,ε x)))
  exact Measurable.comp (g := fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) (f := fun x => (Y x,ε x))
      (measurable_cavityRestrictedFactor K L C T B) hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded restricted factor as a measurable function of the
original disorder, fresh group rotation, base state and cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityHaarRestrictedWeight e v A₀ K L C T B) := by
  apply measurable_from_prod_countable_left
  intro x
  have hy : Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavitySelectedSiteProjection e (v z.1) (cavityGroupHaarFrames A₀ z.2) x.1) :=
    (measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const))
  exact measurable_cavityRestrictedFactor_comp K L C T B _ hy (fun _ => x.2) measurable_const

lemma cavityHaarRestrictedWeight_mem {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) :
    cavityHaarRestrictedWeight e v A₀ K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarFiniteOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical restricted Haar overlap test converges to the
unmodified common-level law of the finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_finite_overlap_cutoff (hpub : PanchenkoTalagrandFieldPairInput)
    {m q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod (uniformSpinPrior kspin))
          (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1)
            (cavityOverlapObservable Φ hΦ)) ∂(P n).prod (Measure.pi (μ n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) ∂pathMeasure| < ε := by
  intro p K L Cspin τ
  have hh := cavity_haar_finite_cutoff_comparison N hN μ A₀ hA₀ Ω X P ν hν B hB
    hGram v₀ hvM C hv ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG
    d hd0 hd hE hP hn hoff hdiag g e he heg K L Cspin (uniformSpinPrior kspin)
    (cavityOverlapObservable Φ hΦ) hNpos hC B₀ hB₀ a ha rfl b hb hblim hnull
  dsimp only at hh
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  filter_upwards [hj] with n hn'
  have hf := cavity_strict_finite_overlap_test hpub hdim hkspin ρ eig hρ hρsum B₀ hB₀
    hBE hcomplete g a ha p Φ hΦ (n := n) hΦb
  dsimp only at hf
  rw [hf] at hn'
  exact hn'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityOrientationLift_right {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (V : SpecialOrthogonal N) :
    cavityOrientationLift hN (U * cavitySpecialOrthogonal V) = cavityOrientationLift hN U * V := by
  apply Subtype.ext
  have hd : ((cavitySpecialOrthogonal V : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ).det = 1 :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp V.property).2
  have hs : cavityOrientationSign hN (U * cavitySpecialOrthogonal V) = cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Submonoid.coe_mul, Matrix.det_mul, hd, mul_one]
  change cavityOrientationSign hN (U * cavitySpecialOrthogonal V) *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) =
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [hs, Matrix.mul_assoc]

lemma cavityOrientationLift_measure_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [μ.IsMulRightInvariant] :
    (μ.map (cavityOrientationLift hN)).IsMulRightInvariant := by
  constructor
  intro V
  rw [Measure.map_map (measurable_mul_const V) (measurable_cavityOrientationLift hN)]
  have he : (fun S : SpecialOrthogonal N => S * V) ∘ cavityOrientationLift hN =
      cavityOrientationLift hN ∘ (fun U => U * cavitySpecialOrthogonal V) := by
    funext U
    exact (cavityOrientationLift_right hN U V).symm
  rw [he, ← Measure.map_map (measurable_cavityOrientationLift hN)
    (measurable_mul_const (cavitySpecialOrthogonal V)), map_mul_right_eq_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomPriorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of a normalized cutoff when the labeled cascade prior
is part of the retained disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_random_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean (ν ω) (fun x => H (ω,x)) (s ω)
      (fun σ => F (ω,σ))) := by
  classical
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hn := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then F p else (0 : ℝ))
    (Measurable.ite hS hF measurable_const)
  have hd := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then (1 : ℝ) else 0)
    (Measurable.ite hS measurable_const measurable_const)
  exact hn.div hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeCutoffMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original cutoff average is measurable in the actual labeled
tree. The Gaussian and rotation coordinates remain unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_cavityFullCutoffDisorderTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) |
      p.2 ∈ s p.1})
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun T => cavityFullCutoffDisorderTest μ T eig I u s F) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.fst
  let H : Ω × X → ℝ := fun p => cavityFullHamiltonian eig I u (p.1.1.2,p.1.2) p.2
  have hH : Measurable H := by
    have hp : Measurable (fun p : Ω × X => ((p.1.1.2,p.1.2),p.2)) :=
      (measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd
    exact Measurable.comp
      (g := Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u))
      (f := fun p : Ω × X => ((p.1.1.2,p.1.2),p.2))
      (measurable_cavityFullHamiltonian eig I u) hp
  have hS : MeasurableSet {p : Ω × X | p.2 ∈ s p.1.1.2} :=
    hs.preimage (measurable_fst.fst.snd.prodMk measurable_snd)
  have hG : Measurable (fun p : Ω × (Fin 2 → X) => F p.1.1.2 p.2) :=
    hF.comp (measurable_fst.fst.snd.prodMk measurable_snd)
  have hh := measurable_random_cavityCutoffReplicaMean ν hν H hH
    (fun p => s p.1.2) hS (fun p => F p.1.1.2 p.2) hG
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeFullRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded full and restricted Gibbs tests can be averaged over the
original labeled-tree law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityFullTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun T => cavityFullTest μ T eig I u F) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.fst
  let H : Ω × X → ℝ := fun p => cavityFullHamiltonian eig I u (p.1.1.2,p.1.2) p.2
  have hH : Measurable H := by
    have hp : Measurable (fun p : Ω × X => ((p.1.1.2,p.1.2),p.2)) :=
      (measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd
    exact Measurable.comp
      (g := Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u))
      (f := fun p : Ω × X => ((p.1.1.2,p.1.2),p.2))
      (measurable_cavityFullHamiltonian eig I u) hp
  have hh := measurable_random_referenceReplicaMean hν hH
    (D := fun p => F p.2) ((measurable_of_countable F).comp measurable_snd)
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationArray
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral array of the concrete base rotation/Gaussian Gibbs
law. The same rotation supplies its overlaps and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityRotationEntry_gram {N m depth : ℕ} (I : Fin m → Finset (Fin N))
    (p : ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)) :
    SpectralGram (cavitySampledEntryArray (cavityRotationEntry I) p) := by
  intro a r
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_tree] using
      treeOverlap_posSemidef depth (fun i : Fin r => (p.2 i).2)
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (matrixRotation p.1.1.1⁻¹) (I j)
        (fun i : Fin r => (p.2 i).1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable physical group vectors and their covariance in the actual
base Gibbs disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p a => cavityRotationVectors k e p a x) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro j
  exact (measurable_cavityRotation_eval (spinVector x.1) (e ⟨a,j⟩)).comp measurable_fst.fst

lemma cavityRotationVectors_gram_bound {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)))
    {c : ℝ} (hc : 0 < c) (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i)) a i j| ≤ 1/c :=
  cavityGroupSpinCoordinates_gram_bound hN k e p.1.1.1
    (fun i => (p.2 i).1) hc hk

lemma cavityRotationVectors_covariance {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth))) (q : ℕ) :
    cavityGroupReplicaCovariance q (cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i))) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (spectralBlockView (m+1) r (cavitySampledEntryArray
        (cavityRotationEntry (cavitySpectralGroup (fun i => (e.symm i).1))) p)) :=
  cavityGroupSpinCoordinates_covariance hN k e p.1.1.1 (fun i => p.2 i) q

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalRadialCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original geometric cutoff is the radial special-coordinate
cutoff under the oriented Haar law, with the exact spin split. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_original_radial_cutoff {N n m d depth : ℕ}
    (μ : Measure (Orthogonal (N+n))) (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (T : LabeledTree depth) (eig : Fin (N+n) → ℝ)
    (u : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    (∫ U, cavityOriginalGeometricMean g B T eig u (1+R^2) F
      (cavityOrientationLift hN U) ∂μ) =
    cavityFullCutoffDisorderTest (μ.map (cavityOrientationLift hN)) T eig
      (cavitySpectralGroup g) u
      (cavitySpecialCutoff g (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R)
      (fun _ σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) := by
  have hs (U : SpecialOrthogonal (N+n)) :
      {x : Spin (N+n) × LabeledLeaf depth | cavityGeometricWeight g
        (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavitySpinSplit N n x.1) ≤ 1+R^2} =
      cavitySpecialCutoff g
        (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R U := by
    have he (σ : Spin (N+n)) : cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [cavityJoinedSpin, cavitySpinSplit]
    dsimp only [cavityGeometricWeight,cavitySpecialCutoff]
    simp only [he]
    exact (cavity_radial_square_cutoff _ (fun x => norm_nonneg _) hR).symm
  have he : (fun U => cavityOriginalGeometricMean g B T eig u (1+R^2) F U) =
      fun U => ∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        (cavityFullHamiltonian eig (cavitySpectralGroup g) u (U,z))
        (cavitySpecialCutoff g
          (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R U)
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates := by
    funext U
    simp only [cavityOriginalGeometricMean,hs]
    rfl
  rw [← integral_map_of_stronglyMeasurable (measurable_cavityOrientationLift hN)
    (measurable_cavityOriginalGeometricMean g B hB T eig u (1+R^2) F).stronglyMeasurable]
  rw [he]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalTreeRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original geometric cutoff average is bounded and measurable in
the labeled tree, so its comparison may be averaged over that tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_original_tree_regular {N n m d depth : ℕ}
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    Measurable (fun T : LabeledTree depth => ∫ U,
      cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U) ∂μ) ∧
    ∀ T : LabeledTree depth, |∫ U,
      cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U) ∂μ| ≤ M := by
  constructor
  · have he := funext fun T : LabeledTree depth =>
      cavity_original_radial_cutoff μ hN g B hB T eig u hR F
    rw [he]
    have hmB : Measurable (fun U : SpecialOrthogonal (N+n) =>
        B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) :=
      hB.comp ((measurable_cavityCompressionGrams g).comp
        (measurable_subtype_coe.subtype_mk))
    exact measurable_cavityFullCutoffDisorderTest_tree _ eig (cavitySpectralGroup g) u _
      (measurableSet_cavitySpecialCutoff g _ hmB R) _
      ((measurable_of_countable (fun σ : Fin 2 → Spin (N+n) × LabeledLeaf depth =>
        F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2)))).comp measurable_snd)
  · intro T
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun U => cavityOriginalGeometricMean g B T eig u (1+R^2) F (cavityOrientationLift hN U))
      (C := M) (ae_of_all _ fun U => cavityOriginalGeometricMean_bound g B T eig u (1+R^2) F hM hF _)
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeRestrictedAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging fixed-tree restricted Gibbs means gives exactly the
physical product-disorder mean with its original random tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_restricted_tree_average {N m depth q d k r : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (dims : Fin m → ℕ) (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    (η : Measure ((a : Fin m) → Orthogonal (dims a))) [IsProbabilityMeasure η]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (e : Fin d → Fin m × Fin q)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T B : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin k) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
      (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
      F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η) ∂θ) =
    ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
      (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
      F ∂(((μ.prod θ).prod gaussianCoordinates).prod η) := by
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight e (cavityRotationVectors (depth := depth) dims E) A₀ K L C T B
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (dims a))
    ν (measurable_cavityRotationProbability eig I u) π
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight e
    (cavityRotationVectors dims E) (measurable_cavityRotationVectors dims E) A₀ K L C T B
  have hf : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd) 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos T).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem e (cavityRotationVectors dims E) A₀ K L C T B (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hh := cavity_bounded_dirac_average μ θ gaussianCoordinates η f hf hb
  simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeRestrictedRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and boundedness of the fixed-tree physical restricted
mean needed to restore the random cascade prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_restricted_tree_regular {N m depth q d k r : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (dims : Fin m → ℕ) (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    (η : Measure ((a : Fin m) → Orthogonal (dims a))) [IsProbabilityMeasure η]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (e : Fin d → Fin m × Fin q)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T B : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin k) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    Measurable (fun V : LabeledTree depth =>
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
        F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η)) ∧
    ∀ V : LabeledTree depth,
      |∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
        F ∂(((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η)| ≤ M := by
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight e (cavityRotationVectors (depth := depth) dims E) A₀ K L C T B
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (dims a))
    ν (measurable_cavityRotationProbability eig I u) π
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight e
    (cavityRotationVectors dims E) (measurable_cavityRotationVectors dims E) A₀ K L C T B
  have hf : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd) 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos T).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem e (cavityRotationVectors dims E) A₀ K L C T B (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  constructor
  · have hh := measurable_cavity_bounded_dirac_integral μ gaussianCoordinates η f hf hb
    simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh
  · intro V
    have hh := abs_integral_le_const_of_bound
      (μ := ((μ.prod (Measure.dirac V)).prod gaussianCoordinates).prod η) hf hb
    simpa only [f,κ,cavityHaarSpinPriorKernel_apply,ν,w] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityUniformTreeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A limit valid for every sequence of labeled trees is uniform in the
tree choice and survives averaging over the original cascade law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_uniform_zero_of_all_selections {X : ℕ → Type*} [∀ n, Nonempty (X n)]
    (f : (n : ℕ) → X n → ℝ)
    (h : ∀ x : (n : ℕ) → X n, Tendsto (fun n => f n (x n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |f n x| < ε := by
  classical
  intro ε hε
  let x : (n : ℕ) → X n := fun n =>
    if hn : ∃ x, ε ≤ |f n x| then Classical.choose hn else Classical.choice inferInstance
  have hx := (h x).eventually (Metric.ball_mem_nhds 0 hε)
  filter_upwards [hx] with n hn
  rw [Real.dist_eq,sub_zero] at hn
  intro y
  by_contra hy
  have he : ∃ y, ε ≤ |f n y| := ⟨y, le_of_not_gt hy⟩
  have hb : ε ≤ |f n (x n)| := by
    dsimp only [x]
    rw [dite_eq_left he]
    exact Classical.choose_spec he
  linarith

lemma cavity_average_zero_of_all_selections {X : ℕ → Type*}
    [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
    (P : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (P n)]
    (f : (n : ℕ) → X n → ℝ)
    (h : ∀ x : (n : ℕ) → X n, Tendsto (fun n => f n (x n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂P n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_uniform_zero_of_all_selections f h (ε/2) (by positivity)] with n hn
  have hh := norm_integral_le_of_norm_le_const (μ := P n) (f := f n)
    (C := ε/2) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hn x).le)
  rw [Real.dist_eq,sub_zero]
  have hb : |∫ x, f n x ∂P n| ≤ ε/2 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
  exact hb.trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalTreeLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original cutoff comparison averaged over the actual random
cascade tree and all retained Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_original_restricted_tree_limit {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
    Tendsto (fun j => (∫ T, (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) T
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) ∂θ j) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (θ j)).prod gaussianCoordinates).prod (η j))) atTop (𝓝 0) := by
  intro E eig τ
  let O := fun j (T : LabeledTree (depth j)) => (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) T
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j)
  let C := fun j (T : LabeledTree (depth j)) => ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (Measure.dirac T)).prod gaussianCoordinates).prod (η j))
  have hfix : ∀ T : (j : ℕ) → LabeledTree (depth j),
      Tendsto (fun j => O j (T j)-C j (T j)) atTop (𝓝 0) := by
    intro T
    exact cavity_original_restricted_haar_limit_family N depth hN hNlim g k ek e es B₀ a₀ hk η
      l w hg hln hw μ ν T lam v hv u hu t hR hM F hF A hprob
  have havg := cavity_average_zero_of_all_selections θ (fun j T => O j T-C j T) hfix
  apply havg.congr'
  filter_upwards [] with j
  have hO := cavity_original_tree_regular (μ j) (Nat.add_pos_left (hN j) n) (g j)
    (cavityConcreteComplement es B₀) (measurable_cavityConcreteComplement es B₀)
    (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
    (u j) hR hM (fun σ => F j (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
    (fun σ => hF j _)
  have hC := cavity_restricted_tree_regular (ν j) (cavityBaseGroupDimension (k j) a₀) (E j)
    (η j) (eig j) (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j)
    (fun i => (a₀ i,i)) (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (t • A.1) (t • A.2.1) (t • A.2.2) (uniformSpinPrior n : Measure (Spin n))
    τ R hM (F j) (hF j)
  have hOi : Integrable (O j) (θ j) := integrable_of_measurable_abs_le hO.1 hO.2
  have hCi : Integrable (C j) (θ j) := integrable_of_measurable_abs_le hC.1 hC.2
  rw [integral_sub hOi hCi]
  have he := cavity_restricted_tree_average (ν j) (θ j)
    (cavityBaseGroupDimension (k j) a₀) (E j) (η j) (eig j)
    (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j)
    (fun i => (a₀ i,i)) (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (t • A.1) (t • A.2.1) (t • A.2.2) (uniformSpinPrior n : Measure (Spin n))
    τ R hM (F j) (hF j)
  exact congrArg (fun x => (∫ T, O j T ∂θ j)-x) he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalFullComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full original Gibbs law converges, through the proved geometric
cutoff, to the actual fresh-Haar restricted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_original_full_haar_comparison {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L M : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := fun j => cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ r in atTop,
      |(∫ T, cavityFullTest ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) t)
        (cavitySpectralGroup (g r)) (u r)
        (fun σ => F r (fun i => (((cavitySpinSplit (N r) n (σ i).1).1,(σ i).2),
          (cavitySpinSplit (N r) n (σ i).1).2))) ∂θ r) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig r)
          (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k r) a₀) (E r))
          (cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r))
          (t • A.1) (t • A.2.1) (t • A.2.2) (τ j) (b j) (p,x)) (F r)
        ∂((((ν r).prod (θ r)).prod gaussianCoordinates).prod (η r))| < ε := by
  intro E eig τ
  let μO := fun j => (μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))
  let (j : ℕ) : IsProbabilityMeasure (μO j) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cavityOrientationLift _).aemeasurable).mpr inferInstance
  let (j : ℕ) : (μO j).IsMulRightInvariant := cavityOrientationLift_measure_rightInvariant _ _
  let eigFull := fun j => diagonalPerturbedEigenvalues (fun i => lam (g j i))
    (cavitySpectralGroup (g j)) (v j) t
  let test := fun j (σ : Fin 2 → Spin (N j+n) × LabeledLeaf (depth j)) =>
    F j (fun i => (((cavitySpinSplit (N j) n (σ i).1).1,(σ i).2),
      (cavitySpinSplit (N j) n (σ i).1).2))
  let B := fun j (U : SpecialOrthogonal (N j+n)) =>
    cavityConcreteComplement es B₀ (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U))
  have hmB : ∀ j, Measurable (B j) := fun j =>
    (measurable_cavityConcreteComplement es B₀).comp
      ((measurable_cavityCompressionGrams (g j)).comp
        (show Measurable (cavitySpecialOrthogonal (N := N j+n)) from
          measurable_subtype_coe.subtype_mk))
  have hcut := cavity_full_tree_cutoff_sequence N depth
    (fun j => Nat.add_pos_left (hN j) n) μO θ eigFull g u hu B hmB
    (fun j U => cavityConcreteComplement_gram (g j) es B₀ (cavitySpecialOrthogonal U))
    good hgood hp hL hbound test hM (fun j σ => hF j _) b hb hblim
  intro ε hε
  filter_upwards [hcut (ε/2) (by positivity)] with j hj
  have hmatch := cavity_original_restricted_tree_limit N depth hN hNlim g k ek e es B₀ a₀ hk η
    l w hg hln hw μ ν θ lam v hv u hu t (hb j).le hM F hF A hprob
  have hmatch' := hmatch.eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε/2 by positivity))
  filter_upwards [hj,hmatch'] with r hr hr'
  rw [Real.dist_eq,sub_zero] at hr'
  have heq :
      (∫ T, ∫ U, cavityOriginalGeometricMean (g r) (cavityConcreteComplement es B₀) T
        (eigFull r) (u r) (1+(b j)^2)
        (fun σ => F r (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN r) n) U) ∂μ r ∂θ r) =
      ∫ T, cavityFullCutoffDisorderTest (μO r) T (eigFull r) (cavitySpectralGroup (g r)) (u r)
        (cavitySpecialCutoff (g r) (B r) (b j)) (fun _ => test r) ∂θ r := by
    apply integral_congr_ae
    filter_upwards [] with T
    exact cavity_original_radial_cutoff (μ r) (Nat.add_pos_left (hN r) n) (g r)
      (cavityConcreteComplement es B₀) (measurable_cavityConcreteComplement es B₀) T
      (eigFull r) (u r) (hb j).le _
  change |(∫ T, cavityFullTest (μO r) T (eigFull r) (cavitySpectralGroup (g r)) (u r)
    (test r) ∂θ r) - _| < ε
  rw [heq] at hr'
  exact (abs_sub_le _ _ _).trans_lt (add_lt_add hr hr') |>.trans_eq (by ring)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalSpinObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the physical spectral components recovers the ordinary spin
overlap. Thus the scalar test needed by self-consistency has no frame dependence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma sum_projectedOverlap_groups {N m : ℕ} (g : Fin N → Fin m)
    (U : Rotation N) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (cavitySpectralGroup g a) σ τ) =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  calc
    _ = (N : ℝ)⁻¹ * ∑ a, ∑ i, if g i = a then
        U (spinVector σ) i * U (spinVector τ) i else 0 := by
      simp only [projectedOverlap,cavitySpectralGroup,Finset.sum_filter,Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ∑ i, U (spinVector σ) i * U (spinVector τ) i := by
      congr 1
      rw [Finset.sum_comm]
      simp
    _ = projectedOverlap U Finset.univ σ τ := by simp only [projectedOverlap]
    _ = _ := projectedOverlap_univ U σ τ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinSplitOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing finitely many cavity sites changes the ordinary spin
overlap by at most twice their fraction of the system. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityTotalSpinOverlap_mul_size {N : ℕ} (x : Spin N × Spin N) :
    (N : ℝ) * cavityTotalSpinOverlap x = ∑ i, spinValue (x.1 i) * spinValue (x.2 i) := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · rw [cavityTotalSpinOverlap, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]

lemma abs_cavityTotalSpinOverlap_le {N : ℕ} (x : Spin N × Spin N) :
    |cavityTotalSpinOverlap x| ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    unfold cavityTotalSpinOverlap
    rw [abs_mul,abs_of_pos (inv_pos.mpr hNpos)]
    calc
      _ ≤ (N:ℝ)⁻¹ * ∑ i, |spinValue (x.1 i) * spinValue (x.2 i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hNpos).le
      _ = (N:ℝ)⁻¹ * N := by simp only [abs_mul,abs_spinValue,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      _ = 1 := inv_mul_cancel₀ hNpos.ne'

lemma cavity_spin_split_overlap {N n : ℕ} (σ τ : Spin (N+n)) :
    ((N+n:ℕ):ℝ) * cavityTotalSpinOverlap (σ,τ) =
      (N:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1) +
      (n:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).2,(cavitySpinSplit N n τ).2) := by
  simp only [cavityTotalSpinOverlap_mul_size,Fin.sum_univ_add,
    cavitySpinSplit_left,cavitySpinSplit_right]

lemma cavity_spin_split_overlap_error {N n : ℕ} (hN : 0 < N) (σ τ : Spin (N+n)) :
    |cavityTotalSpinOverlap (σ,τ) -
      cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1)| ≤
      2*(n:ℝ)/(N+n) := by
  let a := cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1)
  let b := cavityTotalSpinOverlap ((cavitySpinSplit N n σ).2,(cavitySpinSplit N n τ).2)
  let c := cavityTotalSpinOverlap (σ,τ)
  have hpos : (0:ℝ) < N+n := by exact_mod_cast Nat.add_pos_left hN n
  have hs : ((N:ℝ)+n)*c = N*a+n*b := by
    simpa only [Nat.cast_add] using cavity_spin_split_overlap σ τ
  have he : c-a = (n:ℝ)*(b-a)/(N+n) := by
    apply (eq_div_iff hpos.ne').mpr
    nlinarith [hs]
  change |c-a| ≤ _
  rw [he,abs_div,abs_of_pos hpos,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ hpos.le
  have ha : |a| ≤ 1 := abs_cavityTotalSpinOverlap_le _
  have hb : |b| ≤ 1 := abs_cavityTotalSpinOverlap_le _
  have hab : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralCutoffRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single deterministic cutoff sequence avoids the Gaussian-mixture
boundaries for every replica count in the spectral limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_spectral_common_cutoff_radii {m q d : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m+1))) (ρ : Fin m → ℝ)
    (e : Fin d → Fin m × Fin q) :
    ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧ ∀ j, 0 < b j ∧ ∀ r,
      (cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r) : Measure
        (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
        {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0 :=
  cavity_replica_common_null_radii (fun r => SpectralBlock m r)
    (fun r => cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r))
    (fun _ => cavitySelectedGroupProjection e)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySplitTestContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous overlap tests are insensitive to removal of finitely many
cavity sites, uniformly over all spin configurations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_split_test_uniform {n : ℕ} (N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ σ τ : Spin (N k+n),
      |Φ (cavityTotalSpinOverlap (σ,τ)) -
        Φ (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n σ).1,
          (cavitySpinSplit (N k) n τ).1))| < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (-1:ℝ) 1) hΦ.continuousOn
  have hi : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNlim)
  have hr : Tendsto (fun k => 2*(n:ℝ)/(N k)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul (2*(n:ℝ))
  intro ε hε
  obtain ⟨δ,hδ,hφ⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  filter_upwards [hr.eventually (Iio_mem_nhds hδ)] with k hk
  intro σ τ
  have hfull := abs_le.mp (abs_cavityTotalSpinOverlap_le (σ,τ))
  have hbase := abs_le.mp (abs_cavityTotalSpinOverlap_le
    ((cavitySpinSplit (N k) n σ).1,(cavitySpinSplit (N k) n τ).1))
  apply (show dist (Φ (cavityTotalSpinOverlap (σ,τ)))
    (Φ (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n σ).1,
      (cavitySpinSplit (N k) n τ).1))) < ε from ?_)
  apply hφ _ hfull _ hbase
  rw [Real.dist_eq]
  apply (cavity_spin_split_overlap_error (hN k) σ τ).trans_lt
  apply lt_of_le_of_lt _ hk
  apply div_le_div_of_nonneg_left (by positivity)
    (Nat.cast_pos.mpr (hN k))
  exact le_add_of_nonneg_right (Nat.cast_nonneg n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalOverlapCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual base-system spectral coordinates recover its ordinary
spin-overlap law under the fresh-Haar cutoff comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_physical_overlap_observable {N m depth k : ℕ}
    (g : Fin N → Fin m)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (σ : Fin 2 → (Spin N × LabeledLeaf depth) × Spin k) :
    cavityProjectedSpinTest
      (cavitySampledGroupBlock (cavityRotationEntry (cavitySpectralGroup g)) p)
      (cavityOverlapObservable Φ hΦ) σ =
      Φ ((N : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1.1 i) * spinValue ((σ 1).1.1 i)) := by
  simp only [cavityProjectedSpinTest,cavityOverlapObservable,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,cavitySampledGroupBlock,cavityRotationEntry,spectralJointEntry_spectral]
  rw [sum_projectedOverlap_groups]

theorem cavity_physical_overlap_cutoff (hpub : PanchenkoTalagrandFieldPairInput)
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ n a, 0 < dims n a)
    (hdims : ∀ a, Tendsto (fun n => dims n a) atTop atTop)
    (E : (n : ℕ) → ((a : Fin m) × Fin (dims n a)) ≃ Fin (N n))
    (μ : (n : ℕ) → Measure (Orthogonal (N n))) [∀ n, IsProbabilityMeasure (μ n)]
    (θ : (n : ℕ) → Measure (LabeledTree (depth n))) [∀ n, IsProbabilityMeasure (θ n)]
    (μG : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (dims n a)))
    [∀ n a, IsProbabilityMeasure (μG n a)] [∀ n a, (μG n a).IsMulRightInvariant]
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (dims n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    (eigN : (n : ℕ) → Fin (N n) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hcG : ∀ n a, c ≤ (dims n a : ℝ)/N n)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρlim : Tendsto (fun n a => (dims n a : ℝ)/N n) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun n => cavityRotationArrayLaw (μ n) (θ n) (eigN n)
      (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean
          ((cavityRotationProbability (eigN n)
            (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n) ω.1).prod
            (uniformSpinPrior kspin))
          (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors (dims n) (E n))
            (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1)))
          ∂(((μ n).prod (θ n)).prod gaussianCoordinates).prod (Measure.pi (μG n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) ∂pathMeasure| < ε := by
  intro p K L Cspin τ
  let I n := cavitySpectralGroup (fun i => ((E n).symm i).1)
  let Ω n := (Orthogonal (N n) × LabeledTree (depth n)) × (ℕ → ℝ)
  let X n := Spin (N n) × LabeledLeaf (depth n)
  let P n := ((μ n).prod (θ n)).prod gaussianCoordinates
  let ν n := cavityRotationProbability (depth := depth n) (eigN n) (I n) (u n)
  let B n := cavityRotationEntry (depth := depth n) (I n)
  let Q n := cavityRotationArrayLaw (μ n) (θ n) (eigN n) (I n) (u n)
  have hρs n a : 0 < (dims n a : ℝ)/N n :=
    div_pos (Nat.cast_pos.mpr (hgroups n a)) (Nat.cast_pos.mpr (hN n))
  have hh := cavity_haar_finite_overlap_cutoff hpub dims hdims μG A₀ hA₀ Ω X P ν
    (fun n => measurable_cavityRotationProbability _ _ _) B
    (fun n => measurable_cavityRotationEntry (I n))
    (fun n => cavityRotationEntry_gram (I n))
    (fun n => cavityRotationVectors (dims n) (E n))
    (fun n => measurable_cavityRotationVectors (dims n) (E n)) (1/c)
    (fun s n x => cavityRotationVectors_gram_bound (r := s) (hN n) (dims n) (E n) x hc (hcG n))
    (fun n a => (dims n a : ℝ)/N n) ρ eig hρs hρ hρlim hρsum
    (fun s n x => cavityRotationVectors_covariance (r := s) (hN n) (dims n) (E n) x q)
    Q Q₀ (fun _ => rfl) hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    hgroups (div_nonneg zero_le_one hc.le) hdim hkspin B₀ hB₀ hBE hcomplete a ha Φ hΦ hΦb
    b hb hblim hnull
  dsimp only at hh
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  filter_upwards [hj] with n hn'
  have htest (ω : Ω n × ((a : Fin m) → Orthogonal (dims n a))) : cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1)
      (cavityOverlapObservable Φ hΦ) =
      (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))) := by
    funext σ
    exact cavity_physical_overlap_observable (fun i => ((E n).symm i).1) ω.1 Φ hΦ σ
  simpa only [htest] using hn'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySplitOverlapTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full and retained ordinary-overlap observables differ uniformly
by a vanishing amount, also under the random-tree Gibbs average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_full_split_overlap_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (T : (k : ℕ) → LabeledTree (depth k)) (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun k =>
      cavityFullTest (μ k) (T k) (eig k) (I k) (u k)
        (cavityFullOverlapInsertion Φ) -
      cavityFullTest (μ k) (T k) (eig k) (I k) (u k)
        (cavitySplitOverlapInsertion Φ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_split_test_uniform (n := n) N hN hNlim Φ Φ.continuous
    (ε/2) (by positivity)] with k hk
  let F : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavityFullOverlapInsertion Φ
  let G : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavitySplitOverlapInsertion Φ
  have hmF : Measurable (Function.uncurry F) :=
    (measurable_of_countable (cavityFullOverlapInsertion Φ)).comp measurable_snd
  have hmG : Measurable (Function.uncurry G) :=
    (measurable_of_countable (cavitySplitOverlapInsertion (N := N k) Φ)).comp measurable_snd
  have hFb U σ : |F U σ| ≤ ‖Φ‖ := by
    simpa only [F,cavityFullOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hGb U σ : |G U σ| ≤ ‖Φ‖ := by
    simpa only [G,cavitySplitOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n (σ 0).1).1,
        (cavitySpinSplit (N k) n (σ 1).1).1))
  have hd U σ : |F U σ-G U σ| ≤ ε/2 := by
    simpa only [F,G,cavityFullOverlapInsertion,cavitySplitOverlapInsertion,cavityReplicaOverlap,
      ← sub_mul,abs_mul,abs_spinValue,one_mul,mul_one] using (hk (σ 0).1 (σ 1).1).le
  have hh := cavityFullDisorderTest_abs_le (μ k) (T k) (eig k) (I k) (u k)
    (fun U σ => F U σ-G U σ) (hmF.sub hmG) (show 0 ≤ ε/2 by positivity) hd
  rw [cavityFullDisorderTest_sub (μ k) (T k) (eig k) (I k) (u k) F G hmF hmG
    (norm_nonneg Φ) hFb hGb] at hh
  rw [Real.dist_eq,sub_zero]
  exact hh.trans_lt (by linarith)

theorem cavity_full_split_tree_overlap_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun k =>
      (∫ T, cavityFullTest (μ k) T (eig k) (I k) (u k)
        (cavityFullOverlapInsertion Φ) ∂θ k) -
      ∫ T, cavityFullTest (μ k) T (eig k) (I k) (u k)
        (cavitySplitOverlapInsertion Φ) ∂θ k) atTop (𝓝 0) := by
  let O := fun k (T : LabeledTree (depth k)) =>
    cavityFullTest (μ k) T (eig k) (I k) (u k)
      (cavityFullOverlapInsertion Φ)
  let C := fun k (T : LabeledTree (depth k)) =>
    cavityFullTest (μ k) T (eig k) (I k) (u k) (cavitySplitOverlapInsertion Φ)
  have hlim := cavity_average_zero_of_all_selections θ (fun k T => O k T-C k T)
    (fun T => cavity_full_split_overlap_test_tendsto N depth hN hNlim μ T eig I u Φ)
  apply hlim.congr'
  filter_upwards [] with k
  have hO : Integrable (O k) (θ k) := integrable_of_measurable_abs_le
    (measurable_cavityFullTest_tree _ _ _ _ _) (fun T =>
      cavityFullDisorderTest_abs_le (μ k) T (eig k) (I k) (u k) (fun _ => cavityFullOverlapInsertion Φ)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavityFullOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)))
  have hC : Integrable (C k) (θ k) := integrable_of_measurable_abs_le
    (measurable_cavityFullTest_tree _ _ _ _ _) (fun T =>
      cavityFullDisorderTest_abs_le (μ k) T (eig k) (I k) (u k) (fun _ => cavitySplitOverlapInsertion (N := N k) Φ)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavitySplitOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityTotalSpinOverlap
              ((cavitySpinSplit (N k) n (σ 0).1).1,(cavitySpinSplit (N k) n (σ 1).1).1))))
  exact integral_sub hO hC


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalOverlapLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Gibbs overlap test converges to the unchanged common-level law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_original_split_overlap_limit (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A : CavityFactorBlocks d n)
    (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => cavityRotationArrayLaw (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (Φ : ℝ →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r =>
      (∫ T, cavityFullTest ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r) -
      ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
  let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
    (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) 1
  let B := cavityCompressionLimitFrame es B₀
  let F := fun j (σ : Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) =>
    Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  have hF j σ : |F j σ| ≤ ‖Φ‖ := by
    simpa only [F,abs_mul,abs_spinValue,mul_one,one_mul,Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  obtain ⟨b,hblim,hb⟩ := cavity_spectral_common_cutoff_radii Q₀ ρ (fun i : Fin d => (a₀ i,i))
  have hbpos j := (hb j).1
  have hnull j r := (hb j).2 r
  have hfinite := cavity_physical_overlap_cutoff hpub N depth hN
    (fun j => cavityBaseGroupDimension (k j) a₀) hgroups hdims E ν θ μG
    (fun j => cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (fun j a => cavityCanonicalGroupFrame_gram (k j) (e j) a₀ (hk j) a)
    eig u hc hcG ρ lam hρ hρsum hρlim Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a₀ (fun i => (a₀ i,i)) (fun i j hij => congrArg Prod.snd hij) (fun _ => rfl)
    hd hn B (cavityCompressionLimitFrame_gram es B₀ hB₀)
    (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
    (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
    a ha Φ Φ.continuous (fun x => by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm x)
    b hbpos hblim hnull
  have horig := cavity_original_full_haar_comparison N depth hN hNlim g k ek e es B₀ a₀ hk
    (fun j => Measure.pi (μG j)) l w hg hln hw μ ν θ lam v hv u hu 1 good hgood hp hL hbound
    (norm_nonneg Φ) F hF A hprob b hbpos hblim
  dsimp only at hfinite horig
  rw [hA] at horig
  simp only [one_smul] at horig
  let cut := fun j r => ∫ ω, cavityWeightedReplicaMean
    ((cavityRotationProbability (eig r) (cavitySpectralGroup (fun i => ((E r).symm i).1))
      (u r) ω.1).prod (uniformSpinPrior n))
    (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
      (cavityRotationVectors (cavityBaseGroupDimension (k r) a₀) (E r))
      (cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r))
      A.1 A.2.1 A.2.2 (cavityFactorSize A.1 A.2.1 A.2.2*(1+(b j)^2)) (b j) (ω,x)) (F r)
    ∂(((ν r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))
  let full := fun r => ∫ T, cavityFullTest
    ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
    (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
    (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r
  let scalar := fun r => ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hjO,hjF⟩ := ((horig (ε/2) (by positivity)).and
    (hfinite (ε/2) (by positivity))).exists
  filter_upwards [hjO,hjF] with r hrO hrF
  have hrO' : |full r-cut j r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrO
  have hrF' : |cut j r-scalar r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrF
  rw [Real.dist_eq,sub_zero]
  exact (abs_sub_le (full r) (cut j r) (scalar r)).trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalFullOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full-model spin-overlap law in the same cavity comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_original_overlap_limit_oai (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A : CavityFactorBlocks d n)
    (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => cavityRotationArrayLaw (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (Φ : ℝ →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r =>
      (∫ T, cavityFullTest ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) (cavityFullOverlapInsertion Φ) ∂θ r) -
      ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  have ho := cavity_original_split_overlap_limit hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a ha Φ
  let μO := fun r => (μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))
  let (r : ℕ) : IsProbabilityMeasure (μO r) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cavityOrientationLift _).aemeasurable).mpr inferInstance
  have hs := cavity_full_split_tree_overlap_test_tendsto N depth hN hNlim μO θ
    (fun r => diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
    (fun r => cavitySpectralGroup (g r)) u Φ
  have hh := hs.add ho
  simp only [add_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  ring

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_original_overlap_limit_oai := @OAI.InvariantIsing.cavity_original_overlap_limit_oai
