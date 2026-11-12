-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_base_perturbed_array_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:15.651908+00:00
-- url     : https://prove2.me/submissions/8d14dd8c-3c6e-4b95-a92c-0352844ce860

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
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_orientation_tensor_probability_law

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-volume perturbation minimizers provide exactly the natural-index
amplitudes used in the physical cavity model. The unused coordinates are one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityBaseAmplitude_fin {N : ℕ} (u : Fin N → ℝ) (j : Fin N) :
    cavityBaseAmplitude u j = u j := by
  simp only [cavityBaseAmplitude, dite_eq_left j.isLt]

lemma cavityBaseAmplitude_restrict {N : ℕ} (u : Fin N → ℝ) :
    (fun j : Fin N => cavityBaseAmplitude u j) = u :=
  funext (cavityBaseAmplitude_fin u)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The SO correction changes only coordinate signs in the spectral
basis, so every physical projected overlap and quadratic energy agrees. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityOrientationLift_eval {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i =
      (if i=(⟨0,hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)*
        matrixRotation U x i := by
  change ((cavityOrientationSign hN U*(U : Matrix (Fin N) (Fin N) ℝ))*ᵥ x) i = _
  rw [← Matrix.mulVec_mulVec]
  simp only [cavityOrientationSign, Matrix.mulVec_diagonal]
  rfl

lemma cavityOrientationLift_product {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x y : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i *
      specialRotation (cavityOrientationLift hN U) y i =
        matrixRotation U x i * matrixRotation U y i := by
  rw [cavityOrientationLift_eval, cavityOrientationLift_eval]
  split_ifs
  · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
  · ring

lemma cavityOrientationLift_overlap {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap (specialRotation (cavityOrientationLift hN U)) I σ τ =
      projectedOverlap (matrixRotation U) I σ τ := by
  unfold projectedOverlap
  simp_rw [cavityOrientationLift_product]

lemma cavityOrientationLift_jointEntry {N m depth : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × IsingPerceptron.LabeledLeaf depth) :
    spectralJointEntry (specialRotation (cavityOrientationLift hN U)) I depth x y =
      spectralJointEntry (matrixRotation U) I depth x y := by
  funext a
  apply Subtype.ext
  refine Fin.lastCases ?_ (fun j => ?_) a
  · rw [spectralJointEntry_tree, spectralJointEntry_tree]
  · rw [spectralJointEntry_spectral, spectralJointEntry_spectral,
      cavityOrientationLift_overlap]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaProbabilityLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality in law of random Gibbs probabilities transports the full
infinite replica sample, without integrability assumptions on tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma cavity_probability_subtype_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (he : P.map ν = P.map η) :
    P.map (fun ω => (⟨ν ω, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hν.aemeasurable | exact hη.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure X)) =
      P.map (fun ω => (⟨η ω, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hν.aemeasurable | exact hη.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure X)) := by
  apply (MeasurableEmbedding.subtype_coe ProbabilityMeasure.measurableSet_isProbabilityMeasure).map_injective
  rw [Measure.map_map measurable_subtype_coe hν.subtype_mk,
    Measure.map_map measurable_subtype_coe hη.subtype_mk]
  exact he

theorem cavity_replica_lintegral_same_probability_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (he : P.map ν = P.map η)
    (F : (ℕ → X) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P) =
      ∫⁻ ω, ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => η ω) ∂P := by
  let G : ProbabilityMeasure X → ℝ≥0∞ := fun μ =>
    ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => (μ : Measure X))
  have hG : Measurable G :=
    hF.lintegral_kernel (κ := replicaKernel
      (fun μ : ProbabilityMeasure X => (μ : Measure X)) measurable_subtype_coe)
  have hh := congrArg (fun Q : Measure (ProbabilityMeasure X) => ∫⁻ μ, G μ ∂Q)
    (cavity_probability_subtype_law P ν η hν hη he)
  have hν' : Measurable (fun ω => (⟨ν ω, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hν.aemeasurable | exact hη.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure X)) := hν.subtype_mk
  have hη' : Measurable (fun ω => (⟨η ω, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hν.aemeasurable | exact hη.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure X)) := hη.subtype_mk
  exact (lintegral_map (μ := P) hG hν').symm.trans
    (hh.trans (lintegral_map (μ := P) hG hη'))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaDisorderTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica observables retain their external disorder when a Gaussian
Gibbs-probability law is replaced or the external disorder is transported. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

theorem cavity_observed_replica_law_congr {Ω Z X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Measure Z) [IsProbabilityMeasure R]
    (ν η : Ω × Z → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ p, IsProbabilityMeasure (ν p)] [∀ p, IsProbabilityMeasure (η p)]
    (he : ∀ ω, R.map (fun z => ν (ω,z)) = R.map (fun z => η (ω,z)))
    (A : Ω → (ℕ → X) → Y) (hA : Measurable (Function.uncurry A)) :
    (disorderReplicaLaw (P.prod R) ν hν).map (fun p => A p.1.1 p.2) =
      (disorderReplicaLaw (P.prod R) η hη).map (fun p => A p.1.1 p.2) := by
  have hm : Measurable (fun p : (Ω × Z) × (ℕ → X) => A p.1.1 p.2) :=
    hA.comp (measurable_fst.fst.prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro F hF
  have hFm : Measurable (fun p : (Ω × Z) × (ℕ → X) => F (A p.1.1 p.2)) := hF.comp hm
  rw [lintegral_map hF hm, lintegral_map hF hm]
  unfold disorderReplicaLaw
  rw [Measure.lintegral_compProd hFm, Measure.lintegral_compProd hFm]
  have hGν := hFm.lintegral_kernel_prod_right' (κ := replicaKernel ν hν)
  have hGη := hFm.lintegral_kernel_prod_right' (κ := replicaKernel η hη)
  rw [lintegral_prod _ hGν.aemeasurable, lintegral_prod _ hGη.aemeasurable]
  apply lintegral_congr
  intro ω
  exact cavity_replica_lintegral_same_probability_law R
    (fun z => ν (ω,z)) (fun z => η (ω,z))
    (hν.comp measurable_prodMk_left) (hη.comp measurable_prodMk_left) (he ω)
    (fun σ => F (A ω σ)) (hF.comp (hA.comp measurable_prodMk_left))

theorem cavity_observed_replica_law_transport {Ω Ξ Z X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (R : Measure Z) [IsProbabilityMeasure R] (φ : Ω → Ξ) (hφ : MeasurePreserving φ P Q)
    (η : Ξ × Z → Measure X) (hη : Measurable η) [∀ p, IsProbabilityMeasure (η p)]
    (A : Ξ → (ℕ → X) → Y) (hA : Measurable (Function.uncurry A)) :
    (disorderReplicaLaw (P.prod R) (fun p => η (φ p.1,p.2))
      (hη.comp ((hφ.measurable.comp measurable_fst).prodMk measurable_snd))).map
      (fun p => A (φ p.1.1) p.2) =
    (disorderReplicaLaw (Q.prod R) η hη).map (fun p => A p.1.1 p.2) := by
  let ν : Ω × Z → Measure X := fun p => η (φ p.1,p.2)
  have hν : Measurable ν := hη.comp ((hφ.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : (Ξ × Z) × (ℕ → X) => A p.1.1 p.2) :=
    hA.comp (measurable_fst.fst.prodMk measurable_snd)
  have hm' : Measurable (fun p : (Ω × Z) × (ℕ → X) => A (φ p.1.1) p.2) :=
    hA.comp ((hφ.measurable.comp measurable_fst.fst).prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro F hF
  have hFm : Measurable (fun p : (Ξ × Z) × (ℕ → X) => F (A p.1.1 p.2)) := hF.comp hm
  have hFm' : Measurable (fun p : (Ω × Z) × (ℕ → X) => F (A (φ p.1.1) p.2)) := hF.comp hm'
  rw [lintegral_map hF hm', lintegral_map hF hm]
  unfold disorderReplicaLaw
  rw [Measure.lintegral_compProd hFm', Measure.lintegral_compProd hFm]
  have hGν := hFm'.lintegral_kernel_prod_right' (κ := replicaKernel ν hν)
  have hGη := hFm.lintegral_kernel_prod_right' (κ := replicaKernel η hη)
  rw [lintegral_prod _ hGν.aemeasurable, lintegral_prod _ hGη.aemeasurable]
  exact hφ.lintegral_comp hGη.lintegral_prod_right'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete base-rotation array is exactly the namespaced tensor
array after orienting its inverse eigenbasis. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityOrientedBaseLaw_preserving {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) :
    MeasurePreserving (fun V => cavityOrientationLift hN V⁻¹) μ (cavityOrientedBaseLaw hN μ) :=
  ⟨(measurable_cavityOrientationLift hN).comp measurable_inv, rfl⟩

lemma measurable_cavityBaseSOArray {N m depth : ℕ} (I : Fin m → Finset (Fin N)) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree depth) ×
      (ℕ → Spin N × LabeledLeaf depth) => fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation p.1.1) I depth (p.2 ij.1) (p.2 ij.2)) := by
  exact measurable_spectralReplicaArray (Ω := SpecialOrthogonal N × LabeledTree depth)
    (N := N) (m := m) (fun p => p.1) measurable_fst I depth

theorem cavity_orientation_array_law {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (b : ℕ → ℝ) :
    cavityRotationArrayLaw μ (labeledCascadeLaw depth b : Measure (LabeledTree depth)) eig I u =
      tensorNamespacedArrayLaw (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth b
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) := by
  let Ω := Orthogonal N × LabeledTree depth
  let Ξ := SpecialOrthogonal N × LabeledTree depth
  let X := Spin N × LabeledLeaf depth
  let φ : Ω → Ξ := fun p => (cavityOrientationLift hN p.1⁻¹,p.2)
  let ρ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
  let P : Measure Ω := μ.prod ρ
  let Q : Measure Ξ := (cavityOrientedBaseLaw hN μ).prod ρ
  have hφ : MeasurePreserving φ P Q :=
    (cavityOrientedBaseLaw_preserving hN μ).prod (MeasurePreserving.id ρ)
  let η : Ξ × (ℕ → ℝ) → Measure X := tensorNamespacedReference eig (fun _ => 0) I
    (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  have hη : Measurable η := measurable_tensorNamespacedReference (N := N) (m := m) (k := N)
    eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  let ν : Ω × (ℕ → ℝ) → Measure X := cavityRotationProbability eig I u
  have hν : Measurable ν := measurable_cavityRotationProbability (N := N) (m := m) (depth := depth) eig I u
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (ν p) :=
    cavityRotationProbability_probability eig I u p
  let (p : Ξ × (ℕ → ℝ)) : IsProbabilityMeasure (η p) :=
    tensorNamespacedReference_probability eig (fun _ => 0) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j)) depth
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) p
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (η (φ p.1,p.2)) := by
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let A : Ξ → (ℕ → X) → SpectralArray (m+1) := fun p σ ij =>
    spectralJointEntry (specialRotation p.1) I depth (σ ij.1) (σ ij.2)
  have hA : Measurable (Function.uncurry A) := measurable_cavityBaseSOArray I
  let φS : Ω × (ℕ → X) → Ξ × (ℕ → X) := fun p => (φ p.1,p.2)
  have hφS : Measurable φS := hφ.measurable.prodMap measurable_id
  have hAφ : Measurable (Function.uncurry (fun ω => A (φ ω))) := by
    have hh := hA.comp hφS
    exact hh
  let φZ : Ω × (ℕ → ℝ) → Ξ × (ℕ → ℝ) := fun p => (φ p.1,p.2)
  have hφZ : Measurable φZ := hφ.measurable.prodMap measurable_id
  have hηφ : Measurable (fun p : Ω × (ℕ → ℝ) => η (φ p.1,p.2)) := hη.comp hφZ
  have hc := cavity_observed_replica_law_congr (Ω := Ω) (Z := ℕ → ℝ) (X := X)
    (Y := SpectralArray (m+1)) P gaussianCoordinates ν
    (fun p => η (φ p.1,p.2)) hν
    hηφ
    (fun ω => cavity_orientation_tensor_probability_law hN ω.1 ω.2 eig I u)
    (fun ω => A (φ ω)) hAφ
  have ht := cavity_observed_replica_law_transport (Ω := Ω) (Ξ := Ξ) (Z := ℕ → ℝ)
    (X := X) (Y := SpectralArray (m+1)) P Q gaussianCoordinates φ hφ η hη A hA
  have ho : (fun p : (Ω × (ℕ → ℝ)) × (ℕ → X) => A (φ p.1.1) p.2) =
      cavitySampledEntryArray (cavityRotationEntry I) := by
    funext p ij
    exact cavityOrientationLift_jointEntry hN p.1.1.1⁻¹ I (p.2 ij.1) (p.2 ij.2)
  apply Subtype.ext
  change (disorderReplicaLaw (P.prod gaussianCoordinates) ν hν).map
    (cavitySampledEntryArray (cavityRotationEntry I)) =
      (disorderReplicaLaw (Q.prod gaussianCoordinates) η hη).map (fun p => A p.1.1 p.2)
  rw [ho] at hc ht
  exact hc.trans ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBasePerturbedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical base array uses the very same finite perturbation
minimizers as the tensor GG construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_base_perturbed_array_law_oai {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (b : ℕ → ℝ) :
    cavityRotationArrayLaw μ (labeledCascadeLaw depth b : Measure (LabeledTree depth))
      (diagonalPerturbedEigenvalues eig I v t) I (cavityBaseAmplitude u) =
    tensorPerturbedArrayLaw (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I u v t depth b (fun _ => 0) := by
  unfold tensorPerturbedArrayLaw
  simpa only [cavityBaseAmplitude_restrict] using
    cavity_orientation_array_law hN μ (diagonalPerturbedEigenvalues eig I v t) I (cavityBaseAmplitude u) b

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_base_perturbed_array_law_oai := @OAI.InvariantIsing.cavity_base_perturbed_array_law_oai
