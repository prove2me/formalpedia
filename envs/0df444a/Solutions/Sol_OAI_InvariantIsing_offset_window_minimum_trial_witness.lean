-- Prove2me | solution 1 for OAI.InvariantIsing.offset_window_minimum_trial_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:03:06.019557+00:00
-- url     : https://prove2.me/submissions/46f51ad3-9cc9-439d-975e-dcb5bd157eee

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_offset_product_weak_self_consistency
import Theorems.Thm_OAI_InvariantIsing_priorPerturbation_arrayResidual_bound
import Theorems.Thm_OAI_InvariantIsing_priorPerturbation_minimizers_constantDiagonal
import Theorems.Thm_OAI_InvariantIsing_priorPerturbedArrayLaw_ward_limits
import Theorems.Thm_OAI_InvariantIsing_restricted_physical_trial_lower
import Theorems.Thm_OAI_InvariantIsing_restricted_zero_tree_perturbed_array_law

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
/-- d13f23b's `HasLaw.memLp_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.MemLp (f ∘ X) p P := by
  have h : MeasureTheory.MemLp f p (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h
/-- d13f23b's `HasLaw.memLp`: a variable whose law has `id` in `L^p` is in `L^p`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure E} {X : Ω → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hμ : MeasureTheory.MemLp id p μ) :
    MeasureTheory.MemLp X p P := hX.memLp_comp hμ
/-- d13f23b's `HasLaw.integrable_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.integrable_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω}
    {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω}
    {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E} (hX : ProbabilityTheory.HasLaw X μ P)
    (hf : MeasureTheory.Integrable f μ) : MeasureTheory.Integrable (f ∘ X) P := by
  have h : MeasureTheory.Integrable f (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.integrable_map_measure h.aestronglyMeasurable hX.aemeasurable).1 h
end OAICompat434

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
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbationWeight_pos (j : ℕ) : 0 < perturbationWeight j := by
  unfold perturbationWeight
  positivity

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma contactGGRate_eq {N : ℕ} (hN : 0 < N) (j : ℕ) (L B : ℝ) :
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(N:ℝ)^(-3/8:ℝ) +
      (2*B/perturbationWeight j)*(N:ℝ)^(-1/8:ℝ) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(N:ℝ)^(-1/8:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hw := perturbationWeight_pos j
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  have he2 : (perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    unfold perturbationScale
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    norm_num
  have h1 : 1/(Real.sqrt N*(perturbationScale N)^2) = (N:ℝ)^(-3/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  have h2 : contactStep N/(perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    rw [he2]
    unfold contactStep
    rw [← Real.rpow_sub hn]
    norm_num
  have h3 : 1/(Real.sqrt N*(perturbationScale N)^2*contactStep N) = (N:ℝ)^(-1/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2]
    unfold contactStep
    rw [← Real.rpow_add hn,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  calc
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(1/(Real.sqrt N*(perturbationScale N)^2)) +
      (2*B/perturbationWeight j)*(contactStep N/(perturbationScale N)^2) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(1/(Real.sqrt N*(perturbationScale N)^2*contactStep N)) := by
        unfold contactGGRate perturbationAmplitude
        rw [Real.sqrt_div' L hn.le]
        have hn' : (N:ℝ) = (Real.sqrt N)^2 := (Real.sq_sqrt hn.le).symm
        conv_lhs => rw [hn']
        simp only [Real.sqrt_sq hr.le]
        field_simp
        ring
    _ = _ := by rw [h1,h2,h3]

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

lemma contactStep_tendsto : Tendsto contactStep atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/4:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/4) (by norm_num)

lemma contactGGRate_tendsto (j : ℕ) (L B : ℝ) :
    Tendsto (fun N => contactGGRate N j L B) atTop (𝓝 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 3/8) (by norm_num)).const_mul
    (B*(2/perturbationWeight j+1)/perturbationWeight j)
  have h2 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul (2*B/perturbationWeight j)
  have h3 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul
    (16*B*Real.sqrt L/(perturbationWeight j)^2)
  apply Tendsto.congr' _ (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using (h1.add h2).add h3)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div,one_div] using (contactGGRate_eq hN j L B).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_MonomialEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete complete enumeration of the spectral/tree monomials with linear degree cap. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma multidegreeDecode_encode (m : ℕ) (d : Fin m → ℕ) :
    multidegreeDecode m (multidegreeEncode m d) = d := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    funext i
    induction i using Fin.cases with
    | zero => simp only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_zero]
    | succ i =>
      simpa only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_succ,
        Fin.tail] using congrFun (ih (Fin.tail d)) i

lemma multidegreeDecode_sum_le (m j : ℕ) :
    (∑ i, multidegreeDecode m j i) ≤ j := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [multidegreeDecode, Fin.cases_zero, Fin.cases_succ]
    exact (Nat.add_le_add_left (ih (Nat.unpair j).2) _).trans (Nat.unpair_add_le j)

/-- Every nonconstant joint spectral/tree monomial occurs at a fixed
finite index, hence eventually occurs in the truncation through `N`. -/
theorem enumeratedMonomial_surjective (m : ℕ) (d : Fin m → ℕ) (r : ℕ)
    (h : 1 ≤ (∑ a, d a) + r) :
    ∃ j, (∀ a, enumeratedSpectralDegree m j a = d a) ∧ enumeratedTreeDegree m j = r := by
  let v : Fin (m + 1) → ℕ := Fin.lastCases r d
  let c := multidegreeEncode (m + 1) v
  have hc : 1 ≤ c := by
    have hs := multidegreeDecode_sum_le (m + 1) c
    rw [multidegreeDecode_encode] at hs
    rw [Fin.sum_univ_castSucc] at hs
    simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last] at hs
    exact h.trans hs
  refine ⟨c - 1, ?_, ?_⟩
  · intro a
    have he := congrFun (multidegreeDecode_encode (m + 1) v) a.castSucc
    simpa only [enumeratedSpectralDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_castSucc] using he
  · have he := congrFun (multidegreeDecode_encode (m + 1) v) (Fin.last m)
    simpa only [enumeratedTreeDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_last] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron


lemma matrix_sum_le_of_offDiagonal {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j ≤ -ε) :
    ∑ i, ∑ j, B i j ≤ (n : ℝ) * (D - (n - 1 : ℝ) * ε) := by
  classical
  have hrow : ∀ i, ∑ j, B i j ≤ D - (n - 1 : ℝ) * ε := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag i]
    have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
    have h := Finset.sum_le_sum (s := Finset.univ.erase i) (f := fun j => B i j)
      (g := fun _ => -ε) (fun j hj => hoff i j (Ne.symm (Finset.mem_erase.mp hj).1))
    have hcard : (Finset.univ.erase i).card = n - 1 := by simp
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
    linarith
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)

lemma posSemidef_sum_nonneg {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) : 0 ≤ ∑ i, ∑ j, B i j := by
  simpa [dotProduct, Matrix.mulVec] using hB.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))

lemma no_large_negative_block {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hn : 0 < n) (hsize : D < (n - 1 : ℝ) * ε)
    (hB : B.PosSemidef) (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j < -ε) : False := by
  have hs := matrix_sum_le_of_offDiagonal hdiag (fun i j h => (hoff i j h).le)
  have hp := posSemidef_sum_nonneg hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma measurableSet_negative_finite (n : ℕ) (ε : ℝ) :
    MeasurableSet {b : Fin n → Fin n → ℝ | ∀ i j, i ≠ j → b i j < -ε} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => ?_)))
  exact measurableSet_lt
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

lemma mem_negativeBlock_succ {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) {ω : Ω} {ε : ℝ} {n : ℕ} :
    ω ∈ negativeBlock B ε (n + 1) ↔
      ω ∈ negativeBlock B ε n ∧ ∀ i : Fin n, B ω i n < -ε := by
  constructor
  · intro h
    constructor
    · intro i j hij
      exact h i.castSucc j.castSucc (fun he => hij (Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) he)))
    · intro i
      exact h i.castSucc (Fin.last n) (by intro he; have := congrArg Fin.val he; simp at this; omega)
  · rintro ⟨h, ht⟩ i j hij
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · exact h ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun he => hij (Fin.ext (congrArg (fun t : Fin n => t.val) he)))
      · have hjn : j.val = n := by omega
        change B ω i.val j.val < -ε
        rw [hjn]
        exact ht ⟨i.val, hi⟩
    · have hin : i.val = n := by omega
      by_cases hj : j.val < n
      · change B ω i.val j.val < -ε
        rw [hin, hsym]
        exact ht ⟨j.val, hj⟩
      · have hjn : j.val = n := by omega
        exact (hij (Fin.ext (hin.trans hjn.symm))).elim

lemma negativeBlock_two {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) (ε : ℝ) :
    negativeBlock B ε 2 = {ω | B ω 0 1 < -ε} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h
    · change B ω 1 0 < -ε
      rw [hsym]
      exact h
    · exact (hij rfl).elim

lemma negativeBlock_next_probability {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (ε : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    μ.real (negativeBlock B ε n) * μ.real {ω | B ω 0 1 < -ε} ≤
      μ.real (negativeBlock B ε (n + 1)) := by
  classical
  let A := negativeBlock B ε n
  let Bad := fun i : Fin n => A ∩ {ω | -ε ≤ B ω i n}
  have hbase : μ.real {ω | -ε ≤ B ω 0 1} = 1 - μ.real {ω | B ω 0 1 < -ε} := by
    have hset : {ω | -ε ≤ B ω 0 1} = {ω | B ω 0 1 < -ε}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_lt (hm 0 1) measurable_const), probReal_univ]
  have hbad : ∀ i : Fin n, μ.real (Bad i) =
      μ.real A * (1 - μ.real {ω | B ω 0 1 < -ε}) / n := by
    intro i
    have h := hGG n hn i {b | ∀ i j, i ≠ j → b i j < -ε}
      (measurableSet_negative_finite n ε) (Set.Ici (-ε)) measurableSet_Ici
    have hp : arrayBlock B n ⁻¹' {b | ∀ i j, i ≠ j → b i j < -ε} = A := rfl
    rw [hp] at h
    have hz : ∀ j ∈ Finset.univ.erase i,
        A ∩ {ω | B ω i j ∈ Set.Ici (-ε)} = ∅ := by
      intro j hj
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hω, hω'⟩
      exact (not_le_of_gt (hω i j (Ne.symm (Finset.mem_erase.mp hj).1))) hω'
    have hzero : (∑ j ∈ Finset.univ.erase i,
        μ.real (A ∩ {ω | B ω i j ∈ Set.Ici (-ε)})) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j hj, measureReal_empty]
    rw [hzero] at h
    simp only [zero_div, add_zero, Set.mem_Ici] at h
    simpa only [Bad, hbase] using h
  have hsub : A ⊆ negativeBlock B ε (n + 1) ∪ ⋃ i : Fin n, Bad i := by
    intro ω hω
    by_cases ht : ∀ i : Fin n, B ω i n < -ε
    · exact Or.inl ((mem_negativeBlock_succ hsym).mpr ⟨hω, ht⟩)
    · right
      push Not at ht
      obtain ⟨i, hi⟩ := ht
      exact Set.mem_iUnion.mpr ⟨i, hω, hi⟩
  have hbound := (measureReal_mono (μ := μ) hsub).trans
    (measureReal_union_le (negativeBlock B ε (n + 1)) (⋃ i : Fin n, Bad i))
  have hsum := measureReal_iUnion_fintype_le Bad (μ := μ)
  simp_rw [hbad] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mul_div_left_comm, div_self hn', mul_one] at hsum
  nlinarith

lemma gg_negative_probability_zero {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | B ω 0 1 < -ε} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  by_contra hbne
  have hb : 0 < μ.real {ω | B ω 0 1 < -ε} :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hbne)
  have hblocks : ∀ k : ℕ, 0 < μ.real (negativeBlock B ε (k + 2)) := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add, negativeBlock_two hsym] using hb
    | succ k ih =>
      have h := negativeBlock_next_probability hm hsym hGG ε (k + 2) (by omega)
      exact (mul_pos ih hb).trans_le (by simpa only [Nat.succ_add] using h)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (D / ε)
  have hsize : D < ((m + 2 : ℕ) - 1 : ℝ) * ε := by
    have h := (div_lt_iff₀ hε).mp hmgt
    simp only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hnull : μ (negativeBlock B ε (m + 2)) = 0 := by
    have ha : ∀ᵐ ω ∂μ, ω ∉ negativeBlock B ε (m + 2) := by
      filter_upwards [hGram, hdiag] with ω hg hd
      intro hn
      exact no_large_negative_block (by omega : 0 < m + 2) hsize (hg (m + 2))
        (fun i => hd i) hn
    simpa using ae_iff.mp ha
  have hpos := hblocks m
  rw [Measure.real, hnull, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

 

theorem gg_pair_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  have ha : ∀ k : ℕ, ∀ᵐ ω ∂μ, -(1 / (k + 1 : ℝ)) ≤ B ω 0 1 := by
    intro k
    rw [ae_iff]
    simp only [not_le]
    exact gg_negative_probability_zero hm hsym hGG hGram hdiag (by positivity)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  simp only [neg_zero] at hlim
  exact le_of_tendsto' hlim hω



lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm


lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMinimumRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing rates for diagonal perturbation energies at parameter minima. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma diagonalContactRate_eq {N : ℕ} (hN : 0 < N) (L : ℝ) :
    diagonalContactRate N L = (3 / 2) * (N : ℝ) ^ (-7 / 16 : ℝ) +
      (1 + 8 * Real.sqrt L) * (N : ℝ) ^ (-3 / 16 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have h1 : 1 / (Real.sqrt N * perturbationScale N) = (N : ℝ) ^ (-7 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, ← Real.rpow_add hn,
      one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  have h2 : contactStep N / perturbationScale N = (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [contactStep, perturbationScale, ← Real.rpow_sub hn]
    congr 1
    norm_num
  have h3 : 1 / (Real.sqrt N * perturbationScale N * contactStep N) =
      (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, contactStep,
      ← Real.rpow_add hn, ← Real.rpow_add hn, one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  calc
    _ = (3 / 2) * (1 / (Real.sqrt N * perturbationScale N)) +
        contactStep N / perturbationScale N +
        8 * Real.sqrt L * (1 / (Real.sqrt N * perturbationScale N * contactStep N)) := by
      unfold diagonalContactRate
      rw [Real.sqrt_div' L hn.le]
      have hn' : (N : ℝ) = (Real.sqrt N) ^ 2 := (Real.sq_sqrt hn.le).symm
      conv_lhs => rw [hn']
      simp only [Real.sqrt_sq hr.le]
      field_simp
      ring
    _ = _ := by rw [h1, h2, h3]; ring

lemma diagonalContactRate_tendsto (L : ℝ) :
    Tendsto (fun N => diagonalContactRate N L) atTop (nhds 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 7 / 16) (by norm_num)).const_mul (3 / 2 : ℝ)
  have h2 := (tendsto_nat_rpow_neg (c := 3 / 16) (by norm_num)).const_mul (1 + 8 * Real.sqrt L)
  apply Tendsto.congr' _ (show Tendsto _ _ (nhds (0 : ℝ)) from by simpa using h1.add h2)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div] using (diagonalContactRate_eq hN L).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGGRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete tensor GG rate tends to zero for every fixed monomial. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma tensorContactGGRate_tendsto (j m : ℕ) (L B : ℝ) :
    Tendsto (fun N => tensorContactGGRate N j m L B) atTop (nhds 0) := by
  have h := (contactGGRate_tendsto j L B).add
    ((diagonalContactRate_tendsto L).const_mul (2 * B * ∑ a, (enumeratedSpectralDegree m j a : ℝ)))
  simpa only [tensorContactGGRate, mul_zero, add_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
namespace IsingPerceptron

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma HasGhirlandaGuerra.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {B C : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (he : B =ᵐ[μ] C) :
    HasGhirlandaGuerra C μ := by
  have hm (P : RealArray → Prop) : μ.real {ω | P (C ω)} = μ.real {ω | P (B ω)} := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    change P (C ω) = P (B ω)
    rw [hω]
  intro n hn i A hA t ht
  change μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i n ∈ t} =
    (μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A} * μ.real {ω | C ω 0 1 ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) / n
  rw [hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i n ∈ t),
    hm (fun b => (fun j k : Fin n => b j k) ∈ A), hm (fun b => b 0 1 ∈ t)]
  have hs : (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) =
      ∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A ∧ B ω i j ∈ t} := by
    apply Finset.sum_congr rfl
    intro j _
    exact hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i j ∈ t)
  rw [hs]
  exact h n hn i A hA t ht

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

lemma GramDiagonal.default {D : ℝ} (hD : 0 ≤ D) :
    GramDiagonal D (fun i j => if i=j then D else 0) := by
  constructor
  · intro n
    have he : (fun i j : Fin n => if (i:ℕ)=(j:ℕ) then D else 0) =
        Matrix.diagonal (fun _ : Fin n => D) := by
      ext i j
      simp only [Matrix.diagonal_apply,Fin.val_inj]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun _ => hD)
  · intro i
    simp



lemma gg_pair_nonnegative_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have ht := gg_pair_nonnegative (fun i j => by fun_prop) (fun ω => (hCG ω).symm)
    (hgg.congr_ae he) (ae_of_all _ (fun ω => (hCG ω).1)) (ae_of_all _ (fun ω => (hCG ω).2))
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) :
    Continuous (spectralEntryMonomial d) := by
  exact continuous_finsetProd _ fun a _ => ((continuous_apply a).subtype_val).pow _

lemma continuous_spectralBlockView (m n : ℕ) : Continuous (spectralBlockView m n) := by
  unfold spectralBlockView
  fun_prop

lemma continuous_spectralBlockLink (m n i j : ℕ) : Continuous (spectralBlockLink m n i j) :=
  (continuous_spectralBlockView m n).prodMk (continuous_apply _)

private lemma continuous_spectralBlockPairCoordinate (m n : ℕ)
    (i : ((Fin n × Fin n) × Fin m) ⊕ Fin m) :
    Continuous (spectralBlockPairCoordinate m n i) := by
  cases i <;> unfold spectralBlockPairCoordinate <;> fun_prop

private lemma spectralBlockPairCoordinate_ext (m n : ℕ)
    (x y : SpectralBlock m n × SpectralEntry m)
    (h : ∀ i, spectralBlockPairCoordinate m n i x = spectralBlockPairCoordinate m n i y) : x = y := by
  apply Prod.ext
  · funext i j a
    exact Subtype.ext (h (.inl ((i, j), a)))
  · funext a
    exact Subtype.ext (h (.inr a))

/-- Polynomial moments in the new link, with arbitrary continuous tests
of the old block, determine its full joint law. -/
theorem spectralBlock_pair_monomials_unique (m n : ℕ)
    (P Q : Measure (SpectralBlock m n × SpectralEntry m)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (∫ x, D x.1 * spectralEntryMonomial d x.2 ∂P) =
        ∫ x, D x.1 * spectralEntryMonomial d x.2 ∂Q) : P = Q := by
  classical
  have : TopologicalSpace.SeparableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  let I := ((Fin n × Fin n) × Fin m) ⊕ Fin m
  let g : I → ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨spectralBlockPairCoordinate m n i, continuous_spectralBlockPairCoordinate m n i⟩
  let ev : MvPolynomial I ℝ →ₐ[ℝ] ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : I) (x : SpectralBlock m n × SpectralEntry m) :
      g i x = spectralBlockPairCoordinate m n i x := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i : I, spectralBlockPairCoordinate m n i x ≠
        spectralBlockPairCoordinate m n i y := by
      by_contra! hno
      exact hxy (spectralBlockPairCoordinate_ext m n x y hno)
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using hi
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    let D : SpectralBlock m n → ℝ := fun b =>
      ∏ i : (Fin n × Fin n) × Fin m, (b i.1.1 i.1.2 i.2 : ℝ) ^ k (.inl i)
    have hD : Continuous D := by
      apply continuous_finsetProd
      intro i _
      exact (by fun_prop : Continuous (fun b : SpectralBlock m n => (b i.1.1 i.1.2 i.2 : ℝ))).pow _
    have he (x : SpectralBlock m n × SpectralEntry m) :
        ev (MvPolynomial.monomial k c) x = c * (D x.1 * spectralEntryMonomial (fun a => k (.inr a)) x.2) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_pow]
      simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply,
        BoundedContinuousFunction.coe_prod, BoundedContinuousFunction.coe_pow,
        BoundedContinuousFunction.algebraMap_apply, Finset.prod_apply, Pi.pow_apply, smul_eq_mul, mul_one]
      change c * (∏ i : I, g i x ^ k i) = _
      rw [Fintype.prod_sum_type]
      rfl
    change (∫ x, ev (MvPolynomial.monomial k c) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k c) x ∂Q
    simp only [he, integral_const_mul]
    exact congrArg (c * ·) (h D hD _)

theorem spectral_monomial_measure_identity (m : ℕ) (μ : Measure (SpectralArray m))
    [IsProbabilityMeasure μ] (n : ℕ) (i : Fin n)
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    (n : ℝ≥0∞) • μ.map (spectralBlockLink m n i n) =
      (μ.map (spectralBlockView m n)).prod (μ.map (fun x => x (0, 1))) +
        ∑ j ∈ Finset.univ.erase i, μ.map (spectralBlockLink m n i j) := by
  classical
  let block := μ.map (spectralBlockView m n)
  let pair := μ.map (fun x => x (0, 1))
  let link := fun j : ℕ => μ.map (spectralBlockLink m n i j)
  have : IsProbabilityMeasure block := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockView m n).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure pair := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply (0, 1)).aemeasurable).mpr inferInstance
  have (j : ℕ) : IsProbabilityMeasure (link j) := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockLink m n i j).measurable.aemeasurable).mpr inferInstance
  change (n : ℝ≥0∞) • link n = block.prod pair + ∑ j ∈ Finset.univ.erase i, link j
  have : IsFiniteMeasure ((n : ℝ≥0∞) • link n) := (link n).smul_finite (by simp)
  apply spectralBlock_pair_monomials_unique m n
  intro D hD d
  let F : SpectralBlock m n × SpectralEntry m → ℝ := fun x => D x.1 * spectralEntryMonomial d x.2
  have hF : Continuous F := (hD.comp continuous_fst).mul
    ((continuous_spectralEntryMonomial d).comp continuous_snd)
  have hi (j : ℕ) : (∫ x, F x ∂link j) =
      ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ :=
    integral_map (continuous_spectralBlockLink m n i j).measurable.aemeasurable hF.aestronglyMeasurable
  change (∫ x, F x ∂(n : ℝ≥0∞) • link n) = ∫ x, F x ∂(block.prod pair + ∑ j ∈ Finset.univ.erase i, link j)
  rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    integral_add_measure (compact_integrable hF) (compact_integrable hF),
    integral_finsetSum_measure (fun j _ => compact_integrable hF), hi]
  simp_rw [hi]
  rw [h D hD d]
  congr 1
  have hp := continuous_spectralEntryMonomial d
  have he : (∫ x, F x ∂block.prod pair) =
      (∫ b, D b ∂block) * (∫ x, spectralEntryMonomial d x ∂pair) :=
    integral_prod_mul D (spectralEntryMonomial d)
  rw [he, integral_map (continuous_spectralBlockView m n).measurable.aemeasurable hD.aestronglyMeasurable,
    integral_map (measurable_pi_apply (0, 1)).aemeasurable hp.aestronglyMeasurable]

theorem spectral_monomialGG_measurable (m : ℕ) (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (h : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) μ := by
  classical
  intro n hn i A hA t ht
  have he := congrArg (fun ν : Measure (SpectralBlock m n × SpectralEntry m) => (ν (A ×ˢ t)).toReal)
    (spectral_monomial_measure_identity m μ n i (h n hn i))
  have hmap : ∀ j : ℕ, Measurable (spectralBlockLink m n i j) := fun j =>
    (continuous_spectralBlockLink m n i j).measurable
  have hblock := (continuous_spectralBlockView m n).measurable
  have hpair : Measurable (fun x : SpectralArray m => x (0, 1)) := measurable_pi_apply _
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    Measure.add_apply, Measure.prod_prod, Measure.finsetSum_apply,
    Measure.map_apply (hmap _) (hA.prod ht), Measure.map_apply hblock hA, Measure.map_apply hpair ht] at he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at he
  change (n : ℝ) * μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t} +
    ∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t}) at he
  change μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    (μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t})) / n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]
  nlinarith [he]

lemma spectralMonomialResidual_zero {m : ℕ} (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) :
    spectralMonomialResidual μ n i D 0 = 0 := by
  classical
  have hn : 1 ≤ n := by have hi := i.isLt; omega
  simp only [spectralMonomialResidual, spectralEntryMonomial, Pi.zero_apply, pow_zero,
    Finset.prod_const_one, mul_one, integral_const, probReal_univ, one_smul,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
  ring

lemma spectralMonomialResidual_weak_limit {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) (hD : Continuous D) (d : Fin m → ℕ) :
    Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop
      (𝓝 (spectralMonomialResidual μ n i D d)) := by
  have hI : ∀ F : SpectralArray m → ℝ, Continuous F →
      Tendsto (fun N => ∫ x, F x ∂(L N : Measure (SpectralArray m))) atTop
        (𝓝 (∫ x, F x ∂(μ : Measure (SpectralArray m)))) := by
    intro F hF
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hcD := hD.comp (continuous_spectralBlockView m n)
  have ht (j : ℕ) := hI (fun x => D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)))
    (hcD.mul ((continuous_spectralEntryMonomial d).comp (continuous_apply _)))
  exact (((ht n).const_mul (n : ℝ)).sub ((hI _ hcD).mul
    (hI _ ((continuous_spectralEntryMonomial d).comp (continuous_apply _))))).sub
      (tendsto_finsetSum _ fun j _ => ht j)

/-- Vanishing monomial residuals imply the Ghirlanda–Guerra identities
for the weak limit of the spectral overlap arrays. -/
theorem spectralGG_of_weak_monomial_residuals {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectral_monomialGG_measurable
  intro n hn i D hD d
  have he := tendsto_nhds_unique (spectralMonomialResidual_weak_limit hL n i D hD d)
    (hg n hn i D hD d)
  dsimp only [spectralMonomialResidual] at he
  linarith

theorem spectralGG_of_weak_nonconstant_monomial_residuals {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray m)} {μ : ProbabilityMeasure (SpectralArray m)}
    (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D →
      ∀ d : Fin m → ℕ, d ≠ 0 →
        Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectralGG_of_weak_monomial_residuals hL
  intro n hn i D hD d
  by_cases hd : d = 0
  · subst d
    simpa only [spectralMonomialResidual_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact hg n hn i D hD d hd

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every weak spectral-array limit of actual finite perturbation minimizers
satisfies the full vector Ghirlanda–Guerra identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma enumeratedJointMonomial_surjective (m : ℕ) (d : Fin (m + 1) → ℕ) (hd : d ≠ 0) :
    ∃ j, (fun a => Fin.lastCases (enumeratedTreeDegree m j) (enumeratedSpectralDegree m j) a) = d := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, d a ≠ 0 := by
    by_contra! h
    exact hd (funext h)
  have hs : 1 ≤ ∑ a, d a :=
    (Nat.one_le_iff_ne_zero.mpr ha).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  rw [Fin.sum_univ_castSucc] at hs
  obtain ⟨j, hj, hr⟩ := enumeratedMonomial_surjective m (fun a => d a.castSucc) (d (Fin.last m)) hs
  refine ⟨j, ?_⟩
  funext a
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [Fin.lastCases_last] using hr
  · simpa only [Fin.lastCases_castSucc] using hj b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRows
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian rows used to generate the finite fresh frames. Their empirical
Gram matrices converge almost surely to the identity at fixed frame width. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma cavityGaussianRow_eval_law {q : ℕ} (i : Fin q) :
    HasLaw (fun x : Fin q → ℝ => x i) (gaussianReal 0 1) (cavityGaussianRow q) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin q => gaussianReal 0 1) i).map_eq⟩

lemma cavityGaussianRow_product_integrable {q : ℕ} (i j : Fin q) :
    Integrable (fun x : Fin q → ℝ => x i * x j) (cavityGaussianRow q) := by
  have hi : MemLp (fun x : Fin q → ℝ => x i) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law i).memLp (memLp_id_gaussianReal 2)
  have hj : MemLp (fun x : Fin q → ℝ => x j) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law j).memLp (memLp_id_gaussianReal 2)
  exact hi.integrable_mul hj

lemma cavityGaussianRow_product_integral {q : ℕ} (i j : Fin q) :
    (∫ x : Fin q → ℝ, x i * x j ∂cavityGaussianRow q) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hvar := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id.aemeasurable] at hvar
    simp only [id_eq, integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hvar
    have hl := (cavityGaussianRow_eval_law i).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa only [pow_two, Function.comp_apply, ite_true, if_true] using hl.trans hvar
  · have hi : iIndepFun (fun k : Fin q => fun x : Fin q → ℝ => x k) (cavityGaussianRow q) :=
      iIndepFun_pi (fun _ => aemeasurable_id)
    have h := (hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    have hm k : (∫ x : Fin q → ℝ, x k ∂cavityGaussianRow q) = 0 := by
      simpa only [Function.comp_apply, integral_id_gaussianReal] using
        (cavityGaussianRow_eval_law k).integral_comp (f := fun x : ℝ => x) (by fun_prop)
    simpa only [hm, zero_mul, ite_eq_right hij] using h

lemma cavityGaussianRows_eval_law (q n : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x n) (cavityGaussianRow q) (cavityGaussianRows q) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  exact Measure.infinitePi_map_eval (fun _ : ℕ => cavityGaussianRow q) n

/-- The fixed-width Gaussian Gram matrix tends to the identity. -/
theorem cavityGaussianRows_gram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n i j => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hp (i j : Fin q) : ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (if i = j then 1 else 0)) := by
    let f := fun x : Fin q → ℝ => x i * x j
    have hf : Measurable f := by fun_prop
    have hind : iIndepFun (fun k => fun x : ℕ → Fin q → ℝ => f (x k)) (cavityGaussianRows q) :=
      iIndepFun_infinitePi (fun _ => hf)
    have hid (k : ℕ) : IdentDistrib (fun x : ℕ → Fin q → ℝ => x k)
        (fun x : ℕ → Fin q → ℝ => x 0) (cavityGaussianRows q) (cavityGaussianRows q) :=
      ⟨(cavityGaussianRows_eval_law q k).aemeasurable,
        (cavityGaussianRows_eval_law q 0).aemeasurable,
        (cavityGaussianRows_eval_law q k).map_eq.trans (cavityGaussianRows_eval_law q 0).map_eq.symm⟩
    have hmean : (∫ x, f (x 0) ∂cavityGaussianRows q) = if i = j then 1 else 0 := by
      exact ((cavityGaussianRows_eval_law q 0).integral_comp hf.aestronglyMeasurable).trans
        (cavityGaussianRow_product_integral i j)
    have h := strong_law_ae_real (fun k (x : ℕ → Fin q → ℝ) => f (x k))
      ((cavityGaussianRows_eval_law q 0).integrable_comp (cavityGaussianRow_product_integrable i j))
      (fun k l hkl => hind.indepFun hkl) (fun k => (hid k).comp hf)
    simpa only [hmean, f] using h
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hp i))] with x hx
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.one_apply] using hx i j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGram
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma cavityEmpiricalGram_posSemidef {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityEmpiricalGram x n).PosSemidef := by
  have he : cavityEmpiricalGram x n =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Matrix.vecMulVec (x k) (x k) := by
    ext i j
    simp only [cavityEmpiricalGram, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  apply (Matrix.posSemidef_sum (Finset.range n) (fun k _ => ?_)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (x k)

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

lemma cavityEmpiricalGram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (cavityEmpiricalGram x) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) :=
  cavityGaussianRows_gram_tendsto q

/-- Almost every Gaussian row sequence yields nondegenerate Gram matrices
at all sufficiently large sample sizes. -/
theorem cavityEmpiricalGram_eventually_posDef (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q, ∀ᶠ n in atTop, (cavityEmpiricalGram x n).PosDef := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  have hdet : Tendsto (fun n => (cavityEmpiricalGram x n).det) atTop (𝓝 (1 : ℝ)) := by
    have hd : Continuous (fun G : Matrix (Fin q) (Fin q) ℝ => G.det) :=
      continuous_id.matrix_det
    have ht := (hd.tendsto (1 : Matrix (Fin q) (Fin q) ℝ)).comp hx
    change Tendsto (fun n => (cavityEmpiricalGram x n).det) atTop
      (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ).det) at ht
    simpa only [Matrix.det_one] using ht
  filter_upwards [hdet.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  exact cavity_posDef_of_posSemidef_det_ne_zero (cavityEmpiricalGram_posSemidef x n)
    (ne_of_gt (show 0 < (cavityEmpiricalGram x n).det from hn))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGramProbability
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nondegenerate Gaussian frames have probability tending to one.
This also supplies the positive mass needed to condition the finite frame
construction, without any assertion about zero sets of polynomials. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_cavityEmpiricalGram (q n : ℕ) :
    Continuous (fun x : ℕ → Fin q → ℝ => cavityEmpiricalGram x n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold cavityEmpiricalGram
  fun_prop

lemma measurableSet_cavityGoodGram (q n : ℕ) : MeasurableSet (cavityGoodGram q n) :=
  measurableSet_lt measurable_const (continuous_cavityEmpiricalGram q n).matrix_det.measurable

lemma cavityGoodGram_ae_eventually (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q, ∀ᶠ n in atTop, x ∈ cavityGoodGram q n := by
  filter_upwards [cavityEmpiricalGram_eventually_posDef q] with x hx
  filter_upwards [hx] with n hn
  exact hn.det_pos

theorem cavityGoodGram_probability_tendsto (q : ℕ) :
    Tendsto (fun n => (cavityGaussianRows q).real (cavityGoodGram q n)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => ∫ x, (cavityGoodGram q n).indicator
      (fun _ => (1 : ℝ)) x ∂cavityGaussianRows q) atTop
      (𝓝 (∫ _x, (1 : ℝ) ∂cavityGaussianRows q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact aestronglyMeasurable_const.indicator (measurableSet_cavityGoodGram q n)
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun x => by
        by_cases hx : x ∈ cavityGoodGram q n <;> simp [hx])
    · filter_upwards [cavityGoodGram_ae_eventually q] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp only [Set.indicator_of_mem hn]
  have he (n : ℕ) : (∫ x, (cavityGoodGram q n).indicator (fun _ => (1 : ℝ)) x
      ∂cavityGaussianRows q) = (cavityGaussianRows q).real (cavityGoodGram q n) :=
    integral_indicator_one (measurableSet_cavityGoodGram q n)
  simp_rw [he] at hi
  simpa using hi

lemma cavityGoodGram_eventually_positive (q : ℕ) :
    ∀ᶠ n in atTop, 0 < (cavityGaussianRows q).real (cavityGoodGram q n) :=
  (cavityGoodGram_probability_tendsto q).eventually
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning on the nondegenerate Gram event does not change the
limit of bounded observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_conditioning_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (f : Ω → Ω') (hf : Measurable f)
    (s : Set Ω') (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul, Measure.map_apply hf hs,
    Measure.restrict_map hf hs]

lemma cavity_conditioning_invariant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : Measurable T) (hμ : μ.map T = μ)
    (s : Set Ω) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s) :
    (cond μ s).map T = cond μ s := by
  have hr : (μ.restrict s).map T = μ.restrict s := by
    calc
      (μ.restrict s).map T = (μ.restrict (T ⁻¹' s)).map T := by rw [hinv]
      _ = (μ.map T).restrict s := (Measure.restrict_map hT hs).symm
      _ = μ.restrict s := by rw [hμ]
  rw [ProbabilityTheory.cond, Measure.map_smul, hr]

lemma cavity_conditioning_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)
    (hp : 0 < μ.real s) (f : Ω → ℝ) (hf : Integrable f μ)
    (M : ℝ) (hbound : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ| ≤ 2 * M * (1 - μ.real s) := by
  let p := μ.real s
  have hp1 : p ≤ 1 := measureReal_le_one
  have hpc : μ.real sᶜ = 1 - p := by
    simpa only [p, Measure.real, measure_univ, ENNReal.toReal_one] using
      (measureReal_compl (μ := μ) hs)
  have hA : |∫ x in s, f x ∂μ| ≤ p * M := by
    simpa only [Real.norm_eq_abs, mul_comm, p] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ s)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hB : |∫ x in sᶜ, f x ∂μ| ≤ M * (1 - p) := by
    simpa only [Real.norm_eq_abs, hpc, mul_comm] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ sᶜ)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfac : 0 ≤ p⁻¹ - 1 := by
    have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp).mpr hp1
    linarith
  have hmul : (p⁻¹ - 1) * p = 1 - p := by
    rw [sub_mul, inv_mul_cancel₀ hp.ne', one_mul]
  have he : (∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ =
      (p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      ← integral_add_compl hs hf]
    change p⁻¹ • (∫ x in s, f x ∂μ) - _ = _
    simp only [smul_eq_mul]
    ring
  rw [he]
  calc
    |(p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ| ≤
        (p⁻¹ - 1) * |∫ x in s, f x ∂μ| + |∫ x in sᶜ, f x ∂μ| := by
      simpa only [abs_mul, abs_of_nonneg hfac] using
        abs_sub ((p⁻¹ - 1) * (∫ x in s, f x ∂μ)) (∫ x in sᶜ, f x ∂μ)
    _ ≤ (p⁻¹ - 1) * (p * M) + M * (1 - p) :=
      add_le_add (mul_le_mul_of_nonneg_left hA hfac) hB
    _ = 2 * M * (1 - p) := by rw [← mul_assoc, hmul]; ring

theorem cavity_conditioning_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n))
    (hp : Tendsto (fun n => μ.real (s n)) atTop (𝓝 1))
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (M : ℝ) (hbound : ∀ n x, |f n x| ≤ M) :
    Tendsto (fun n => (∫ x, f n x ∂cond μ (s n)) - ∫ x, f n x ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun n => 2 * M * (1 - μ.real (s n)))
  · filter_upwards [hp.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    simpa only [Real.norm_eq_abs] using
      cavity_conditioning_bound μ (s n) (hs n) hn (f n) (hf n) M (hbound n)
  · simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp).const_mul
        (2 * M)

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

lemma cavityGaussianMatrix_gram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n =
      cavityEmpiricalGram x n := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityGaussianMatrix]
  simp_rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [← Finset.sum_div]
  change (∑ k : Fin n, x k i * x k j) / (n : ℝ) =
    (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => x k i * x k j) n

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
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

lemma cavityRotationMatrix_apply {n : ℕ} (U : Rotation n)
    (x : EuclideanSpace ℝ (Fin n)) : matrixRotation (cavityRotationMatrix U) x = U x := by
  have h := U.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis x
  ext i
  exact congrFun h i

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

theorem cavityFrame_transitive {n q : ℕ} (A B : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    ∃ U : Orthogonal n, (U : Matrix (Fin n) (Fin n) ℝ) * A = B := by
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _
    (cavity_orthonormal_of_gram A hA) (cavity_orthonormal_of_gram B hB)
  refine ⟨cavityRotationMatrix U, ?_⟩
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (hU j)
  rw [← cavityRotationMatrix_apply U] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The correction used to orthonormalize a fixed number of Gaussian
columns converges to the identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gram_sqrt_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => CFC.sqrt (G n)) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hw : Tendsto G atTop (𝓝[{A : Matrix (Fin q) (Fin q) ℝ | 0 ≤ A}] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hG n).nonneg)⟩
  have hOne : (0 : Matrix (Fin q) (Fin q) ℝ) ≤ 1 := Matrix.PosSemidef.one.nonneg
  have hc := (CFC.continuousOn_sqrt (A := Matrix (Fin q) (Fin q) ℝ)).continuousWithinAt hOne
  have ht := hc.tendsto.comp hw
  change Tendsto (fun n => CFC.sqrt (G n)) atTop
    (𝓝 (CFC.sqrt (1 : Matrix (Fin q) (Fin q) ℝ))) at ht
  simpa only [CFC.sqrt_one] using ht

lemma cavity_gram_correction_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
      (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hc : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) 1 := by
    have hr : ContinuousAt (Ring.inverse : ℝ → ℝ) 1 := by
      simpa only [Units.val_one] using NormedRing.inverse_continuousAt (1 : ℝˣ)
    exact continuousAt_matrix_inv _ (by simpa only [Matrix.det_one] using hr)
  have ht := hc.tendsto.comp (cavity_gram_sqrt_tendsto G hG hlim)
  change Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
    (𝓝 ((1 : Matrix (Fin q) (Fin q) ℝ)⁻¹)) at ht
  simpa only [inv_one] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGaussian
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-dimensional laws of the independent Gaussian array used
in the fresh-frame construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma cavityGaussianRows_coordinate_law {q : ℕ} (k : ℕ) (i : Fin q) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x k i) (gaussianReal 0 1)
      (cavityGaussianRows q) :=
  (cavityGaussianRow_eval_law i).fun_comp (cavityGaussianRows_eval_law q k)

lemma cavityGaussianRows_coordinates_independent (q : ℕ) :
    iIndepFun (fun p : ℕ × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := by
  simpa only [cavityGaussianRows, cavityGaussianRow, Measure.infinitePi_eq_pi] using
    iIndepFun_uncurry_infinitePi' (fun (_ : ℕ) (_ : Fin q) => gaussianReal 0 1)
      (X := fun _ _ x => x) (fun _ _ => measurable_id)

lemma cavityGaussianRows_finite_array_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => fun p : Fin n × Fin q => x p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1))
      (cavityGaussianRows q) := by
  have hinj : Function.Injective (fun p : Fin n × Fin q => ((p.1 : ℕ), p.2)) := by
    intro p r h
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Fin q => z.1) h))
      (congrArg (fun z : ℕ × Fin q => z.2) h)
  have hind : iIndepFun
      (fun p : Fin n × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := (cavityGaussianRows_coordinates_independent q).precomp hinj
  refine ⟨(measurable_pi_iff.mpr (fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ)))).aemeasurable, ?_⟩
  have hm := hind.map_fun_eq_pi_map (fun (p : Fin n × Fin q) =>
    (cavityGaussianRows_coordinate_law (p.1 : ℕ) p.2).aemeasurable)
  simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm

theorem cavityGaussianRows_finite_standard_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin q)))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityGaussianRows q) := by
  have ht : HasLaw (WithLp.toLp 2 : (Fin n × Fin q → ℝ) →
      EuclideanSpace ℝ (Fin n × Fin q))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact ht.fun_comp (cavityGaussianRows_finite_array_law n q)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal equivariance of the Gaussian frame normalization. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityGram_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (U * A).transpose * (U * A) = A.transpose * A := by
  rw [Matrix.transpose_mul]
  calc
    A.transpose * U.transpose * (U * A) = A.transpose * (U.transpose * U) * A := by
      simp only [Matrix.mul_assoc]
    _ = A.transpose * A := by rw [hU, Matrix.mul_one]

lemma cavityNormalizeFrame_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    cavityNormalizeFrame (U * A) = U * cavityNormalizeFrame A := by
  simp only [cavityNormalizeFrame, cavityGram_left_orthogonal A U hU, Matrix.mul_assoc]


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal invariance of the finite Gaussian array, expressed as a
simultaneous rotation of all its columns. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

lemma cavityColumnRotation_apply {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (k : Fin n) (j : Fin q) :
    cavityColumnRotation q U x (k, j) =
      U (WithLp.toLp 2 (fun i : Fin n => x (i, j))) k := rfl

theorem cavityColumnRotation_gaussian {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map (cavityColumnRotation q U) =
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) :=
  stdGaussian_map (cavityColumnRotation q U)

lemma cavityArrayMatrix_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityArrayMatrix n q z := by
  ext k j
  simp only [cavityArrayMatrix, cavityColumnRotation_apply, matrixRotation_apply,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

lemma cavityArrayFrame_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityNormalizeFrame (cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z)) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityNormalizeFrame (cavityArrayMatrix n q z) := by
  rw [cavityArrayMatrix_rotation]
  exact cavityNormalizeFrame_left_orthogonal _ _
    ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditionedFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityArrayMatrix (n q : ℕ) :
    Measurable (cavityArrayMatrix n q) := by
  unfold cavityArrayMatrix
  fun_prop

lemma measurableSet_cavityArrayGood (n q : ℕ) : MeasurableSet (cavityArrayGood n q) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
      (cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityArrayMatrix]
    fun_prop
  exact measurableSet_lt measurable_const hc.matrix_det.measurable

lemma cavityArrayGood_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityColumnRotation q (matrixRotation U)) ⁻¹' cavityArrayGood n q =
      cavityArrayGood n q := by
  ext z
  simp only [Set.mem_preimage, cavityArrayGood, Set.mem_ofPred_eq, cavityArrayMatrix_rotation,
    cavityGram_left_orthogonal _ _
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)]

lemma cavityArrayGood_probability (n q : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) =
      cavityGaussianRows q (cavityGoodGram q n) := by
  rw [← (cavityGaussianRows_finite_standard_law n q).map_eq,
    Measure.map_apply_of_aemeasurable (cavityGaussianRows_finite_standard_law n q).aemeasurable
      (measurableSet_cavityArrayGood n q)]
  congr 1
  ext x
  change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
  rw [cavityGaussianMatrix_gram]
  rfl

lemma cavityConditionedFrameLaw_of_rows (n q : ℕ) :
    (cond (cavityGaussianRows q) (cavityGoodGram q n)).map
      (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
        cavityConditionedFrameLaw n q := by
  let f := fun x : ℕ → Fin q → ℝ => (WithLp.toLp 2
    (fun p : Fin n × Fin q => x p.1 p.2) : EuclideanSpace ℝ (Fin n × Fin q))
  have hf : Measurable f := (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr (fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ))))
  have hpre : f ⁻¹' cavityArrayGood n q = cavityGoodGram q n := by
    ext x
    change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
    rw [cavityGaussianMatrix_gram]
    rfl
  have hmap := cavity_conditioning_map (cavityGaussianRows q) f hf
    (cavityArrayGood n q) (measurableSet_cavityArrayGood n q)
  rw [hpre, (cavityGaussianRows_finite_standard_law n q).map_eq] at hmap
  rw [cavityConditionedFrameLaw, ← hmap]
  rw [Measure.map_map (show Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)) from
      (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)) hf]
  rfl

lemma cavityConditionedFrameLaw_probability {n q : ℕ}
    (hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0) :
    IsProbabilityMeasure (cavityConditionedFrameLaw n q) := by
  let := cond_isProbabilityMeasure hp
  unfold cavityConditionedFrameLaw
  first | exact Measure.isProbabilityMeasure_map ((measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)).aemeasurable | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem cavityConditionedFrameLaw_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityConditionedFrameLaw n q).map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) =
      cavityConditionedFrameLaw n q := by
  let f := fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)
  let act := fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A
  let R := cavityColumnRotation q (matrixRotation U)
  have hf : Measurable f := (measurable_cavityNormalizeFrame n q).comp
    (measurable_cavityArrayMatrix n q)
  have ha : Measurable act :=
    ((continuous_cavityFrameAction n q).comp (continuous_const.prodMk continuous_id)).measurable
  have hR : Measurable R := R.continuous.measurable
  have he : act ∘ f = f ∘ R := funext (fun z => (cavityArrayFrame_rotation U z).symm)
  have hinv := cavity_conditioning_invariant (stdGaussian _) R hR
    (cavityColumnRotation_gaussian (matrixRotation U)) (cavityArrayGood n q)
    (measurableSet_cavityArrayGood n q) (cavityArrayGood_rotation U)
  change ((cond (stdGaussian _) (cavityArrayGood n q)).map f).map act =
    (cond (stdGaussian _) (cavityArrayGood n q)).map f
  rw [Measure.map_map ha hf, he, ← Measure.map_map hf hR, hinv]

theorem cavityConditionedFrameLaw_orthonormal (n q : ℕ) :
    ∀ᵐ A ∂cavityConditionedFrameLaw n q, A.transpose * A = 1 := by
  have hf : Measurable (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z)) :=
    (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)
  have hs : MeasurableSet {A : Matrix (Fin n) (Fin q) ℝ | A.transpose * A = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
      continuous_const).measurableSet
  rw [cavityConditionedFrameLaw, ae_map_iff hf.aemeasurable hs]
  apply ae_cond_of_forall_mem (measurableSet_cavityArrayGood n q)
  intro z hz
  apply cavityNormalizeFrame_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self (cavityArrayMatrix n q z)
  · exact ne_of_gt hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak continuity of the finite Gaussian marks in their covariance,
including singular limiting covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a : Type*} [Fintype a] [DecidableEq a]

lemma cavity_sqrt_tendsto (S : ℕ → Matrix a a ℝ)
    (S₀ : Matrix a a ℝ) (hS : ∀ n, (S n).PosSemidef)
    (hS₀ : S₀.PosSemidef) (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => CFC.sqrt (S n)) atTop (𝓝 (CFC.sqrt S₀)) := by
  have hw : Tendsto S atTop (𝓝[{A : Matrix a a ℝ | 0 ≤ A}] S₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hS n).nonneg)⟩
  have hc := (CFC.continuousOn_sqrt (A := Matrix a a ℝ)).continuousWithinAt
    hS₀.nonneg
  exact hc.tendsto.comp hw

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the invariant frame law, proved by averaging bounded
continuous tests over the compact orthogonal group. -/

noncomputable section
open MeasureTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityFrame_eq_haar_orbit {n q : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Matrix (Fin n) (Fin q) ℝ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Orthogonal n,
      ν.map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) = ν)
    (hframe : ∀ᵐ A ∂ν, A.transpose * A = 1)
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ν = μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  let : HasOuterApproxClosed (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (HasOuterApproxClosed (Fin n → Fin q → ℝ))
  let : SecondCountableTopology (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin q → ℝ))
  have hact := continuous_cavityFrameAction n q
  have hfix (U : Orthogonal n) :
      Continuous (fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A) :=
    hact.comp (continuous_const.prodMk continuous_id)
  have horbit : Continuous (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
    hact.comp (continuous_id.prodMk continuous_const)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hi : Integrable (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      F ((p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2)) (μ.prod ν) :=
    Integrable.of_bound (F.continuous.comp hact).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun p => F.norm_coe_le_norm _))
  have hrow (U : Orthogonal n) :
      (∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν) = ∫ A, F A ∂ν := by
    rw [← integral_map (hfix U).aemeasurable F.continuous.aestronglyMeasurable, hinv U]
  have hcol : ∀ᵐ A ∂ν,
      (∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ) =
        ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
    filter_upwards [hframe] with A hA
    obtain ⟨V, hV⟩ := cavityFrame_transitive A₀ A hA₀ hA
    rw [← hV]
    simp only [← Matrix.mul_assoc]
    change (∫ U, F (((U * V : Orthogonal n) : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ) = _
    exact integral_mul_right_eq_self (μ := μ)
      (fun U : Orthogonal n => F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀)) V
  calc
    (∫ A, F A ∂ν) = ∫ U, ∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν ∂μ := by
      simp only [hrow]
      simp
    _ = ∫ A, ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ ∂ν :=
      integral_integral_swap hi
    _ = ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
      rw [integral_congr_ae hcol]
      simp
    _ = ∫ A, F A ∂μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
      (integral_map horbit.aemeasurable F.continuous.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowGram
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Gram matrices compressed to a growing spectral coordinate
window. Prefix differences avoid introducing a second Gaussian array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_cavityPrefixGram (N q l : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityPrefixGram A l) :=
  (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma cavityPrefixGram_apply {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l : ℕ) (i j : Fin q) :
    cavityPrefixGram A l i j = ∑ k : Fin N, if k.val < l then A k i * A k j else 0 := by
  change (∑ k : Fin N, (∑ t : Fin N,
    A t i * (if t = k then (if t.val < l then (1 : ℝ) else 0) else 0)) * A k j) = _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma cavityPrefixGram_mul {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) (l : ℕ) :
    cavityPrefixGram (A * C) l = C.transpose * cavityPrefixGram A l * C := by
  simp only [cavityPrefixGram, Matrix.transpose_mul, Matrix.mul_assoc]

lemma cavityPrefixGram_gaussian {q : ℕ} (x : ℕ → Fin q → ℝ)
    (N l : ℕ) (hl : l ≤ N) :
    cavityPrefixGram (cavityGaussianMatrix x N) l =
      ((l : ℝ) / N) • cavityEmpiricalGram x l := by
  ext i j
  rw [cavityPrefixGram_apply]
  simp only [cavityGaussianMatrix, div_mul_div_comm,
    Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have hsum : (∑ k : Fin N, if k.val < l then x k i * x k j / N else 0) =
      (∑ k ∈ Finset.range l, x k i * x k j) / N := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < l then x k i * x k j / N else 0) N]
    rw [← Finset.sum_filter]
    have hs : (Finset.range N).filter (fun k => k < l) = Finset.range l := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hs, Finset.sum_div]
  rw [hsum]
  simp only [Matrix.smul_apply, cavityEmpiricalGram, smul_eq_mul]
  by_cases hzero : l = 0
  · subst l
    simp
  · have hnz : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
    field_simp

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma cavityPrefixGram_normalized {q : ℕ} (x : ℕ → Fin q → ℝ)
    (N l : ℕ) (hl : l ≤ N) :
    cavityPrefixGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l =
      ((CFC.sqrt (cavityEmpiricalGram x N))⁻¹).transpose *
        (((l : ℝ) / N) • cavityEmpiricalGram x l) *
        (CFC.sqrt (cavityEmpiricalGram x N))⁻¹ := by
  rw [cavityNormalizeFrame, cavityGaussianMatrix_gram, cavityPrefixGram_mul,
    cavityPrefixGram_gaussian x N l hl]

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem cavityPrefixGram_tendsto {q : ℕ} (x : ℕ → Fin q → ℝ)
    (hx : Tendsto (cavityEmpiricalGram x) atTop (𝓝 1))
    (N l : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hl : Tendsto l atTop atTop)
    (hle : ∀ k, l k ≤ N k) (ρ : ℝ)
    (hρ : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρ)) :
    Tendsto (fun k => cavityPrefixGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k))
      atTop (𝓝 (ρ • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
  have hG := hρ.smul (hx.comp hl)
  have hC := (cavity_gram_correction_tendsto (cavityEmpiricalGram x)
    (cavityEmpiricalGram_posSemidef x) hx).comp hN
  have hc : Continuous (fun p : Matrix (Fin q) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ =>
      p.2.transpose * p.1 * p.2) :=
    (continuous_snd.matrix_transpose.matrix_mul continuous_fst).matrix_mul continuous_snd
  have ht := hc.tendsto (ρ • 1, 1) |>.comp (hG.prodMk_nhds hC)
  simpa only [Function.comp_def, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    ← cavityPrefixGram_normalized x _ _ (hle _)] using ht

lemma cavityPrefixGram_zero {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) :
    cavityPrefixGram A 0 = 0 := by
  ext i j
  simp only [cavityPrefixGram_apply, Nat.not_lt_zero, ite_false, if_false, Finset.sum_const_zero,
    Matrix.zero_apply]

lemma continuous_cavityWindowGram (N q l u : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityWindowGram A l u) :=
  (continuous_cavityPrefixGram N q u).sub (continuous_cavityPrefixGram N q l)

lemma cavityWindowGram_posSemidef {N q : ℕ}
    (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) (hlu : l ≤ u) :
    (cavityWindowGram A l u).PosSemidef := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal
    (fun i : Fin N => if l ≤ i.val ∧ i.val < u then (1 : ℝ) else 0)
  have he : cavityWindowGram A l u = A.transpose * D * A := by
    have hd : Matrix.diagonal (fun i : Fin N => if i.val < u then (1 : ℝ) else 0) -
        Matrix.diagonal (fun i : Fin N => if i.val < l then (1 : ℝ) else 0) = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [D, Matrix.sub_apply, Matrix.diagonal_apply_eq]
        split_ifs <;> norm_num at * <;> omega
      · simp [D, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]
    rw [cavityWindowGram, cavityPrefixGram, cavityPrefixGram,
      ← Matrix.sub_mul, ← Matrix.mul_sub, hd]
  rw [he]
  have hd : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> norm_num)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hd.conjTranspose_mul_mul_same A

theorem cavityWindowGram_tendsto_ae (q : ℕ)
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : Tendsto u atTop atTop) (hl : (∀ k, l k = 0) ∨ Tendsto l atTop atTop)
    (hle : ∀ k, l k ≤ N k) (hue : ∀ k, u k ≤ N k)
    (ρl ρu : ℝ)
    (hρl : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρl))
    (hρu : Tendsto (fun k => (u k : ℝ) / N k) atTop (𝓝 ρu)) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun k => cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))
        atTop (𝓝 ((ρu - ρl) • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  have hupper := cavityPrefixGram_tendsto x hx N u hN hu hue ρu hρu
  have hlower : Tendsto (fun k => cavityPrefixGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k))
      atTop (𝓝 (ρl • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
    rcases hl with hz | hlt
    · have hr : ρl = 0 := by
        have he : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ρl) := by
          simpa only [hz, Nat.cast_zero, zero_div] using hρl
        exact tendsto_nhds_unique he tendsto_const_nhds
      simpa only [hz, cavityPrefixGram_zero, hr, zero_smul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Matrix (Fin q) (Fin q) ℝ)) atTop (𝓝 0))
    · exact cavityPrefixGram_tendsto x hx N l hN hlt hle ρl hρl
  simpa only [cavityWindowGram, sub_smul] using hupper.sub hlower

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar cavity compressions converge to their spectral proportions.
The proof transfers the almost sure Gaussian Gram limit through the
exact conditioned frame law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGaussianNormalizedFrame (q N : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ =>
      cavityNormalizeFrame (cavityGaussianMatrix x N)) := by
  apply (measurable_cavityNormalizeFrame N q).comp
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_pi_apply j).comp (measurable_pi_apply (i : ℕ))).div_const _

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

lemma cavityNormalizeFrame_tendsto {r d : ℕ}
    (B : ℕ → Matrix (Fin r) (Fin d) ℝ) (B₀ : Matrix (Fin r) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1) (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun k => cavityNormalizeFrame (B k)) atTop (𝓝 B₀) := by
  have hGram : Tendsto (fun k => (B k).transpose * B k) atTop
      (𝓝 (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    have hc : Continuous (fun A : Matrix (Fin r) (Fin d) ℝ => A.transpose * A) :=
      continuous_id.matrix_transpose.matrix_mul continuous_id
    simpa only [Function.comp_def, hB₀] using hc.tendsto B₀ |>.comp hB
  have hInv := cavity_gram_correction_tendsto (fun k => (B k).transpose * B k)
    (fun k => by simpa using Matrix.posSemidef_conjTranspose_mul_self (B k)) hGram
  have hc : Continuous (fun p : Matrix (Fin r) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ =>
      p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
  simpa only [Function.comp_def, Matrix.mul_one, cavityNormalizeFrame] using
    hc.tendsto (B₀, 1) |>.comp (hB.prodMk_nhds hInv)

lemma cavityRawComplement_eq {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hEB : E.transpose * B₀ = 0) :
    cavityRawComplement E B₀ = B₀ := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hEB, Matrix.mul_zero, sub_zero]

theorem cavityComplement_tendsto {r n d : ℕ}
    (E : ℕ → Matrix (Fin r) (Fin n) ℝ) (E₀ : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun k => cavityComplement (E k) B₀) atTop (𝓝 B₀) := by
  apply cavityNormalizeFrame_tendsto _ B₀ hB₀
  have hc : Continuous (fun A : Matrix (Fin r) (Fin n) ℝ => cavityRawComplement A B₀) :=
    (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose)).matrix_mul
      continuous_const
  simpa only [Function.comp_def, cavityRawComplement_eq E₀ B₀ hEB] using
    hc.tendsto E₀ |>.comp hE

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma cavitySelectedComplement_eq_local {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hg : cavityGoodCandidate B₀ E 0) :
    cavitySelectedComplement B₀ E = cavityComplement E B₀ := by
  classical
  have hp : cavityComplementChoicePredicate B₀ E 1 := by
    simpa only [cavityComplementChoicePredicate, one_ne_zero, ite_false, if_false, Nat.sub_self] using hg
  have hs := Nat.find_spec (cavityComplementChoice_exists B₀ E)
  have hle := Nat.find_le (h := cavityComplementChoice_exists B₀ E) hp
  have hn : Nat.find (cavityComplementChoice_exists B₀ E) ≠ 0 := by
    intro h
    simp only [cavityComplementChoicePredicate, h, ite_true, if_true] at hs
    exact hs ⟨0, hg⟩
  have heq : Nat.find (cavityComplementChoice_exists B₀ E) = 1 := by omega
  simp only [cavitySelectedComplement, heq, Nat.sub_self, cavityComplementCandidate]

theorem cavitySelectedComplement_tendsto {d n : ℕ}
    (E : ℕ → Matrix (Fin (d + n)) (Fin n) ℝ)
    (E₀ : Matrix (Fin (d + n)) (Fin n) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun k => cavitySelectedComplement B₀ (E k)) atTop (𝓝 B₀) := by
  have hraw := continuous_cavityRawComplement (n := n) B₀
  have hdet := ((hraw.matrix_transpose.matrix_mul hraw).matrix_det).tendsto E₀ |>.comp hE
  have hdet₀ : ((cavityRawComplement E₀ B₀).transpose *
      cavityRawComplement E₀ B₀).det = 1 := by
    rw [cavityRawComplement_eq E₀ B₀ hEB, hB₀, Matrix.det_one]
  rw [hdet₀] at hdet
  have hevent : ∀ᶠ k in atTop, cavityGoodCandidate B₀ (E k) 0 :=
    hdet.eventually (Ioi_mem_nhds zero_lt_one)
  apply (cavityComplement_tendsto E E₀ B₀ hB₀ hEB hE).congr'
  filter_upwards [hevent] with k hk
  exact (cavitySelectedComplement_eq_local B₀ (E k) hk).symm

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

theorem cavitySpectralStack_tendsto {m n : ℕ}
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavitySpectralStack (M k)) atTop
      (𝓝 (fun i j => Real.sqrt (ρ (finProdFinEquiv.symm i).1) *
        (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm i).2 j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm i).2
  have ht := cavity_sqrt_tendsto (fun k => M k a) (ρ a • 1) (fun k => hM k a)
    (Matrix.PosSemidef.one.smul (hρ a)) (hlim a)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A b j) :=
    continuous_id.matrix_elem b j
  have he := hc.tendsto (CFC.sqrt (ρ a • 1)) |>.comp ht
  simpa only [Function.comp_def, cavity_sqrt_scalar_identity (ρ a) (hρ a),
    Matrix.smul_apply, smul_eq_mul, cavitySpectralStack, a, b] using he

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

lemma continuous_cavitySpecialBlocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) :
    Continuous (fun p : Matrix (Fin r) (Fin d) ℝ × Matrix (Fin r) (Fin n) ℝ =>
      cavitySpecialBlocks D p.1 p.2) := by
  apply Continuous.matrix_fromBlocks
  · exact (continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_fst
  · exact (continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_snd
  · exact (continuous_snd.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_fst
  · exact (continuous_snd.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_snd

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

theorem cavityLimitingStack_cavity_block {m n : ℕ} (ρ lam : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) ρ = (∑ a, ρ a * lam a) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  change (∑ k : Fin (m * n), (∑ t : Fin (m * n),
    cavityLimitingStack (n := n) ρ t i *
      (if t = k then lam (finProdFinEquiv.symm t).1 else 0)) *
      cavityLimitingStack (n := n) ρ k j) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [cavityLimitingStack, Equiv.symm_apply_apply]
  change (∑ a : Fin m, ∑ b : Fin n,
    Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
      (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
    (∑ a, ρ a * lam a) * (if i = j then 1 else 0)
  have hs (a : Fin m) :
      (∑ b : Fin n, Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
        (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
      (ρ a * lam a) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      rw [mul_right_comm, Real.mul_self_sqrt (hρ a)]
    · have hji : j ≠ i := Ne.symm hij
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp [hij, hji]
  simp_rw [hs]
  exact (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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

lemma cavityFrame_measurable_integral_eq_haar {n q : ℕ}
    (hp : 0 < (cavityGaussianRows q).real (cavityGoodGram q n))
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1)
    (f : Matrix (Fin n) (Fin q) ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (cavityNormalizeFrame (cavityGaussianMatrix x n))
      ∂cond (cavityGaussianRows q) (cavityGoodGram q n)) =
      ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
  have hp' : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability]
    exact fun h => by simp [Measure.real, h] at hp
  let := cavityConditionedFrameLaw_probability hp'
  have hlaw := cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw n q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal n q) A₀ hA₀
  rw [← integral_map (measurable_cavityGaussianNormalizedFrame q n).aemeasurable
      hf.aestronglyMeasurable, cavityConditionedFrameLaw_of_rows, hlaw]
  exact integral_map
    ((continuous_cavityFrameAction n q).comp (continuous_id.prodMk continuous_const)).aemeasurable
    hf.aestronglyMeasurable

lemma measurable_cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n)) :
    Measurable (cavityReindexedStack e) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm (e.symm i)).1)
      (finProdFinEquiv.symm (e.symm i)).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm (e.symm i)).1)).eval_matrix

lemma measurable_cavityCompressionBlocks {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityCompressionBlocks e D B₀) := by
  have hE : Measurable (cavityReindexedStack e) := measurable_cavityReindexedStack e
  have hB : Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
      cavitySelectedComplement B₀ (cavityReindexedStack e M)) :=
    (measurable_cavitySelectedComplement B₀).comp hE
  have h := (continuous_cavitySpecialBlocks (d := d) (n := n) D).measurable.comp
    (hB.prodMk hE)
  unfold cavityCompressionBlocks
  exact h

theorem cavityCompressionBlocks_tendsto {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0)
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavityCompressionBlocks e D B₀ (M k)) atTop
      (𝓝 (cavitySpecialBlocks D B₀ (cavityReindexedStack e (fun a => ρ a • 1)))) := by
  have hs := cavitySpectralStack_tendsto M ρ hρ hM hlim
  have he : Tendsto (fun k => cavityReindexedStack e (M k)) atTop
      (𝓝 (cavityReindexedStack e (fun a => ρ a • 1))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hh := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hs (e.symm i)) j)
    simpa only [cavityReindexedStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul] using hh
  have hb := cavitySelectedComplement_tendsto _ _ B₀ hB₀ hEB he
  have ht := (continuous_cavitySpecialBlocks (d := d) (n := n) D).tendsto
    (B₀, cavityReindexedStack e (fun a => ρ a • 1)) |>.comp (hb.prodMk_nhds he)
  simpa only [cavityCompressionBlocks, Function.comp_def] using ht

theorem cavityHaarCompressionBlocks_integral_tendsto {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k)
    (hle : ∀ a k, l a k ≤ N k) (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (hEB : (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin n) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityCompressionBlocks e D B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))) ∂μ k)
      atTop (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
  let G := fun k (A : Matrix (Fin (N k)) (Fin n) ℝ) =>
    F (cavityCompressionBlocks e D B₀ (fun a => cavityWindowGram A (l a k) (u a k)))
  have hG (k : ℕ) : Measurable (G k) :=
    F.continuous.measurable.comp ((measurable_cavityCompressionBlocks e D B₀).comp
      (measurable_pi_iff.mpr (fun a => (continuous_cavityWindowGram
        (N k) n (l a k) (u a k)).measurable)))
  let f := fun k (x : ℕ → Fin n → ℝ) =>
    G k (cavityNormalizeFrame (cavityGaussianMatrix x (N k)))
  have hfm (k : ℕ) : Measurable (f k) :=
    (hG k).comp (measurable_cavityGaussianNormalizedFrame n (N k))
  have hb (k : ℕ) (x : ℕ → Fin n → ℝ) : |f k x| ≤ ‖F‖ := F.norm_coe_le_norm _
  have hfi (k : ℕ) : Integrable (f k) (cavityGaussianRows n) :=
    Integrable.of_bound (hfm k).aestronglyMeasurable ‖F‖ (ae_of_all _ (hb k))
  have hlim : ∀ᵐ x ∂cavityGaussianRows n, ∀ a,
      Tendsto (fun k => cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l a k) (u a k))
        atTop (𝓝 ((ρu a - ρl a) • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    ae_all_iff.mpr (fun a => cavityWindowGram_tendsto_ae n N (l a) (u a)
      hN (hu a) (hl a) (hle a) (hue a) (ρl a) (ρu a) (hρl a) (hρu a))
  have hfu : Tendsto (fun k => ∫ x, f k x ∂cavityGaussianRows n) atTop
      (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
    have ht := tendsto_integral_of_dominated_convergence (fun _ : ℕ → Fin n → ℝ => ‖F‖)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (hb k)) (hlim.mono (fun x hx =>
        F.continuous.continuousAt.tendsto.comp (cavityCompressionBlocks_tendsto e D B₀ hB₀
          (fun a => ρu a - ρl a) hρ hEB _
          (fun k a => cavityWindowGram_posSemidef _ _ _ (hlu a k)) hx)))
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hdiff := cavity_conditioning_tendsto (cavityGaussianRows n)
    (fun k => cavityGoodGram n (N k)) (fun k => measurableSet_cavityGoodGram n (N k))
    ((cavityGoodGram_probability_tendsto n).comp hN) f hfi ‖F‖ hb
  have hcond : Tendsto (fun k => ∫ x, f k x
      ∂cond (cavityGaussianRows n) (cavityGoodGram n (N k))) atTop
      (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
    convert hdiff.add hfu using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  apply hcond.congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive n)] with k hk
  exact cavityFrame_measurable_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k) (G k) (hG k)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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

lemma cavityColumns_eq_mul {N n : ℕ} (U : Orthogonal (N + n)) :
    cavityColumns U = (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
      cavityColumns (1 : Orthogonal (N + n)) := by
  ext i j
  change (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) =
    ∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i k *
      (if k = Fin.natAdd N j then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

lemma cavityCompressionGrams_eq_window {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (a : Fin m) (l u : ℕ) (hlu : l ≤ u)
    (hg : ∀ i, g i = a ↔ l ≤ i.val ∧ i.val < u) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g U a = cavityWindowGram (cavityColumns U) l u := by
  ext i j
  change (∑ k : Fin (N + n), (if g k = a then cavityColumns U k i else 0) *
    (if g k = a then cavityColumns U k j else 0)) = _
  rw [cavityWindowGram, Matrix.sub_apply, cavityPrefixGram_apply, cavityPrefixGram_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hg k]
  split_ifs <;> simp_all <;> omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma measurable_cavityConcreteComplement {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n)) (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityConcreteComplement e B₀) := by
  have h := (measurable_cavitySelectedComplement B₀).comp (measurable_cavityReindexedStack e)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionFactors
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cavity factor coefficients as functions of the compression
grams, with their limit at the deterministic scalar compression. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavitySpectralStack (m n : ℕ) :
    Measurable (cavitySpectralStack :
      (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm i).1)).eval_matrix

lemma measurable_cavityCompressionFactorBlocks {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) :
    Measurable (cavityCompressionFactorBlocks e lam lam₀ B₀) := by
  have hB := measurable_cavityConcreteComplement e B₀
  have hT := measurable_cavitySpectralStack m n
  unfold cavityCompressionFactorBlocks cavitySmallFactorBlocks
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  all_goals
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoefficientProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded continuous test detects deviations of the three cavity
coefficients. Weak convergence to deterministic coefficients therefore
gives the probability estimate required by the replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_factor_coefficients_probability {d n : ℕ}
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (hlim : ∀ F : CavityFactorBlocks d n →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, F (A k ω) ∂P k) atTop (𝓝 (F A₀)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀})
      atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  let F := cavityFactorDeviationTest A₀ δ hδ
  have hm k : Measurable (fun ω => cavityFactorDeviation (A k ω) A₀) :=
    (continuous_cavityFactorDeviation A₀).measurable.comp (hA k)
  have hs k : MeasurableSet {ω : Ω k | δ < cavityFactorDeviation (A k ω) A₀} :=
    measurableSet_lt measurable_const (hm k)
  have hF k : Integrable (fun ω => F (A k ω)) (P k) :=
    Integrable.of_bound (F.continuous.measurable.comp (hA k)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        change ‖min 1 (cavityFactorDeviation (A k ω) A₀ / δ)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg
          (le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg _ _) hδ.le))]
        exact min_le_left _ _)
  have hb k : (P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} ≤
      ∫ ω, F (A k ω) ∂P k := by
    rw [← integral_indicator_one (hs k)]
    apply integral_mono ((integrable_const (1 : ℝ)).indicator (hs k)) (hF k)
    intro ω
    by_cases h : δ < cavityFactorDeviation (A k ω) A₀
    · rw [indicator_of_mem (show ω ∈ {ω | δ < cavityFactorDeviation (A k ω) A₀} from h)]
      change 1 ≤ min 1 (cavityFactorDeviation (A k ω) A₀ / δ)
      exact le_min le_rfl ((le_div_iff₀ hδ).mpr (by simpa using h.le))
    · rw [indicator_of_notMem (show ω ∉ {ω | δ < cavityFactorDeviation (A k ω) A₀} from h)]
      exact le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg _ _) hδ.le)
  apply squeeze_zero (fun k => measureReal_nonneg) hb
  simpa only [F, cavityFactorDeviationTest, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    cavityFactorDeviation_self, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hlim F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBlockProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extraction of cavity coefficients from the full small compression
matrix. This lets the proved Haar compression law act on the actual
factor coefficients, including the subtracted base diagonal. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma continuous_cavityFactorBlocksFromMatrix {d n : ℕ}
    (A₀ : Matrix (Fin d) (Fin d) ℝ) : Continuous (cavityFactorBlocksFromMatrix (n := n) A₀) :=
  ((continuous_id.matrix_submatrix _ _).sub continuous_const).prodMk
    ((continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _))

lemma cavityFactorBlocksFromMatrix_special {s d n : ℕ}
    (D : Matrix (Fin s) (Fin s) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ) :
    cavityFactorBlocksFromMatrix A₀ (cavitySpecialBlocks D B T) =
      cavitySmallFactorBlocks D A₀ B T := rfl

lemma cavitySmallFactorBlocks_reindex {s d n r : ℕ}
    (e : Fin s ≃ Fin r) (D : Matrix (Fin s) (Fin s) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (T : Matrix (Fin s) (Fin n) ℝ) :
    cavitySmallFactorBlocks (D.submatrix e.symm e.symm) A₀
      (B.submatrix e.symm id) (T.submatrix e.symm id) = cavitySmallFactorBlocks D A₀ B T := by
  simp only [cavitySmallFactorBlocks, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

lemma cavityCompressionFactorBlocks_eq_projection {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    cavityCompressionFactorBlocks e lam lam₀ B₀ M =
      cavityFactorBlocksFromMatrix (Matrix.diagonal lam₀)
        (cavityCompressionBlocks e
          ((cavityRepeatedSpectrum (n := n) lam).submatrix e.symm e.symm) B₀ M) := by
  rw [cavityCompressionFactorBlocks, ← cavitySmallFactorBlocks_reindex e,
    cavityCompressionBlocks, cavityFactorBlocksFromMatrix_special]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, cavityConcreteComplement, id_eq, Equiv.apply_symm_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarFactorCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence of the actual random cavity factor coefficients,
obtained from the joint Haar compression theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityHaarFactorCoefficients_integral_tendsto {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k)
    (hle : ∀ a k, l a k ≤ N k) (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (hEB : (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin n) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : CavityFactorBlocks d n →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityCompressionFactorBlocks e lam lam₀ B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))) ∂μ k)
      atTop (𝓝 (F (cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
        (Matrix.diagonal lam₀) (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))))) := by
  let D := cavityRepeatedSpectrum (n := n) lam
  let A := Matrix.diagonal lam₀
  let G := F.compContinuous ⟨cavityFactorBlocksFromMatrix A,
    continuous_cavityFactorBlocksFromMatrix A⟩
  have h := cavityHaarCompressionBlocks_integral_tendsto e
    (D.submatrix e.symm e.symm) B₀ hB₀ N l u hN hu hl hlu hle hue
    ρl ρu hρ hρl hρu hEB μ A₀ hA₀ G
  have heq (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
      G (cavityCompressionBlocks e (D.submatrix e.symm e.symm) B₀ M) =
        F (cavityCompressionFactorBlocks e lam lam₀ B₀ M) := by
    exact congrArg F (cavityCompressionFactorBlocks_eq_projection e lam lam₀ B₀ M).symm
  have hb : (Matrix.submatrix (fun i j => B₀ (e i) j) e.symm id) = B₀ := by
    ext i j
    exact congrArg (fun k => B₀ k j) (e.apply_symm_apply i)
  have hp := cavitySmallFactorBlocks_reindex e D A (fun i j => B₀ (e i) j)
    (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))
  rw [hb] at hp
  have hlimit : G (cavitySpecialBlocks (D.submatrix e.symm e.symm) B₀
      (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))) =
      F (cavitySmallFactorBlocks D A (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))) := by
    change F (cavitySmallFactorBlocks (D.submatrix e.symm e.symm) A B₀
      (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))) = _
    exact congrArg F hp
  simpa only [heq, hlimit] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCoefficientProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Haar cavity coefficients concentrate at the deterministic
finite-spectrum coefficients, in the metric used by the replica bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityHaarFactorCoefficients_probability {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k)
    (hle : ∀ a k, l a k ≤ N k) (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (hEB : (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin n) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (μ k).real {U | δ < cavityFactorDeviation
      (cavityCompressionFactorBlocks e lam lam₀ B₀ (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))
      (cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
        (Matrix.diagonal lam₀) (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1)))}) atTop (𝓝 0) := by
  let A := fun k (U : Orthogonal (N k)) => cavityCompressionFactorBlocks e lam lam₀ B₀
    (fun a => cavityWindowGram ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))
  have hA k : Measurable (A k) := by
    apply (measurable_cavityCompressionFactorBlocks e lam lam₀ B₀).comp
    apply measurable_pi_iff.mpr
    intro a
    exact (continuous_cavityWindowGram (N k) n (l a k) (u a k)).measurable.comp
      (continuous_subtype_val.matrix_mul continuous_const).measurable
  exact cavity_factor_coefficients_probability μ A hA _
    (fun F => cavityHaarFactorCoefficients_integral_tendsto e lam lam₀ B₀ hB₀
      N l u hN hu hl hlu hle hue ρl ρu hρ hρl hρu hEB μ A₀ hA₀ F) hδ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurFiniteR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Schur field of the actual limiting cavity block is the
finite spectral R-transform, including its prescribed value at zero. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_limiting_cavityBlock_eq_finiteR_zero {m n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    (cavityLimitingStack (n := n) rho).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho = finiteR rho lam hrho hsum 0 • 1 := by
  simpa only [finiteR, lt_self_iff_false, ite_false, if_false] using
    cavityLimitingStack_cavity_block rho lam (fun a => (hrho a).le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualFactorLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contiguous spectral groups give the precise deterministic
factor blocks required by the original-model spin and entropy limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix BigOperators

namespace InvariantIsing

theorem cavity_actual_factor_probability {m n d : ℕ}
    (es : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l w : Fin m → ℕ → ℕ)
    (g : (k : ℕ) → Fin (N k+n) → Fin m)
    (hg : ∀ a k i, g k i = a ↔ l a k ≤ i.val ∧ i.val < w a k)
    (hN : Tendsto (fun k => N k+n) atTop atTop)
    (hw : ∀ a, Tendsto (w a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlw : ∀ a k, l a k ≤ w a k)
    (hle : ∀ a k, l a k ≤ N k+n) (hwe : ∀ a k, w a k ≤ N k+n)
    (ρl ρw : Fin m → ℝ) (hρ : ∀ a, 0 < ρw a-ρl a)
    (hsum : ∑ a, (ρw a-ρl a) = 1)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ)/(N k+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun k => (w a k : ℝ)/(N k+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => (ρw a-ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k+n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant] :
    let ρ := fun a => ρw a-ρl a
    let B := cavityCompressionLimitFrame es B₀
    let A : CavityFactorBlocks d n :=
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun i => lam (a₀ i)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hsum 0) • 1)
    ∀ δ > 0, Tendsto (fun k => (μ k).real {U | δ < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
        (cavityCompressionGrams (g k) U)) A}) atTop (𝓝 0) := by
  intro ρ B A δ hδ
  have hh := cavityHaarFactorCoefficients_probability es lam (fun i => lam (a₀ i)) B₀ hB₀
    (fun k => N k+n) l w hN hw hl hlw hle hwe ρl ρw (fun a => (hρ a).le)
    (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρw a) hperp μ (fun k => cavityColumns (1 : Orthogonal (N k+n)))
    (fun _ => cavityColumns_gram _) hδ
  have hA : cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun i => lam (a₀ i))) (fun i j => B₀ (es i) j)
      (cavitySpectralStack (fun a => (ρw a-ρl a) • (1 : Matrix (Fin n) (Fin n) ℝ))) = A := by
    change cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun i => lam (a₀ i))) B
      (cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ))) = A
    rw [cavitySpectralStack_scalar_eq ρ (fun a => (hρ a).le)]
    change (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun i => lam (a₀ i)),
      B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
      (cavityLimitingStack (n := n) ρ).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) ρ) = A
    rw [cavity_limiting_cavityBlock_eq_finiteR_zero ρ lam hρ hsum]
  rw [hA] at hh
  have hgram (k : ℕ) (U : Orthogonal (N k+n)) :
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k+n)) (Fin (N k+n)) ℝ)*cavityColumns (1 : Orthogonal (N k+n)))
        (l a k) (w a k)) = cavityCompressionGrams (g k) U := by
    funext a
    rw [cavityCompressionGrams_eq_window (g k) a (l a k) (w a k) (hlw a k) (hg a k) U,
      cavityColumns_eq_mul U]
  apply hh.congr
  intro k
  apply congrArg ((μ k).real)
  ext U
  change (δ < cavityFactorDeviation
    (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k+n)) (Fin (N k+n)) ℝ)*cavityColumns (1 : Orthogonal (N k+n)))
        (l a k) (w a k))) A) ↔ _
  rw [hgram k U]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarBoundedLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer bounded measurable cutoff limits from the normalized
Gaussian frame to the actual Haar frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavityHaarWindowGram_bounded_limit {q : ℕ}
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : ℕ → Matrix (Fin q) (Fin q) ℝ → ℝ) (hF : ∀ k, Measurable (F k))
    {C a : ℝ} (hb : ∀ k M, |F k M| ≤ C)
    (hlim : ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun k => F k (cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k)))
        atTop (𝓝 a)) :
    Tendsto (fun k => ∫ U, F k (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)) ∂μ k)
      atTop (𝓝 a) := by
  let f := fun k (x : ℕ → Fin q → ℝ) => F k (cavityWindowGram
    (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))
  have hfm (k : ℕ) : Measurable (f k) :=
    ((hF k).comp (continuous_cavityWindowGram (N k) q (l k) (u k)).measurable).comp
      (measurable_cavityGaussianNormalizedFrame q (N k))
  have hfi (k : ℕ) : Integrable (f k) (cavityGaussianRows q) :=
    Integrable.of_bound (hfm k).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb k _)
  have hfu : Tendsto (fun k => ∫ x, f k x ∂cavityGaussianRows q) atTop (𝓝 a) := by
    have ht := tendsto_integral_of_dominated_convergence (fun _ : ℕ → Fin q → ℝ => C)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb k _)
      hlim
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hdiff := cavity_conditioning_tendsto (cavityGaussianRows q)
    (fun k => cavityGoodGram q (N k)) (fun k => measurableSet_cavityGoodGram q (N k))
    ((cavityGoodGram_probability_tendsto q).comp hN) f hfi C (fun k x => hb k _)
  have hcond : Tendsto (fun k => ∫ x, f k x
      ∂cond (cavityGaussianRows q) (cavityGoodGram q (N k))) atTop (𝓝 a) := by
    convert hdiff.add hfu using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  apply hcond.congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive q)] with k hk
  exact cavityFrame_measurable_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k)
    (fun A => F k (cavityWindowGram A (l k) (u k)))
    ((hF k).comp (continuous_cavityWindowGram (N k) q (l k) (u k)).measurable)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCorrection
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse square-root compression is bounded with probability
tending to one. No global inverse moment is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_inverse_sqrt_tendsto_pos {q : ℕ}
    (G : ℕ → Matrix (Fin q) (Fin q) ℝ) (hG : ∀ k, (G k).PosSemidef)
    {ρ : ℝ} (hρ : 0 < ρ) (hlim : Tendsto G atTop (𝓝 (ρ • 1))) :
    Tendsto (fun k => (CFC.sqrt (G k))⁻¹) atTop
      (𝓝 ((CFC.sqrt (ρ • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹)) := by
  have hp : (ρ • (1 : Matrix (Fin q) (Fin q) ℝ)).PosDef := Matrix.PosDef.one.smul hρ
  have hu := cavity_sqrt_det_isUnit _ hp
  have hc : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _)
      (CFC.sqrt (ρ • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext (fun x => Ring.inverse_eq_inv x)
    rw [he]
    exact continuousAt_inv₀ hu.ne_zero
  exact hc.tendsto.comp (cavity_sqrt_tendsto G _ hG hp.posSemidef hlim)

theorem cavityHaarWindow_correction_probability {q : ℕ}
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : Tendsto u atTop atTop) (hl : (∀ k, l k = 0) ∨ Tendsto l atTop atTop)
    (hlu : ∀ k, l k ≤ u k) (hle : ∀ k, l k ≤ N k) (hue : ∀ k, u k ≤ N k)
    (ρl ρu : ℝ) (hρ : 0 < ρu - ρl)
    (hρl : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρl))
    (hρu : Tendsto (fun k => (u k : ℝ) / N k) atTop (𝓝 ρu))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    {L : ℝ} (hL : ‖(CFC.sqrt ((ρu - ρl) • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹‖ < L) :
    Tendsto (fun k => (μ k).real {U | ‖(CFC.sqrt (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  let F := fun G : Matrix (Fin q) (Fin q) ℝ => if ‖(CFC.sqrt G)⁻¹‖ ≤ L then (1 : ℝ) else 0
  have hmnorm : Measurable (fun G : Matrix (Fin q) (Fin q) ℝ => ‖(CFC.sqrt G)⁻¹‖) :=
    (cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm
  have hmF : Measurable F :=
    Measurable.ite (measurableSet_le hmnorm measurable_const) measurable_const measurable_const
  have hb : ∀ G, |F G| ≤ 1 := by intro G; dsimp only [F]; split_ifs <;> norm_num
  have hlim := cavityWindowGram_tendsto_ae q N l u hN hu hl hle hue ρl ρu hρl hρu
  have hFae : ∀ᵐ x ∂cavityGaussianRows q, Tendsto (fun k => F (cavityWindowGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))) atTop (𝓝 1) := by
    filter_upwards [hlim] with x hx
    have hc := cavity_inverse_sqrt_tendsto_pos _
      (fun k => cavityWindowGram_posSemidef _ _ _ (hlu k)) hρ hx
    have he := hc.norm.eventually (Iio_mem_nhds hL)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    simp only [F, hk.le, ite_true, if_true]
  have ht := cavityHaarWindowGram_bounded_limit N l u hN μ A₀ hA₀
    (fun _ => F) (fun _ => hmF) (fun _ => hb) hFae
  have he (k : ℕ) : (∫ U, F (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)) ∂μ k) =
      (μ k).real {U | ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖ ≤ L} := by
    have hm : Measurable (fun U : Orthogonal (N k) => ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖) :=
      hmnorm.comp (((continuous_cavityWindowGram (N k) q (l k) (u k)).comp
        (continuous_subtype_val.matrix_mul continuous_const)).measurable)
    simpa only [F, Set.indicator, mem_ofPred_eq, Pi.one_apply] using
      (integral_indicator_one (μ := μ k) (measurableSet_le hm measurable_const))
  simpa only [he] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGoodCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous control of the finitely many spectral compression
blocks, obtained from their positive limiting proportions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavityHaarWindow_correction_all {q m : ℕ}
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k) (hle : ∀ a k, l a k ≤ N k)
    (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 < ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun k => (μ k).real {U | ∀ a,
      ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  let K := fun a => ‖(CFC.sqrt ((ρu a - ρl a) • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹‖
  let L := 1 + ∑ a, K a
  have hK : ∀ a, K a < L := by
    intro a
    have hs : K a ≤ ∑ a, K a :=
      Finset.single_le_sum (f := K) (fun a _ => norm_nonneg _) (Finset.mem_univ a)
    dsimp only [L]
    linarith
  have hL : 0 < L := by
    have hs : 0 ≤ ∑ a, K a := Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp only [L]
    linarith
  let A := fun k a => {U : Orthogonal (N k) | ‖(CFC.sqrt (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))⁻¹‖ ≤ L}
  have hmA : ∀ k a, MeasurableSet (A k a) := by
    intro k a
    apply measurableSet_le _ measurable_const
    exact ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      (((continuous_cavityWindowGram (N k) q (l a k) (u a k)).comp
        (continuous_subtype_val.matrix_mul continuous_const)).measurable)
  have hp : ∀ a, Tendsto (fun k => (μ k).real (A k a)) atTop (𝓝 1) := by
    intro a
    exact cavityHaarWindow_correction_probability N (l a) (u a) hN (hu a) (hl a)
      (hlu a) (hle a) (hue a) (ρl a) (ρu a) (hρ a) (hρl a) (hρu a) μ A₀ hA₀ (hK a)
  let G := fun k => ⋂ a, A k a
  have hmG : ∀ k, MeasurableSet (G k) := fun k => MeasurableSet.iInter (hmA k)
  have hpc : ∀ a, Tendsto (fun k => (μ k).real (A k a)ᶜ) atTop (𝓝 0) := by
    intro a
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hp a)
    simpa only [measureReal_compl (hmA _ a), probReal_univ, sub_self] using ht
  have hbound : ∀ k, (μ k).real (G k)ᶜ ≤ ∑ a, (μ k).real (A k a)ᶜ := by
    intro k
    have he : (G k)ᶜ = ⋃ a, (A k a)ᶜ := by ext U; simp [G]
    rw [he]
    exact measureReal_iUnion_fintype_le _
  have hzero : Tendsto (fun k => (μ k).real (G k)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) hbound
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _ => hpc a)
  refine ⟨L, hL, ?_⟩
  have ht := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  have he (k : ℕ) : 1 - (μ k).real (G k)ᶜ = (μ k).real (G k) := by
    rw [measureReal_compl (hmG k), probReal_univ]
    ring
  have ht' : Tendsto (fun k => (μ k).real (G k)) atTop (𝓝 1) := by
    simpa only [he, sub_zero] using ht
  convert ht' using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  congr 1
  ext U
  simp [G, A]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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

lemma cavityOrientationLift_compression {N n m : ℕ} (hN : 0 < N + n)
    (g : Fin (N + n) → Fin m) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityCompressionGrams g U := by
  funext a
  ext i j
  change (∑ k : Fin (N + n),
    (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N i) else 0) *
      (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N j) else 0)) =
    ∑ k : Fin (N + n), (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N i) else 0) *
      (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N j) else 0)
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : g k = a
  · simp only [hk, ite_true, if_true, cavityOrientationSign, Matrix.diagonal_mul]
    split_ifs
    · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
    · ring
  · simp only [hk, ite_false, if_false, mul_zero]

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

lemma cavityOrientationLift_compression_event {N n m : ℕ} (hN : 0 < N + n)
    (g : Fin (N + n) → Fin m) (μ : Measure (Orthogonal (N + n))) (L : ℝ) :
    (μ.map (cavityOrientationLift hN)).real {U | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} =
    μ.real {U | ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g U a))⁻¹‖ ≤ L} := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hs : MeasurableSet {U : SpecialOrthogonal (N + n) | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} := by
    have he : {U : SpecialOrthogonal (N + n) | ∀ a,
        ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} =
        ⋂ a, {U : SpecialOrthogonal (N + n) |
          ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} := by
      ext U
      simp
    rw [he]
    apply MeasurableSet.iInter
    intro a
    apply measurableSet_le _ measurable_const
    exact ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      ((measurable_pi_apply a).comp ((measurable_cavityCompressionGrams g).comp hO))
  simp only [Measure.real, Measure.map_apply (measurable_cavityOrientationLift hN) hs]
  congr 2
  ext U
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, cavityOrientationLift_compression]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualGoodCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good compression events for the actual cavity columns, after the
orientation correction used by the full-model comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_actual_compression_good_probability {n m : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k + n)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (l u : Fin m → ℕ → ℕ)
    (hg : ∀ a k i, g k i = a ↔ l a k ≤ i.val ∧ i.val < u a k)
    (hN : Tendsto (fun k => N k + n) atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k) (hle : ∀ a k, l a k ≤ N k + n)
    (hue : ∀ a k, u a k ≤ N k + n)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 < ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / (N k + n)) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / (N k + n)) atTop (𝓝 (ρu a)))
    (μ : (k : ℕ) → Measure (Orthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant] :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun k =>
      ((μ k).map (cavityOrientationLift (hNpos k))).real {U | ∀ a,
        ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  obtain ⟨L, hL, hlim⟩ := cavityHaarWindow_correction_all (fun k => N k + n)
    l u hN hu hl hlu hle hue ρl ρu hρ
    (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρu a) μ
    (fun k => cavityColumns (1 : Orthogonal (N k + n)))
    (fun _ => cavityColumns_gram _)
  refine ⟨L, hL, hlim.congr fun k => ?_⟩
  rw [cavityOrientationLift_compression_event]
  have hgram (U : Orthogonal (N k + n)) (a : Fin m) :
      cavityCompressionGrams (g k) U a = cavityWindowGram
        ((U : Matrix (Fin (N k + n)) (Fin (N k + n)) ℝ) *
          cavityColumns (1 : Orthogonal (N k + n))) (l a k) (u a k) := by
    rw [cavityCompressionGrams_eq_window (g k) a (l a k) (u a k)
      (hlu a k) (hg a k) U, cavityColumns_eq_mul U]
  have he : {U : Orthogonal (N k + n) | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) U a))⁻¹‖ ≤ L} =
      {U : Orthogonal (N k + n) | ∀ a, ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k + n)) (Fin (N k + n)) ℝ) *
          cavityColumns (1 : Orthogonal (N k + n))) (l a k) (u a k)))⁻¹‖ ≤ L} := by
    ext U
    simp only [mem_ofPred_eq, hgram]
  rw [he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) :
    Continuous (permuteSpectralArray (m := m) e) := by
  unfold permuteSpectralArray
  fun_prop

lemma disorderReplicaLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (disorderReplicaLaw P ν hν).map (Prod.map id (fun σ i => σ (e i))) =
      disorderReplicaLaw P ν hν := by
  unfold disorderReplicaLaw
  rw [← Measure.compProd_map (by fun_prop)]
  congr 1
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (by fun_prop)]
  change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => σ (e i)) =
    Measure.infinitePi (fun _ : ℕ => ν ω)
  exact Measure.map_infinitePi_infinitePi_of_inj he

lemma spectralArrayLaw_map_reindex {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (e : ℕ → ℕ) (he : Function.Injective e) :
    (spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = spectralArrayLaw P U hU I n ν hν := by
  change ((disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)).map _ = _
  rw [Measure.map_map (continuous_permuteSpectralArray e).measurable
    (measurable_spectralReplicaArray U hU I n)]
  have heq : permuteSpectralArray e ∘ spectralReplicaArray U I n =
      spectralReplicaArray U I n ∘ Prod.map id (fun σ i => σ (e i)) := rfl
  rw [heq, ← Measure.map_map (measurable_spectralReplicaArray U hU I n) (by fun_prop),
    disorderReplicaLaw_map_reindex P ν hν e he]
  rfl

lemma spectralArray_limit_reindex {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (e : ℕ → ℕ)
    (hE : ∀ k, (L k : Measure (SpectralArray m)).map (permuteSpectralArray e) = L k) :
    (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_permuteSpectralArray e)).tendsto Q
  have he : (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = L := by
    funext k
    exact Subtype.ext (hE k)
  have ht := hc.comp hL
  change Tendsto (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) _ _ at ht
  rw [he] at ht
  have heq : Q.map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = Q := tendsto_nhds_unique ht hL
  exact congrArg Subtype.val heq

lemma continuous_spectralCoordinateArray {m : ℕ} (a : Fin m) :
    Continuous (spectralCoordinateArray a) := by
  unfold spectralCoordinateArray
  fun_prop

lemma isClosed_spectralGram (m : ℕ) : IsClosed {x : SpectralArray m | SpectralGram x} := by
  unfold SpectralGram
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun n =>
    (isClosed_setOf_posSemidef n).preimage (by unfold spectralCoordinateArray; fun_prop)

lemma spectralReplicaArray_gram {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralGram (spectralReplicaArray U I n p) := by
  intro a z
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_tree] using
      treeOverlap_posSemidef n (fun i : Fin z => (p.2 i).2)
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (specialRotation (U p.1)) (I j) (fun i : Fin z => (p.2 i).1)

lemma spectralArrayLaw_gram {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))), SpectralGram x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n), SpectralGram x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralGram (m + 1)).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_gram U I n)

lemma spectralArray_limit_gram {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray m)), SpectralGram x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x :=
  ae_closed_of_weak_limit hL (isClosed_spectralGram m) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGGGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma spectralGram_diagonal {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a) (a : Fin m) :
    GramDiagonal (q a) (spectralCoordinateArray a x) :=
  ⟨hG a, fun i => hd i a⟩

lemma spectralGG_coordinate_nonnegative {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ a, 0 ≤ (x (0,1) a : ℝ) := by
  apply ae_all_iff.mpr
  intro a
  exact gg_pair_nonnegative_ae (continuous_spectralCoordinateArray a).measurable
    (hgg.real_map (f := fun x => (x a : ℝ)) (by fun_prop)) (hq a)
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_diagonal hx q hdx a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma projectedOverlap_partition {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ τ) = projectedOverlap U Finset.univ σ τ := by
  classical
  unfold projectedOverlap
  rw [← Finset.mul_sum]
  congr 1
  have hs := Finset.sum_biUnion (f := fun i => U (spinVector σ) i * U (spinVector τ) i)
    (show Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis)
  rw [hcover] at hs
  exact hs.symm

lemma projectedOverlap_partition_self {N m : ℕ} (hN : 0 < N) (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ σ) = 1 := by
  rw [projectedOverlap_partition U I hdis hcover, projectedOverlap_univ]
  simp only [← pow_two, spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')

lemma isClosed_spectralPartitionGeometry (m : ℕ) :
    IsClosed {x : SpectralArray (m + 1) | SpectralPartitionGeometry m x} := by
  unfold SpectralPartitionGeometry
  apply IsClosed.inter
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i j, |spectralSpinArray x i j| ≤ 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le
      (by unfold spectralSpinArray; fun_prop) continuous_const
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i, spectralSpinArray x i i = 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by unfold spectralSpinArray; fun_prop) continuous_const

lemma spectralReplicaArray_partition {Ω : Type*} {N m : ℕ} (hN : 0 < N)
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) :
    SpectralPartitionGeometry m (spectralReplicaArray U I n p) := by
  have he (i j : ℕ) : spectralSpinArray (spectralReplicaArray U I n p) i j =
      projectedOverlap (specialRotation (U p.1)) Finset.univ (p.2 i).1 (p.2 j).1 := by
    simp only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral]
    exact projectedOverlap_partition _ I hdis hcover _ _
  constructor
  · intro i j
    rw [he]
    exact projectedOverlap_abs_le_one _ _ _ _
  · intro i
    simpa only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_partition_self hN (specialRotation (U p.1)) I hdis hcover (p.2 i).1

lemma spectralArrayLaw_partition {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ} (hN : 0 < N)
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))),
      SpectralPartitionGeometry m x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    SpectralPartitionGeometry m x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralPartitionGeometry m).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_partition hN U I hdis hcover n)

lemma spectralArray_limit_partition {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x :=
  ae_closed_of_weak_limit hL (isClosed_spectralPartitionGeometry m) hG


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

lemma cavityBaseAmplitude_bound {N : ℕ} (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (j : ℕ) :
    |cavityBaseAmplitude u j| ≤ 2 := by
  unfold cavityBaseAmplitude
  split_ifs with hj
  · exact abs_le.mpr ⟨by linarith [(hu ⟨j,hj⟩).1], (hu ⟨j,hj⟩).2⟩
  · norm_num

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical spectral labels form the actual finite partition with
exact prescribed block dimensions. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavitySpectralGroup_pairwiseDisjoint {N m : ℕ} (g : Fin N → Fin m) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (cavitySpectralGroup g) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' : g i=a := (Finset.mem_filter.mp hi).2
  have hj' : g i=b := (Finset.mem_filter.mp hj).2
  exact hab (hi'.symm.trans hj')

lemma cavitySpectralGroup_cover {N m : ℕ} (g : Fin N → Fin m) :
    Finset.univ.biUnion (cavitySpectralGroup g)=Finset.univ := by
  classical
  ext i
  simp [cavitySpectralGroup]

lemma cavity_group_dimension_card {N m : ℕ} (dims : Fin m → ℕ)
    (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N) (a : Fin m) :
    (cavitySpectralGroup (fun i => (E.symm i).1) a).card=dims a := by
  have he := Fintype.card_congr (cavityGroupSetEquiv dims E a)
  simpa only [Fintype.card_fin, Fintype.card_coe] using he.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSides
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A right-invariant probability has the same inverse law and is
left-invariant. In particular the oriented base law supplies the SO Haar
hypothesis used by the finite-model concentration estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

instance cavityOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (Orthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : Orthogonal N × Orthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (SpecialOrthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : SpecialOrthogonal N × SpecialOrthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableInv (N : ℕ) : MeasurableInv (SpecialOrthogonal N) where
  measurable_inv := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun U : SpecialOrthogonal N => (U : Matrix (Fin N) (Fin N) ℝ) j i)
    exact (Matrix.measurable_apply (i := j) (j := i)).comp measurable_subtype_coe

lemma cavity_right_probability_inv_eq {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] : μ = μ.inv := by
  let : IsProbabilityMeasure μ.inv :=
    (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ y, ∫⁻ x, f (x*y) ∂μ ∂μ.inv := by
      simp only [lintegral_mul_right_eq_self, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, ∫⁻ y, f (x*y) ∂μ.inv ∂μ :=
      lintegral_lintegral_swap (hf.comp (measurable_snd.mul measurable_fst)).aemeasurable
    _ = ∫⁻ y, f y ∂μ.inv := by
      simp only [lintegral_mul_left_eq_self, lintegral_const, measure_univ, mul_one]

lemma cavity_right_probability_left {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] : μ.IsMulLeftInvariant := by
  rw [cavity_right_probability_inv_eq μ]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cavityOrientedBaseLaw_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    (cavityOrientedBaseLaw hN μ).IsMulRightInvariant := by
  let : μ.IsMulLeftInvariant := cavity_right_probability_left μ
  have he : cavityOrientedBaseLaw hN μ = μ.inv.map (cavityOrientationLift hN) := by
    rw [Measure.inv_def, Measure.map_map (measurable_cavityOrientationLift hN) measurable_inv]
    rfl
  rw [he]
  exact cavityOrientationLift_measure_rightInvariant hN μ.inv

lemma cavityOrientedBaseLaw_leftInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    (cavityOrientedBaseLaw hN μ).IsMulLeftInvariant := by
  let := cavityOrientedBaseLaw_rightInvariant hN μ
  exact cavity_right_probability_left (cavityOrientedBaseLaw hN μ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowInputs
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two probabilistic compression premises follow from the actual
contiguous spectral windows and their positive limiting masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

lemma measurableSet_cavityCompressionGoodEvent {N n m : ℕ}
    (g : Fin (N+n) → Fin m) (L : ℝ) : MeasurableSet (cavityCompressionGoodEvent g L) := by
  have hmO : Measurable (cavitySpecialOrthogonal : SpecialOrthogonal (N+n) → Orthogonal (N+n)) := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe
  have hm a : Measurable (fun U : SpecialOrthogonal (N+n) =>
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖) :=
    ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      (((measurable_pi_apply a).comp (measurable_cavityCompressionGrams g)).comp hmO)
  simpa only [cavityCompressionGoodEvent, ofPred_forall] using
    MeasurableSet.iInter (fun a => measurableSet_le (hm a) (measurable_const (a := L)))

theorem cavity_window_inputs {m n d : ℕ}
    (es : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose*B₀=1)
    (N : ℕ → ℕ) (hNpos : ∀ r, 0<N r+n) (l w : Fin m → ℕ → ℕ)
    (g : (r : ℕ) → Fin (N r+n) → Fin m)
    (hg : ∀ a r i, g r i=a ↔ l a r ≤ i.val ∧ i.val<w a r)
    (hN : Tendsto (fun r => N r+n) atTop atTop)
    (hw : ∀ a, Tendsto (w a) atTop atTop)
    (hl : ∀ a, (∀ r, l a r=0) ∨ Tendsto (l a) atTop atTop)
    (hlw : ∀ a r, l a r≤w a r) (hle : ∀ a r, l a r≤N r+n)
    (hwe : ∀ a r, w a r≤N r+n)
    (ρl ρw : Fin m → ℝ) (hρ : ∀ a, 0<ρw a-ρl a)
    (hsum : ∑ a, (ρw a-ρl a)=1)
    (hρl : ∀ a, Tendsto (fun r => (l a r : ℝ)/(N r+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun r => (w a r : ℝ)/(N r+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => (ρw a-ρl a) • 1)).transpose*B₀=0)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n)))
    [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant] :
    let ρ := fun a => ρw a-ρl a
    let B := cavityCompressionLimitFrame es B₀
    let A : CavityFactorBlocks d n :=
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hsum 0) • 1)
    (∃ L : ℝ, 0<L ∧ Tendsto (fun r =>
      ((μ r).map (cavityOrientationLift (hNpos r))).real (cavityCompressionGoodEvent (g r) L))
      atTop (𝓝 1)) ∧
    (∀ ε>0, Tendsto (fun r => (μ r).real {U | ε < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A}) atTop (𝓝 0)) := by
  intro ρ B A
  exact ⟨cavity_actual_compression_good_probability N hNpos g l w hg hN hw hl hlw hle hwe
      ρl ρw hρ hρl hρw μ,
    cavity_actual_factor_probability es lam a₀ B₀ hB₀ N l w g hg hN hw hl hlw hle hwe
      ρl ρw hρ hsum hρl hρw hperp μ⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayDiagonalLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact array/center subsequences and constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma spectralArray_center_subsequence (m : ℕ) (L : ℕ → ProbabilityMeasure (SpectralArray m))
    (c : ℕ → Fin m → Set.Icc (0 : ℝ) 1) :
    ∃ Q : ProbabilityMeasure (SpectralArray m), ∃ q : Fin m → Set.Icc (0 : ℝ) 1,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (L ∘ φ) atTop (nhds Q) ∧
        Tendsto (c ∘ φ) atTop (nhds q) := by
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq (fun k => (L k, c k))
  refine ⟨p.1, p.2, φ, hφ, ?_, ?_⟩
  · exact (continuous_fst.tendsto p).comp hp
  · exact (continuous_snd.tendsto p).comp hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector GG identities in weak limits of actual constrained-prior minimizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem priorPerturbation_minimizers_spectralGG
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) (u k) (v k)≤
        priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) := by
  obtain ⟨C,hC,hbound⟩ := priorPerturbation_arrayResidual_bound hhaar hgauss
  apply spectralGG_of_weak_nonconstant_monomial_residuals hL
  intro z hz i D hD d hd
  cases z with
  | zero => omega
  | succ q =>
    obtain ⟨j,hj⟩ := enumeratedJointMonomial_surjective m d hd
    let BD := BoundedContinuousFunction.mkOfCompact ⟨D,hD⟩
    have hDb : ∀ x, |D x|≤‖BD‖ := fun x => by
      simpa only [BD,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,Real.norm_eq_abs]
        using BD.norm_coe_le_norm x
    let L := H+4+C*(K+4*m+8)^2
    have he : ∀ᶠ k in atTop, perturbationScale (N k)≤1/32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k)≤1/4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hjN : ∀ᶠ k in atTop, j<N k := hNlim.eventually (eventually_gt_atTop j)
    apply squeeze_zero_norm' _ ((tensorContactGGRate_tendsto j m L ‖BD‖).comp hNlim)
    filter_upwards [he,hs,hjN] with k he hs hjN
    let j' : Fin (N k) := ⟨j,hjN⟩
    have hg := hbound (N k) (hN k) (μ k) (hμinv k) m n (ν k)
      (eig k) (c k) K hK (heig k) (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k)
      (h k) (hh k) (h0 k) H (hH k) he hs (hmin k) j' q i D hD ‖BD‖ (norm_nonneg BD) hDb
    simpa only [priorPerturbedArrayLaw,j',hj,Real.norm_eq_abs,Function.comp_def,L] using hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorGGExistence
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of geometric GG limits from actual constrained-prior minima. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorPerturbedArrayLaw_gram {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ∀ᵐ x ∂(priorPerturbedArrayLaw μ ν eig c I u v t h : Measure (SpectralArray (m+1))),
      SpectralGram x := by
  unfold priorPerturbedArrayLaw priorNamespacedArrayLaw
  exact spectralArrayLaw_gram _ _ _ _ _ _ _

lemma priorPerturbedArrayLaw_reindex {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ)
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (priorPerturbedArrayLaw μ ν eig c I u v t h : Measure (SpectralArray (m+1))).map
      (permuteSpectralArray e)=priorPerturbedArrayLaw μ ν eig c I u v t h := by
  unfold priorPerturbedArrayLaw priorNamespacedArrayLaw
  exact spectralArrayLaw_map_reindex _ _ _ _ _ _ _ e he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFixedGeometricLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every prescribed sequence of actual prior minima has a geometric GG subsequence. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem prior_minimizers_geometric_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) (u k) (v k)≤
        priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) u' v') :
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => priorPerturbedArrayLaw (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) := by
  let L := fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
    (u k) (v k) (t k) (h k)
  let center := fun k => tensorMinimumArrayDiagonal (N k) n (v k)
  obtain ⟨Q,q,φ,hφ,hL,hc⟩ := spectralArray_center_subsequence (m+1) L center
  have hgg := priorPerturbation_minimizers_spectralGG hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => ν (φ k))
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL
  have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  have hd := priorPerturbation_minimizers_constantDiagonal hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => ν (φ k))
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL (fun a => (q a : ℝ)) ((hco.tendsto q).comp hc)
  have hg := spectralArray_limit_gram hL (fun k => priorPerturbedArrayLaw_gram
    (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
    (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)))
  have hr : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q := by
    intro e he
    exact spectralArray_limit_reindex hL e (fun k => priorPerturbedArrayLaw_reindex
      (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
      (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)) e he)
  exact ⟨Q,q,φ,hφ,hL,hgg,hd,hg,hr,
    spectralGG_coordinate_nonnegative hgg hg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorGGWardExistence
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fixed-prior minima admit geometric limits with both Ward identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorPerturbedArrayLaw_partition {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I=Finset.univ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ∀ᵐ x ∂(priorPerturbedArrayLaw μ ν eig c I u v t h : Measure (SpectralArray (m+1))),
      SpectralPartitionGeometry m x := by
  unfold priorPerturbedArrayLaw priorNamespacedArrayLaw
  exact spectralArrayLaw_partition hN _ _ _ _ hdis hcover _ _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFixedMinimumLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full GG/Ward subsequence retains any prescribed actual minima. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem prior_fixed_minimum_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ k) (ν k) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) (u k) (v k)≤
        priorPerturbationObjective (μ k) (ν k) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) u' v') :
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => priorPerturbedArrayLaw (μ (φ k)) (ν (φ k)) (eig (φ k)) (fun _ => 0)
        (I (φ k)) (u (φ k)) (v (φ k)) 1 (fun _ => 0)) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b Φ=0) ∧
      (∀ a b, spectralDiagonalWardResidual Q ρ lam a b=0) := by
  obtain ⟨Q,q,φ,hφ,hL,hgg,hd,hG,hE,hn⟩ :=
    prior_minimizers_geometric_GG_limit hhaar hgauss N hN hNlim m n μ hμinv ν
      eig (fun _ _ => 0) K hK heig I (fun _ => 1) (fun _ => by norm_num)
      (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl) 0 (fun _ => le_rfl) u hu v hv hmin
  have hpos k : 0<N (φ k) := by have := hN (φ k); omega
  have hpart := spectralArray_limit_partition hL (fun k => priorPerturbedArrayLaw_partition
    (hpos k) (μ (φ k)) (ν (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k))
    (hdis (φ k)) (hcover (φ k)) (u (φ k)) (v (φ k)) 1 (fun _ => 0))
  have hua k j : |u (φ k) j|≤2 := abs_le.mpr ⟨by linarith [(hu (φ k) j).1],(hu (φ k) j).2⟩
  have hva k a : |v (φ k) a|≤2 := abs_le.mpr ⟨by linarith [(hv (φ k) a).1],(hv (φ k) a).2⟩
  have hw := priorPerturbedArrayLaw_ward_limits (fun k => N (φ k)) hpos
    (hNlim.comp hφ.tendsto_atTop) m n (fun k => μ (φ k)) (fun k => hμinv (φ k))
    (fun k => ν (φ k)) (fun k => eig (φ k)) (fun _ _ => 0) (fun k => I (φ k))
    (fun k => hdis (φ k)) (fun k => hcover (φ k)) lam (fun k => hlam (φ k))
    (fun k => u (φ k)) hua (fun k => v (φ k)) hva (fun _ => 1) tendsto_const_nhds
    (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ (hρ.comp hφ.tendsto_atTop)
  simp only [one_mul] at hw
  exact ⟨Q,q,φ,hφ,hL,hgg,hd,hG,hE,hpart,hn,hw.1,hw.2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFixedMinimumLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical GG/Ward limits preserve any specified sequence of constrained minima. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem restricted_fixed_minimum_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (S : (k : ℕ) → Finset (Spin (N k))) (hS : ∀ k, (S k).Nonempty)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        priorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
          (restrictedZeroTreePrior (S k) (hS k)) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) (u k) (v k)≤
        priorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
          (restrictedZeroTreePrior (S k) (hS k)) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) u' v') :
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => restrictedRotationArrayLaw (S (φ k)) (hS (φ k)) (μ (φ k)) (θ (φ k))
        (diagonalPerturbedEigenvalues (eig (φ k)) (I (φ k)) (v (φ k)) 1)
        (I (φ k)) (cavityBaseAmplitude (u (φ k)))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b Φ=0) ∧
      (∀ a b, spectralDiagonalWardResidual Q ρ lam a b=0) := by
  have hpos k : 0<N k := by have := hN k; omega
  obtain ⟨Q,q,φ,hφ,hL,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩ :=
    prior_fixed_minimum_geometric_limit hhaar hgauss N hN hNlim m 0
      (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
      (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
      (fun k => restrictedZeroTreePrior (S k) (hS k)) eig K hK heig I hdis hcover lam hlam ρ hρ u hu v hv hmin
  refine ⟨Q,q,φ,hφ,?_,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩
  apply hL.congr
  intro k
  exact (restricted_zero_tree_perturbed_array_law (hpos (φ k)) (S (φ k)) (hS (φ k))
    (μ (φ k)) (θ (φ k)) (eig (φ k)) (I (φ k)) (u (φ k)) (v (φ k)) 1).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetProductTrialWitness
attribute [-instance] _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical subsequence supplies both block self-consistency and the constrained pressure trial. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators
namespace InvariantIsing

theorem offset_product_minimum_trial_witness (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n r₀ : ℕ}
    (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j) (hKlim : Tendsto K atTop atTop)
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < r₀+K j*n) (hNlim : Tendsto (fun j => r₀+K j*n) atTop atTop)
    (hN3 : ∀ j, 3 ≤ r₀+K j*n)
    (g : (j : ℕ) → Fin (r₀+K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (r₀+K j*n+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (r₀+K j*n))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ r₀+K j*n+n)
    (μ : (j : ℕ) → Measure (Orthogonal (r₀+K j*n+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (r₀+K j*n)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (r₀+K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) (u j) (v j) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) u' v')
    (good : (j : ℕ) → Set (SpecialOrthogonal (r₀+K j*n+n)))
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
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ))
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
    (A_ : CavityFactorBlocks d n)
    (hA : A_ = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A_}) atTop (𝓝 0))
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
    let Δ := fun j =>
      (∫ z, restrictedRotationLogMean
        (cavityProductSlice (offsetBlockConstraint (K j) R Cset) Cset)
        (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR Cset hCset) Cset hCset) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
        (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
      ∫ z, restrictedRotationLogMean (offsetBlockConstraint (K j) R Cset)
        (offsetBlockConstraint_nonempty R hR Cset hCset) z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e j).symm i)))
          (cavityBaseGroup (k j) (e j) a₀) (v j) 1)
        (cavityBaseGroup (k j) (e j) a₀) (cavityBaseAmplitude (u j)) z.1 ∂(ν j).prod (θ j)

    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
        Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
          (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField ρ lam hρ hρsum p r) t -
            cavityStrictUniformPath p r t) ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField ρ lam hρ hρsum p r)+
          fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
          spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
          (n : ℝ)⁻¹*(Δ (φ r)+(Real.log Cset.card-n*Real.log 2)) < ε := by
  intro Δ
  let I := fun j => cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
  let eig := fun j i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1
  let S := fun j => offsetBlockConstraint (K j) R Cset
  have hS j : (S j).Nonempty := offsetBlockConstraint_nonempty R hR Cset hCset
  let M := 1+∑ a, |lam a|
  have hM : 0<M := by
    have hh : 0≤∑ a, |lam a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [M]
    linarith
  have heig j i : |eig j i|≤M := by
    have hh := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
    dsimp only [eig,M]
    linarith
  have hlam j a i (hi : i∈I j a) : eig j i=lam a := by
    have hi' : ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1=a := (Finset.mem_filter.mp hi).2
    change lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1=lam a
    rw [hi']
  have hmass : Tendsto (fun j a => ((I j a).card : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ) := by
    apply hρlim.congr
    intro j
    funext a
    rw [cavity_group_dimension_card]
  obtain ⟨Q,q,φ,hφ,hlim,hgg,hδ,hG,hE,hP,hnonneg,hoff,hdiag⟩ :=
    restricted_fixed_minimum_geometric_limit hhaar hgauss (fun j => r₀+K j*n) hN3 hNlim m
      S hS ν θ eig M hM heig I (fun _ => cavitySpectralGroup_pairwiseDisjoint _)
      (fun _ => cavitySpectralGroup_cover _) lam hlam ρ hmass u hu v hv hmin
  let p := spectralSpinQuantilePath Q hP hnonneg
  have hua j i : |cavityBaseAmplitude (u j) i|≤2 := cavityBaseAmplitude_bound (u j) (hu j) i
  have hva j a : |v j a|≤2 := abs_le.mpr ⟨by linarith [(hv j a).1],(hv j a).2⟩
  refine ⟨p,φ,hφ,?_,?_⟩
  · intro Φ
    exact offset_product_weak_self_consistency hpub (fun j => K (φ j)) (fun _ => 0)
      (fun j => hK (φ j)) (hKlim.comp hφ.tendsto_atTop) R hR Cset hCset (fun j => hN (φ j)) (hNlim.comp hφ.tendsto_atTop)
      (fun j => g (φ j)) (fun j => k (φ j)) (fun j => ek (φ j)) (fun j => e (φ j)) es B₀ a₀
      (fun j => hk (φ j)) (fun j => μG (φ j)) (fun j => l (φ j)) (fun j => w (φ j))
      (fun j => hg (φ j)) (fun j => hln (φ j)) (fun j => hw (φ j))
      (fun j => μ (φ j)) (fun j => ν (φ j)) (fun j => θ (φ j)) lam
      (fun j => v (φ j)) (fun j => hva (φ j)) (fun j => cavityBaseAmplitude (u (φ j)))
      (fun j => hua (φ j)) (fun j => good (φ j)) (fun j => hgood (φ j))
      (hp.comp hφ.tendsto_atTop) hL (fun j => hbound (φ j)) hd hn hB₀ ρ hρ hρsum hperp
      (fun j => hgroups (φ j)) (fun a => (hdims a).comp hφ.tendsto_atTop) hc
      (fun j => hcG (φ j)) (hρlim.comp hφ.tendsto_atTop) A_ hA
      (fun δ hδ => (hprob δ hδ).comp hφ.tendsto_atTop)
      Q hlim hgg hG (fun a => (q a : ℝ)) (fun a => (q a).property.1) hδ hE hP hnonneg hoff hdiag
      amax hmax Φ
  · have hh := restricted_physical_trial_lower hn (fun j => r₀+K (φ j)*n) (fun _ => 0)
      (fun j => S (φ j)) (fun j => hS (φ j)) Cset hCset
      (fun j => hN (φ j)) (hNlim.comp hφ.tendsto_atTop)
      (fun j => g (φ j)) (fun j => k (φ j)) (fun j => e (φ j)) (fun j => ek (φ j)) es B₀
      (fun a j => l (φ j) a) (fun a j => w (φ j) a)
      (fun j => hg (φ j)) (fun j => hln (φ j)) (fun j => hw (φ j)) a₀ (fun j => hk (φ j))
      (fun j => hgroups (φ j)) (fun a => (hdims a).comp hφ.tendsto_atTop)
      (fun j => μ (φ j)) (fun j => ν (φ j)) (fun j => θ (φ j)) (fun j => μG (φ j))
      lam (fun j => v (φ j)) (fun j => cavityBaseAmplitude (u (φ j)))
      (fun j => hva (φ j)) (fun j => hua (φ j)) hc (fun j => hcG (φ j)) ρ hρ hρsum
      (hρlim.comp hφ.tendsto_atTop) Q hlim hgg hG (fun a => (q a : ℝ))
      (fun a => (q a).property.1) hδ hE hP hnonneg hoff hdiag
      (cavityCompressionLimitFrame es B₀) (cavityCompressionLimitFrame_gram es B₀ hB₀)
      (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
      (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
      amax hmax counts hcounts_le hcounts hcounts_rho
      (fun ε hε => by simpa only [hA, Function.comp_def] using (hprob ε hε).comp hφ.tendsto_atTop)
    exact hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetWindowTrialWitness
attribute [-instance] _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar window theorems supply the physical compression hypotheses of block consistency. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators
namespace InvariantIsing

theorem offset_window_minimum_trial_witness_oai (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n r₀ : ℕ}
    (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j) (hKlim : Tendsto K atTop atTop)
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < r₀+K j*n) (hNlim : Tendsto (fun j => r₀+K j*n) atTop atTop)
    (hN3 : ∀ j, 3 ≤ r₀+K j*n)
    (g : (j : ℕ) → Fin (r₀+K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (r₀+K j*n+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (r₀+K j*n))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ r₀+K j*n+n)
    (μ : (j : ℕ) → Measure (Orthogonal (r₀+K j*n+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (r₀+K j*n)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (r₀+K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) (u j) (v j) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) u' v')
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun j => w j a) atTop atTop)
    (hllim : ∀ a, (∀ j, l j a=0) ∨ Tendsto (fun j => l j a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun j => (l j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun j => (w j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ))
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
    let Δ := fun j =>
      (∫ z, restrictedRotationLogMean
        (cavityProductSlice (offsetBlockConstraint (K j) R Cset) Cset)
        (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR Cset hCset) Cset hCset) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
        (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
      ∫ z, restrictedRotationLogMean (offsetBlockConstraint (K j) R Cset)
        (offsetBlockConstraint_nonempty R hR Cset hCset) z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e j).symm i)))
          (cavityBaseGroup (k j) (e j) a₀) (v j) 1)
        (cavityBaseGroup (k j) (e j) a₀) (cavityBaseAmplitude (u j)) z.1 ∂(ν j).prod (θ j)

    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
        Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
          (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField ρ lam hρ hρsum p r) t -
            cavityStrictUniformPath p r t) ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField ρ lam hρ hρsum p r)+
          fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
          spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
          (n : ℝ)⁻¹*(Δ (φ r)+(Real.log Cset.card-n*Real.log 2)) < ε := by
  intro Δ
  subst ρ
  have hsumlim : Tendsto (fun j => r₀+K j*n+n) atTop atTop :=
    (tendsto_add_atTop_nat n).comp hNlim
  obtain ⟨⟨L,hL,hgood⟩,hprob⟩ := cavity_window_inputs es lam a₀ B₀ hB₀ (fun j => r₀+K j*n)
    (fun j => Nat.add_pos_left (hN j) n) (fun a j => l j a) (fun a j => w j a) g
    (fun a j => hg j a) hsumlim hwlim hllim
    (fun a j => by have := hln j a; omega)
    (fun a j => by have := hln j a; have := hw j a; omega)
    (fun a j => hw j a) ρl ρw hρ hρsum (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρw a) hperp μ
  let A : CavityFactorBlocks d n :=
    ((cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityCompressionLimitFrame es B₀-Matrix.diagonal (fun j => lam (a₀ j)),
     (cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) (fun a => ρw a-ρl a),
     (finiteR (fun a => ρw a-ρl a) lam hρ hρsum 0) • 1)
  exact offset_product_minimum_trial_witness hhaar hgauss hpub K hK hKlim R hR Cset hCset hN hNlim hN3
    g k ek e es B₀ a₀ hk μG l w hg hln hw μ ν θ lam v hv u hu hmin
    (fun j => cavityCompressionGoodEvent (g j) L)
    (fun j => measurableSet_cavityCompressionGoodEvent (g j) L) hgood hL
    (fun _ _ hU => hU) hd hn hB₀ (fun a => ρw a-ρl a) hρ hρsum hperp
    hgroups hdims hc hcG hρlim A rfl hprob amax hmax counts hcounts_le hcounts hcounts_rho

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.offset_window_minimum_trial_witness_oai := @OAI.InvariantIsing.offset_window_minimum_trial_witness_oai
