-- Prove2me | solution 1 for OAI.InvariantIsing.marchenkoPastur_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:30:27.94524+00:00
-- url     : https://prove2.me/submissions/9ddd4194-ad9e-47f0-8c47-35d38e17cd15

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
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
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_gaussianPatternStieltjes_tendsto
import Theorems.Thm_OAI_InvariantIsing_gaussianPattern_spectralExcess_tendsto

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive real resolvent of the physical Gaussian Gram matrix. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianPatternCoupling_posSemidef {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (gaussianPatternCoupling 1 z).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (gaussianPatternArray z)
  simpa only [gaussianPatternCoupling,Matrix.conjTranspose_eq_transpose_of_trivial] using
    h.smul (show 0 ≤ (1 : ℝ)/N by positivity)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_HermitianEigenvalueRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Hermitian eigenvalues are uniquely determined by their real characteristic roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace InvariantIsing

lemma hermitian_eigenvalues₀_eval {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (t : ℝ) :
    A.charpoly.eval t = ∏ i : Fin (Fintype.card (Fin N)), (t-hA.eigenvalues₀ i) := by
  have hp := hA.roots_charpoly_eq_eigenvalues₀
  have hs := hA.splits_charpoly
  rw [hs.eval_eq_prod_roots_of_monic (Matrix.charpoly_monic A) t,hp]
  rw [Multiset.map_map]
  rfl

lemma hermitian_eigenvalues₀_unique {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (e : Fin (Fintype.card (Fin N)) → ℝ) (he : Antitone e)
    (hroot : ∀ t : ℝ, A.charpoly.eval t = ∏ i, (t-e i)) : hA.eigenvalues₀ = e := by
  have hp : A.charpoly = ∏ i, (X-C (e i)) := by
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using hroot t
  have hr : A.charpoly.roots = Multiset.map e Finset.univ.val := by
    rw [hp,Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero]
  have ho := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hr] at ho
  simp only [Fin.univ_val_map,Multiset.map_coe,List.map_ofFn,Function.comp_def,
    RCLike.re_to_real,Multiset.coe_sort] at ho
  have hsort : (List.ofFn e).mergeSort (fun x y => decide (x ≥ y)) = List.ofFn e := by
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq,← List.sortedGE_iff_pairwise]
    exact he.sortedGE_ofFn
  rw [hsort] at ho
  exact List.ofFn_inj.mp ho.symm

lemma hermitian_eigenvalues₀_norm_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin N))) : |hA.eigenvalues₀ i| ≤ ‖A‖ := by
  let j : Fin N := (Fintype.equivOfCardEq (Fintype.card_fin _)) i
  let : Nonempty (Fin N) := ⟨j⟩
  have hm := hA.eigenvalues_mem_spectrum_real j
  have hh := spectrum.norm_le_norm_of_mem hm
  simpa only [Real.norm_eq_abs,Matrix.IsHermitian.eigenvalues,j,Equiv.symm_apply_apply] using hh

lemma hermitian_eval_tendsto {N : ℕ} {A : ℕ → Matrix (Fin N) (Fin N) ℝ}
    {B : Matrix (Fin N) (Fin N) ℝ} (hA : Filter.Tendsto A Filter.atTop (nhds B)) (t : ℝ) :
    Filter.Tendsto (fun n => (A n).charpoly.eval t) Filter.atTop (nhds (B.charpoly.eval t)) := by
  simp only [Matrix.eval_charpoly]
  exact ((continuous_const.sub continuous_id).matrix_det.tendsto B).comp hA

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_HermitianEigenvalueLimits
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Limits of ordered Hermitian roots, with multiplicities retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Polynomial Filter Set
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace InvariantIsing

lemma hermitian_eigenvalues₀_limit_unique {N : ℕ}
    (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ n, (A n).IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.IsHermitian)
    (hAB : Tendsto A atTop (𝓝 B)) (e : Fin (Fintype.card (Fin N)) → ℝ)
    (he : Tendsto (fun n => (hA n).eigenvalues₀) atTop (𝓝 e)) : e = hB.eigenvalues₀ := by
  have heord : Antitone e := by
    intro i j hij
    exact le_of_tendsto_of_tendsto ((continuous_apply j).tendsto e |>.comp he)
      ((continuous_apply i).tendsto e |>.comp he)
      (Eventually.of_forall fun n => (hA n).eigenvalues₀_antitone hij)
  apply (hermitian_eigenvalues₀_unique B hB e heord ?_).symm
  intro t
  have hp : Tendsto (fun n => ∏ i, (t-(hA n).eigenvalues₀ i)) atTop (𝓝 (∏ i, (t-e i))) := by
    apply tendsto_finsetProd
    intro i _
    exact tendsto_const_nhds.sub ((continuous_apply i).tendsto e |>.comp he)
  have hq := hermitian_eval_tendsto hAB t
  have hfn : (fun n => (A n).charpoly.eval t) =
      (fun n => ∏ i, (t-(hA n).eigenvalues₀ i)) :=
    funext fun n => hermitian_eigenvalues₀_eval (A n) (hA n) t
  rw [hfn] at hq
  exact tendsto_nhds_unique hq hp

theorem hermitian_eigenvalues₀_tendsto {N : ℕ}
    (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ n, (A n).IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.IsHermitian)
    (hAB : Tendsto A atTop (𝓝 B)) :
    Tendsto (fun n => (hA n).eigenvalues₀) atTop (𝓝 hB.eigenvalues₀) := by
  obtain ⟨R,hR,hAR⟩ := (Metric.isBounded_range_of_tendsto A hAB).exists_pos_norm_le
  have hb (n : ℕ) : ‖(hA n).eigenvalues₀‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro i
    exact (hermitian_eigenvalues₀_norm_le (A n) (hA n) i).trans (hAR (A n) (mem_range_self n))
  by_contra ht
  simp only [Metric.tendsto_nhds] at ht
  push Not at ht
  obtain ⟨ε,hε,hfreq⟩ := ht
  let K : Set (Fin (Fintype.card (Fin N)) → ℝ) :=
    Metric.closedBall 0 R ∩ {e | ε ≤ dist e hB.eigenvalues₀}
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hmem : ∃ᶠ n in atTop, (hA n).eigenvalues₀ ∈ K := by
    apply hfreq.mono
    intro n hn
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hb n,hn⟩
  obtain ⟨e,heK,φ,hφ,hφe⟩ := hK.tendsto_subseq' hmem
  have heq : e = hB.eigenvalues₀ := hermitian_eigenvalues₀_limit_unique
    (fun n => A (φ n)) (fun n => hA (φ n)) B hB (hAB.comp hφ.tendsto_atTop) e hφe
  have hz : ε ≤ dist e hB.eigenvalues₀ := heK.2
  rw [heq,dist_self] at hz
  exact (not_le_of_gt hε) hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternEigenvalueMeasurability
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual sorted Gaussian Gram spectrum, including repeated zero roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace InvariantIsing

lemma continuous_hermitian_eigenvalues₀ {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {N : ℕ} (A : X → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) : Continuous (fun x => (hA x).eigenvalues₀) := by
  apply SeqContinuous.continuous
  intro x p hp
  exact hermitian_eigenvalues₀_tendsto (fun n => A (x n)) (fun n => hA (x n)) (A p) (hA p)
    ((hc.tendsto p).comp hp)

lemma continuous_hermitian_eigenvalues {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {N : ℕ} (A : X → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) : Continuous (fun x => (hA x).eigenvalues) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp (continuous_hermitian_eigenvalues₀ A hA hc)

lemma continuous_gaussianPatternCoupling (N m : ℕ) (c : ℝ) :
    Continuous (gaussianPatternCoupling (N := N) (m := m) c) := by
  unfold gaussianPatternCoupling gaussianPatternArray
  fun_prop

theorem continuous_gaussianPatternEigenvalues (N m : ℕ) :
    Continuous (gaussianPatternEigenvalues (N := N) (m := m)) := by
  unfold gaussianPatternEigenvalues
  exact continuous_hermitian_eigenvalues (gaussianPatternCoupling 1)
    (gaussianPatternCoupling_isHermitian 1) (continuous_gaussianPatternCoupling N m 1)

theorem measurable_gaussianPatternEigenvalues (N m : ℕ) :
    Measurable (gaussianPatternEigenvalues (N := N) (m := m)) :=
  (continuous_gaussianPatternEigenvalues N m).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_FiniteSpectralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general measure transform agrees with the finite-alphabet transform.
Positive masses ensure that the upper edge is an atom and the inverse is uncapped. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralMeasure (ρ eig : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (f : ℝ → ℝ) :
    (∫ y, f y ∂finiteSpectralMeasure ρ eig) = ∑ a, ρ a * f (eig a) := by
  have hi a : Integrable f (ENNReal.ofReal (ρ a) • Measure.dirac (eig a)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [finiteSpectralMeasure, Measure.sum_fintype,
    integral_finsetSum_measure (fun a _ => hi a)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hρ _), smul_eq_mul]

theorem ae_finiteSpectralMeasure (ρ eig : ι → ℝ) {P : ℝ → Prop} (hP : ∀ a, P (eig a)) :
    ∀ᵐ y ∂finiteSpectralMeasure ρ eig, P y := by
  rw [finiteSpectralMeasure, Measure.ae_sum_iff]
  intro a
  have hd : ∀ᵐ y ∂Measure.dirac (eig a), P y := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hP a
  exact Measure.ae_smul_measure hd _

end InvariantIsing

end

end OAI
end

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

lemma empiricalSpectralLaw_integral {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(empiricalSpectralLaw hN eig : Measure ℝ))=(1 : ℝ)/N*∑ i, f (eig i) := by
  change (∫ x, f x ∂finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig)=_
  rw [integral_finiteSpectralMeasure _ _ (fun _ => by positivity)]
  rw [Finset.mul_sum]

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

lemma spectralClip_close {a b x η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hx : a-η ≤ x ∧ x ≤ b+η) : |spectralClip a b x-x| ≤ η := by
  by_cases ha : x < a
  · have he : spectralClip a b x=a := by simp [spectralClip,min_eq_right (ha.le.trans hab),max_eq_left ha.le]
    rw [he,abs_of_nonneg (sub_nonneg.mpr ha.le)]
    linarith [hx.1]
  · by_cases hb : b < x
    · have he : spectralClip a b x=b := by simp [spectralClip,min_eq_left hb.le,max_eq_right hab]
      rw [he,abs_of_nonpos (sub_nonpos.mpr hb.le)]
      linarith [hx.2]
    · rw [spectralClip_eq ⟨le_of_not_gt ha,le_of_not_gt hb⟩,sub_self,abs_zero]
      exact hη

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral excess vanishes under the no-outlier condition. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

lemma spectralExcess_nonneg {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) :
    0 ≤ spectralExcess eig a b := Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma spectralExcess_bounds {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) (i : Fin N) :
    a-spectralExcess eig a b ≤ eig i ∧ eig i ≤ b+spectralExcess eig a b := by
  have hh : max (a-eig i) (eig i-b) ≤ spectralExcess eig a b := by
    unfold spectralExcess
    exact Finset.le_max' (insert (0 : ℝ) (Finset.univ.image (fun j => max (a-eig j) (eig j-b))))
      (max (a-eig i) (eig i-b)) (by
        rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hl := (le_max_left (a-eig i) (eig i-b)).trans hh
  have hu := (le_max_right (a-eig i) (eig i-b)).trans hh
  constructor <;> linarith

lemma spectralExcess_le {N : ℕ} (eig : Fin N → ℝ) (a b ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i, a-ε ≤ eig i ∧ eig i ≤ b+ε) : spectralExcess eig a b ≤ ε := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hε
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact max_le (by linarith [(h i).1]) (by linarith [(h i).2])

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventEigenbasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive resolvent in the eigenbasis of the original positive matrix. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma positiveResolvent_eigenvector {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (i : Fin N) :
    (positiveResolvent t B).toEuclideanLin (hB.isHermitian.eigenvectorBasis i) =
      (t+hB.isHermitian.eigenvalues i)⁻¹ • hB.isHermitian.eigenvectorBasis i := by
  let u := (hB.isHermitian.eigenvectorBasis i).ofLp
  let a := hB.isHermitian.eigenvalues i
  have ha : 0 < t+a := add_pos_of_pos_of_nonneg ht (hB.eigenvalues_nonneg i)
  have hBu : B *ᵥ u = a • u := hB.isHermitian.mulVec_eigenvectorBasis i
  have hAu : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ u = (t+a) • u := by
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hBu,add_smul]
  have hinv : positiveResolvent t B*(t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have hh : (t+a) • (positiveResolvent t B *ᵥ u) = u := by
    rw [← Matrix.mulVec_smul,← hAu,Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  have hu : positiveResolvent t B *ᵥ u = (t+a)⁻¹ • u := by
    calc
      _ = (t+a)⁻¹ • ((t+a) • (positiveResolvent t B *ᵥ u)) := by
        rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
      _ = _ := by rw [hh]
  ext j
  exact congrFun hu j

lemma positiveResolvent_trace_eigenvalues {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (positiveResolvent t B).trace = ∑ i, (t+hB.isHermitian.eigenvalues i)⁻¹ := by
  have htr := LinearMap.trace_eq_sum_inner (positiveResolvent t B).toEuclideanLin hB.isHermitian.eigenvectorBasis
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.trace_toLin_eq] at htr
  rw [htr]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [positiveResolvent_eigenvector ht hB,real_inner_smul_right,real_inner_self_eq_norm_sq]
  simp only [hB.isHermitian.eigenvectorBasis.orthonormal.1 i,one_pow,mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramEmpiricalTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the physical matrix resolvent with the empirical spectral transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

theorem gaussianGramStieltjes_empirical_integral {N m : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN (gaussianPatternEigenvalues z) : Measure ℝ)) =
      gaussianGramStieltjes t z := by
  rw [empiricalSpectralLaw_integral]
  have hB := gaussianPatternCoupling_posSemidef z
  have hs (i : Fin N) : positiveResolventTest t (gaussianPatternEigenvalues z i) =
      (t+hB.isHermitian.eigenvalues i)⁻¹ := by
    have hp : 0 ≤ gaussianPatternEigenvalues z i := by
      unfold gaussianPatternEigenvalues
      exact hB.eigenvalues_nonneg i
    unfold positiveResolventTest
    rw [max_eq_left hp]
    simp only [one_div,gaussianPatternEigenvalues]
  simp_rw [hs]
  rw [← positiveResolvent_trace_eigenvalues ht hB]
  change (1/(N : ℝ))*(gaussianGramResolvent t z).trace = (gaussianGramResolvent t z).trace/N
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the angular MP density, including the critical zero edge. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_angular_denominator_nonneg {α : ℝ} (hα : 0 ≤ α) (x : ℝ) :
    0 ≤ 1+α+2*sqrt α*cos x := by
  have hs := sq_sqrt hα
  have hc := neg_one_le_cos x
  have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*sqrt α by positivity)
  nlinarith [sq_nonneg (sqrt α-1)]

lemma mp_angular_denominator_pos {α : ℝ} (hα : 0 < α) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) : 0 < 1+α+2*sqrt α*cos x := by
  have hs := sq_sqrt hα.le
  have hc : -1 < cos x := by
    simpa only [cos_pi] using cos_lt_cos_of_nonneg_of_le_pi hx.1.le (le_refl Real.pi) hx.2
  have h := mul_lt_mul_of_pos_left hc (mp_radius_positive hα)
  nlinarith [sq_nonneg (sqrt α-1)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary shifted angular integral for the MP Stieltjes transform. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_shifted_centre_exceeds_radius {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    |2*sqrt α| < 1+α+t := by
  have hs := sq_sqrt hα
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (sqrt α-1)]

lemma mp_shifted_sine_integrable {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    IntervalIntegrable (fun x => (sin x)^2/(1+α+t+2*sqrt α*cos x)) volume 0 Real.pi :=
  ((continuous_sin.pow 2).div (continuous_const.add (continuous_const.mul continuous_cos))
    (fun x => (mp_cos_denominator_pos (mp_shifted_centre_exceeds_radius hα ht) x).ne')).intervalIntegrable _ _

lemma mp_shifted_angular_integral {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/(1+α+t+2*sqrt α*cos x)) =
        (1+α+t-sqrt ((1+α+t)^2-4*α))/2 := by
  have hab := mp_shifted_centre_exceeds_radius hα.le ht
  rw [mp_integral_sine_fraction hab (mp_radius_positive hα).ne']
  have hs : (2*sqrt α)^2 = 4*α := by nlinarith [sq_sqrt hα.le]
  rw [hs]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular Stieltjes transform, with the MP zero atom retained. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_angular_partial_fraction {α t : ℝ} (hα : 0 < α) (ht : 0 < t) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) :
    (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x))) =
      ((sin x)^2/(1+α+2*sqrt α*cos x)-(sin x)^2/(1+α+t+2*sqrt α*cos x))/t := by
  have hd := (mp_angular_denominator_pos hα hx).ne'
  have he := (mp_cos_denominator_pos (mp_shifted_centre_exceeds_radius hα.le ht) x).ne'
  have hs : t+(1+α+2*sqrt α*cos x) = 1+α+t+2*sqrt α*cos x := by ring
  rw [hs]
  field_simp [ht.ne',hd,he]
  ring

theorem mp_angular_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    max (1-α) 0/t+(2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) =
        marchenkoPasturTransform t α := by
  have he : (∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) =
      ((∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(1+α+2*sqrt α*cos x))-
        ∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(1+α+t+2*sqrt α*cos x))/t := by
    rw [← intervalIntegral.integral_sub (mp_angular_sine_integrable hα) (mp_shifted_sine_integrable hα.le ht),
      ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr_Ioo_of_le pi_pos.le (fun x hx => mp_angular_partial_fraction hα ht hx)
  rw [he,← mul_div_assoc,mul_sub,mp_angular_continuous_mass hα,mp_shifted_angular_integral hα ht]
  have hs : (1+α+t)^2-4*α = (t+α-1)^2+4*t := by ring
  rw [hs]
  have hm := mp_total_mass α
  unfold marchenkoPasturTransform
  field_simp
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensitySubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact real change of variables for the literal MP density on its support interval. -/
noncomputable section
open Real Set MeasureTheory
namespace InvariantIsing

lemma measurable_mpDensity (α : ℝ) : Measurable (mpDensity α) := by
  unfold mpDensity
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensityTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive resolvent transform of the literal Marchenko--Pastur measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace InvariantIsing

lemma mpDensity_measure_integral (α : ℝ) (g : ℝ → ℝ) :
    (∫ x, g x ∂(volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
      (fun x => ENNReal.ofReal (mpDensity α x))) =
    ∫ x in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α x*g x := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_mpDensity α).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [ENNReal.toReal_ofReal (mpDensity_nonneg hx),smul_eq_mul]

theorem marchenkoPastur_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (∫ x, positiveResolventTest t x ∂marchenkoPasturMeasure α) =
      marchenkoPasturTransform t α := by
  have := marchenkoPastur_probability hα
  let ν := (volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
    (fun x => ENNReal.ofReal (mpDensity α x))
  have hν : ν ≤ marchenkoPasturMeasure α := by
    rw [marchenkoPasturMeasure_eq_density]
    exact Measure.le_add_left le_rfl
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  have : IsFiniteMeasure (ENNReal.ofReal (max (1-α) 0) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  have hi (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (positiveResolventTest t) μ := by
    apply (integrable_const (1/t)).mono' (continuous_positiveResolventTest ht).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (positiveResolventTest_bound ht x).1]
      exact (positiveResolventTest_bound ht x).2
  have hv : (∫ x, positiveResolventTest t x ∂ν) =
      (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
        (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) := by
    rw [mpDensity_measure_integral,mpDensity_substitution hα]
    have he : (∫ x in Icc 0 Real.pi,
        (2*α/Real.pi)*((sin x)^2/mpAngle α x)*positiveResolventTest t (mpAngle α x)) =
        ∫ x in Icc 0 Real.pi, (2*α/Real.pi)*
          ((sin x)^2/(mpAngle α x*(t+mpAngle α x))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      unfold positiveResolventTest
      rw [max_eq_left (show 0 ≤ mpAngle α x from mp_angular_denominator_nonneg hα.le x)]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le pi_pos.le,
      intervalIntegral.integral_const_mul]
    rfl
  rw [marchenkoPasturMeasure_eq_density,integral_add_measure (hi _) (hi ν),
    integral_smul_measure,integral_dirac]
  change (ENNReal.ofReal (max (1-α) 0)).toReal*positiveResolventTest t 0+
    (∫ x, positiveResolventTest t x ∂ν) = _
  rw [ENNReal.toReal_ofReal (le_max_right _ _),hv]
  simpa only [positiveResolventTest,max_self,add_zero,mul_one_div] using mp_angular_transform hα ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ResolventPowerDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of bounded positive-resolvent moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

lemma positiveResolventTest_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => positiveResolventTest s x) (-(positiveResolventTest t x)^2) t := by
  have hn : t+max x 0 ≠ 0 := (add_pos_of_pos_of_nonneg ht (le_max_right x 0)).ne'
  refine ((((hasDerivAt_id t).add_const (max x 0)).inv hn).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [positiveResolventTest,one_div,Pi.inv_apply,id_eq]
  · simp only [positiveResolventTest,div_eq_mul_inv,inv_pow,one_mul,id_eq,neg_mul]

lemma positiveResolventPower_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℕ) :
    HasDerivAt (fun s => (positiveResolventTest s x)^n)
      (-(n : ℝ)*(positiveResolventTest t x)^(n+1)) t := by
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,neg_zero,zero_mul] using hasDerivAt_const t (1 : ℝ)
  | succ n ih =>
    refine ((ih.mul (positiveResolventTest_hasDerivAt ht x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      exact pow_succ _ _
    · simp only [Nat.cast_succ,pow_succ]
      ring

lemma positiveResolventPower_integrable {t : ℝ} (ht : 0 < t) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => (positiveResolventTest t x)^n) μ := by
  apply Integrable.of_bound ((continuous_positiveResolventTest ht).pow n).aestronglyMeasurable ((1/t)^n)
  exact ae_of_all _ fun x => by
    change ‖(positiveResolventTest t x)^n‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (positiveResolventTest_bound ht x).1 _)]
    exact pow_le_pow_left₀ (positiveResolventTest_bound ht x).1 (positiveResolventTest_bound ht x).2 n

theorem positiveResolventPower_integral_hasDerivAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s => ∫ x, (positiveResolventTest s x)^n ∂μ)
      (-(n : ℝ)*(∫ x, (positiveResolventTest t x)^(n+1) ∂μ)) t := by
  have hs : Ioi (t/2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => (positiveResolventTest s x)^n) μ := by
    filter_upwards [hs] with s hs'
    exact ((continuous_positiveResolventTest (lt_trans (half_pos ht) hs')).pow n).aestronglyMeasurable
  have hd : ∀ᵐ x ∂μ, ∀ s ∈ Ioi (t/2),
      HasDerivAt (fun u => (positiveResolventTest u x)^n)
        (-(n : ℝ)*(positiveResolventTest s x)^(n+1)) s :=
    ae_of_all _ fun x s hs' => positiveResolventPower_hasDerivAt (lt_trans (half_pos ht) hs') x n
  have hb : ∀ᵐ x ∂μ, ∀ s ∈ Ioi (t/2),
      ‖-(n : ℝ)*(positiveResolventTest s x)^(n+1)‖ ≤ (n : ℝ)*(2/t)^(n+1) := by
    refine ae_of_all _ fun x s hs' => ?_
    have hsp : 0 < s := lt_trans (half_pos ht) hs'
    have hr : positiveResolventTest s x ≤ 2/t := by
      calc
        _ ≤ 1/s := (positiveResolventTest_bound hsp x).2
        _ ≤ 1/(t/2) := one_div_le_one_div_of_le (half_pos ht) hs'.le
        _ = 2/t := by ring
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (Nat.cast_nonneg n),
      Real.norm_of_nonneg (pow_nonneg (positiveResolventTest_bound hsp x).1 _)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (positiveResolventTest_bound hsp x).1 hr _) (Nat.cast_nonneg n)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm
    (positiveResolventPower_integrable ht n μ)
    (((continuous_positiveResolventTest ht).pow (n+1)).const_mul (-(n : ℝ))).aestronglyMeasurable
    hb (integrable_const _) hd).2
  simpa only [integral_const_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ResolventMomentIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of positive resolvents determines all their bounded powers. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem positiveResolvent_moments_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 < t → (∫ x, positiveResolventTest t x ∂μ) =
      ∫ x, positiveResolventTest t x ∂ν) :
    ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      (∫ x, (positiveResolventTest t x)^(n+1) ∂μ) =
        ∫ x, (positiveResolventTest t x)^(n+1) ∂ν := by
  intro n
  induction n with
  | zero => simpa only [zero_add,pow_one] using h
  | succ n ih =>
    intro t ht
    have he : (fun s => ∫ x, (positiveResolventTest s x)^(n+1) ∂ν) =ᶠ[𝓝 t]
        fun s => ∫ x, (positiveResolventTest s x)^(n+1) ∂μ := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (ih s hs).symm
    have hd := ((positiveResolventPower_integral_hasDerivAt μ ht (n+1)).congr_of_eventuallyEq he).unique
      (positiveResolventPower_integral_hasDerivAt ν ht (n+1))
    exact mul_left_cancel₀ (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_UnitIntervalMomentUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded polynomial moments determine a probability measure on the unit interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace InvariantIsing

theorem unitInterval_moments_unique (μ ν : Measure (Set.Icc (0 : ℝ) 1))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, (∫ x, (x : ℝ)^n ∂μ) = ∫ x, (x : ℝ)^n ∂ν) : μ = ν := by
  let g : Set.Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨Subtype.val,continuous_subtype_val⟩
  let ev : Polynomial ℝ →ₐ[ℝ] (Set.Icc (0 : ℝ) 1 →ᵇ ℝ) := Polynomial.aeval g
  let A : StarSubalgebra ℝ (Set.Icc (0 : ℝ) 1 →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    refine ⟨g,?_,?_⟩
    · refine ⟨g.toContinuousMap,?_,rfl⟩
      exact ⟨g,⟨Polynomial.X,by simp [ev]⟩,rfl⟩
    · exact fun he => hxy (Subtype.ext he)
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p,rfl⟩ := hf
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial n c =>
    have he (x : Set.Icc (0 : ℝ) 1) : ev (Polynomial.monomial n c) x = c*(x : ℝ)^n := by
      simp [ev,Polynomial.aeval_monomial,g]
    change (∫ x, ev (Polynomial.monomial n c) x ∂μ) =
      ∫ x, ev (Polynomial.monomial n c) x ∂ν
    simp only [he,integral_const_mul]
    exact congrArg (c * ·) (h n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ResolventMeasureUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvents determine probability measures on the nonnegative real line. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma continuous_resolventUnit : Continuous resolventUnit :=
  (continuous_positiveResolventTest (by norm_num : (0 : ℝ) < 1)).subtype_mk _

lemma resolventUnit_inverse {x : ℝ} (hx : 0 ≤ x) : 1/(resolventUnit x : ℝ)-1 = x := by
  change 1/(1/(1+max x 0))-1=x
  rw [max_eq_left hx,one_div_one_div]
  ring

lemma resolventUnit_map_inverse (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    (μ.map resolventUnit).map (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) = μ := by
  have hm : Measurable (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) := by fun_prop
  rw [Measure.map_map hm continuous_resolventUnit.measurable]
  calc
    μ.map ((fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) ∘ resolventUnit) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with x hx
      exact resolventUnit_inverse hx
    _ = μ := Measure.map_id

theorem positiveResolvent_unique (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ t : ℝ, 0 < t → (∫ x, positiveResolventTest t x ∂μ) =
      ∫ x, positiveResolventTest t x ∂ν) : μ = ν := by
  have : IsProbabilityMeasure (μ.map resolventUnit) :=
    (Measure.isProbabilityMeasure_map_iff continuous_resolventUnit.measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (ν.map resolventUnit) :=
    (Measure.isProbabilityMeasure_map_iff continuous_resolventUnit.measurable.aemeasurable).mpr inferInstance
  have he : μ.map resolventUnit = ν.map resolventUnit := by
    apply unitInterval_moments_unique
    intro n
    have hc : Continuous (fun x : Icc (0 : ℝ) 1 => (x : ℝ)^n) := continuous_subtype_val.pow n
    rw [integral_map continuous_resolventUnit.measurable.aemeasurable hc.aestronglyMeasurable,
      integral_map continuous_resolventUnit.measurable.aemeasurable hc.aestronglyMeasurable]
    cases n with
    | zero => simp only [pow_zero,integral_const,probReal_univ,smul_eq_mul,mul_one]
    | succ n => exact positiveResolvent_moments_eq μ ν h n 1 (by norm_num)
  have hi := congrArg (fun η : Measure (Icc (0 : ℝ) 1) =>
    η.map (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1)) he
  rwa [resolventUnit_map_inverse μ hμ,resolventUnit_map_inverse ν hν] at hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactFiniteTestControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many separating tests control a continuous image of a compact space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace InvariantIsing

theorem compact_finite_test_control {X ι Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i))
    (hsep : ∀ x y, (∀ i, F i x = F i y) → x = y)
    (G : X → Y) (hG : Continuous G) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ∃ δ : ι → ℝ, (∀ i, 0 < δ i) ∧
      ∀ x, (∀ i ∈ s, dist (F i x) (F i x₀) < δ i) → dist (G x) (G x₀) < ε := by
  classical
  let E : X → (ι → ℝ) := fun x i => F i x
  have hE : Continuous E := continuous_pi hF
  have he : Function.Injective E := fun x y h => hsep x y (congrFun h)
  have hi := (hE.isClosedEmbedding he).isEmbedding.isInducing
  have hu : G ⁻¹' Metric.ball (G x₀) ε ∈ 𝓝 x₀ :=
    hG.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  rw [hi.nhds_eq_comap] at hu
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hu
  rw [nhds_pi] at hV
  obtain ⟨s,W,hW,hWV⟩ := Filter.mem_pi'.mp hV
  choose δ hδ hd using fun i => Metric.mem_nhds_iff.mp (hW i)
  refine ⟨s,δ,hδ,fun x hx => ?_⟩
  apply hVU
  apply hWV
  intro i hi'
  exact hd i (hx i hi')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactTestsInMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence in measure from separating continuous tests on a compact state space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace InvariantIsing

theorem compact_tests_tendstoInMeasure {X ι Y Ω : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Ω] (P : Measure Ω)
    (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i))
    (hsep : ∀ x y, (∀ i, F i x = F i y) → x = y)
    (G : X → Y) (hG : Continuous G) (x₀ : X) (Z : ℕ → Ω → X)
    (hZ : ∀ i, TendstoInMeasure P (fun n ω => F i (Z n ω)) atTop (fun _ => F i x₀)) :
    TendstoInMeasure P (fun n ω => G (Z n ω)) atTop (fun _ => G x₀) := by
  classical
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  obtain ⟨s,δ,hδ,hcontrol⟩ := compact_finite_test_control F hF hsep G hG x₀ hε
  have hb (n : ℕ) : {ω | ε ≤ dist (G (Z n ω)) (G x₀)} ⊆
      ⋃ i ∈ s, {ω | δ i ≤ dist (F i (Z n ω)) (F i x₀)} := by
    intro ω hω
    have hh : ∃ i ∈ s, δ i ≤ dist (F i (Z n ω)) (F i x₀) := by
      by_contra! hh
      exact (not_lt_of_ge hω) (hcontrol (Z n ω) hh)
    obtain ⟨i,hi,hii⟩ := hh
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hii⟩⟩
  have ht := tendsto_finsetSum s (fun i _ => (tendstoInMeasure_iff_dist.mp (hZ i)) (δ i) (hδ i))
  have ht' : Tendsto (fun n => ∑ i ∈ s, P {ω | δ i ≤ dist (F i (Z n ω)) (F i x₀)})
      atTop (𝓝 0) := by simpa only [Finset.sum_const_zero] using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun _ => bot_le) (fun n => (measure_mono (hb n)).trans (measure_biUnion_finset_le _ _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactResolventTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvents as a separating family for compact nonnegative spectral laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

lemma compactResolventTests_separate (R : ℝ) (μ ν : ProbabilityMeasure (Icc (0 : ℝ) R))
    (h : ∀ t : {t : ℝ // 0 < t},
      (∫ x, compactResolventTest R t x ∂(μ : Measure _)) =
        ∫ x, compactResolventTest R t x ∂(ν : Measure _)) : μ = ν := by
  have hnonneg (η : ProbabilityMeasure (Icc (0 : ℝ) R)) :
      ∀ᵐ x ∂(η.map (f := (fun x => (x : ℝ))) measurable_subtype_coe.aemeasurable : Measure ℝ), 0 ≤ x := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Ici).mpr
    exact ae_of_all _ fun x => x.property.1
  have he := positiveResolvent_unique (μ.map (f := (fun x => (x : ℝ))) measurable_subtype_coe.aemeasurable : Measure ℝ)
    (ν.map (f := (fun x => (x : ℝ))) measurable_subtype_coe.aemeasurable : Measure ℝ) (hnonneg μ) (hnonneg ν) (fun t ht => ?_)
  · apply ProbabilityMeasure.toMeasure_injective
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    exact he
  · simp only [ProbabilityMeasure.toMeasure_map]
    rw [integral_map measurable_subtype_coe.aemeasurable
      (continuous_positiveResolventTest ht).aestronglyMeasurable,
      integral_map measurable_subtype_coe.aemeasurable
      (continuous_positiveResolventTest ht).aestronglyMeasurable]
    exact h ⟨t,ht⟩

theorem compact_resolvent_tendstoInMeasure (R : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ProbabilityMeasure (Icc (0 : ℝ) R)) (ν : ProbabilityMeasure (Icc (0 : ℝ) R))
    (h : ∀ t : {t : ℝ // 0 < t}, TendstoInMeasure P
      (fun n ω => ∫ x, compactResolventTest R t x ∂(Z n ω : Measure _)) Filter.atTop
      (fun _ => ∫ x, compactResolventTest R t x ∂(ν : Measure _))) :
    TendstoInMeasure P
      (fun n ω => LevyProkhorov.ofMeasure ((Z n ω).map (f := (fun x => (x : ℝ))) measurable_subtype_coe.aemeasurable)) Filter.atTop
      (fun _ => LevyProkhorov.ofMeasure (ν.map (f := (fun x => (x : ℝ))) measurable_subtype_coe.aemeasurable)) := by
  let F : {t : ℝ // 0 < t} → ProbabilityMeasure (Icc (0 : ℝ) R) → ℝ :=
    fun t η => ∫ x, compactResolventTest R t x ∂(η : Measure _)
  let G : ProbabilityMeasure (Icc (0 : ℝ) R) → LevyProkhorov (ProbabilityMeasure ℝ) :=
    fun η => LevyProkhorov.ofMeasure (η.map (measurable_subtype_coe.aemeasurable (f := fun x : Icc (0 : ℝ) R => (x : ℝ))))
  have hF : ∀ t, Continuous (F t) := fun t =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (compactResolventTest R t)
  have hG : Continuous G :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
      (ProbabilityMeasure.continuous_map (f := fun x : Icc (0 : ℝ) R => (x : ℝ)) continuous_subtype_val)
  exact compact_tests_tendstoInMeasure P F hF (compactResolventTests_separate R) G hG ν Z h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_LevyMapDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct coupling bound for the Levy--Prokhorov distance of two images. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace InvariantIsing

theorem levyProkhorov_map_dist_le_ae {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g)
    {δ : ℝ} (hδ : 0 ≤ δ) (hfg : ∀ᵐ ω ∂P, dist (f ω) (g ω) ≤ δ) :
    levyProkhorovDist (P.map f) (P.map g) ≤ δ := by
  have : IsProbabilityMeasure (P.map f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (P.map g) := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε S hε hS
  rw [Measure.map_apply hf hS,Measure.map_apply hg isOpen_thickening.measurableSet]
  have hs : f ⁻¹' S ≤ᵐ[P] g ⁻¹' thickening ε S := by
    filter_upwards [hfg] with ω hω hS'
    apply mem_thickening_iff.mpr
    exact ⟨f ω,hS',(by rw [dist_comm]; exact hω.trans_lt hε)⟩
  exact (measure_mono_ae hs).trans (le_add_right le_rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both spectral edges of the physical Gaussian Gram matrix, with arbitrary real scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma marchenkoPasturLower_positive_part {α : ℝ} (hα : 0 ≤ α) :
    marchenkoPasturLower α = (max (Real.sqrt α-1) 0)^2 := by
  have hs := Real.sq_sqrt hα
  have hn := Real.sqrt_nonneg α
  by_cases ha : α ≤ 1
  · have hh : Real.sqrt α-1 ≤ 0 := by nlinarith
    simp only [marchenkoPasturLower,ite_eq_left ha,max_eq_right hh,zero_pow (by decide : 2 ≠ 0)]
  · have hh : 0 ≤ Real.sqrt α-1 := by nlinarith
    rw [marchenkoPasturLower,ite_eq_right ha,marchenkoPasturA,max_eq_left hh]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensitySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support of the literal MP density, with its zero atom distinguished. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Topology
namespace InvariantIsing

lemma mp_edges_strict {α : ℝ} (hα : 0 < α) : marchenkoPasturA α < marchenkoPasturB α := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα.le
  rw [ha,hb]
  linarith [sqrt_pos.mpr hα]

lemma mpDensity_pos {α x : ℝ} (hx : x ∈ Ioo (marchenkoPasturA α) (marchenkoPasturB α)) :
    0 < mpDensity α x := by
  have hx0 : 0 < x := (sq_nonneg (1-sqrt α)).trans_lt hx.1
  exact div_pos (sqrt_pos.mpr (mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hx.1))) (by positivity)

lemma mp_interior_absolutelyContinuous {α : ℝ} :
    volume.restrict (Ioo (marchenkoPasturA α) (marchenkoPasturB α)) ≪ marchenkoPasturMeasure α := by
  let s := Ioo (marchenkoPasturA α) (marchenkoPasturB α)
  let f := fun x => ENNReal.ofReal (mpDensity α x)
  have hp : ∀ᵐ x ∂volume.restrict s, f x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (ENNReal.ofReal_pos.mpr (mpDensity_pos hx)).ne'
  have ha := withDensity_absolutelyContinuous' (μ := volume.restrict s)
    (measurable_mpDensity α).ennreal_ofReal.aemeasurable hp
  apply ha.trans
  apply Measure.absolutelyContinuous_of_le
  rw [marchenkoPasturMeasure_eq_density,← withDensity_indicator measurableSet_Ioo,
    ← withDensity_indicator measurableSet_Icc]
  apply le_trans (withDensity_mono (ae_of_all _ fun x => ?_)) (Measure.le_add_left le_rfl)
  exact indicator_le_indicator_of_subset Ioo_subset_Icc_self (fun _ => bot_le) x

theorem mp_interval_subset_support {α : ℝ} (hα : 0 < α) :
    Icc (marchenkoPasturA α) (marchenkoPasturB α) ⊆ (marchenkoPasturMeasure α).support := by
  have hi : Ioo (marchenkoPasturA α) (marchenkoPasturB α) ⊆
      (marchenkoPasturMeasure α).support := by
    intro x hx
    apply mp_interior_absolutelyContinuous.support_mono
    apply Measure.interior_inter_support
    exact ⟨by simpa only [isOpen_Ioo.interior_eq] using hx,by rw [Measure.support_eq_univ]; trivial⟩
  rw [← closure_Ioo (mp_edges_strict hα).ne]
  exact closure_minimal hi Measure.isClosed_support

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPMeasureSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise support and both endpoint clauses of the Gaussian MP input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Topology
namespace InvariantIsing

lemma mp_continuous_support_bound (α : ℝ) :
    ((volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
      (fun x => ENNReal.ofReal (mpDensity α x))).support ⊆
        Icc (marchenkoPasturA α) (marchenkoPasturB α) := by
  apply (withDensity_absolutelyContinuous _ _).support_mono.trans
  exact (Measure.support_restrict_subset).trans fun _ hx => by
    simpa only [isClosed_Icc.closure_eq] using hx.1

theorem marchenkoPastur_support_bound {α : ℝ} (_hα : 0 < α) :
    (marchenkoPasturMeasure α).support ⊆ Icc (marchenkoPasturLower α) (marchenkoPasturB α) := by
  rw [marchenkoPasturMeasure_eq_density,Measure.support_add]
  by_cases ha : α ≤ 1
  · rw [marchenkoPasturLower,ite_eq_left ha]
    rintro x (hx|hx)
    · have hs : (ENNReal.ofReal (max (1-α) 0) • Measure.dirac (0 : ℝ)).support ⊆ {0} := by
        apply Measure.smul_absolutelyContinuous.support_mono.trans
        apply Measure.support_subset_of_isClosed isClosed_singleton
        rw [mem_ae_iff]
        simp
      have he : x = 0 := hs hx
      subst x
      exact ⟨le_rfl,sq_nonneg _⟩
    · exact ⟨(sq_nonneg (1-sqrt α)).trans (mp_continuous_support_bound α hx).1,
        (mp_continuous_support_bound α hx).2⟩
  · rw [marchenkoPasturLower,ite_eq_right ha]
    have hz : max (1-α) 0 = 0 := max_eq_right (by linarith)
    simpa only [hz,ENNReal.ofReal_zero,zero_smul,Measure.support_zero,empty_union] using
      mp_continuous_support_bound α

theorem marchenkoPastur_right_mem {α : ℝ} (hα : 0 < α) :
    marchenkoPasturB α ∈ (marchenkoPasturMeasure α).support :=
  mp_interval_subset_support hα ⟨(mp_edges_strict hα).le,le_rfl⟩

theorem marchenkoPastur_left_mem {α : ℝ} (hα : 0 < α) :
    marchenkoPasturLower α ∈ (marchenkoPasturMeasure α).support := by
  by_cases ha : α < 1
  · rw [marchenkoPasturLower,ite_eq_left ha.le]
    have hp : ENNReal.ofReal (max (1-α) 0) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_max_of_lt_left (by linarith))).ne'
    have hac : Measure.dirac (0 : ℝ) ≪ marchenkoPasturMeasure α := by
      apply (Measure.absolutelyContinuous_smul hp).trans
      apply Measure.absolutelyContinuous_of_le
      rw [marchenkoPasturMeasure_eq_density]
      exact Measure.le_add_right le_rfl
    apply hac.support_mono
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hu : (0 : ℝ) ∈ U := mem_of_mem_nhds hU
    simp only [Measure.dirac_apply_of_mem hu,zero_lt_one]
  · have he : marchenkoPasturLower α = marchenkoPasturA α := by
      by_cases hle : α ≤ 1
      · have h : α = 1 := le_antisymm hle (not_lt.mp ha)
        subst α
        simp [marchenkoPasturLower,marchenkoPasturA]
      · simp only [marchenkoPasturLower,ite_eq_right hle]
    rw [he]
    exact mp_interval_subset_support hα ⟨le_rfl,(mp_edges_strict hα).le⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_InMeasurePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A vanishing metric perturbation preserves convergence in probability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem tendstoInMeasure_zero_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : ℕ → Ω → ℝ) (hg : TendstoInMeasure P g atTop (fun _ => 0))
    (hbound : ∀ n ω, |f n ω| ≤ |g n ω|) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoInMeasure_iff_dist.mp hg ε hε) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  simp only [mem_ofPred_eq,Real.dist_eq,sub_zero] at hω ⊢
  exact hω.trans (hbound n ω)

theorem tendstoInMeasure_div_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : TendstoInMeasure P f atTop (fun _ => 0))
    {c : ℝ} (hc : 0 < c) :
    TendstoInMeasure P (fun n ω => f n ω/c) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  convert (tendstoInMeasure_iff_dist.mp hf) (ε*c) (mul_pos hε hc) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  congr 1
  ext ω
  simp only [Real.dist_eq,sub_zero,abs_div,abs_of_pos hc]
  exact le_div_iff₀ hc

theorem tendstoInMeasure_of_dist_le {Ω Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Y]
    (P : Measure Ω) (f g : ℕ → Ω → Y) (h : ℕ → Ω → ℝ) (z : Ω → Y)
    (hg : TendstoInMeasure P g atTop z) (hh : TendstoInMeasure P h atTop (fun _ => 0))
    (hbound : ∀ n ω, dist (f n ω) (g n ω) ≤ h n ω) :
    TendstoInMeasure P f atTop z := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := half_pos hε
  have ht₁ := tendstoInMeasure_iff_dist.mp hh (ε/2) hhalf
  have ht₂ := tendstoInMeasure_iff_dist.mp hg (ε/2) hhalf
  have hb (n : ℕ) : {ω | ε ≤ dist (f n ω) (z ω)} ⊆
      {ω | ε/2 ≤ dist (h n ω) 0} ∪ {ω | ε/2 ≤ dist (g n ω) (z ω)} := by
    intro ω hω
    by_cases hh' : ε/2 ≤ dist (h n ω) 0
    · exact Or.inl hh'
    · right
      have hp : h n ω < ε/2 := lt_of_le_of_lt (by simpa only [Real.dist_eq,sub_zero] using le_abs_self (h n ω))
        (lt_of_not_ge hh')
      have hx := dist_triangle (f n ω) (g n ω) (z ω)
      have hb' := hbound n ω
      change ε ≤ dist (f n ω) (z ω) at hω
      change ε/2 ≤ dist (g n ω) (z ω)
      linarith
  have ht : Tendsto (fun n => P {ω | ε/2 ≤ dist (h n ω) 0}+
      P {ω | ε/2 ≤ dist (g n ω) (z ω)}) atTop (𝓝 0) := by
    simpa only [zero_add] using ht₁.add ht₂
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun n => (measure_mono (hb n)).trans (measure_union_le _ _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianZeroUpperExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved Gaussian edge law also controls clipping to the nonnegative MP interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma mp_lower_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ marchenkoPasturLower α := by
  rw [marchenkoPasturLower_positive_part hα]
  exact sq_nonneg _

lemma mp_lower_le_upper {α : ℝ} (hα : 0 < α) :
    marchenkoPasturLower α ≤ marchenkoPasturB α :=
  (marchenkoPastur_support_bound hα (marchenkoPastur_left_mem hα)).2

theorem gaussianPattern_zero_upper_excess {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => spectralExcess (gaussianPatternEigenvalues (Z (k+1) ω))
      0 (marchenkoPasturB α)) atTop (fun _ => 0) := by
  have ht := gaussianPattern_spectralExcess_tendsto hα P Z hZ 1
  simp only [one_mul,min_eq_left (mp_lower_le_upper hα),max_eq_right (mp_lower_le_upper hα)] at ht
  apply tendstoInMeasure_zero_of_abs_le P _ _ ht
  intro k ω
  rw [abs_of_nonneg (spectralExcess_nonneg _ _ _),abs_of_nonneg (spectralExcess_nonneg _ _ _)]
  apply spectralExcess_le _ _ _ _ (spectralExcess_nonneg _ _ _)
  intro i
  have hb := spectralExcess_bounds (gaussianPatternEigenvalues (Z (k+1) ω))
    (marchenkoPasturLower α) (marchenkoPasturB α) i
  exact ⟨by linarith [mp_lower_nonneg hα.le],hb.2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactSpectralClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped spectral probability laws on their compact interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma compactClippedLaw_real (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ) :
    (compactClippedLaw R hR μ).map (measurable_subtype_coe.aemeasurable (f := fun x : Icc (0 : ℝ) R => (x : ℝ))) = μ.map (f := (spectralClip 0 R)) (by first | (apply Continuous.aemeasurable; apply continuous_spectralClip <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [compactClippedLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_subtype_coe (continuous_compactSpectralClip R hR).measurable]
  rfl

lemma compactClippedLaw_integral (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ)
    (t : {t : ℝ // 0 < t}) :
    (∫ x, compactResolventTest R t x ∂(compactClippedLaw R hR μ : Measure _)) =
      ∫ x, positiveResolventTest t (spectralClip 0 R x) ∂(μ : Measure ℝ) := by
  rw [compactClippedLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_compactSpectralClip R hR).measurable.aemeasurable
      (compactResolventTest R t).continuous.aestronglyMeasurable]
  rfl

lemma compactClippedLaw_real_eq (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) R) :
    (compactClippedLaw R hR μ).map (measurable_subtype_coe.aemeasurable (f := fun x : Icc (0 : ℝ) R => (x : ℝ))) = μ := by
  rw [compactClippedLaw_real]
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  calc
    (μ : Measure ℝ).map (spectralClip 0 R) = (μ : Measure ℝ).map id :=
      Measure.map_congr (hμ.mono fun _ hx => spectralClip_eq hx)
    _ = μ := Measure.map_id

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ResolventLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact uniform modulus used when clipping nonnegative spectra. -/
noncomputable section
namespace InvariantIsing

theorem positiveResolventTest_sub_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |positiveResolventTest t x-positiveResolventTest t y| ≤ |x-y|/t^2 := by
  have hx := le_max_right x 0
  have hy := le_max_right y 0
  have htx : 0 < t+max x 0 := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t+max y 0 := add_pos_of_pos_of_nonneg ht hy
  have hd : t^2 ≤ (t+max x 0)*(t+max y 0) := by
    nlinarith [mul_nonneg hx hy]
  have hn : |max y 0-max x 0| ≤ |x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,abs_sub_comm,id_eq] using
      (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul y x
  have he : positiveResolventTest t x-positiveResolventTest t y =
      (max y 0-max x 0)/((t+max x 0)*(t+max y 0)) := by
    unfold positiveResolventTest
    field_simp [htx.ne',hty.ne']
    ring
  rw [he,abs_div,abs_of_pos (mul_pos htx hty)]
  exact (div_le_div_of_nonneg_right hn (mul_pos htx hty).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ht) hd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ClippedEmpiricalTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform resolvent error for the actual finite empirical spectral clipping. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

theorem empirical_transform_clip_error {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R η t : ℝ} (ht : 0 < t)
    (hclip : ∀ i, |spectralClip 0 R (eig i)-eig i| ≤ η) :
    |(∫ x, positiveResolventTest t (spectralClip 0 R x)
      ∂(empiricalSpectralLaw hN eig : Measure ℝ))-
      ∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN eig : Measure ℝ)| ≤ η/t^2 := by
  let μ := (empiricalSpectralLaw hN eig : Measure ℝ)
  have hc : Integrable (fun x => positiveResolventTest t (spectralClip 0 R x)) μ := by
    apply Integrable.of_bound
      ((continuous_positiveResolventTest ht).comp (continuous_spectralClip 0 R)).aestronglyMeasurable (1/t)
    exact ae_of_all _ fun x => by
      change ‖positiveResolventTest t (spectralClip 0 R x)‖ ≤ 1/t
      rw [Real.norm_eq_abs,abs_of_nonneg (positiveResolventTest_bound ht _).1]
      exact (positiveResolventTest_bound ht _).2
  have hi : Integrable (positiveResolventTest t) μ := by
    simpa only [pow_one] using positiveResolventPower_integrable ht 1 μ
  rw [← integral_sub hc hi,← Real.norm_eq_abs]
  have ha : ∀ᵐ x ∂μ, |spectralClip 0 R x-x| ≤ η := ae_finiteSpectralMeasure
    (fun _ => (1 : ℝ)/N) eig hclip
  have hb : ∀ᵐ x ∂μ, ‖positiveResolventTest t (spectralClip 0 R x)-positiveResolventTest t x‖ ≤ η/t^2 := by
    filter_upwards [ha] with x hx
    rw [Real.norm_eq_abs]
    exact (positiveResolventTest_sub_le ht _ _).trans
      (div_le_div_of_nonneg_right hx (sq_nonneg t))
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

theorem empirical_transform_clip_excess {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t) :
    |(∫ x, positiveResolventTest t (spectralClip 0 R x)
      ∂(empiricalSpectralLaw hN eig : Measure ℝ))-
      ∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN eig : Measure ℝ)| ≤
        spectralExcess eig 0 R/t^2 := by
  apply empirical_transform_clip_error hN eig ht
  intro i
  exact spectralClip_close hR (spectralExcess_nonneg _ _ _) (spectralExcess_bounds eig 0 R i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianClippedStieltjes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Gaussian transform limit survives clipping to the MP support bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_clipped_stieltjes {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => ∫ x, positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x)
      ∂(empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)) : Measure ℝ))
      atTop (fun _ => marchenkoPasturTransform t α) := by
  have hE := tendstoInMeasure_div_pos P _ (gaussianPattern_zero_upper_excess hα P Z hZ) (sq_pos_of_pos ht)
  apply tendstoInMeasure_of_dist_le P _ _ _ _ (gaussianPatternStieltjes_tendsto hα.le ht P Z hZ) hE
  intro k ω
  rw [Real.dist_eq,← gaussianGramStieltjes_empirical_integral (Nat.succ_pos k) ht]
  exact empirical_transform_clip_excess (Nat.succ_pos k) _ (sq_nonneg _) ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPClippedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal MP law is fixed by clipping to its nonnegative support interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma marchenkoPastur_mem_nonnegative_interval {α : ℝ} (hα : 0 < α) :
    ∀ᵐ x ∂marchenkoPasturMeasure α, x ∈ Icc (0 : ℝ) (marchenkoPasturB α) := by
  have := marchenkoPastur_probability hα
  filter_upwards [(marchenkoPasturMeasure α).support_mem_ae] with x hx
  have hb := marchenkoPastur_support_bound hα hx
  exact ⟨(mp_lower_nonneg hα.le).trans hb.1,hb.2⟩

lemma marchenkoPastur_clipped_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (∫ x, positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x)
      ∂marchenkoPasturMeasure α) = marchenkoPasturTransform t α := by
  calc
    _ = ∫ x, positiveResolventTest t x ∂marchenkoPasturMeasure α := by
      apply integral_congr_ae
      filter_upwards [marchenkoPastur_mem_nonnegative_interval hα] with x hx
      rw [spectralClip_eq hx]
    _ = _ := marchenkoPastur_transform hα ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianClippedWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence in probability of the actual Gaussian empirical law after clipping. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_clipped_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      ((empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω))).map
        (continuous_spectralClip 0 (marchenkoPasturB α)).measurable.aemeasurable)) atTop
      (fun _ => LevyProkhorov.ofMeasure (⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ : ProbabilityMeasure ℝ)) := by
  let R := marchenkoPasturB α
  have hR : 0 ≤ R := sq_nonneg _
  let ν : ProbabilityMeasure ℝ := ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩
  let W := fun k ω => compactClippedLaw R hR
    (empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)))
  have hh : ∀ t : {t : ℝ // 0 < t}, TendstoInMeasure P
      (fun k ω => ∫ x, compactResolventTest R t x ∂(W k ω : Measure _)) atTop
      (fun _ => ∫ x, compactResolventTest R t x ∂(compactClippedLaw R hR ν : Measure _)) := by
    intro t
    simp only [W,compactClippedLaw_integral]
    change TendstoInMeasure P _ atTop (fun _ => ∫ x,
      positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x) ∂marchenkoPasturMeasure α)
    rw [marchenkoPastur_clipped_transform hα t.property]
    exact gaussianPattern_clipped_stieltjes hα t.property P Z hZ
  have hc := compact_resolvent_tendstoInMeasure R P W (compactClippedLaw R hR ν) hh
  have hn : (compactClippedLaw R hR ν).map (measurable_subtype_coe.aemeasurable (f := fun x : Set.Icc (0 : ℝ) R => (x : ℝ))) = ν :=
    compactClippedLaw_real_eq R hR ν (marchenkoPastur_mem_nonnegative_interval hα)
  rw [hn] at hc
  simpa only [W,compactClippedLaw_real] using hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_EmpiricalClippingDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral clipping moves the empirical law by at most its edge excess. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

theorem empirical_clipping_distance {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    dist (LevyProkhorov.ofMeasure (empiricalSpectralLaw hN eig))
      (LevyProkhorov.ofMeasure ((empiricalSpectralLaw hN eig).map (continuous_spectralClip 0 R).measurable.aemeasurable)) ≤
        spectralExcess eig 0 R := by
  let μ := empiricalSpectralLaw hN eig
  have hh : ∀ᵐ x ∂(μ : Measure ℝ), dist (id x) (spectralClip 0 R x) ≤ spectralExcess eig 0 R := by
    apply ae_finiteSpectralMeasure
    intro i
    rw [Real.dist_eq,abs_sub_comm]
    exact spectralClip_close hR (spectralExcess_nonneg _ _ _) (spectralExcess_bounds eig 0 R i)
  have h := levyProkhorov_map_dist_le_ae (μ : Measure ℝ) id (spectralClip 0 R)
    measurable_id (continuous_spectralClip 0 R).measurable (spectralExcess_nonneg _ _ _) hh
  rw [Measure.map_id] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianEmpiricalWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Gaussian Gram empirical measures converge to the literal MP law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_empirical_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)))) atTop
      (fun _ => LevyProkhorov.ofMeasure (⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ : ProbabilityMeasure ℝ)) := by
  apply tendstoInMeasure_of_dist_le P _ _ _ _ (gaussianPattern_clipped_weak hα P Z hZ)
    (gaussianPattern_zero_upper_excess hα P Z hZ)
  intro k ω
  exact empirical_clipping_distance (Nat.succ_pos k) _ (sq_nonneg _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_EmpiricalLawContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of finite empirical spectral measures in their actual eigenvalues. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace InvariantIsing

theorem continuous_empiricalSpectralLaw {N : ℕ} (hN : 0 < N) :
    Continuous (fun eig : Fin N → ℝ => empiricalSpectralLaw hN eig) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp only [empiricalSpectralLaw_integral]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => f.continuous.comp (continuous_apply i))

theorem continuous_scaled_gaussianEmpirical {N m : ℕ} (hN : 0 < N) (c : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw hN (fun i => c*gaussianPatternEigenvalues z i))) := by
  apply LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
  apply (continuous_empiricalSpectralLaw hN).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul ((continuous_apply i).comp (continuous_gaussianPatternEigenvalues N m))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianScaledEmpiricalWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full real-coupling empirical MP limit, without cross-dimensional independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma empiricalSpectralLaw_scale {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (c : ℝ) :
    (empiricalSpectralLaw hN eig).map (f := fun x : ℝ => c*x) (by fun_prop) =
      empiricalSpectralLaw hN (fun i => c*eig i) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map hN eig (fun x => c*x) (measurable_const.mul measurable_id)

theorem gaussianPattern_scaled_empirical_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) (c : ℝ) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) atTop
      (fun _ => LevyProkhorov.ofMeasure (scaledSpectralLaw
        ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ c)) := by
  have hm (k : ℕ) : AEStronglyMeasurable (fun ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) P := by
    exact (continuous_scaled_gaussianEmpirical (m := gaussianPatternCount α (k+1))
      (Nat.succ_pos k) c).aestronglyMeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hm).mpr
  intro ns hns
  obtain ⟨u,hu,heu⟩ := ((gaussianPattern_empirical_weak hα P Z hZ).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [heu] with ω hω
  have hw := (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp hω
  have hs := (ProbabilityMeasure.continuous_map
    (show Continuous (fun x : ℝ => c*x) from continuous_const.mul continuous_id)).tendsto _ |>.comp hw
  have hl := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hs
  change Tendsto (fun k => LevyProkhorov.ofMeasure
    ((empiricalSpectralLaw (Nat.succ_pos (ns (u k))) (gaussianPatternEigenvalues (Z (ns (u k)+1) ω))).map
      (f := fun x : ℝ => c*x) (by fun_prop))) atTop
    (𝓝 (LevyProkhorov.ofMeasure (scaledSpectralLaw
      ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ c))) at hl
  simpa only [empiricalSpectralLaw_scale,scaledSpectralLaw,Function.comp_apply] using hl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MarchenkoPasturInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Marchenko–Pastur theorem, including real spectral scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory
universe u
namespace InvariantIsing

theorem marchenkoPastur_proved_oai (α : ℝ) (hα : 0 < α) : MarchenkoPasturInput.{u} α hα where
  probability := marchenkoPastur_probability hα
  support_bound := marchenkoPastur_support_bound hα
  left_mem := marchenkoPastur_left_mem hα
  right_mem := marchenkoPastur_right_mem hα
  measurable_eigenvalues := fun N => measurable_gaussianPatternEigenvalues N (gaussianPatternCount α N)
  weak := by
    intro Ω _ P _ Z hZ c
    exact gaussianPattern_scaled_empirical_weak hα P Z hZ c

end InvariantIsing

end

end OAI
end

theorem solution.{u} : type_of% @OAI.InvariantIsing.marchenkoPastur_proved_oai.{u} := @OAI.InvariantIsing.marchenkoPastur_proved_oai.{u}
