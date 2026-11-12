-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:17:39.606888+00:00
-- url     : https://prove2.me/submissions/94b08260-3226-4876-a686-1aa14a199a38

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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
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
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001
import Definitions.Def_OAIQ258002
import Theorems.Thm_OAI_InvariantIsing_gaussianPatternSingularMax_upper_edge
import Theorems.Thm_OAI_InvariantIsing_gaussianPatternTranspose_lower_edge

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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Gram eigenvalues dominate the squared transposed least singular value. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma gaussianPattern_quadratic {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (x : EuclideanSpace ℝ (Fin N)) :
    ⟪x,(gaussianPatternCoupling 1 z).toEuclideanLin x⟫ =
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖^2/N := by
  have hn : ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖^2 =
      ((gaussianPatternArray z)ᵀ *ᵥ x.ofLp) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ x.ofLp) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct,pow_two]
    rfl
  rw [hn]
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
  simp only [star_trivial]
  change x.ofLp ⬝ᵥ ((1/(N : ℝ)) • (gaussianPatternArray z*(gaussianPatternArray z)ᵀ)) *ᵥ x.ofLp = _
  rw [Matrix.smul_mulVec,dotProduct_smul,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

lemma gaussianPatternSingularMin_nonneg {N m : ℕ} (hm : 0 < m)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianPatternSingularMin z := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    refine ⟨⟨EuclideanSpace.single (⟨0,hm⟩ : Fin m) (1 : ℝ),?_⟩⟩
    simp
  exact le_ciInf (fun _ => norm_nonneg _)

lemma gaussianPatternEigenvalues_lower_singular {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (i : Fin N) :
    (gaussianPatternSingularMin (gaussianPatternTranspose N m z))^2/N ≤
      gaussianPatternEigenvalues z i := by
  let hA := gaussianPatternCoupling_isHermitian 1 z
  let u := hA.eigenvectorBasis i
  have hu : ‖u‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hb : BddBelow (Set.range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖)) :=
    ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hl : gaussianPatternSingularMin (gaussianPatternTranspose N m z) ≤
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) u‖ :=
    ciInf_le hb ⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
  have hs := sq_le_sq₀ (gaussianPatternSingularMin_nonneg hN _) (norm_nonneg _) |>.2 hl
  have he : gaussianPatternEigenvalues z i = ⟪u,(gaussianPatternCoupling 1 z).toEuclideanLin u⟫ := by
    unfold gaussianPatternEigenvalues
    change hA.eigenvalues i = _
    rw [hA.eigenvalues_eq i,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,RCLike.re_to_real]
    exact dotProduct_comm _ _
  rw [he,gaussianPattern_quadratic]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramNormBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Gram eigenvalues are bounded by the squared rectangular operator norm. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace InvariantIsing

lemma gaussianPatternCoupling_norm_le {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternCoupling 1 z‖ ≤ (gaussianPatternSingularMax z)^2/N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : ‖(gaussianPatternArray z)ᵀ‖ = ‖gaussianPatternArray z‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (gaussianPatternArray z)
  have he : ‖gaussianPatternArray z‖ = gaussianPatternSingularMax z := rfl
  calc
    _ = |1/(N : ℝ)| * ‖gaussianPatternArray z*(gaussianPatternArray z)ᵀ‖ := by
      rw [gaussianPatternCoupling,norm_smul,Real.norm_eq_abs]
    _ ≤ (1/(N : ℝ))*(‖gaussianPatternArray z‖*‖gaussianPatternArray z‖) := by
      rw [abs_of_pos (one_div_pos.mpr hN')]
      exact mul_le_mul_of_nonneg_left ((Matrix.l2_opNorm_mul _ _).trans_eq (by rw [ht]))
        (by positivity)
    _ = _ := by rw [he]; ring

lemma gaussianPatternEigenvalues_abs_le {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (i : Fin N) :
    |gaussianPatternEigenvalues z i| ≤ (gaussianPatternSingularMax z)^2/N := by
  apply le_trans _ (gaussianPatternCoupling_norm_le hN z)
  unfold gaussianPatternEigenvalues Matrix.IsHermitian.eigenvalues
  exact hermitian_eigenvalues₀_norm_le _ _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramExcessBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic transport of the two singular-value edge errors to Gram spectral excess. -/
noncomputable section
open scoped Topology
namespace InvariantIsing

lemma gaussianGram_singular_bounds {n m : ℕ}
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) (i : Fin (n+1)) :
    (gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1))^2 ≤
      gaussianPatternEigenvalues z i ∧
    gaussianPatternEigenvalues z i ≤ (gaussianPatternSingularMax z/Real.sqrt (n+1))^2 := by
  have hs : (Real.sqrt (n+1))^2 = (n+1 : ℝ) := Real.sq_sqrt (by positivity)
  constructor
  · simpa only [div_pow,hs,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      gaussianPatternEigenvalues_lower_singular (Nat.succ_pos n) z i
  · have h := (le_abs_self (gaussianPatternEigenvalues z i)).trans
      (gaussianPatternEigenvalues_abs_le (Nat.succ_pos n) z i)
    simpa only [div_pow,hs,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using h

lemma squared_lower_edge_bound (L b : ℝ) (hL : 0 ≤ L) (hb : 0 ≤ b) :
    L^2-2*L*max (L-b) 0 ≤ b^2 := by
  by_cases h : L ≤ b
  · rw [max_eq_right (sub_nonpos.mpr h)]
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ L-b)]
    nlinarith [sq_nonneg (L-b)]

lemma gaussianGram_spectralExcess_bound {n m : ℕ}
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    spectralExcess (gaussianPatternEigenvalues z) (L^2) (U^2) ≤
      (U+max (gaussianPatternSingularMax z/Real.sqrt (n+1)-U) 0)^2-U^2 +
        2*L*max (L-gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1)) 0 := by
  let a := gaussianPatternSingularMax z/Real.sqrt (n+1)
  let b := gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1)
  let du := max (a-U) 0
  let dl := max (L-b) 0
  have ha : 0 ≤ a := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb : 0 ≤ b := div_nonneg (gaussianPatternSingularMin_nonneg (Nat.succ_pos n) _)
    (Real.sqrt_nonneg _)
  have hdu : 0 ≤ du := le_max_right _ _
  have hdl : 0 ≤ dl := le_max_right _ _
  have hu : 0 ≤ (U+du)^2-U^2 := by nlinarith
  have hl : 0 ≤ 2*L*dl := by positivity
  apply spectralExcess_le _ _ _ _ (add_nonneg hu hl)
  intro i
  have hbounds := gaussianGram_singular_bounds z i
  change b^2 ≤ gaussianPatternEigenvalues z i ∧ gaussianPatternEigenvalues z i ≤ a^2 at hbounds
  have hblo := squared_lower_edge_bound L b hL hb
  have hau : a ≤ U+du := by dsimp only [du] <;> linarith [le_max_left (a-U) 0]
  constructor
  · change L^2-2*L*dl ≤ b^2 at hblo
    linarith [hbounds.1]
  · nlinarith [hbounds.2]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExcessContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the finite nonempty spectral excess. -/
noncomputable section
namespace InvariantIsing

lemma spectralExcess_eq_max_sup {n : ℕ} (eig : Fin (n+1) → ℝ) (a b : ℝ) :
    spectralExcess eig a b = max 0
      (Finset.univ.sup' Finset.univ_nonempty (fun i => max (a-eig i) (eig i-b))) := by
  classical
  unfold spectralExcess
  rw [Finset.max'_insert _ _ (Finset.univ_nonempty.image _),Finset.max'_eq_sup',Finset.sup'_image]
  rfl

lemma continuous_spectralExcess {X : Type*} [TopologicalSpace X] {n : ℕ}
    (eig : X → Fin (n+1) → ℝ) (heig : ∀ i, Continuous (fun x => eig x i)) (a b : ℝ) :
    Continuous (fun x => spectralExcess (eig x) a b) := by
  simp_rw [spectralExcess_eq_max_sup]
  exact continuous_const.max (Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => (continuous_const.sub (heig i)).max ((heig i).sub continuous_const)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExcessScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by a real coupling transports the spectral interval and its error. -/
noncomputable section
namespace InvariantIsing

lemma spectralExcess_scale_le {N : ℕ} (eig : Fin N → ℝ) (a b c : ℝ) :
    spectralExcess (fun i => c*eig i) (min (c*a) (c*b)) (max (c*a) (c*b)) ≤
      |c| * spectralExcess eig a b := by
  have he := spectralExcess_nonneg eig a b
  apply spectralExcess_le _ _ _ _ (mul_nonneg (abs_nonneg c) he)
  intro i
  have h := spectralExcess_bounds eig a b i
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    have hl := mul_le_mul_of_nonneg_left h.1 hc
    have hu := mul_le_mul_of_nonneg_left h.2 hc
    constructor
    · nlinarith [min_le_left (c*a) (c*b)]
    · nlinarith [le_max_right (c*a) (c*b)]
  · have hc' : c ≤ 0 := le_of_not_ge hc
    rw [abs_of_nonpos hc']
    have hl := mul_le_mul_of_nonpos_left h.1 hc'
    have hu := mul_le_mul_of_nonpos_left h.2 hc'
    constructor
    · nlinarith [min_le_right (c*a) (c*b)]
    · nlinarith [le_max_left (c*a) (c*b)]

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

lemma positive_part_deficit (x b : ℝ) (hb : 0 ≤ b) :
    max (max x 0-b) 0 = max (x-b) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx',max_eq_right (by linarith : 0-b ≤ 0),max_eq_right (by linarith : x-b ≤ 0)]

theorem gaussianPattern_spectralExcess_tendsto_oai {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) (c : ℝ) :
    TendstoInMeasure P (fun k ω => spectralExcess
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))) atTop (fun _ => 0) := by
  let L := max (Real.sqrt α-1) 0
  let U := 1+Real.sqrt α
  let du (k : ℕ) (ω : Ω) := max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1)-U) 0
  let dl (k : ℕ) (ω : Ω) := max (Real.sqrt α-1-
    gaussianPatternSingularMin (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1))
      (Z (k+1) ω))/Real.sqrt (k+1)) 0
  let E (k : ℕ) (ω : Ω) := spectralExcess
    (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
    (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
    (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
  have hU : TendstoInMeasure P du atTop (fun _ => 0) := gaussianPatternSingularMax_upper_edge hα.le P Z hZ
  have hL : TendstoInMeasure P dl atTop (fun _ => 0) := gaussianPatternTranspose_lower_edge hα P Z hZ
  have hbound (k : ℕ) (ω : Ω) : E k ω ≤ |c| * ((U+du k ω)^2-U^2+2*L*dl k ω) := by
    have hh := gaussianGram_spectralExcess_bound (Z (k+1) ω) L U (le_max_right _ _)
      (by dsimp [U] <;> positivity)
    have hb : 0 ≤ gaussianPatternSingularMin
        (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1)) (Z (k+1) ω))/Real.sqrt (k+1) :=
      div_nonneg (gaussianPatternSingularMin_nonneg (Nat.succ_pos k) _) (Real.sqrt_nonneg _)
    rw [positive_part_deficit _ _ hb] at hh
    have hlo : marchenkoPasturLower α = L^2 := marchenkoPasturLower_positive_part hα.le
    have hup : marchenkoPasturB α = U^2 := rfl
    have he := spectralExcess_scale_le (gaussianPatternEigenvalues (Z (k+1) ω)) (L^2) (U^2) c
    dsimp only [E]
    rw [hlo,hup]
    exact he.trans (mul_le_mul_of_nonneg_left hh (abs_nonneg c))
  have hmeas (k : ℕ) : AEStronglyMeasurable (E k) P := by
    have hh := continuous_spectralExcess
      (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        fun i => c*gaussianPatternEigenvalues z i)
      (fun i => continuous_const.mul ((continuous_apply i).comp (continuous_gaussianPatternEigenvalues _ _)))
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
    exact (hh.measurable.aemeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hua⟩ := (hU.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨v,hv,hva⟩ := (hL.comp (hns.comp hu).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u ∘ v,hu.comp hv,?_⟩
  filter_upwards [hua,hva] with ω hωu hωv
  have hau : Tendsto (fun k => du (ns (u (v k))) ω) atTop (𝓝 0) := hωu.comp hv.tendsto_atTop
  have hav : Tendsto (fun k => dl (ns (u (v k))) ω) atTop (𝓝 0) := hωv
  have ht := (((tendsto_const_nhds (x := U)).add hau).pow 2 |>.sub_const (U^2)).add
    (hav.const_mul (2*L)) |>.const_mul |c|
  have ht' : Tendsto (fun k => |c| *((U+du (ns (u (v k))) ω)^2-U^2+2*L*dl (ns (u (v k))) ω))
      atTop (𝓝 0) := by simpa only [add_zero,sub_self,mul_zero,zero_add] using ht
  exact squeeze_zero (fun k => spectralExcess_nonneg _ _ _)
    (fun k => hbound (ns (u (v k))) ω) ht'

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto_oai.{u_1} := @OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto_oai.{u_1}
