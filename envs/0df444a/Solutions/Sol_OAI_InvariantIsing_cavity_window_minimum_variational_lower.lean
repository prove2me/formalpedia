-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_window_minimum_variational_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:51.533197+00:00
-- url     : https://prove2.me/submissions/68ae357b-2184-422f-aa6f-42b0c57f0c9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Fin.InsertNth
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
import Theorems.Thm_OAI_InvariantIsing_cavity_fixed_minimum_geometric_limit
import Theorems.Thm_OAI_InvariantIsing_cavity_original_scalar_self_consistency
import Theorems.Thm_OAI_InvariantIsing_cavity_physical_trial_lower
import Theorems.Thm_OAI_InvariantIsing_field_entropy_sequence_of_support
import Theorems.Thm_OAI_InvariantIsing_field_support_equal_cutList
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot

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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

lemma uniformCell_right_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ)) atTop (𝓝 u) := by
  simpa only [add_div,Nat.cast_add,Nat.cast_one,add_zero] using
    (uniformCell_left_tendsto hu).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellAverage_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) (hc : ContinuousAt q u) :
    Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hc.tendsto.comp (uniformCell_left_tendsto hu)) (hc.tendsto.comp (uniformCell_right_tendsto hu))
    (fun n => (uniformCellAverage_bounds hq hb n _).1) (fun n => (uniformCellAverage_bounds hq hb n _).2)

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

lemma uniformCellAverage_ae_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  filter_upwards [monotone_ae_continuous_unit hq,ae_restrict_mem measurableSet_Ioo] with u hc hu
  exact uniformCellAverage_tendsto hq hb ⟨hu.1.le,hu.2⟩ hc

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma measurable_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) :
    Measurable (finiteStepFunction ζ v) := by
  unfold finiteStepFunction
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

/-- Equation (4.10): uniform deficit error is bounded by the L¹ path error. -/
lemma abs_deficit_sub_path_le (p q : OverlapPath) (r : ℝ) :
    |deficit p r - deficit q r| ≤ ∫ s, |p s - q s| ∂pathMeasure := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (q.integrable_complement_max r)]
  calc
    _ ≤ ∫ s, |(1 - max (p s) r) - (1 - max (q s) r)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, |p s - q s| ∂pathMeasure := by
      apply integral_mono
        ((p.integrable_complement_max r).sub (q.integrable_complement_max r)).abs
        (p.integrable.sub q.integrable).abs
      intro s
      have he : (1 - max (p s) r) - (1 - max (q s) r) =
          -(max (p s) r - max (q s) r) := by ring
      change |(1 - max (p s) r) - (1 - max (q s) r)| ≤ |p s - q s|
      rw [he, abs_neg]
      exact abs_max_sub_max_le_abs (p s) (q s) r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
    all_goals try with_reducible_and_instances rfl
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, sub_zero]
  field_simp [hx'.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteSpectralSlope ρ eig hρ hρsum) := by
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_projectedResolventDerivative ρ eig hρ hρsum a)

theorem finiteSpectralSlope_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    finiteSpectralSlope ρ eig hρ hρsum 0 = ∑ a, ρ a * eig a := by
  simp only [finiteSpectralSlope, projectedResolventDerivative, lt_self_iff_false, ite_false, if_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finiteSpectralSlope_bounds (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteSpectralSlope ρ eig hρ hρsum x ∧ finiteSpectralSlope ρ eig hρ hρsum x ≤ u := by
  have hw := sum_projectedResolventDerivative ρ eig hρ hρsum x
  constructor
  · calc
      l = ∑ a, l * projectedResolventDerivative ρ eig hρ hρsum a x := by
        rw [← Finset.mul_sum, hw, mul_one]
      _ ≤ finiteSpectralSlope ρ eig hρ hρsum x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hl a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
  · calc
      finiteSpectralSlope ρ eig hρ hρsum x ≤
          ∑ a, u * projectedResolventDerivative ρ eig hρ hρsum a x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hu a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
      _ = u := by rw [← Finset.mul_sum, hw, mul_one]

theorem sum_eig_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, eig a * projectedResolvent ρ eig hρ hρsum a x) =
      x * finiteR ρ eig hρ hρsum x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero,
      Finset.sum_const_zero, zero_mul]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hterm : ∀ a, eig a * (ρ a / (B - eig a)) = B * (ρ a / (B - eig a)) - ρ a := by
      intro a
      have hgap : B - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
      field_simp [hgap]
      ring
    simp only [projectedResolvent, finiteR, ite_eq_left h]
    change (∑ a, eig a * (ρ a / (B - eig a))) = x * (B - 1 / x)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hρsum]
    change B * finiteResolvent ρ eig B - 1 = x * (B - 1 / x)
    rw [hs.2]
    field_simp

theorem hasDerivWithinAt_mul_finiteR_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
  have hd : HasDerivWithinAt
      (fun y => ∑ a, eig a * projectedResolvent ρ eig hρ hρsum a y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
    convert! HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx).const_mul (eig a)) using 1
    all_goals try with_reducible_and_instances rfl
  exact hd.congr (fun y hy => (sum_eig_projectedResolvent ρ eig hρ hρsum hy).symm)
    (sum_eig_projectedResolvent ρ eig hρ hρsum hx).symm

theorem hasDerivWithinAt_finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum t)
      (finiteSpectralSlope ρ eig hρ hρsum (t * x)) (Ici 0) x := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_mul, finiteSpectralSlope_zero]
    have hd := (hasDerivAt_id x).mul_const (∑ a, ρ a * eig a)
    convert! hd.hasDerivWithinAt using 1
    · funext y
      simp [finiteThermalScalar, finiteR]
    · simp
  · have hdH := hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum (mul_nonneg h.le hx)
    have hdlin : HasDerivWithinAt (fun y : ℝ => t * y) t (Ici 0) x := by
      convert! ((hasDerivAt_id x).const_mul t).hasDerivWithinAt using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd := (hdH.comp x hdlin (fun y hy => mul_nonneg h.le hy)).const_mul (1 / t)
    convert! hd using 1
    · funext y
      dsimp [finiteThermalScalar, Function.comp_def]
      field_simp [h.ne']
    · field_simp [h.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavityRDerivative_le (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {K : ℝ} (_hK : 0 ≤ K)
    (hlam : ∀ a, |lam a| ≤ K) (x : ℝ) :
    cavityRDerivative rho lam hrho hsum x ≤ 4 * K ^ 2 := by
  have hR := finiteR_mem_interval rho lam hrho hsum
    (fun a => (abs_le.mp (hlam a)).1) (fun a => (abs_le.mp (hlam a)).2) x
  calc
    cavityRDerivative rho lam hrho hsum x ≤
        ∑ a, projectedResolventDerivative rho lam hrho hsum a x * (4 * K ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (projectedResolventDerivative_pos rho lam hrho hsum a x).le
      have ha := abs_le.mp (hlam a)
      have hlow : -2 * K ≤ lam a - finiteR rho lam hrho hsum x := by linarith
      have hupp : lam a - finiteR rho lam hrho hsum x ≤ 2 * K := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)]
    _ = 4 * K ^ 2 := by rw [← Finset.sum_mul, sum_projectedResolventDerivative, one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true, if_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false, if_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true, if_true] using hi

lemma fieldLevelPath_on_cell (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) {s : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelPath h q hq hunit s = q i := by
  change q (fieldLevelIndex h s) = q i
  rw [fieldLevelIndex_on_cell h i hs]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_zero_variance (ζ : ℝ) (F a : ℝ → ℝ) (z : ℝ) :
    fieldSpinTransition ζ 0 F a z = a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianReal_zero_var]
  simp only [integral_dirac]
  exact mul_div_cancel_left₀ (a z) (Real.exp_ne_zero _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual magnetization-overlap path for a finite scalar Ising field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldMagnetizationPath_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldMagnetizationPath h s = fieldMagnetizationLevel h i :=
  fieldLevelPath_on_cell h _ _ _ i hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

lemma cavityStrictLevels_dist {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin (n + 1)) : |cavityStrictLevels q ε i - q i| ≤ ε := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hd : |cavityInteriorLevel i - q i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2, hq'.1, hq'.2]
  have he : cavityStrictLevels q ε i - q i = ε * (cavityInteriorLevel i - q i) := by
    dsimp only [cavityStrictLevels]
    ring
  rw [he, abs_mul, abs_of_nonneg hε]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hε

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma cavityStrictUniformPath_dist (p : OverlapPath) (n : ℕ) (s : ℝ) :
    |cavityStrictUniformPath p n s - uniformCellAverage p n (uniformCellIndex n s)| ≤
      1 / ((n : ℝ) + 1) :=
  cavityStrictLevels_dist _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n).1.le (cavityUniformLevel n s)

lemma cavityStrictUniformPath_ae_tendsto (p : OverlapPath) :
    ∀ᵐ s ∂pathMeasure, Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) := by
  have ha := uniformCellAverage_ae_tendsto p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩)
  change ∀ᵐ s ∂pathMeasure, _ at ha
  filter_upwards [ha] with s hs
  have hd : Tendsto (fun n => cavityStrictUniformPath p n s -
      uniformCellAverage p n (uniformCellIndex n s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Real.norm_eq_abs] using cavityStrictUniformPath_dist p n s
  simpa only [sub_add_cancel, zero_add] using hd.add hs

lemma cavityStrictUniformPath_l1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |cavityStrictUniformPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have ha := cavityStrictUniformPath_ae_tendsto p
  have hd := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |cavityStrictUniformPath p n s - p s|) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (((cavityStrictUniformPath p n).measurable.sub p.measurable).abs).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith [(cavityStrictUniformPath p n).nonneg s,
        (cavityStrictUniformPath p n).le_one s, p.nonneg s, p.le_one s])
    (ha.mono fun s hs => by simpa only [sub_self, abs_zero] using (hs.sub_const (p s)).abs)
  simpa only [integral_zero] using hd

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDomain
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma measurable_fieldFunction (h : FieldStep) : Measurable (fieldFunction h) :=
  IsingPerceptron.measurable_finiteStepFunction h.cut h.height

lemma fieldFunction_le_last (h : FieldStep) (s : ℝ) :
    fieldFunction h s ≤ h.height (Fin.last h.depth) := by
  classical
  by_cases hex : ∃ i : Fin (h.depth + 1), h.cut i.castSucc < s ∧ s < h.cut i.succ
  · obtain ⟨i, hi⟩ := hex
    have he := IsingPerceptron.finiteStepFunction_on_cell h.ordered_cut h.height hi
    change IsingPerceptron.finiteStepFunction h.cut h.height s ≤ _
    rw [he]
    exact h.ordered_height (Fin.le_last _)
  · have he : fieldFunction h s = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hex ⟨i, hi⟩)
    rw [he]
    exact h.nonneg _

lemma integrable_fieldFunction (h : FieldStep) : Integrable (fieldFunction h) pathMeasure := by
  apply (integrable_const (h.height (Fin.last h.depth))).mono'
    (measurable_fieldFunction h).aestronglyMeasurable
  filter_upwards [] with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fieldFunction_nonneg h s)] using
    fieldFunction_le_last h s

lemma integrable_path_mul_field (p : OverlapPath) (h : FieldStep) :
    Integrable (fun s => p s * fieldFunction h s) pathMeasure := by
  apply (integrable_fieldFunction h).mono'
    (p.measurable.mul (measurable_fieldFunction h)).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (p.nonneg s),
    abs_of_nonneg (fieldFunction_nonneg h s)]
  exact mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPairingContinuity
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing errors for the rounded quantile paths used in the cavity
calculation. A uniform field-height bound suffices for L1 stability. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma field_pairing_path_error (p q : OverlapPath) (h : FieldStep) :
    |fieldPairing p h - fieldPairing q h| ≤ h.height (Fin.last h.depth) *
      ∫ s, |p s - q s| ∂pathMeasure := by
  have hi : Integrable (fun s => (p s - q s) * fieldFunction h s) pathMeasure := by
    apply ((integrable_path_mul_field p h).sub (integrable_path_mul_field q h)).congr
    apply ae_of_all
    intro s
    change p s * fieldFunction h s - q s * fieldFunction h s = _
    ring
  have he : fieldPairing p h - fieldPairing q h =
      ∫ s, (p s - q s) * fieldFunction h s ∂pathMeasure := by
    rw [fieldPairing, fieldPairing, ← integral_sub (integrable_path_mul_field p h)
      (integrable_path_mul_field q h)]
    congr 1
    funext s
    ring
  rw [he]
  calc
    _ ≤ ∫ s, |(p s - q s) * fieldFunction h s| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, h.height (Fin.last h.depth) * |p s - q s| ∂pathMeasure := by
      apply integral_mono hi.abs (((p.integrable.sub q.integrable).abs).const_mul _)
      intro s
      dsimp only
      rw [abs_mul, abs_of_nonneg (fieldFunction_nonneg h s)]
      exact (mul_le_mul_of_nonneg_left (fieldFunction_le_last h s) (abs_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem field_pairing_path_tendsto (p : OverlapPath) (q : ℕ → OverlapPath)
    (h : ℕ → FieldStep) {C : ℝ}
    (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => fieldPairing (q n) (h n) - fieldPairing p (h n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => C * ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0) by
      simpa only [mul_zero] using hq.const_mul C)
  rw [Real.norm_eq_abs]
  exact (field_pairing_path_error (q n) p (h n)).trans
    (mul_le_mul_of_nonneg_right (hC n) (integral_nonneg (fun _ => abs_nonneg _)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact concatenation and linear propagation identities for the finite
scalar field recursion. The exponents may include the zero root level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_append (P S : List (ℝ × ℝ≥0)) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ S) F = fieldScalarValue P (fieldScalarValue S F) := by
  exact List.foldr_append

lemma fieldScalarMean_append (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) :
    fieldScalarMean (P ++ S) F a =
      fieldScalarMean P (fieldScalarValue S F) (fieldScalarMean S F a) := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    simp only [List.cons_append, fieldScalarMean, fieldScalarValue_append, ih]

lemma fieldScalarSquares_congr_list {P Q : List (ℝ × ℝ≥0)} (he : P = Q)
    (F a : ℝ → ℝ) (i : Fin (P.length + 1)) (j : Fin (Q.length + 1))
    (hij : i.val = j.val) : fieldScalarSquares P F a i = fieldScalarSquares Q F a j := by
  subst Q
  have hi : i = j := Fin.ext hij
  rw [hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_value (h : FieldStep) (z : ℝ) :
    fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
      h.height (Fin.last h.depth) / 2 = fieldValue h z := by
  unfold fieldScalarValue fieldAllIncrements fieldValue
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldAllIncrements_root (h : FieldStep) :
    fieldAllIncrements h = (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
      scalarFieldIncrements h := by
  unfold fieldAllIncrements scalarFieldIncrements
  rw [List.ofFn_succ]
  congr 1
  apply Prod.ext
  · exact h.first
  · apply Subtype.ext
    simp [fieldIncrement]

lemma fieldAllSquares_magnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldScalarSquares (fieldAllIncrements h) (fun y => Real.log (Real.cosh y))
      Real.tanh ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ 0 = fieldMagnetizationLevel h i := by
  have hroot := fieldAllIncrements_root h
  let j : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have hs := fieldScalarSquares_congr_list hroot
    (fun y => Real.log (Real.cosh y)) Real.tanh
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ j.succ (by rfl)
  rw [congrFun hs 0]
  change fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)))
    (fieldScalarSquares (scalarFieldIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh j) 0 = _
  simp only [fieldSpinTransition, integral_tilted_eq_div, zero_mul, Real.exp_zero,
    one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, div_one]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldZeroIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inserting a zero covariance increment preserves the scalar Ising
value and spin mean. Its adjacent overlap levels are the same. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ (a, 0) :: S) F = fieldScalarValue (P ++ S) F := by
  rw [fieldScalarValue_append, fieldScalarValue_append]
  change fieldScalarValue P (gaussianOperator a 0 (fieldScalarValue S F)) = _
  rw [gaussianOperator_zero_variance]

lemma fieldScalarMean_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F b : ℝ → ℝ) :
    fieldScalarMean (P ++ (a, 0) :: S) F b = fieldScalarMean (P ++ S) F b := by
  rw [fieldScalarMean_append, fieldScalarMean_append]
  change fieldScalarMean P (gaussianOperator a 0 (fieldScalarValue S F))
    (fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b)) = _
  rw [gaussianOperator_zero_variance]
  have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
      fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
  rw [hs]

lemma fieldScalarSquareAt_eq (L : List (ℝ × ℝ≥0)) (F b : ℝ → ℝ)
    (i : Fin (L.length + 1)) :
    fieldScalarSquareAt L F b i.val = fieldScalarSquares L F b i := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
        (fieldScalarSquareAt L F b j.val) = _
      rw [ih]
      rfl

lemma fieldScalarSquareAt_insert_zero (P S : List (ℝ × ℝ≥0))
    (a : ℝ) (F b : ℝ → ℝ) (i : ℕ) :
    fieldScalarSquareAt (P ++ (a, 0) :: S) F b i =
      fieldScalarSquareAt (P ++ S) F b (if i ≤ P.length then i else i - 1) := by
  induction P generalizing i with
  | nil =>
    cases i with
    | zero =>
      simp only [List.nil_append, List.length_nil, le_refl, ite_true, if_true,
        fieldScalarSquareAt, fieldScalarMean]
      have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
          fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
      rw [hs]
      cases S <;> rfl
    | succ i =>
      simp only [List.nil_append, List.length_nil,
        Nat.add_sub_cancel, fieldScalarSquareAt]
      exact funext (fieldSpinTransition_zero_variance _ _ _)
  | cons av P ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_le, ite_true, if_true, List.cons_append, fieldScalarSquareAt]
      have he := fieldScalarMean_insert_zero (av :: P) S a F b
      simpa only [List.cons_append] using congrArg (fun f : ℝ → ℝ => fun z => f z ^ 2) he
    | succ i =>
      have hv := fieldScalarValue_insert_zero P S a F
      simp only [List.cons_append, List.length_cons, Nat.succ_le_succ_iff]
      by_cases hi : i ≤ P.length
      · simp only [hi, ite_true, if_true, fieldScalarSquareAt]
        rw [hv, ih, ite_eq_left hi]
      · have hp : 0 < i := by omega
        simp only [hi, ite_false, if_false, fieldScalarSquareAt]
        have he : i + 1 - 1 = (i - 1) + 1 := by omega
        rw [he]
        change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ (a, 0) :: S) F)
          (fieldScalarSquareAt (P ++ (a, 0) :: S) F b i) =
          fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
            (fieldScalarSquareAt (P ++ S) F b (i - 1))
        rw [hv, ih, ite_eq_right hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineCut
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting one interval of a finite field without changing its height. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_ofFn_insertNth {α : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : α) (f : Fin n → α) :
    List.ofFn (Fin.insertNth i a f) =
      (List.ofFn f).take i.val ++ a :: (List.ofFn f).drop i.val := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hf : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
      rw [hf, Fin.insertNth_succ_cons]
      simp only [List.ofFn_cons, Fin.val_succ, List.take_succ_cons,
        List.drop_succ_cons, ih, List.cons_append]

lemma fieldInsertCut_last_height (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) =
      h.height (Fin.last h.depth) := by
  change fieldSplitHeight h i (Fin.last (h.depth + 1)) = _
  simp only [fieldSplitHeight, Fin.val_last]
  rw [dite_eq_right (show ¬h.depth + 1 ≤ i.val by omega)]
  rfl

lemma fieldInsertCut_cut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : j.val ≤ i.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_below (α := fun _ => ℝ) (show j < i.castSucc.succ by
    change j.val < i.val + 1; omega)]
  simp only [eq_rec_constant]
  rfl

lemma fieldInsertCut_cut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).cut i.castSucc.succ = c := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut i.castSucc.succ = c
  exact Fin.insertNth_apply_same _ _ _

lemma fieldInsertCut_cut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : i.val + 1 < j.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val - 1, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_above (α := fun _ => ℝ) (show i.castSucc.succ < j by exact hj)]
  simp only [eq_rec_constant]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineIncrements
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A one-cut refinement inserts exactly one zero covariance increment. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut i.succ.castSucc = c
    simpa only [Fin.succ_castSucc] using fieldInsertCut_cut_at h i c hc₀ hc₁
  · change fieldSplitHeight h i i.succ -
      (if hz : i.succ.val = 0 then 0 else
        fieldSplitHeight h i ⟨i.succ.val - 1, by change i.val + 1 - 1 < h.depth + 2; omega⟩) = 0
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel]
    unfold fieldSplitHeight
    simp only [Fin.val_succ]
    rw [dite_eq_right (show ¬i.val + 1 ≤ i.val by omega),
      dite_eq_left (show i.val ≤ i.val by omega)]
    simp

lemma fieldIncrement_insertCut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : j.val ≤ i.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.castSucc = fieldIncrement h j := by
  apply Prod.ext
  · exact fieldInsertCut_cut_below h i c hc₀ hc₁ _ hj
  · change fieldSplitHeight h i j.castSucc -
      (if hz : j.val = 0 then 0 else fieldSplitHeight h i ⟨j.val - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    have hp : fieldSplitHeight h i j.castSucc = h.height j := by
      unfold fieldSplitHeight
      exact dite_eq_left hj
    rw [hp]
    split_ifs with hz
    · rfl
    · have hp' : fieldSplitHeight h i ⟨j.val - 1, by omega⟩ =
          h.height ⟨j.val - 1, by omega⟩ := by
        unfold fieldSplitHeight
        exact dite_eq_left (show j.val - 1 ≤ i.val by omega)
      rw [hp']

lemma fieldIncrement_insertCut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : i.val < j.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.succ = fieldIncrement h j := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut j.succ.castSucc = h.cut j.castSucc
    convert fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ.castSucc (by
      change i.val + 1 < j.val + 1; omega) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  · change fieldSplitHeight h i j.succ -
      (if hz : j.val + 1 = 0 then 0 else fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    have hp : fieldSplitHeight h i j.succ = h.height j := by
      unfold fieldSplitHeight
      rw [dite_eq_right (show ¬j.succ.val ≤ i.val by change ¬j.val + 1 ≤ i.val; omega)]
      rfl
    have hp' : fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩ =
        h.height ⟨j.val - 1, by omega⟩ := by
      unfold fieldSplitHeight
      rw [dite_eq_right (by change ¬j.val + 1 - 1 ≤ i.val; omega)]
      rfl
    rw [hp, hp']

lemma fieldNNIncrement_eq_of_real {h k : FieldStep} {i : Fin (h.depth + 1)}
    {j : Fin (k.depth + 1)} (he : fieldIncrement h i = fieldIncrement k j) :
    fieldNNIncrement h i = fieldNNIncrement k j := by
  apply Prod.ext
  · exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldNNIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  have he := fieldIncrement_insertCut_at h i c hc₀ hc₁
  apply Prod.ext
  · change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).1 = c
    exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).2 = 0
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldAllIncrements_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldAllIncrements (fieldInsertCut h i c hc₀ hc₁) =
      (fieldAllIncrements h).take (i.val + 1) ++
        (c, 0) :: (fieldAllIncrements h).drop (i.val + 1) := by
  let f : Fin (h.depth + 1) → ℝ × ℝ≥0 := fieldNNIncrement h
  let g : Fin (h.depth + 2) → ℝ × ℝ≥0 :=
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁)
  have he : g = Fin.insertNth i.succ (c, 0) f := by
    apply (Fin.eq_insertNth_iff).mpr
    constructor
    · exact fieldNNIncrement_insertCut_at h i c hc₀ hc₁
    · funext j
      change g (i.succ.succAbove j) = f j
      by_cases hj : j.val ≤ i.val
      · have hs : i.succ.succAbove j = j.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by change j.val < i.val + 1; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_below h i c hc₀ hc₁ j hj)
      · have hs : i.succ.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by change i.val + 1 ≤ j.val; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_above h i c hc₀ hc₁ j (by omega))
  change List.ofFn g = (List.ofFn f).take (i.val + 1) ++ (c, 0) :: (List.ofFn f).drop (i.val + 1)
  rw [he, field_ofFn_insertNth]
  rfl

lemma fieldValue_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (z : ℝ) :
    fieldValue (fieldInsertCut h i c hc₀ hc₁) z = fieldValue h z := by
  rw [← fieldAllIncrements_value, fieldAllIncrements_insertCut,
    fieldScalarValue_insert_zero, List.take_append_drop]
  change fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) / 2 = _
  rw [fieldInsertCut_last_height, fieldAllIncrements_value]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact magnetization levels under a one-cut field refinement. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSplitHeight_eq (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : fieldSplitHeight h i j = h.height (fieldSplitIndex i j) := by
  unfold fieldSplitHeight fieldSplitIndex
  split_ifs <;> rfl

lemma fieldScalarSquareAt_magnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldScalarSquareAt (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (i.val + 1) 0 = fieldMagnetizationLevel h i := by
  rw [fieldScalarSquareAt_eq (fieldAllIncrements h) _ _
    ⟨i.val + 1, by rw [fieldAllIncrements_length]; omega⟩]
  exact fieldAllSquares_magnetization h i

lemma fieldMagnetizationLevel_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) :
    fieldMagnetizationLevel (fieldInsertCut h i c hc₀ hc₁) j =
      fieldMagnetizationLevel h (fieldSplitIndex i j) := by
  apply (fieldScalarSquareAt_magnetization (fieldInsertCut h i c hc₀ hc₁) j).symm.trans
  rw [fieldAllIncrements_insertCut, fieldScalarSquareAt_insert_zero]
  have hp : ((fieldAllIncrements h).take (i.val + 1)).length = i.val + 1 := by
    rw [List.length_take, fieldAllIncrements_length, Nat.min_eq_left (by omega)]
  rw [hp, List.take_append_drop]
  rw [← fieldScalarSquareAt_magnetization]
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left (show j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_true]
  · rw [ite_eq_right (show ¬j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_false]
    have hj0 : 0 < j.val := by omega
    congr 2
    omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefinePaths
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height and physical magnetization paths survive a one-cut refinement. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldInsertCut_cell_subset (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) :
    Ioo ((fieldInsertCut h i c hc₀ hc₁).cut j.castSucc)
        ((fieldInsertCut h i c hc₀ hc₁).cut j.succ) ⊆
      Ioo (h.cut (fieldSplitIndex i j).castSucc) (h.cut (fieldSplitIndex i j).succ) := by
  have hlo : h.cut (fieldSplitIndex i j).castSucc ≤
      (fieldInsertCut h i c hc₀ hc₁).cut j.castSucc := by
    by_cases hj : j.val ≤ i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.castSucc hj]
      simp only [fieldSplitIndex, hj, dite_true]
      rfl
    · by_cases he : j.val = i.val + 1
      · have hjc : j.castSucc = i.castSucc.succ := Fin.ext he
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₀.le using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, hj, dite_false, Fin.val_castSucc]
        omega
      · rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.castSucc (by
          change i.val + 1 < j.val; omega)]
        simp only [fieldSplitIndex, hj, dite_false]
        rfl
  have hhi : (fieldInsertCut h i c hc₀ hc₁).cut j.succ ≤
      h.cut (fieldSplitIndex i j).succ := by
    by_cases hj : j.val < i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.succ (by
        change j.val + 1 ≤ i.val; omega)]
      simp only [fieldSplitIndex, show j.val ≤ i.val from hj.le, dite_true]
      rfl
    · by_cases he : j.val = i.val
      · have hjc : j.succ = i.castSucc.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₁.le using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, show j.val ≤ i.val by omega, dite_true, Fin.val_succ]
        omega
      · have hgt : i.val < j.val := by omega
        rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ (by
          change i.val + 1 < j.val + 1; omega)]
        simp only [fieldSplitIndex, show ¬j.val ≤ i.val by omega, dite_false,
          Fin.val_succ, Nat.add_sub_cancel]
        apply le_of_eq
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
  intro s hs
  exact ⟨hlo.trans_lt hs.1, hs.2.trans_le hhi⟩

lemma fieldFunction_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldFunction (fieldInsertCut h i c hc₀ hc₁) =ᵐ[pathMeasure] fieldFunction h := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with s hs
  obtain ⟨j, hj⟩ := hs
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  change finiteStepFunction _ _ s = finiteStepFunction _ _ s
  rw [finiteStepFunction_on_cell (fieldInsertCut h i c hc₀ hc₁).ordered_cut _ hj,
    finiteStepFunction_on_cell h.ordered_cut _ hi]
  exact fieldSplitHeight_eq h i j

lemma fieldMagnetizationPath_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldMagnetizationPath (fieldInsertCut h i c hc₀ hc₁)).val =ᵐ[pathMeasure]
      (fieldMagnetizationPath h).val := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with s hs
  obtain ⟨j, hj⟩ := hs
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  rw [fieldMagnetizationPath_on_cell _ j hj,
    fieldMagnetizationPath_on_cell h (fieldSplitIndex i j) hi]
  exact fieldMagnetizationLevel_insertCut h i c hc₀ hc₁ j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCommonRefinement
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite common refinements, built only by duplicating constant-height cells. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldCutSet_bounds (h : FieldStep) {s : ℝ} (hs : s ∈ fieldCutSet h) :
    s ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨i, rfl⟩ := (mem_fieldCutSet h s).mp hs
  constructor
  · rw [← h.first]; exact h.ordered_cut.monotone (Fin.zero_le i)
  · rw [← h.last]; exact h.ordered_cut.monotone (Fin.le_last i)

lemma fieldCutSet_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldCutSet (fieldInsertCut h i c hc₀ hc₁) = insert c (fieldCutSet h) := by
  classical
  have he := Fin.range_insertNth i.castSucc.succ c h.cut
  ext s
  simp only [mem_fieldCutSet, Finset.mem_insert]
  change (∃ j, Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = s) ↔
    s = c ∨ ∃ j, h.cut j = s
  simpa only [Set.insert, Set.mem_ofPred_eq, Set.mem_range] using Set.ext_iff.mp he s

lemma FieldRefines.value {h k : FieldStep} (hk : FieldRefines h k) (z : ℝ) :
    fieldValue k z = fieldValue h z := by
  induction hk with
  | refl => rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldValue_insertCut _ i c hc₀ hc₁ z).trans ih

lemma FieldRefines.field_ae {h k : FieldStep} (hk : FieldRefines h k) :
    fieldFunction k =ᵐ[pathMeasure] fieldFunction h := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldFunction_insertCut_ae _ i c hc₀ hc₁).trans ih

lemma FieldRefines.magnetization_ae {h k : FieldStep} (hk : FieldRefines h k) :
    (fieldMagnetizationPath k).val =ᵐ[pathMeasure] (fieldMagnetizationPath h).val := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih =>
    exact (fieldMagnetizationPath_insertCut_ae _ i c hc₀ hc₁).trans ih

lemma field_exists_refinement (h : FieldStep) (S : Finset ℝ)
    (hS : ∀ s ∈ S, s ∈ Icc (0 : ℝ) 1) :
    ∃ k, FieldRefines h k ∧ fieldCutSet k = fieldCutSet h ∪ S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨h, FieldRefines.refl h, by simp⟩
  | @insert c S hc ih =>
    obtain ⟨k, hk, hcuts⟩ := ih (fun s hs => hS s (Finset.mem_insert_of_mem hs))
    by_cases hck : c ∈ fieldCutSet k
    · refine ⟨k, hk, ?_⟩
      rw [hcuts] at hck ⊢
      ext s
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · intro hs; rcases hs with hs | hs
        · exact Or.inl hs
        · exact Or.inr (Or.inr hs)
      · intro hs; rcases hs with hs | rfl | hs
        · exact Or.inl hs
        · simpa only [Finset.mem_union] using hck
        · exact Or.inr hs
    · have hcb := hS c (Finset.mem_insert_self c S)
      have hc0 : 0 < c := by
        have hne : c ≠ 0 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨0, k.first.trans he.symm⟩
        exact lt_of_le_of_ne hcb.1 (Ne.symm hne)
      have hc1 : c < 1 := by
        have hne : c ≠ 1 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨Fin.last (k.depth + 1), k.last.trans he.symm⟩
        exact lt_of_le_of_ne hcb.2 hne
      obtain ⟨i, hi₀, hi₁⟩ := finite_partition_cell k.cut
        (by simpa only [k.first] using hc0.le) (by simpa only [k.last] using hc1)
      have hi : k.cut i.castSucc < c := lt_of_le_of_ne hi₀ (by
        intro he; exact hck ((mem_fieldCutSet k c).mpr ⟨i.castSucc, he⟩))
      refine ⟨fieldInsertCut k i c hi hi₁, FieldRefines.insert hk i c hi hi₁, ?_⟩
      rw [fieldCutSet_insertCut, hcuts]
      ext s
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

lemma field_cutList_eq_of_set_eq {h k : FieldStep} (he : fieldCutSet h = fieldCutSet k) :
    List.ofFn h.cut = List.ofFn k.cut := by
  have hh : (List.ofFn h.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr h.ordered_cut)
  have hk : (List.ofFn k.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr k.ordered_cut)
  apply hh.eq_of_mem_iff hk
  intro s
  have hs := Finset.ext_iff.mp he s
  simpa only [mem_fieldCutSet, List.mem_ofFn] using hs

lemma field_common_refinement (h k : FieldStep) :
    ∃ h' k', FieldRefines h h' ∧ FieldRefines k k' ∧
      List.ofFn h'.cut = List.ofFn k'.cut := by
  obtain ⟨h', hh', hhcut⟩ := field_exists_refinement h (fieldCutSet k)
    (fun _ hs => fieldCutSet_bounds k hs)
  obtain ⟨k', hk', hkcut⟩ := field_exists_refinement k (fieldCutSet h)
    (fun _ hs => fieldCutSet_bounds h hs)
  refine ⟨h', k', hh', hk', field_cutList_eq_of_set_eq ?_⟩
  rw [hhcut, hkcut, Finset.union_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPartitionSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar-field supporting inequality, independent of the finite partition. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The exact scalar supporting inequality for arbitrary finite field partitions. -/
theorem field_support (h k : FieldStep) :
    fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨h', k', hh', hk', hcuts⟩ := field_common_refinement h k
  have hi := field_support_equal_cutList hcuts
  rw [hh'.value, hk'.value] at hi
  have he : (∫ s, fieldMagnetizationPath h' s * (fieldFunction k' s - fieldFunction h' s)
      ∂pathMeasure) = ∫ s, fieldMagnetizationPath h s *
        (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [hh'.magnetization_ae, hh'.field_ae, hk'.field_ae] with s hB hh hk
    rw [hB, hh, hk]
  rwa [he] at hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergyPrimitive
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature primitive of the finite-spectrum interaction energy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralSlope_temperature (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (∫ u in 0..t, finiteSpectralSlope ρ eig hρ hρsum (u * x)) =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  have hc : Continuous (finiteThermalScalar ρ eig hρ hρsum x) :=
    continuous_id.mul ((continuous_finiteR ρ eig hρ hρsum).comp
      (continuous_const.mul continuous_id))
  have hd : ∀ u ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum x)
        (finiteSpectralSlope ρ eig hρ hρsum (u * x)) (Ioi u) u := by
    intro u hu
    have h := hasDerivWithinAt_finiteThermalScalar ρ eig hρ hρsum hx hu.1.le
    rw [mul_comm x u] at h
    exact h.mono fun y hy => (lt_trans hu.1 (show u < y from hy)).le
  have hint : IntervalIntegrable (fun u => finiteSpectralSlope ρ eig hρ hρsum (u * x))
      volume 0 t :=
    ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
      (continuous_id.mul continuous_const)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc.continuousOn hd hint
  simpa only [finiteThermalScalar, zero_mul, sub_zero, mul_comm x t] using hFTC

/-- Equation `up:primitive`, for the actual finite atomic spectral transform. -/
theorem integral_finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    (∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p) =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p := by
  let K := ∑ a, |eig a|
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hS : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  let f : ℝ → ℝ → ℝ := fun u r => finiteSpectralSlope ρ eig hρ hρsum (u * deficit p r)
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (Function.uncurry f) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).measurable.comp
      (measurable_fst.mul ((continuous_deficit p).measurable.comp measurable_snd))
  have hi : Integrable (Function.uncurry f) ((volume.restrict (uIoc 0 t)).prod pathMeasure) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖finiteSpectralSlope ρ eig hρ hρsum (z.1 * deficit p z.2)‖ ≤ K
      simpa only [Real.norm_eq_abs] using hS (z.1 * deficit p z.2)
  have hswap := intervalIntegral_integral_swap hi
  unfold finiteInteractionEnergy spectralFunctional
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in 0..t, ∫ r, f u r ∂pathMeasure) =
    (1 / 2 : ℝ) * ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact integral_finiteSpectralSlope_temperature ρ eig hρ hρsum ht (deficit_nonneg p hr.2.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperatureFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteTemperatureFunctional_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {t : ℝ} (ht : 0 ≤ t) :
    finiteTemperatureFunctional ρ eig hρ hρsum p t =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p :=
  integral_finiteInteractionEnergy ρ eig hρ hρsum ht p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPathLimit
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 approximation of the trial path preserves the finite spectral
interaction functional, as required when removing a finite partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma finiteTemperatureFunctional_tendsto_of_L1 {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun k => ∫ s, |q k s - p s| ∂pathMeasure) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => finiteTemperatureFunctional ρ eig hρ hρsum (q k) t) atTop
      (𝓝 (finiteTemperatureFunctional ρ eig hρ hρsum p t)) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun b _ => abs_nonneg (eig b)) (Finset.mem_univ a)
  have hbound (x : ℝ) : |finiteR ρ eig hρ hρsum x| ≤ K :=
    abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hd (r : ℝ) : Tendsto (fun k => deficit (q k) r) atTop (𝓝 (deficit p r)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ hL
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [Real.norm_eq_abs] using abs_deficit_sub_path_le (q k) p r)
  have hi : Tendsto (fun k => ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit (q k) r)
      ∂pathMeasure) atTop
      (𝓝 (∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => t * K)
    · intro k
      exact (continuous_const.mul ((continuous_finiteR ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit (q k))))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left (hbound _) ht)
    · exact ae_of_all _ (fun r =>
        (((continuous_finiteR ρ eig hρ hρsum).tendsto _).comp ((hd r).const_mul t)).const_mul t)
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ ht,
    spectralFunctional] using hi.const_mul (1 / 2 : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityEntropyMaximum
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the entropy in the cavity limit. Approximate
self-consistency, with the actual scalar supporting inequality, makes the
finite field trials approach the entropy supremum. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem field_entropy_sequence (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0)) :
    entropyFunctional p ≠ ⊤ ∧
    Tendsto (fun n => fieldValue (h n) 0 + fieldPairing p (h n) / 2)
      atTop (𝓝 (entropyFunctional p).toReal) := by
  apply field_entropy_sequence_of_support p h hC _ hself
  intro n k
  simpa only [one_div, inv_mul_eq_div] using field_support (h n) k

theorem cavity_entropy_trial_tendsto {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    entropyFunctional p ≠ ⊤ ∧
    Tendsto (fun n => fieldValue (h n) 0 + fieldPairing (q n) (h n) / 2 +
      spectralFunctional (finiteR ρ eig hρ hsum) (q n)) atTop
      (𝓝 ((entropyFunctional p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p)) := by
  obtain ⟨htop, hent⟩ := field_entropy_sequence p h hC hself
  have hpair := field_pairing_path_tendsto p q h hC hq
  have hspec := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hsum p q hq zero_le_one
  simp only [finiteTemperatureFunctional_eq ρ eig hρ hsum _ zero_le_one, one_mul] at hspec
  refine ⟨htop, ?_⟩
  have ht := (hent.add (hpair.div_const 2)).add hspec
  have he : (fun n => (fieldValue (h n) 0 + fieldPairing p (h n) / 2 +
      (fieldPairing (q n) (h n) - fieldPairing p (h n)) / 2) +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) =
      (fun n => fieldValue (h n) 0 + fieldPairing (q n) (h n) / 2 +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) := by
    funext n
    ring
  rw [he] at ht
  simpa only [zero_div, add_zero] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldModulus
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform plateau control for the actual strict finite cavity fields.
The spectral derivative bound and the conditional-variance estimate
turn convergence of overlap levels into asymptotic preservation of ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFieldPrimitive_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (s t : ℝ) :
    |cavityFieldPrimitive rho lam hrho hsum p s -
      cavityFieldPrimitive rho lam hrho hsum p t| ≤ 4 * K^2 * |s - t| := by
  rw [cavityFieldPrimitive_sub]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 4 * K^2)
    (f := cavityFieldDensity rho lam hrho hsum p) (fun u _ => by
      dsimp only [cavityFieldDensity]
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRDerivative_nonneg rho lam hrho hsum _)]
      exact cavityRDerivative_le rho lam hrho hsum hK hlam _)
  simpa only [Real.norm_eq_abs] using hb

lemma cavityStrictUniformField_height_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    (cavityStrictUniformField rho lam hrho hsum p n).height i ≤ 4 * K^2 := by
  have hb := cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n i) 0
  have hq := cavityStrictUniformLevels_mem p n i
  have hp0 : cavityFieldPrimitive rho lam hrho hsum (cavityStrictUniformPath p n) 0 = 0 := by
    simp only [cavityFieldPrimitive, intervalIntegral.integral_same]
  rw [hp0, sub_zero, abs_of_nonneg (cavityFieldPrimitive_nonneg _ _ _ _ _ hq.1.le),
    sub_zero, abs_of_pos hq.1] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity) hq.2.le)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalEntropyLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-model cavity field reaches the exact entropy supremum
and hence the finite-spectrum variational trial value. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_original_entropy_trial_limit (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
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
    :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    entropyFunctional p ≠ ⊤ ∧
    Tendsto (fun r =>
      fieldValue (cavityStrictUniformField ρ lam hρ hρsum p r) 0 +
      fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r) / 2 +
      spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)) atTop
      (𝓝 ((entropyFunctional p).toReal + spectralFunctional (finiteR ρ lam hρ hρsum) p)) := by
  intro p
  have hself := cavity_original_scalar_self_consistency hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag a ha
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hKl a : |lam a| ≤ K := Finset.single_le_sum (fun b _ => abs_nonneg (lam b)) (Finset.mem_univ a)
  exact cavity_entropy_trial_tendsto ρ lam hρ hρsum p (cavityStrictUniformPath p)
    (cavityStrictUniformField ρ lam hρ hρsum p)
    (fun r => cavityStrictUniformField_height_le ρ lam hρ hρsum hK hKl p r (Fin.last r))
    hself (cavityStrictUniformPath_l1_tendsto p)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityVariationalTrialLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from the convergent physical entropy trial to the finite
spectral variational lower bound. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_variational_lower_of_trial_limit {m : ℕ}
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hsum : ∑ a, ρ a=1)
    (p : OverlapPath) (f A : ℕ → ℝ) (hent : entropyFunctional p ≠ ⊤)
    (hconv : Tendsto f atTop
      (𝓝 ((entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p)))
    (hlower : ∀ ε>0, ∀ᶠ r in atTop, f r-A r<ε) :
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hsum)).toReal-A r<ε := by
  have hbot : entropyFunctional p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (entropyFunctional_nonneg p)
  have hfinite := finiteVariational_ne_top_bot ρ lam hρ hsum
  have hi := iInf_le (fun q : OverlapPath => entropyFunctional q+
    (spectralFunctional (finiteR ρ lam hρ hsum) q : EReal)) p
  change variationalFunctional (finiteR ρ lam hρ hsum) ≤ _ at hi
  rw [← EReal.coe_toReal hfinite.1 hfinite.2, ← EReal.coe_toReal hent hbot,
    ← EReal.coe_add] at hi
  have hi' : (variationalFunctional (finiteR ρ lam hρ hsum)).toReal ≤
      (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p := by
    exact_mod_cast hi
  intro ε hε
  have he : 0<ε/2 := by positivity
  have hc := hconv.eventually (lt_mem_nhds (show
    (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p-ε/2 <
    (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p by linarith))
  filter_upwards [hc, hlower (ε/2) he] with r hr hl
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalVariationalLower
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original physical model satisfies the finite-spectrum variational
lower bound along a spectral/GG/Ward subsequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_physical_variational_lower (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
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
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro Δ
  let p := spectralSpinQuantilePath Q₀ hP hnonneg
  let B := cavityCompressionLimitFrame es B₀
  have hprob' := hprob
  rw [hA] at hprob'
  have hlower := cavity_physical_trial_lower hn N depth hN hNlim g k e ek es B₀
    (fun a r => l r a) (fun a r => w r a) hg hln hw a₀ hk hgroups hdims μ ν θ μG
    lam v u hv hu hc hcG ρ hρ hρsum hρlim Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg
    hoff hdiag B (cavityCompressionLimitFrame_gram es B₀ hB₀)
    (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
    (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
    a ha counts hcounts_le hcounts hcounts_rho R hprob'
  obtain ⟨hent,hconv⟩ := cavity_original_entropy_trial_limit hpub N depth hN hNlim g k ek e
    es B₀ a₀ hk μG l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀
    ρ hρ hρsum hperp hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP
    hnonneg hoff hdiag a ha
  exact cavity_variational_lower_of_trial_limit ρ lam hρ hρsum p
    (fun r => fieldValue (cavityStrictUniformField ρ lam hρ hρsum p r) 0+
      fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
      spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r))
    (fun r => (n : ℝ)⁻¹*Δ r) hent hconv hlower

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySubsequenceLower
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The subsequence principle needed to remove the compact Gibbs-array
limit from the eventual physical pressure increment inequality. -/

noncomputable section
open Filter

namespace InvariantIsing

theorem cavity_eventual_lower_of_subsequence (f : ℕ → ℝ) (L : ℝ)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ ε>0, ∀ᶠ r in atTop, L-ε<f (φ (ψ r))) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε<f r := by
  intro ε hε
  by_contra hn
  have hf : ∃ᶠ r in atTop, ¬L-ε<f r := by
    simpa only [Filter.Frequently, not_not] using hn
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨ψ,_hψ,hgood⟩ := h φ hφ
  obtain ⟨r,hr⟩ := (hgood ε hε).exists
  exact hbad (ψ r) hr

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowVariationalLower
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variational lower bound with compression convergence and its
good event discharged by the actual contiguous-window laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_window_variational_lower (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
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
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun r => w r a) atTop atTop)
    (hllim : ∀ a, (∀ r, l r a=0) ∨ Tendsto (fun r => l r a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun r => (l r a : ℝ)/(N r+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun r => (w r a : ℝ)/(N r+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
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
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro Δ
  subst ρ
  have hsumlim : Tendsto (fun r => N r+n) atTop atTop :=
    (tendsto_add_atTop_nat n).comp hNlim
  obtain ⟨⟨L,hL,hgood⟩,hprob⟩ := cavity_window_inputs es lam a₀ B₀ hB₀ N
    (fun r => Nat.add_pos_left (hN r) n) (fun a r => l r a) (fun a r => w r a) g
    (fun a r => hg r a) hsumlim hwlim hllim
    (fun a r => by have := hln r a; omega)
    (fun a r => by have := hln r a; have := hw r a; omega)
    (fun a r => hw r a) ρl ρw hρ hρsum hρl hρw hperp μ
  let A : CavityFactorBlocks d n :=
    ((cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityCompressionLimitFrame es B₀-Matrix.diagonal (fun j => lam (a₀ j)),
     (cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) (fun a => ρw a-ρl a),
     (finiteR (fun a => ρw a-ρl a) lam hρ hρsum 0) • 1)
  exact cavity_physical_variational_lower hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu (fun r => cavityCompressionGoodEvent (g r) L)
    (fun r => measurableSet_cavityCompressionGoodEvent (g r) L) hgood hL
    (fun _ _ hU => hU) hd hn hB₀ (fun a => ρw a-ρl a) hρ hρsum hperp
    hgroups hdims hc hcG hρlim A rfl hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg
    hoff hdiag a ha counts hcounts_le hcounts hcounts_rho R

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowMinimumLower
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite pressure minima imply the physical variational
increment lower bound. No Gibbs-array limit is assumed here. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_window_minimum_variational_lower_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N : ℕ → ℕ) (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (hN : ∀ j, 3 ≤ N j) (hNlim : Tendsto N atTop atTop)
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
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a ∈ Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (N j) → ℝ) (hu : ∀ j i, u j i ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN j; omega) (ν j))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 depth b (fun _ => 0) (u j) (v j) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN j; omega) (ν j))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 depth b (fun _ => 0) u' v')
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun r => w r a) atTop atTop)
    (hllim : ∀ a, (∀ r, l r a=0) ∨ Tendsto (fun r => l r a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun r => (l r a : ℝ)/(N r+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun r => (w r a : ℝ)/(N r+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (cavityBaseAmplitude (u r)) z.1 ∂(μ r).prod θ) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (cavityBaseAmplitude (u r)) z.1 ∂(ν r).prod θ
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro θ Δ
  let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
  let I := fun r => cavitySpectralGroup (fun i => ((E r).symm i).1)
  let eig := fun r i => lam ((E r).symm i).1
  let K := 1+∑ a, |lam a|
  have hK : 0<K := by
    have hs : 0≤∑ a, |lam a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [K]
    linarith
  have hKeig r i : |eig r i|≤K := by
    have hs := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (((E r).symm i).1))
    dsimp only [eig, K]
    linarith
  have hlabel r a i (hi : i∈I r a) : eig r i=lam a := by
    have he : ((E r).symm i).1=a := (Finset.mem_filter.mp hi).2
    change lam ((E r).symm i).1=lam a
    rw [he]
  have hmass : Tendsto (fun r a => ((I r a).card : ℝ)/N r) atTop (𝓝 ρ) := by
    apply hρlim.congr
    intro r
    funext a
    rw [cavity_group_dimension_card]
  have hpos r : 0<N r := by have := hN r; omega
  have hua r j : |cavityBaseAmplitude (u r) j|≤2 := cavityBaseAmplitude_bound (u r) (hu r) j
  have hva r a : |v r a|≤2 := abs_le.mpr ⟨by linarith [(hv r a).1], (hv r a).2⟩
  have hlower := cavity_eventual_lower_of_subsequence (fun r => (n : ℝ)⁻¹*Δ r)
    (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal (by
      intro φ hφ
      obtain ⟨ψ,hψ,Q,q,hlim,hgg,hδ,hG,hE,hP,hnonneg,hoff,hdiag⟩ :=
        cavity_fixed_minimum_geometric_limit hhaar hgauss (fun r => N (φ r))
          (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop) m depth b hb
          (fun r => ν (φ r)) (fun r => eig (φ r)) K hK (fun r => hKeig (φ r))
          (fun r => I (φ r)) (fun r => cavitySpectralGroup_pairwiseDisjoint _)
          (fun r => cavitySpectralGroup_cover _) lam (fun r => hlabel (φ r))
          ρ (hmass.comp hφ.tendsto_atTop) (fun r => u (φ r)) (fun r => v (φ r))
          (fun r => hu (φ r)) (fun r => hv (φ r)) (fun r => hmin (φ r))
      let χ := φ ∘ ψ
      have hχ : StrictMono χ := hφ.comp hψ
      have hh := cavity_window_variational_lower hpub (fun r => N (χ r)) (fun _ => depth)
        (fun r => hpos (χ r)) (hNlim.comp hχ.tendsto_atTop)
        (fun r => g (χ r)) (fun r => k (χ r)) (fun r => ek (χ r)) (fun r => e (χ r))
        es B₀ a₀ (fun r => hk (χ r)) (fun r => μG (χ r))
        (fun r => l (χ r)) (fun r => w (χ r)) (fun r => hg (χ r))
        (fun r => hln (χ r)) (fun r => hw (χ r)) (fun r => μ (χ r)) (fun r => ν (χ r))
        (fun _ => θ) lam (fun r => v (χ r)) (fun r => hva (χ r))
        (fun r => cavityBaseAmplitude (u (χ r))) (fun r => hua (χ r)) hd hn hB₀
        ρ hρ hρsum ρl ρw hρdef (fun a => (hwlim a).comp hχ.tendsto_atTop)
        (fun a => (hllim a).elim (fun h => Or.inl (fun r => h (χ r)))
          (fun h => Or.inr (h.comp hχ.tendsto_atTop)))
        (fun a => (hρl a).comp hχ.tendsto_atTop) (fun a => (hρw a).comp hχ.tendsto_atTop)
        hperp (fun r => hgroups (χ r)) (fun a => (hdims a).comp hχ.tendsto_atTop)
        hc (fun r => hcG (χ r)) (hρlim.comp hχ.tendsto_atTop)
        Q hlim hgg hG (fun a => (q a : ℝ)) (fun a => (q a).property.1) hδ
        hE hP hnonneg hoff hdiag a ha counts hcounts_le hcounts hcounts_rho R
      refine ⟨ψ,hψ,?_⟩
      intro ε hε
      filter_upwards [hh ε hε] with r hr
      change (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-
        (n : ℝ)⁻¹*Δ (φ (ψ r))<ε at hr
      linarith)
  intro ε hε
  filter_upwards [hlower ε hε] with r hr
  linarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_window_minimum_variational_lower_oai := @OAI.InvariantIsing.cavity_window_minimum_variational_lower_oai
