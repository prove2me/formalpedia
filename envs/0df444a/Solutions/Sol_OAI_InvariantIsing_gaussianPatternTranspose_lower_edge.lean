-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPatternTranspose_lower_edge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:26.574863+00:00
-- url     : https://prove2.me/submissions/075eb5a0-55ec-4bd9-9880-663a0244489a

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
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_finiteGaussian_centered_tendsto
import Theorems.Thm_OAI_InvariantIsing_gaussianNorm_lower_mean

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
-- module Solutions.OAIQ258_II.IsingPerceptron_GaussianIntegration
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hm' : Measurable f')
    {K K' : ℝ} (hb : ∀ x, |f x| ≤ K) (hb' : ∀ x, |f' x| ≤ K') :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hm : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)).measurable
  have hif : Integrable f (gaussianReal 0 1) :=
    (MemLp.of_bound hm.aestronglyMeasurable K
      (ae_of_all _ (fun x => by simpa using hb x)) (p := 1)).integrable le_rfl
  have hif' : Integrable f' (gaussianReal 0 1) :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun x => by simpa using hb' x)) (p := 1)).integrable le_rfl
  apply gaussian_integration_by_parts hd hif hif'
  exact ((memLp_id_gaussianReal 1).integrable le_rfl).mul_bdd
    hm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hb x))

lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {F F' : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F) (hm' : Measurable F')
    (hd : ∀ (g : Fin n → ℝ) (x : ℝ),
      HasDerivAt (fun y => F (i.insertNth y g)) (F' (i.insertNth x g)) x)
    {K K' : ℝ} (hb : ∀ g, |F g| ≤ K) (hb' : ∀ g, |F' g| ≤ K') :
    (∫ g, g i * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, F' g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm ((gaussianReal 0 1).prod ν) μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hF' : Integrable F' μ :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun g => by simpa using hb' g)) (p := 1)).integrable le_rfl
  have hFi : Integrable (fun g => g i * F g) μ := by
    have hc : Integrable (fun g : Fin (n + 1) → ℝ => g i) μ :=
      (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)
    exact hc.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa using hb g))
  change (∫ g, g i * F g ∂μ) = ∫ g, F' g ∂μ
  rw [← he.integral_comp' (fun g => g i * F g), ← he.integral_comp' F']
  have hi1 : Integrable (fun v => e.symm v i * F (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hFi
  have hi2 : Integrable (fun v => F' (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hF'
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  apply gaussian_integration_by_parts_bounded (hd g)
  · exact hm'.comp (measurable_pi_iff.mpr (i.forall_iff_succAbove.mpr
      ⟨by simp only [Fin.insertNth_apply_same]; exact measurable_id,
        fun j => by simp⟩))
  · exact fun x => hb _
  · exact fun x => hb' _

section FiniteGibbs
variable {S : Type*} [Fintype S]

lemma finiteGibbs_nonneg {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    0 ≤ finiteGibbs w H x :=
  div_nonneg (mul_nonneg (hw.1 x) (Real.exp_pos _).le) (finitePartition_pos hw H).le

lemma finiteGibbs_sum {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    ∑ x, finiteGibbs w H x = 1 := by
  simp only [finiteGibbs, ← Finset.sum_div]
  exact div_self (finitePartition_pos hw H).ne'

lemma finiteGibbs_le_one {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    finiteGibbs w H x ≤ 1 := by
  rw [← finiteGibbs_sum hw H]
  exact Finset.single_le_sum (fun y _ => finiteGibbs_nonneg hw H y) (Finset.mem_univ x)

lemma finiteGibbs_average_bound {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ x, |A x| ≤ K) :
    |∑ x, finiteGibbs w H x * A x| ≤ K := by
  calc
    _ ≤ ∑ x, |finiteGibbs w H x * A x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, finiteGibbs w H x * |A x| := by
      congr 1; ext x; rw [abs_mul, abs_of_nonneg (finiteGibbs_nonneg hw H x)]
    _ ≤ ∑ x, finiteGibbs w H x * K := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hA x) (finiteGibbs_nonneg hw H x))
    _ = K := by rw [← Finset.sum_mul, finiteGibbs_sum hw H, one_mul]

lemma hasDerivAt_finitePartition {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (w : S → ℝ) :
    HasDerivAt (fun s => finitePartition w (H s))
      (∑ x, w x * Real.exp (H t x) * dH x) t := by
  simpa only [finitePartition, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hH x).exp.const_mul (w x)))

lemma hasDerivAt_finiteGibbs {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (x : S) :
    HasDerivAt (fun s => finiteGibbs w (H s) x)
      (finiteGibbs w (H t) x *
        (dH x - ∑ y, finiteGibbs w (H t) y * dH y)) t := by
  have hd := ((hH x).exp.const_mul (w x)).div
    (hasDerivAt_finitePartition hH w) (finitePartition_pos hw (H t)).ne'
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [finiteGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(finitePartition_pos hw (H t)).ne']

lemma hasDerivAt_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) :
    HasDerivAt (fun s => Real.log (finitePartition w (H s)))
      (∑ x, finiteGibbs w (H t) x * dH x) t := by
  convert (hasDerivAt_finitePartition hH w).log (finitePartition_pos hw (H t)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteGibbs, div_mul_eq_mul_div, Finset.sum_div]

end FiniteGibbs

section GaussianGibbs
variable {S : Type*} [Fintype S]

omit [Fintype S] in
lemma hasDerivAt_linearGaussian_insert {n : ℕ} (C : S → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => linearGaussian C (i.insertNth y g) x) (C x i) t := by
  have he : (fun y => linearGaussian C (i.insertNth y g) x) =
      fun y => C x i * y + ∑ j : Fin n, C x (i.succAbove j) * g j := by
    funext y
    simp only [linearGaussian, i.sum_univ_succAbove, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  rw [he]
  simpa using ((hasDerivAt_id t).const_mul (C x i)).add_const
    (∑ j : Fin n, C x (i.succAbove j) * g j)

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

lemma integrable_gaussian_coordinate_mul {n : ℕ} (i : Fin n)
    {F : (Fin n → ℝ) → ℝ} (hm : Measurable F) {K : ℝ} (hK : ∀ g, |F g| ≤ K) :
    Integrable (fun g => g i * F g) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hc : Integrable (fun g : Fin n → ℝ => g i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal 1).integrable le_rfl)
  exact hc.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun g => by simpa using hK g))

omit [Fintype S] in
lemma gaussian_pi_linear_insertion {n : ℕ} (a : Fin (n + 1) → ℝ)
    {F : (Fin (n + 1) → ℝ) → ℝ} {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
    (hm : Measurable F) (hm' : ∀ i, Measurable (F' i))
    (hd : ∀ i g x, HasDerivAt (fun y => F (i.insertNth y g)) (F' i (i.insertNth x g)) x)
    {K : ℝ} {K' : Fin (n + 1) → ℝ}
    (hb : ∀ g, |F g| ≤ K) (hb' : ∀ i g, |F' i g| ≤ K' i) :
    (∫ g, (∑ i, a i * g i) * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, ∑ i, a i * F' i g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hi i : Integrable (F' i) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (MemLp.of_bound (hm' i).aestronglyMeasurable (K' i)
      (ae_of_all _ (fun g => by simpa using hb' i g)) (p := 1)).integrable le_rfl
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (integrable_gaussian_coordinate_mul i hm hb).const_mul _),
    integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul,
    gaussian_pi_integration_by_parts i hm (hm' i) (hd i) hb (hb' i)]

end Replicas

section Perturbation
variable {S : Type*} [Fintype S]

lemma log_finitePartition_le_add {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, H x ≤ J x + K) :
    Real.log (finitePartition w H) ≤ Real.log (finitePartition w J) + K := by
  rw [← Real.log_exp K, ← Real.log_mul (finitePartition_pos hw J).ne' (Real.exp_pos K).ne']
  apply Real.log_le_log (finitePartition_pos hw H)
  unfold finitePartition
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h x)) (hw.1 x)

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

omit [Fintype S] in
lemma linearGaussian_scale {n : ℕ} (A : S → Fin n → ℝ) (t : ℝ) (g : Fin n → ℝ) (x : S) :
    linearGaussian (fun y i => t * A y i) g x = t * linearGaussian A g x := by
  simp only [linearGaussian, Finset.mul_sum, mul_assoc]

end Perturbation

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotationCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trigonometric interpolation between independent Gaussian fields,
with the cavity-size penalty removed along the same path. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityGaussianCurve_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurve C A t) g x =
      Real.cos t * linearGaussian C g x + Real.sin t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurve, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurveDerivative_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurveDerivative C A t) g x =
      -Real.sin t * linearGaussian C g x + Real.cos t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurveDerivative, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurve_hasDerivAt {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    HasDerivAt (fun s => linearGaussian (cavityGaussianCurve C A s) g x)
      (linearGaussian (cavityGaussianCurveDerivative C A t) g x) t := by
  simp_rw [cavityGaussianCurve_linear, cavityGaussianCurveDerivative_linear]
  exact ((Real.hasDerivAt_cos t).mul_const _).add ((Real.hasDerivAt_sin t).mul_const _)

lemma cavityGaussianCurveDerivative_bound {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    |linearGaussian (cavityGaussianCurveDerivative C A t) g x| ≤
      |linearGaussian C g x| + |linearGaussian A g x| := by
  rw [cavityGaussianCurveDerivative_linear]
  calc
    _ ≤ |-Real.sin t * linearGaussian C g x| + |Real.cos t * linearGaussian A g x| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_neg]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _)).trans_eq (one_mul _))
        ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _)).trans_eq (one_mul _))

lemma cavityGaussianCurve_cross {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (x y : X)
    (hCA : ∀ x y, gaussianCross C A x y = 0) :
    gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      (Real.sin t * Real.cos t) * (gaussianCross A A x y - gaussianCross C C x y) := by
  have hAC : gaussianCross A C x y = 0 := by
    simpa only [gaussianCross, mul_comm] using hCA y x
  have hexpand : gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      -Real.sin t * Real.cos t * gaussianCross C C x y +
      (-Real.sin t * Real.sin t) * gaussianCross C A x y +
      (Real.cos t * Real.cos t) * gaussianCross A C x y +
      Real.cos t * Real.sin t * gaussianCross A A x y := by
    simp only [gaussianCross, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cavityGaussianCurveDerivative, cavityGaussianCurve]
    ring
  rw [hexpand, hCA x y, hAC]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_DenseFiniteMaximum
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing finite maxima exhaust a continuous function on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma le_prefixMaximum (f : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : f i ≤ prefixMaximum f n := by
  exact Finset.le_sup' (fun j : Fin (n+1) => f j) (Finset.mem_univ ⟨i,by omega⟩)

lemma prefixMaximum_le (f : ℕ → ℝ) {n : ℕ} {b : ℝ} (h : ∀ i ≤ n, f i ≤ b) :
    prefixMaximum f n ≤ b := by
  apply Finset.sup'_le
  intro i _
  exact h i (by omega)

lemma prefixMaximum_monotone (f : ℕ → ℝ) : Monotone (prefixMaximum f) := by
  intro n m hnm
  exact prefixMaximum_le f (fun i hi => le_prefixMaximum f (hi.trans hnm))

lemma prefixMaximum_bddAbove {f : ℕ → ℝ} (hf : BddAbove (range f)) :
    BddAbove (range (prefixMaximum f)) := by
  obtain ⟨b,hb⟩ := hf
  exact ⟨b,fun _ ⟨n,hn⟩ => hn ▸ prefixMaximum_le f (fun i _ => hb (mem_range_self i))⟩

lemma prefixMaximum_tendsto {f : ℕ → ℝ} (hf : BddAbove (range f)) :
    Tendsto (prefixMaximum f) atTop (𝓝 (⨆ i, f i)) := by
  have hb := prefixMaximum_bddAbove hf
  have he : (⨆ n, prefixMaximum f n) = ⨆ i, f i := by
    apply le_antisymm
    · exact ciSup_le (fun n => prefixMaximum_le f (fun i _ => le_ciSup hf i))
    · exact ciSup_le (fun i => (le_prefixMaximum f (le_refl i)).trans (le_ciSup hb i))
  rw [← he]
  exact tendsto_atTop_ciSup (prefixMaximum_monotone f) hb

theorem dense_prefixMaximum_tendsto {S : Type*} [TopologicalSpace S] [Nonempty S]
    (s : ℕ → S) (hs : DenseRange s) (f : S → ℝ) (hf : Continuous f)
    (hb : BddAbove (range f)) :
    Tendsto (prefixMaximum (f ∘ s)) atTop (𝓝 (⨆ x, f x)) := by
  have hbs : BddAbove (range (f ∘ s)) := hb.mono (range_comp_subset_range _ _)
  have he : (⨆ i, f (s i)) = ⨆ x, f x := by
    apply le_antisymm
    · exact ciSup_le (fun i => le_ciSup hb (s i))
    · apply ciSup_le
      exact isClosed_property hs (isClosed_le hf continuous_const)
        (fun i => le_ciSup hbs i)
  simpa only [Function.comp_def,he] using prefixMaximum_tendsto hbs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_DenseFiniteMinimum
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing finite minima exhaust continuous functions on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma prefixMinimum_le (f : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : prefixMinimum f n ≤ f i :=
  Finset.inf'_le (fun j : Fin (n+1) => f j) (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1)))

lemma le_prefixMinimum (f : ℕ → ℝ) {n : ℕ} {b : ℝ} (h : ∀ i ≤ n, b ≤ f i) :
    b ≤ prefixMinimum f n := by
  apply Finset.le_inf'
  intro i _
  exact h i (by omega)

lemma prefixMinimum_antitone (f : ℕ → ℝ) : Antitone (prefixMinimum f) := by
  intro n m hnm
  exact le_prefixMinimum f (fun i hi => prefixMinimum_le f (hi.trans hnm))

lemma prefixMinimum_bddBelow {f : ℕ → ℝ} (hf : BddBelow (range f)) :
    BddBelow (range (prefixMinimum f)) := by
  obtain ⟨b,hb⟩ := hf
  exact ⟨b,fun _ ⟨n,hn⟩ => hn ▸ le_prefixMinimum f (fun i _ => hb (mem_range_self i))⟩

lemma prefixMinimum_tendsto {f : ℕ → ℝ} (hf : BddBelow (range f)) :
    Tendsto (prefixMinimum f) atTop (𝓝 (⨅ i, f i)) := by
  have hb := prefixMinimum_bddBelow hf
  have he : (⨅ n, prefixMinimum f n) = ⨅ i, f i := by
    apply le_antisymm
    · exact le_ciInf (fun i => (ciInf_le hb i).trans (prefixMinimum_le f (le_refl i)))
    · exact le_ciInf (fun n => le_prefixMinimum f (fun i _ => ciInf_le hf i))
  rw [← he]
  exact tendsto_atTop_ciInf (prefixMinimum_antitone f) hb

theorem dense_prefixMinimum_tendsto {S : Type*} [TopologicalSpace S] [Nonempty S]
    (s : ℕ → S) (hs : DenseRange s) (f : S → ℝ) (hf : Continuous f)
    (hb : BddBelow (range f)) :
    Tendsto (prefixMinimum (f ∘ s)) atTop (𝓝 (⨅ x, f x)) := by
  have hbs : BddBelow (range (f ∘ s)) := hb.mono (range_comp_subset_range _ _)
  have he : (⨅ i, f (s i)) = ⨅ x, f x := by
    apply le_antisymm
    · apply le_ciInf
      exact isClosed_property hs (isClosed_le continuous_const hf)
        (fun i => ciInf_le hbs i)
    · exact le_ciInf (fun i => ciInf_le hb (s i))
  simpa only [Function.comp_def,he] using prefixMinimum_tendsto hbs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two finite Gibbs levels in the Gaussian minimum--maximum comparison. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_reference {X : Type*} [Nonempty X] : GibbsReference (fun _ : X => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one,⟨Classical.choice inferInstance,zero_lt_one⟩⟩

lemma gordonWeight_nonneg (H : U × V → ℝ) (x : U × V) : 0 ≤ gordonWeight H x :=
  mul_nonneg (finiteGibbs_nonneg gordon_reference _ _) (finiteGibbs_nonneg gordon_reference _ _)

lemma gordonWeight_le_one (H : U × V → ℝ) (x : U × V) : gordonWeight H x ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (finiteGibbs_le_one gordon_reference _ _)
      (finiteGibbs_le_one gordon_reference _ _)
      (finiteGibbs_nonneg gordon_reference _ _) zero_le_one
    _ = _ := one_mul _

omit [Nonempty U] [Nonempty V] in
lemma gordonMean_eq_sum (H D : U × V → ℝ) : gordonMean H D = ∑ x, gordonWeight H x*D x := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [gordonMean,gordonRowMean,Finset.mul_sum,gordonWeight,mul_assoc]

omit [Fintype V] [Nonempty V] in
lemma gordonRow_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) (v : V) :
    HasDerivAt (fun s => gordonRow (H s) v) (gordonRowMean (H t) D v) t :=
  hasDerivAt_log_finitePartition gordon_reference (fun u => hH (u,v))

lemma gordonValue_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) :
    HasDerivAt (fun s => gordonValue (H s)) (gordonMean (H t) D) t := by
  have h := (hasDerivAt_log_finitePartition gordon_reference
    (fun v => (gordonRow_hasDerivAt hH v).neg)).neg
  convert h using 1 <;> first | rfl |
    simp only [gordonMean,gordonOuter,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,neg_neg]

lemma gordonWeight_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) (x : U × V) :
    HasDerivAt (fun s => gordonWeight (H s) x)
      (gordonWeight (H t) x*(D x-2*gordonRowMean (H t) D x.2+gordonMean (H t) D)) t := by
  have hi := hasDerivAt_finiteGibbs gordon_reference (fun u => hH (u,x.2)) x.1
  have ho := hasDerivAt_finiteGibbs gordon_reference
    (fun v => (gordonRow_hasDerivAt hH v).neg) x.2
  convert (config := {transparency := .instances, preTransparency := .instances}) ho.mul hi using 1
  · rfl
  simp only [gordonMean,gordonRowMean,gordonWeight,gordonInner,gordonOuter,
    Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds and continuity for the two-level Gaussian comparison weights. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
lemma gordonRowMean_bound (H D : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |D x| ≤ K) (v : V) : |gordonRowMean H D v| ≤ K :=
  finiteGibbs_average_bound gordon_reference _ _ (fun u => hD (u,v))

lemma gordonMean_bound (H D : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |D x| ≤ K) : |gordonMean H D| ≤ K :=
  finiteGibbs_average_bound gordon_reference _ _ (gordonRowMean_bound H D K hD)

lemma gordonWeight_derivative_bound (H D : U × V → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hD : ∀ x, |D x| ≤ K) (x : U × V) :
    |gordonWeight H x*(D x-2*gordonRowMean H D x.2+gordonMean H D)| ≤ 4*K := by
  have hb : |D x-2*gordonRowMean H D x.2+gordonMean H D| ≤ 4*K := by
    calc
      _ ≤ |D x|+|2*gordonRowMean H D x.2|+|gordonMean H D| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = |D x|+2*|gordonRowMean H D x.2|+|gordonMean H D| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 4*K := by linarith [hD x,gordonRowMean_bound H D K hD x.2,gordonMean_bound H D K hD]
  rw [abs_mul,abs_of_nonneg (gordonWeight_nonneg H x)]
  exact (mul_le_mul_of_nonneg_left hb (gordonWeight_nonneg H x)).trans
    (by nlinarith [gordonWeight_le_one H x])

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonRow {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (v : V) :
    Continuous (fun s => gordonRow (H s) v) := by
  apply Continuous.log
  · exact continuous_finsetSum _ (fun u _ => (Real.continuous_exp.comp (hH (u,v))).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun u => H s (u,v))).ne'

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonInner {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (u : U) (v : V) :
    Continuous (fun s => gordonInner (H s) u v) := by
  apply Continuous.div
  · exact (Real.continuous_exp.comp (hH (u,v))).const_mul 1
  · exact continuous_finsetSum _ (fun u _ => (Real.continuous_exp.comp (hH (u,v))).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun u => H s (u,v))).ne'

lemma continuous_gordonOuter {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (v : V) :
    Continuous (fun s => gordonOuter (H s) v) := by
  apply Continuous.div
  · exact (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1
  · exact continuous_finsetSum _ (fun v _ =>
      (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun v => -gordonRow (H s) v)).ne'

lemma continuous_gordonWeight {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (x : U × V) :
    Continuous (fun s => gordonWeight (H s) x) :=
  (continuous_gordonOuter H hH x.2).mul (continuous_gordonInner H hH x.1 x.2)

lemma continuous_gordonValue {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) :
    Continuous (fun s => gordonValue (H s)) := by
  apply Continuous.neg
  apply Continuous.log
  · exact continuous_finsetSum _ (fun v _ =>
      (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun v => -gordonRow (H s) v)).ne'

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonRowMean {S : Type*} [TopologicalSpace S] (H D : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (hD : ∀ x, Continuous (fun s => D s x)) (v : V) :
    Continuous (fun s => gordonRowMean (H s) (D s) v) :=
  continuous_finsetSum _ (fun u _ => (continuous_gordonInner H hH u v).mul (hD (u,v)))

lemma continuous_gordonMean {S : Type*} [TopologicalSpace S] (H D : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (hD : ∀ x, Continuous (fun s => D s x)) :
    Continuous (fun s => gordonMean (H s) (D s)) :=
  continuous_finsetSum _ (fun v _ =>
    (continuous_gordonOuter H hH v).mul (continuous_gordonRowMean H D hH hD v))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonValueBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Lipschitz and integrability bounds for the Gaussian minimum--maximum value. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordonValue_sub_bound (H J : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |H x-J x| ≤ K) : |gordonValue H-gordonValue J| ≤ K := by
  let F := fun t : ℝ => fun x => J x+t*(H x-J x)
  have hd (t : ℝ) : HasDerivAt (fun t => gordonValue (F t))
      (gordonMean (F t) (fun x => H x-J x)) t := by
    apply gordonValue_hasDerivAt
    intro x
    simpa only [F, id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (H x-J x)).const_add (J x))
  have hb (t : ℝ) : ‖gordonMean (F t) (fun x => H x-J x)‖ ≤ K := by
    simpa only [Real.norm_eq_abs] using gordonMean_bound (F t) _ K hD
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => hb t) convex_univ (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  simpa only [F,zero_mul,add_zero,one_mul,add_sub_cancel,sub_zero,norm_one,mul_one,
    Real.norm_eq_abs] using h

lemma integrable_gordonValue {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ) :
    Integrable (fun g => gordonValue (fun x => H x+linearGaussian C g x))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hc : Continuous (fun g : Fin d → ℝ => gordonValue (fun x => H x+linearGaussian C g x)) :=
    continuous_gordonValue _ (fun x => by unfold linearGaussian; fun_prop)
  apply ((integrable_const |gordonValue H|).add
    (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs))).mono'
    hc.aestronglyMeasurable
  apply ae_of_all
  intro g
  have hb := gordonValue_sub_bound (fun x => H x+linearGaussian C g x) H
    (∑ x, |linearGaussian C g x|) (fun x => by
      simpa only [add_sub_cancel_left] using
        Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) (Finset.mem_univ x))
  rw [Real.norm_eq_abs]
  have ht := abs_add_le
    (gordonValue (fun x => H x+linearGaussian C g x)-gordonValue H) (gordonValue H)
  rw [sub_add_cancel] at ht
  change |gordonValue (fun x => H x+linearGaussian C g x)| ≤
    |gordonValue H| + ∑ x, |linearGaussian C g x|
  exact ht.trans (by linarith)

lemma integrable_gordon_linear {d : ℕ} (A C : U × V → Fin d → ℝ) (x : U × V) :
    Integrable (fun g => linearGaussian A g x*gordonWeight (fun y => linearGaussian C g y) x)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_gordonWeight _ (fun y => by unfold linearGaussian; fun_prop) x).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs,abs_of_nonneg (gordonWeight_nonneg _ x)]
  exact gordonWeight_le_one _ x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteMinmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite minimum--maximum values and their two-level log-sum-exp bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma finiteMinmax_le_row (H : U × V → ℝ) (v : V) : finiteMinmax H ≤ finiteRowMax H v :=
  Finset.inf'_le _ (Finset.mem_univ v)

lemma finite_log_sum_exp_bounds {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty H ≤ Real.log (finitePartition (fun _ => 1) H) ∧
    Real.log (finitePartition (fun _ => 1) H) ≤
      Finset.univ.sup' Finset.univ_nonempty H+Real.log (Fintype.card X) := by
  constructor
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty H
    rw [he]
    have hs : Real.exp (H x) ≤ finitePartition (fun _ => 1) H := by
      simpa only [finitePartition,one_mul] using
        Finset.single_le_sum (fun y _ => (Real.exp_pos (H y)).le) hx
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hs
  · have he := log_finitePartition_le_add (gordon_reference (X := X))
      (fun x => show H x ≤ 0+Finset.univ.sup' Finset.univ_nonempty H by
        simpa only [zero_add] using Finset.le_sup' H (Finset.mem_univ x))
    simpa only [finitePartition,Real.exp_zero,mul_one,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,add_comm] using he

lemma gordonValue_finiteMinmax_bounds (H : U × V → ℝ) (β : ℝ) (hβ : 0 < β) :
    β*finiteMinmax H-Real.log (Fintype.card V) ≤ gordonValue (fun x => β*H x) ∧
    gordonValue (fun x => β*H x) ≤ β*finiteMinmax H+Real.log (Fintype.card U) := by
  have hr (v : V) : β*finiteRowMax H v ≤ gordonRow (fun x => β*H x) v ∧
      gordonRow (fun x => β*H x) v ≤ β*finiteRowMax H v+Real.log (Fintype.card U) := by
    have hs : Finset.univ.sup' Finset.univ_nonempty (fun u => β*H (u,v)) =
        β*finiteRowMax H v := by
      obtain ⟨u,hu,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
      apply le_antisymm
      · apply Finset.sup'_le
        intro a _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun u => H (u,v)) (Finset.mem_univ a)) hβ.le
      · change β*(Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v))) ≤ _
        rw [he]
        exact Finset.le_sup' (fun u => β*H (u,v)) hu
    simpa only [hs,gordonRow] using finite_log_sum_exp_bounds (fun u => β*H (u,v))
  constructor
  · have hb (v : V) : -gordonRow (fun x => β*H x) v ≤ 0+(-β*finiteMinmax H) := by
      have hm := mul_le_mul_of_nonneg_left (finiteMinmax_le_row H v) hβ.le
      linarith [(hr v).1]
    have he := log_finitePartition_le_add (gordon_reference (X := V)) hb
    have hz : finitePartition (fun _ : V => (1 : ℝ)) (fun _ => 0) = Fintype.card V := by
      simp [finitePartition]
    rw [hz] at he
    change β*finiteMinmax H-Real.log (Fintype.card V) ≤ -Real.log _
    linarith
  · obtain ⟨v,hv,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
    have hl : -gordonRow (fun x => β*H x) v ≤ Real.log
        (finitePartition (fun _ : V => 1) (fun v => -gordonRow (fun x => β*H x) v)) := by
      exact (Finset.le_sup' (fun v => -gordonRow (fun x => β*H x) v) hv).trans
        (finite_log_sum_exp_bounds _).1
    have hmin : finiteMinmax H = finiteRowMax H v := he
    have hh := (hr v).2
    rw [← hmin] at hh
    change -Real.log _ ≤ _
    linarith

lemma finiteMinmax_linear_integrable {d : ℕ} (C : U × V → Fin d → ℝ) :
    Integrable (fun g => finiteMinmax (fun x => linearGaussian C g x))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g => finiteMinmax (fun x => linearGaussian C g x)) := by
    have hr (v : V) : Continuous (fun g => finiteRowMax (fun x => linearGaussian C g x) v) :=
      Continuous.finset_sup'_apply Finset.univ_nonempty (fun u _ => by
        unfold linearGaussian; fun_prop)
    exact (Continuous.finset_inf'_apply Finset.univ_nonempty (fun v _ => hr v)).measurable
  apply (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (finiteRowMax (fun x => linearGaussian C g x))
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u => linearGaussian C g (u,v))
  change ‖Finset.univ.inf' Finset.univ_nonempty _‖ ≤ _
  rw [hv]
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [hu,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) (Finset.mem_univ (u,v))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteMinmaxBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite extrema transport under shifts, order and continuous evaluation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
lemma finiteRowMax_add_constant (H : U × V → ℝ) (a : ℝ) (v : V) :
    finiteRowMax (fun x => H x+a) v = finiteRowMax H v+a := by
  obtain ⟨u,hu,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
  apply le_antisymm
  · apply Finset.sup'_le
    intro u _
    exact add_le_add (Finset.le_sup' (fun u => H (u,v)) (Finset.mem_univ u)) (le_refl a)
  · change (Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v)))+a ≤ _
    rw [he]
    exact Finset.le_sup' (fun u => H (u,v)+a) hu

lemma finiteMinmax_add_constant (H : U × V → ℝ) (a : ℝ) :
    finiteMinmax (fun x => H x+a) = finiteMinmax H+a := by
  obtain ⟨v,hv,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
  apply le_antisymm
  · calc
      _ ≤ finiteRowMax (fun x => H x+a) v := finiteMinmax_le_row _ v
      _ = finiteRowMax H v+a := finiteRowMax_add_constant H a v
      _ = finiteMinmax H+a := by rw [← he]; rfl
  · apply Finset.le_inf'
    intro v _
    rw [finiteRowMax_add_constant]
    exact add_le_add (finiteMinmax_le_row H v) (le_refl a)

lemma finiteMinmax_abs_le (H : U × V → ℝ) (K : ℝ) (h : ∀ x, |H x| ≤ K) :
    |finiteMinmax H| ≤ K := by
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
  change |Finset.univ.inf' Finset.univ_nonempty _| ≤ K
  rw [hv]
  change |Finset.univ.sup' Finset.univ_nonempty _| ≤ K
  rw [hu]
  exact h (u,v)

lemma continuous_finiteMinmax {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) : Continuous (fun s => finiteMinmax (H s)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun v _ =>
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun u _ => hH (u,v)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternEuclideanNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean operator norm of the physical Gaussian array is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

open scoped Matrix.Norms.Frobenius in
lemma gaussianPattern_frobenius {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternArray z‖ = ‖z‖ := by
  rw [Matrix.frobenius_norm_def,PiLp.norm_eq_of_L2,Real.sqrt_eq_rpow]
  congr 1
  simp only [gaussianPatternArray,Fintype.sum_prod_type,Real.norm_eq_abs,Real.rpow_two, sq_abs]

open scoped Matrix.Norms.Frobenius in
lemma gaussianPatternEuclideanOperator_bound {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    ‖gaussianPatternEuclideanOperator z x‖ ≤ ‖z‖ * ‖x‖ := by
  have h := Matrix.frobenius_norm_mul (gaussianPatternArray z)
    (Matrix.replicateCol Unit (fun j => x j))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol,gaussianPattern_frobenius] at h
  exact h

lemma gaussianPatternEuclideanOperator_norm_le {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ‖gaussianPatternEuclideanOperator z‖ ≤ ‖z‖ :=
  (gaussianPatternEuclideanOperator z).opNorm_le_bound (norm_nonneg _)
    (gaussianPatternEuclideanOperator_bound z)

lemma gaussianPatternEuclideanOperator_sub {N m : ℕ}
    (z w : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternEuclideanOperator (z-w) =
      gaussianPatternEuclideanOperator z-gaussianPatternEuclideanOperator w := by
  unfold gaussianPatternEuclideanOperator
  rw [show gaussianPatternArray (z-w) = gaussianPatternArray z-gaussianPatternArray w from rfl,
    map_sub,map_sub]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMaximumComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian maximum comparison used for rectangular spectral edges. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X]

omit [Fintype X] [Nonempty X] in
lemma gaussianCross_scale_both {d : ℕ} (A C : X → Fin d → ℝ) (β : ℝ) (x y : X) :
    gaussianCross (fun x i => β*A x i) (fun x i => β*C x i) x y =
      β^2*gaussianCross A C x y := by
  unfold gaussianCross
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_IndexedGaussianMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite maximum comparison with an arbitrary nonempty Gaussian coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X ι : Type*} [Fintype X] [Nonempty X] [Fintype ι]

lemma measurable_indexedGaussianMaximum (C : X → ι → ℝ) : Measurable (indexedGaussianMaximum C) := by
  have hm := Finset.measurable_sup' (s := (Finset.univ : Finset X)) Finset.univ_nonempty
    (fun x _ => show Measurable (fun g : ι → ℝ => ∑ i, C x i*g i) from by fun_prop)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  rw [Finset.sup'_apply]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bilinear Gaussian comparison behind the sharp rectangular upper edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma bilinearMatrix_covariance {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m)) (x y : X) :
    (∑ i, bilinearMatrixCoefficient u v x i*bilinearMatrixCoefficient u v y i) =
      1 + ⟪u x,u y⟫*⟪v x,v y⟫ := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,bilinearMatrixCoefficient,
    mul_zero,one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinearVector_covariance {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m)) (x y : X) :
    (∑ i, bilinearVectorCoefficient u v x i*bilinearVectorCoefficient u v y i) =
      ⟪u x,u y⟫+⟪v x,v y⟫ := by
  simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,Finset.sum_const_zero,zero_add,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,mul_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternSingularMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least singular value, as an actual unit-sphere minimum, is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternSingularMin_le_add {N m : ℕ} (hm : 0 < m)
    (z w : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternSingularMin z ≤ gaussianPatternSingularMin w + ‖z-w‖ := by
  have hx : EuclideanSpace.single (⟨0,hm⟩ : Fin m) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    simp
  let : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := ⟨⟨_,hx⟩⟩
  have hb : BddBelow (Set.range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ‖gaussianPatternEuclideanOperator z x‖)) := ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hh : gaussianPatternSingularMin z - ‖z-w‖ ≤ gaussianPatternSingularMin w := by
    apply le_ciInf
    intro x
    have hmin : gaussianPatternSingularMin z ≤ ‖gaussianPatternEuclideanOperator z x‖ := ciInf_le hb x
    have hn : ‖(x : EuclideanSpace ℝ (Fin m))‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    have hd := abs_norm_sub_norm_le (gaussianPatternEuclideanOperator z x)
      (gaussianPatternEuclideanOperator w x)
    rw [← sub_apply,← gaussianPatternEuclideanOperator_sub] at hd
    have hbound := gaussianPatternEuclideanOperator_bound (z-w) x
    rw [hn,mul_one] at hbound
    have hdiff := (le_abs_self (‖gaussianPatternEuclideanOperator z x‖-
      ‖gaussianPatternEuclideanOperator w x‖)).trans (hd.trans hbound)
    linarith
  linarith

theorem gaussianPatternSingularMin_lipschitz (N m : ℕ) (hm : 0 < m) :
    LipschitzWith 1 (gaussianPatternSingularMin (N := N) (m := m)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := gaussianPatternSingularMin_le_add hm w z
    rw [norm_sub_rev] at h
    linarith
  · have h := gaussianPatternSingularMin_le_add hm z w
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSingularFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered Gaussian singular-value fluctuations vanish after square-root dimension scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace InvariantIsing

lemma finiteGaussian_lipschitz_memLp_two {ι : Type*} [Fintype ι] {L : ℝ≥0}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hi : MemLp (fun x : EuclideanSpace ℝ ι => x) 2 (stdGaussian _) :=
    IsGaussian.memLp_id _ 2 (by norm_num)
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hh := (hc.comp_memLp (by simp) hi).add
    (memLp_const (f 0) : MemLp (fun _ : EuclideanSpace ℝ ι => f 0) 2 (stdGaussian _))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCoordinateNorm
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact second moments and the square-root dimension bound for coordinate Gaussian norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma gaussianCoordinate_memLp (i : ι) :
    MemLp (fun g : ι → ℝ => g i) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.memLp
    (IsGaussian.memLp_id _ 2 (by norm_num))

lemma gaussianCoordinate_sq_integral (i : ι) :
    (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
  have he : (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ x : ℝ, x^2 ∂gaussianReal 0 1 := by
    simpa only [Function.comp_def,Function.eval] using
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
        (f := fun x : ℝ => x^2) (by fun_prop)
  rw [he]
  have hv := variance_of_integral_eq_zero (μ := gaussianReal 0 1)
    (X := id) (by fun_prop) (by simp)
  simpa only [variance_id_gaussianReal,NNReal.coe_one,id_eq] using hv.symm

lemma gaussianCoordinateVector_sq_integrable (e : κ → ι) :
    Integrable (fun g => ‖gaussianCoordinateVector e g‖^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply]
    using integrable_finsetSum Finset.univ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)

lemma gaussianCoordinateVector_memLp (e : κ → ι) :
    MemLp (gaussianCoordinateVector e) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hm : Continuous (gaussianCoordinateVector e) := by
    unfold gaussianCoordinateVector
    exact (PiLp.continuous_toLp 2 (fun _ : κ => ℝ)).comp
      (continuous_pi (fun j => continuous_apply (e j)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact gaussianCoordinateVector_sq_integrable e

lemma gaussianCoordinateVector_sq_integral (e : κ → ι) :
    (∫ g, ‖gaussianCoordinateVector e g‖^2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = Fintype.card κ := by
  simp only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)]
  simp only [gaussianCoordinate_sq_integral,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma gaussianCoordinateVector_norm_integral_le (e : κ → ι) :
    (∫ g, ‖gaussianCoordinateVector e g‖
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤ Real.sqrt (Fintype.card κ) := by
  have hvar := variance_nonneg (fun g => ‖gaussianCoordinateVector e g‖)
    (Measure.pi (fun _ : ι => gaussianReal 0 1))
  rw [variance_eq_sub (gaussianCoordinateVector_memLp e).norm] at hvar
  change 0 ≤ (∫ g, ‖gaussianCoordinateVector e g‖^2
    ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) - _ at hvar
  rw [gaussianCoordinateVector_sq_integral] at hvar
  have hs : (Real.sqrt (Fintype.card κ))^2 = (Fintype.card κ : ℝ) := Real.sq_sqrt (by positivity)
  have hp := Real.sqrt_nonneg (Fintype.card κ)
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_IndexedGaussianIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and restriction of finite Gaussian maxima. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {X ι κ : Type*} [Fintype X] [Nonempty X] [Fintype ι] [Fintype κ]

lemma indexedGaussianMaximum_integrable (C : X → ι → ℝ) :
    Integrable (indexedGaussianMaximum C) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi (x : X) : Integrable (fun g : ι → ℝ => ∑ i, C x i*g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      ((gaussianCoordinate_memLp i).integrable (by norm_num)).const_mul _)
  apply (integrable_finsetSum Finset.univ (fun x _ => (hi x).abs)).mono'
    (measurable_indexedGaussianMaximum C).aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [he,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (∑ i, C y i*g i)) hx

lemma iidGaussian_restrict_hasLaw (e : κ → ι) (he : Function.Injective e) :
    HasLaw (fun g : ι → ℝ => fun j => g (e j))
      (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i (g : ι → ℝ) => g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  exact (hi.precomp he).hasLaw_pi (fun j =>
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) (e j)).hasLaw)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_UnitBilinearNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean operator norm as the supremum of unit bilinear tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma unitVector_nonempty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] : Nonempty (UnitVector E) := by
  obtain ⟨x,hx⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟨x,hx⟩⟩

lemma gaussianPattern_unitBilinear {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (u : EuclideanSpace ℝ (Fin N)) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪u,gaussianPatternEuclideanOperator z v⟫ = ∑ ij, (u ij.1*v ij.2)*z ij := by
  change (∑ i, (∑ j, z (i,j)*v j)*u i) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_UnitInnerMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit linear tests recover the norm, including the zero vector. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace InvariantIsing

lemma norm_eq_iSup_unitInner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty (UnitVector E)] (w : E) : ‖w‖ = ⨆ u : UnitVector E, ⟪u.1,w⟫ := by
  have hb : BddAbove (range (fun u : UnitVector E => ⟪u.1,w⟫)) :=
    ⟨‖w‖,by rintro _ ⟨u,rfl⟩; simpa only [u.2,one_mul] using real_inner_le_norm u.1 w⟩
  have hn : 0 ≤ ⨆ u : UnitVector E, ⟪u.1,w⟫ := by
    let u : UnitVector E := Classical.choice inferInstance
    let un : UnitVector E := ⟨-u.1,by simp only [norm_neg,u.2]⟩
    have h₁ := le_ciSup hb u
    have h₂ := le_ciSup hb un
    change ⟪-u.1,w⟫ ≤ _ at h₂
    rw [inner_neg_left] at h₂
    linarith
  apply le_antisymm
  · by_cases hz : w = 0
    · simpa only [hz,norm_zero] using hn
    have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let u : UnitVector E := ⟨‖w‖⁻¹ • w,by simp [norm_smul,hnorm]⟩
    have hh := le_ciSup hb u
    change ⟪‖w‖⁻¹ • w,w⟫ ≤ _ at hh
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_mul_norm,
      ← mul_assoc,inv_mul_cancel₀ hnorm,one_mul] using hh
  · exact ciSup_le (fun u => by simpa only [u.2,one_mul] using real_inner_le_norm u.1 w)

lemma unitInner_prefix_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty (UnitVector E)] (s : ℕ → UnitVector E) (hs : DenseRange s) (w : E) :
    Tendsto (prefixMaximum (fun i => ⟪(s i).1,w⟫)) atTop (𝓝 ‖w‖) := by
  have ht := dense_prefixMaximum_tendsto s hs (fun u => ⟪u.1,w⟫)
    (by fun_prop) ⟨‖w‖,by
      rintro _ ⟨u,rfl⟩
      simpa only [u.2,one_mul] using real_inner_le_norm u.1 w⟩
  rw [← norm_eq_iSup_unitInner] at ht
  exact ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonGaussianInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian integration by parts for the joint minimum--maximum Gibbs weight. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_gaussian_insertion {d : ℕ} (A C : U × V → Fin (d+1) → ℝ) (x : U × V) :
    (∫ g, linearGaussian A g x * gordonWeight (fun y => linearGaussian C g y) x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) =
    ∫ g, ∑ i, A x i * (gordonWeight (fun y => linearGaussian C g y) x *
      (C x i-2*gordonRowMean (fun y => linearGaussian C g y) (fun y => C y i) x.2+
        gordonMean (fun y => linearGaussian C g y) (fun y => C y i)))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let H := fun g : Fin (d+1) → ℝ => fun y => linearGaussian C g y
  have hH (y : U × V) : Continuous (fun g => H g y) := by dsimp [H,linearGaussian]; fun_prop
  have hw : Measurable (fun g => gordonWeight (H g) x) := (continuous_gordonWeight H hH x).measurable
  have hd (i : Fin (d+1)) : Continuous (fun g => gordonWeight (H g) x *
      (C x i-2*gordonRowMean (H g) (fun y => C y i) x.2+gordonMean (H g) (fun y => C y i))) := by
    exact (continuous_gordonWeight H hH x).mul
      ((continuous_const.sub (continuous_const.mul
        (continuous_gordonRowMean H (fun _ y => C y i) hH (fun _ => continuous_const) x.2))).add
          (continuous_gordonMean H (fun _ y => C y i) hH (fun _ => continuous_const)))
  apply gaussian_pi_linear_insertion (A x) hw (fun i => (hd i).measurable)
  · intro i g t
    exact gordonWeight_hasDerivAt (fun y => hasDerivAt_linearGaussian_insert C i g y t) x
  · intro g
    rw [abs_of_nonneg (gordonWeight_nonneg (H g) x)]
    exact gordonWeight_le_one (H g) x
  · intro i g
    apply gordonWeight_derivative_bound (H g) (fun y => C y i) (∑ y, |C y i|)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    intro y
    exact Finset.single_le_sum (fun z _ => abs_nonneg (C z i)) (Finset.mem_univ y)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance contraction of the two-level Gaussian integration-by-parts identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Nonempty U] [Fintype V] [Nonempty V] in
lemma gordonRowMean_linear_sum {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ)
    (a : Fin d → ℝ) (v : V) :
    (∑ i, a i*gordonRowMean H (fun y => C y i) v) =
      ∑ u, gordonInner H u v*(∑ i, a i*C (u,v) i) := by
  simp only [gordonRowMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Nonempty U] [Nonempty V] in
lemma gordonMean_linear_sum {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ)
    (a : Fin d → ℝ) :
    (∑ i, a i*gordonMean H (fun y => C y i)) =
      ∑ y, gordonWeight H y*(∑ i, a i*C y i) := by
  simp only [gordonMean_eq_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Nonempty U] [Nonempty V] in
lemma gordon_covariance_contraction {d : ℕ} (H : U × V → ℝ)
    (A C : U × V → Fin d → ℝ) (x : U × V) :
    (∑ i, A x i*(gordonWeight H x*(C x i-2*gordonRowMean H (fun y => C y i) x.2+
      gordonMean H (fun y => C y i)))) =
    gordonWeight H x*(gaussianCross A C x x-
      2*(∑ u, gordonInner H u x.2*gaussianCross A C x (u,x.2))+
      ∑ y, gordonWeight H y*gaussianCross A C x y) := by
  calc
    _ = gordonWeight H x * ∑ i, (A x i*C x i-
        2*(A x i*gordonRowMean H (fun y => C y i) x.2)+
        A x i*gordonMean H (fun y => C y i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = gordonWeight H x*((∑ i, A x i*C x i)-
        2*(∑ i, A x i*gordonRowMean H (fun y => C y i) x.2)+
        ∑ i, A x i*gordonMean H (fun y => C y i)) := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    _ = _ := by rw [gordonRowMean_linear_sum,gordonMean_linear_sum]; rfl

theorem gordon_gaussian_covariance_insertion {d : ℕ} (A C : U × V → Fin (d+1) → ℝ)
    (x : U × V) :
    (∫ g, linearGaussian A g x*gordonWeight (fun y => linearGaussian C g y) x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) =
    ∫ g, gordonWeight (fun y => linearGaussian C g y) x*(gaussianCross A C x x-
      2*(∑ u, gordonInner (fun y => linearGaussian C g y) u x.2*gaussianCross A C x (u,x.2))+
      ∑ y, gordonWeight (fun y => linearGaussian C g y) y*gaussianCross A C x y)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  rw [gordon_gaussian_insertion]
  exact integral_congr_ae (ae_of_all _ (fun g => gordon_covariance_contraction _ A C x))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonSlopeSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sign of the Gaussian two-level Gibbs slope when row covariances agree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_gaussian_mean_nonpos {d : ℕ} (A C : U × V → Fin (d+1) → ℝ)
    (hrow : ∀ x u, gaussianCross A C x (u,x.2) = 0)
    (hoff : ∀ x y, gaussianCross A C x y ≤ 0) :
    (∫ g, gordonMean (fun y => linearGaussian C g y) (fun y => linearGaussian A g y)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤ 0 := by
  simp_rw [gordonMean_eq_sum]
  rw [integral_finsetSum _ (fun x _ => by
    simpa only [mul_comm] using integrable_gordon_linear A C x)]
  apply Finset.sum_nonpos
  intro x _
  simp only [mul_comm (gordonWeight _ x)]
  rw [gordon_gaussian_covariance_insertion]
  apply integral_nonpos
  intro g
  dsimp only
  have hd : gaussianCross A C x x = 0 := by simpa using hrow x x.1
  have hr : (∑ u, gordonInner (fun y => linearGaussian C g y) u x.2 *
      gaussianCross A C x (u,x.2)) = 0 := by simp only [hrow,mul_zero,Finset.sum_const_zero]
  rw [hd,hr,mul_zero,sub_zero,zero_add]
  apply mul_nonpos_of_nonneg_of_nonpos (gordonWeight_nonneg _ x)
  exact Finset.sum_nonpos (fun y _ =>
    mul_nonpos_of_nonneg_of_nonpos (gordonWeight_nonneg _ y) (hoff x y))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonCurveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation under the finite Gaussian minimum--maximum interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordonCurveMean_hasDerivAt {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (gordonCurveMean C A) (gordonCurveSlope C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let B := fun g : Fin d → ℝ => ∑ x, (|linearGaussian C g x|+|linearGaussian A g x|)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g =>
      gordonValue (fun x => linearGaussian (cavityGaussianCurve C A s) g x)) μ :=
    (continuous_gordonValue _ (fun x => by unfold linearGaussian; fun_prop)).aestronglyMeasurable
  have hi : Integrable (fun g =>
      gordonValue (fun x => linearGaussian (cavityGaussianCurve C A t) g x)) μ := by
    simpa only [zero_add] using integrable_gordonValue (fun _ => 0) (cavityGaussianCurve C A t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => gordonMean (fun x => linearGaussian (cavityGaussianCurve C A s) g x)
      (fun x => linearGaussian (cavityGaussianCurveDerivative C A s) g x))
    (bound := B) Filter.univ_mem (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · exact (continuous_gordonMean _ _
      (fun x => by unfold linearGaussian; fun_prop)
      (fun x => by unfold linearGaussian; fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    apply gordonMean_bound
    intro x
    exact (cavityGaussianCurveDerivative_bound C A s g x).trans
      (Finset.single_le_sum
        (f := fun x => |linearGaussian C g x|+|linearGaussian A g x|)
        (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ x))
  · exact integrable_finsetSum _ (fun x _ =>
      (integrable_linearGaussian C x).abs.add (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    exact gordonValue_hasDerivAt (fun x => cavityGaussianCurve_hasDerivAt C A s g x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian minimum--maximum comparison for matching row covariances. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem finite_gaussian_gordon_comparison {d : ℕ} (C A : U × V → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hrow : ∀ x u, gaussianCross A A x (u,x.2) = gaussianCross C C x (u,x.2))
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, gordonValue (fun x => linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, gordonValue (fun x => linearGaussian C g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := gordonCurveMean_hasDerivAt C A s
  have hs (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi/2)) :
      gordonCurveSlope C A s ≤ 0 := by
    have hsc : 0 ≤ Real.sin s*Real.cos s := mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,Real.pi_pos],hs.2⟩)
    apply gordon_gaussian_mean_nonpos
    · intro x u
      rw [cavityGaussianCurve_cross C A s x (u,x.2) hCA,hrow x u,sub_self,mul_zero]
    · intro x y
      rw [cavityGaussianCurve_cross C A s x y hCA]
      exact mul_nonpos_of_nonneg_of_nonpos hsc (sub_nonpos.mpr (hoff x y))
  have hm : AntitoneOn (gordonCurveMean C A) (Set.Icc (0 : ℝ) (Real.pi/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs'
    exact hs s (interior_subset hs')
  have hp : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have he := hm ⟨le_rfl,hp⟩ ⟨hp,le_rfl⟩ hp
  simpa only [gordonCurveMean,linearGaussian,cavityGaussianCurve,
    Real.cos_zero,Real.sin_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,
    one_mul,zero_mul,mul_zero,zero_add,add_zero] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMinmaxComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the finite entropy error from Gordon's Gaussian comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem finite_gaussian_minmax_comparison {d : ℕ} (C A : U × V → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hrow : ∀ x u, gaussianCross A A x (u,x.2) = gaussianCross C C x (u,x.2))
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, finiteMinmax (fun x => linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x => linearGaussian C g x)
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)
  let MA := ∫ g, finiteMinmax (fun x => linearGaussian A g x) ∂μ
  let MC := ∫ g, finiteMinmax (fun x => linearGaussian C g x) ∂μ
  let K := Real.log (Fintype.card V)+Real.log (Fintype.card U)
  have hbound (β : ℝ) (hβ : 0 < β) : β*MA-Real.log (Fintype.card V) ≤
      β*MC+Real.log (Fintype.card U) := by
    let LA := fun g => gordonValue (fun x => β*linearGaussian A g x)
    let LC := fun g => gordonValue (fun x => β*linearGaussian C g x)
    have hiA : Integrable LA μ := by
      simpa only [zero_add,linearGaussian_scale] using
        integrable_gordonValue (fun _ => 0) (fun x i => β*A x i)
    have hiC : Integrable LC μ := by
      simpa only [zero_add,linearGaussian_scale] using
        integrable_gordonValue (fun _ => 0) (fun x i => β*C x i)
    have hl : β*MA-Real.log (Fintype.card V) ≤ ∫ g, LA g ∂μ := by
      have hc : (∫ _ : Fin (d+1) → ℝ, Real.log (Fintype.card V) ∂μ) =
          Real.log (Fintype.card V) := by simp
      change β*(∫ g, finiteMinmax (fun x => linearGaussian A g x) ∂μ)-_ ≤ _
      rw [← integral_const_mul,← hc,
        ← integral_sub ((finiteMinmax_linear_integrable A).const_mul β) (integrable_const _)]
      exact integral_mono (((finiteMinmax_linear_integrable A).const_mul β).sub (integrable_const _))
        hiA (fun g => (gordonValue_finiteMinmax_bounds _ β hβ).1)
    have hu : (∫ g, LC g ∂μ) ≤ β*MC+Real.log (Fintype.card U) := by
      have hc : (∫ _ : Fin (d+1) → ℝ, Real.log (Fintype.card U) ∂μ) =
          Real.log (Fintype.card U) := by simp
      change _ ≤ β*(∫ g, finiteMinmax (fun x => linearGaussian C g x) ∂μ)+_
      rw [← integral_const_mul,← hc,
        ← integral_add ((finiteMinmax_linear_integrable C).const_mul β) (integrable_const _)]
      exact integral_mono hiC
        (((finiteMinmax_linear_integrable C).const_mul β).add (integrable_const _))
        (fun g => (gordonValue_finiteMinmax_bounds _ β hβ).2)
    have hm : (∫ g, LA g ∂μ) ≤ ∫ g, LC g ∂μ := by
      have h := finite_gaussian_gordon_comparison (fun x i => β*C x i) (fun x i => β*A x i)
        (fun x y => by rw [gaussianCross_scale_both,hCA x y,mul_zero])
        (fun x u => by rw [gaussianCross_scale_both,gaussianCross_scale_both,hrow x u])
        (fun x y => by
          rw [gaussianCross_scale_both,gaussianCross_scale_both]
          exact mul_le_mul_of_nonneg_left (hoff x y) (sq_nonneg β))
      simpa only [linearGaussian_scale] using h
    exact hl.trans (hm.trans hu)
  change MA ≤ MC
  by_contra h
  have hp : 0 < MA-MC := sub_pos.mpr (lt_of_not_ge h)
  let β := (|K|+1)/(MA-MC)
  have hβ : 0 < β := div_pos (by positivity) hp
  have he : β*(MA-MC) = |K|+1 := div_mul_cancel₀ _ hp.ne'
  have hh := hbound β hβ
  have hk := le_abs_self K
  dsimp only [K] at hk he
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_IndexedGaussianMinmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gordon comparison with an arbitrary finite Gaussian coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V ι : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V] [Fintype ι]

lemma indexedGaussianMinmax_integrable (C : U × V → ι → ℝ) :
    Integrable (fun g => finiteMinmax (fun x => ∑ i, C x i*g i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi (x : U × V) : Integrable (fun g : ι → ℝ => ∑ i, C x i*g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    integrable_finsetSum _ (fun i _ =>
      ((gaussianCoordinate_memLp i).integrable (by norm_num)).const_mul _)
  apply (integrable_finsetSum Finset.univ (fun x _ => (hi x).abs)).mono'
    (continuous_finiteMinmax _ (fun x => by fun_prop)).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  exact finiteMinmax_abs_le _ _ (fun x =>
    Finset.single_le_sum (fun y _ => abs_nonneg (∑ i, C y i*g i)) (Finset.mem_univ x))

lemma indexedGaussianMinmax_reindex {n : ℕ} (e : Fin n ≃ ι) (C : U × V → ι → ℝ) :
    (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ g, finiteMinmax (fun x => linearGaussian (fun x j => C x (e j)) g x)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp : MeasurePreserving E
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [← hp.hasLaw.integral_comp (continuous_finiteMinmax _ (fun x => by fun_prop)).aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  dsimp only [Function.comp_def]
  congr 1
  funext x
  have heq (i : ι) : E g i = g (e.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e g (e.symm i))
  simp only [heq]
  have hs := e.sum_comp (fun i => C x i*g (e.symm i))
  simpa only [linearGaussian,Equiv.symm_apply_apply] using hs.symm

theorem indexed_gaussian_minmax_comparison [Nonempty ι] (C A : U × V → ι → ℝ)
    (hCA : ∀ x y, (∑ i, C x i*A y i) = 0)
    (hrow : ∀ x u, (∑ i, A x i*A (u,x.2) i) = ∑ i, C x i*C (u,x.2) i)
    (hoff : ∀ x y, (∑ i, A x i*A y i) ≤ ∑ i, C x i*C y i) :
    (∫ g, finiteMinmax (fun x => ∑ i, A x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x => ∑ i, C x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let d := Fintype.card ι-1
  have hc : Fintype.card ι = d+1 := by
    have := Fintype.card_pos (α := ι)
    dsimp [d]
    omega
  let e : Fin (d+1) ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  rw [indexedGaussianMinmax_reindex e A,indexedGaussianMinmax_reindex e C]
  apply finite_gaussian_minmax_comparison
  · intro x y
    change (∑ j, C x (e j)*A y (e j)) = 0
    rw [e.sum_comp (fun i => C x i*A y i)]
    exact hCA x y
  · intro x u
    change (∑ j, A x (e j)*A (u,x.2) (e j)) = ∑ j, C x (e j)*C (u,x.2) (e j)
    rw [e.sum_comp (fun i => A x i*A (u,x.2) i),e.sum_comp (fun i => C x i*C (u,x.2) i)]
    exact hrow x u
  · intro x y
    change (∑ j, A x (e j)*A y (e j)) ≤ ∑ j, C x (e j)*C y (e j)
    rw [e.sum_comp (fun i => A x i*A y i),e.sum_comp (fun i => C x i*C y i)]
    exact hoff x y

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianMinmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gordon's finite rectangular Gaussian matrix comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem bilinear_gaussian_minmax_comparison {N m : ℕ}
    (u : U → EuclideanSpace ℝ (Fin N)) (v : V → EuclideanSpace ℝ (Fin m))
    (hu : ∀ a, ‖u a‖ = 1) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ g, finiteMinmax (fun x : U × V => ∑ i,
      bilinearVectorCoefficient (fun x : U × V => u x.1) (fun x => v x.2) x i*g i)
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x : U × V => ∑ i,
      bilinearMatrixCoefficient (fun x : U × V => u x.1) (fun x => v x.2) x i*g i)
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1) := by
  apply indexed_gaussian_minmax_comparison
  · intro x y
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,bilinearVectorCoefficient,
      mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  · intro x a
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
    ring
  · intro x y
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    have ha : ⟪u x.1,u y.1⟫ ≤ 1 := by
      simpa only [hu,mul_one] using real_inner_le_norm (u x.1) (u y.1)
    have hb : ⟪v x.2,v y.2⟫ ≤ 1 := by
      simpa only [hv,mul_one] using real_inner_le_norm (v x.2) (v y.2)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianMinmaxMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the auxiliary Gaussian scalar and bounding the comparison's vector term. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem bilinear_gaussian_minmax_mean {N m : ℕ}
    (u : U → EuclideanSpace ℝ (Fin N)) (v : V → EuclideanSpace ℝ (Fin m))
    (hu : ∀ a, ‖u a‖ = 1) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ g, indexedGaussianMaximum (fun a i => u a i) g
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1))-Real.sqrt m ≤
    ∫ g, finiteMinmax (fun x : U × V => ∑ ij : Fin N × Fin m, (u x.1 ij.1*v x.2 ij.2)*g ij)
      ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
  let e : Fin N × Fin m → BilinearGaussianIndex N m := fun ij => .inl (.inl ij)
  let eu : Fin N → BilinearGaussianIndex N m := fun i => .inr (.inl i)
  let ev : Fin m → BilinearGaussianIndex N m := fun j => .inr (.inr j)
  let D : U × V → (Fin N × Fin m) → ℝ := fun x ij => u x.1 ij.1*v x.2 ij.2
  let C := bilinearMatrixCoefficient (fun x : U × V => u x.1) (fun x => v x.2)
  let A := bilinearVectorCoefficient (fun x : U × V => u x.1) (fun x => v x.2)
  have hR := iidGaussian_restrict_hasLaw e (fun _ _ h => Sum.inl.inj (Sum.inl.inj h))
  have hRu := iidGaussian_restrict_hasLaw eu (fun _ _ h => Sum.inl.inj (Sum.inr.inj h))
  have hc : Integrable (fun g : BilinearGaussianIndex N m → ℝ => g (.inl (.inr ()))) μ :=
    (gaussianCoordinate_memLp _).integrable (by norm_num)
  have hzero : (∫ g : BilinearGaussianIndex N m → ℝ, g (.inl (.inr ())) ∂μ) = 0 := by
    simpa only [μ,integral_id_gaussianReal] using
      (measurePreserving_eval (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
        (.inl (.inr ()))).hasLaw.integral_eq
  have hmatrix (g : BilinearGaussianIndex N m → ℝ) :
      finiteMinmax (fun x => ∑ i, C x i*g i) =
        finiteMinmax (fun x => ∑ ij, D x ij*g (e ij)) + g (.inl (.inr ())) := by
    dsimp only [C]
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,zero_mul,
      one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
    exact finiteMinmax_add_constant _ _
  have hright : (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i) ∂μ) =
      ∫ g, finiteMinmax (fun x => ∑ ij, D x ij*g ij)
        ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
    simp_rw [hmatrix]
    change (∫ g, ((fun g => finiteMinmax (fun x => ∑ ij, D x ij*g ij)) ∘
      (fun g : BilinearGaussianIndex N m → ℝ => fun j => g (e j))) g+
      g (.inl (.inr ())) ∂μ) = _
    rw [integral_add (hR.integrable_comp (indexedGaussianMinmax_integrable D)) hc,hzero,add_zero]
    exact hR.integral_comp (indexedGaussianMinmax_integrable D).aestronglyMeasurable
  have himax : Integrable (fun g : BilinearGaussianIndex N m → ℝ =>
      indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i))) μ := by
    simpa only [Function.comp_def] using
      hRu.integrable_comp (indexedGaussianMaximum_integrable (fun a i => u a i))
  have hinorm := ((gaussianCoordinateVector_memLp ev).integrable (by norm_num)).norm
  have hleft : (∫ g, indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i)) ∂μ)-
      (∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ) ≤
      ∫ g, finiteMinmax (fun x => ∑ i, A x i*g i) ∂μ := by
    rw [← integral_sub himax hinorm]
    apply integral_mono (himax.sub hinorm) (indexedGaussianMinmax_integrable A)
    intro g
    obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => ∑ i, u a i*g (eu i))
    change (Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ i, u a i*g (eu i)))-_ ≤ _
    rw [he]
    apply Finset.le_inf'
    intro b _
    apply Finset.le_sup'_of_le _ (Finset.mem_univ a)
    have hb := abs_real_inner_le_norm (v b) (gaussianCoordinateVector ev g)
    rw [hv,one_mul] at hb
    have hl := neg_le_of_abs_le hb
    change -‖gaussianCoordinateVector ev g‖ ≤ _ at hl
    change (∑ i, u a i*g (eu i)) - ‖gaussianCoordinateVector ev g‖ ≤ ∑ i, A (a,b) i*g i
    dsimp only [A]
    simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,
      Finset.sum_const_zero,zero_add]
    have heq : ⟪v b,gaussianCoordinateVector ev g⟫ = ∑ j, v b j*g (ev j) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
        gaussianCoordinateVector,mul_comm]
    rw [heq] at hl
    dsimp only [eu,ev] at hl ⊢
    linarith
  have hmaxeq : (∫ g, indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i)) ∂μ) =
      ∫ g, indexedGaussianMaximum (fun a i => u a i) g
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    simpa only [Function.comp_def] using hRu.integral_comp
      (indexedGaussianMaximum_integrable (fun a i => u a i)).aestronglyMeasurable
  rw [hmaxeq] at hleft
  have hnorm : (∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ) ≤ Real.sqrt m := by
    simpa only [Fintype.card_fin] using gaussianCoordinateVector_norm_integral_le ev
  have hcomp := bilinear_gaussian_minmax_comparison u v hu hv
  change (∫ g, finiteMinmax (fun x => ∑ i, A x i*g i) ∂μ) ≤
    (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i) ∂μ) at hcomp
  rw [hright] at hcomp
  exact (sub_le_sub_left hnorm _).trans (hleft.trans hcomp)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianFiniteColumnMinimum
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the row tests to the full unit sphere in Gordon's matrix comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology
namespace InvariantIsing

lemma continuous_gaussianPattern_apply {N m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternEuclideanOperator z v) := by
  change Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
    WithLp.toLp 2 (fun i => ∑ j, z (i,j)*v j))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    (continuous_pi (fun i => by fun_prop))

theorem gaussian_finite_column_minimum {V : Type*} [Fintype V] [Nonempty V]
    {N m : ℕ} (hN : 0 < N) (v : V → EuclideanSpace ℝ (Fin m)) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ z : EuclideanSpace ℝ (Fin N), ‖z‖ ∂stdGaussian _)-Real.sqrt m ≤
    ∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      Finset.univ.inf' Finset.univ_nonempty (fun b => ‖gaussianPatternEuclideanOperator z (v b)‖)
      ∂stdGaussian _ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin N))) := unitVector_nonempty _
  let S := UnitVector (EuclideanSpace ℝ (Fin N))
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  let μ := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)
  let Z (g : (Fin N × Fin m) → ℝ) : EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 g
  let W (g : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 g
  let A (n : ℕ) (g : Fin N → ℝ) : ℝ :=
    indexedGaussianMaximum (fun i : Fin (n+1) => fun j => (s i).1 j) g
  let C (n : ℕ) (g : (Fin N × Fin m) → ℝ) : ℝ :=
    finiteMinmax (fun x : Fin (n+1) × V => ∑ ij, ((s x.1).1 ij.1*v x.2 ij.2)*g ij)
  let M (z : EuclideanSpace ℝ (Fin N × Fin m)) :=
    Finset.univ.inf' Finset.univ_nonempty (fun b => ‖gaussianPatternEuclideanOperator z (v b)‖)
  have hAlim (g : Fin N → ℝ) : Tendsto (fun n => A n g) atTop (𝓝 ‖W g‖) := by
    have he (n : ℕ) : A n g = prefixMaximum (fun i => ⟪(s i).1,W g⟫) n := by
      unfold A indexedGaussianMaximum prefixMaximum
      congr 1
      funext i
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,W,
        mul_comm]
    simp_rw [he]
    exact unitInner_prefix_tendsto s hs (W g)
  have hClim (g : (Fin N × Fin m) → ℝ) : Tendsto (fun n => C n g) atTop (𝓝 (M (Z g))) := by
    have he (n : ℕ) : C n g = Finset.univ.inf' Finset.univ_nonempty
        (fun b => prefixMaximum (fun i => ⟪(s i).1,gaussianPatternEuclideanOperator (Z g) (v b)⟫) n) := by
      unfold C finiteMinmax finiteRowMax prefixMaximum
      congr 1
      funext b
      congr 1
      funext i
      exact (gaussianPattern_unitBilinear (Z g) (s i).1 (v b)).symm
    simp_rw [he]
    exact Tendsto.finset_inf'_nhds_apply Finset.univ_nonempty
      (fun b _ => unitInner_prefix_tendsto s hs (gaussianPatternEuclideanOperator (Z g) (v b)))
  have hAbound (n : ℕ) (g : Fin N → ℝ) : |A n g| ≤ ‖W g‖ := by
    obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n+1) => ∑ j, (s i).1 j*g j)
    change |Finset.univ.sup' Finset.univ_nonempty _| ≤ _
    rw [he]
    have h := abs_real_inner_le_norm (s i).1 (W g)
    rw [(s i).2,one_mul] at h
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,W,
      PiLp.toLp_apply,mul_comm] using h
  have hCbound (n : ℕ) (g : (Fin N × Fin m) → ℝ) : |C n g| ≤ ‖Z g‖ := by
    apply finiteMinmax_abs_le
    intro x
    rw [← gaussianPattern_unitBilinear (Z g) (s x.1).1 (v x.2)]
    calc
      _ ≤ ‖(s x.1).1‖*‖gaussianPatternEuclideanOperator (Z g) (v x.2)‖ := abs_real_inner_le_norm _ _
      _ = ‖gaussianPatternEuclideanOperator (Z g) (v x.2)‖ := by rw [(s x.1).2,one_mul]
      _ ≤ ‖gaussianPatternEuclideanOperator (Z g)‖*‖v x.2‖ :=
        (gaussianPatternEuclideanOperator (Z g)).le_opNorm _
      _ ≤ ‖Z g‖ := by rw [hv,mul_one]; exact gaussianPatternEuclideanOperator_norm_le _
  have hAint := tendsto_integral_of_dominated_convergence (μ := μ) (fun g => ‖W g‖)
    (fun n => (measurable_indexedGaussianMaximum _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : Fin N → Fin N)).integrable (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hAbound n g))
    (ae_of_all _ hAlim)
  have hCint := tendsto_integral_of_dominated_convergence (μ := ν) (fun g => ‖Z g‖)
    (fun n => (indexedGaussianMinmax_integrable _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : (Fin N × Fin m) → (Fin N × Fin m))).integrable
      (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hCbound n g))
    (ae_of_all _ hClim)
  have hbound (n : ℕ) : (∫ g, A n g ∂μ)-Real.sqrt m ≤ ∫ g, C n g ∂ν :=
    bilinear_gaussian_minmax_mean (fun i : Fin (n+1) => (s i).1) v (fun i => (s i).2) hv
  have hh := le_of_tendsto_of_tendsto (hAint.sub_const (Real.sqrt m)) hCint
    (Filter.Eventually.of_forall hbound)
  have hW : HasLaw W (stdGaussian _) μ :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hZ : HasLaw Z (stdGaussian _) ν :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  have heW : (∫ g, ‖W g‖ ∂μ) = ∫ z : EuclideanSpace ℝ (Fin N), ‖z‖ ∂stdGaussian _ := by
    simpa only [Function.comp_def] using hW.integral_comp (f := norm) (by fun_prop)
  have heZ : (∫ g, M (Z g) ∂ν) = ∫ z, M z ∂stdGaussian _ := by
    have hM : Continuous M := Continuous.finset_inf'_apply Finset.univ_nonempty
      (fun b _ => (continuous_gaussianPattern_apply (v b)).norm)
    simpa only [Function.comp_def] using hZ.integral_comp hM.aestronglyMeasurable
  rw [heW,heZ] at hh
  exact hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternAspect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual integer Gaussian pattern counts and their aspect-ratio limits. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternCount_le {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    (gaussianPatternCount α N : ℝ) ≤ α*N := by
  unfold gaussianPatternCount
  exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))

lemma gaussianPatternCount_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => (gaussianPatternCount α (k+1) : ℝ)/(k+1)) atTop (𝓝 α) := by
  have he (k : ℕ) : 0 ≤ α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ∧
      α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ≤ 1/(k+1) := by
    have hk : (0 : ℝ) < k+1 := by positivity
    have hl := gaussianPatternCount_le hα (k+1)
    have hu : α*(k+1) < (gaussianPatternCount α (k+1) : ℝ)+1 := by
      simpa only [gaussianPatternCount,Nat.cast_add,Nat.cast_one] using
        Nat.lt_floor_add_one (α*(k+1 : ℝ))
    have hr : α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) =
        (α*(k+1)-(gaussianPatternCount α (k+1) : ℝ))/(k+1) := by field_simp
    rw [hr]
    constructor
    · apply div_nonneg _ hk.le
      simpa only [Nat.cast_add,Nat.cast_one] using sub_nonneg.mpr hl
    · apply div_le_div_of_nonneg_right _ hk.le
      linarith
  have ht := squeeze_zero (fun k => (he k).1) (fun k => (he k).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (tendsto_const_nhds (x := α)).sub ht
  simpa only [sub_zero,sub_sub_cancel] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSingularLowerMean
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian least singular value has the sharp asymptotic lower mean bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

theorem gaussianPatternSingularMin_mean_ge {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    Real.sqrt ((N : ℝ)-1)-Real.sqrt m ≤
      ∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMin z ∂stdGaussian _ := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1
  let : Nonempty S := by
    obtain ⟨x⟩ := unitVector_nonempty (EuclideanSpace ℝ (Fin m))
    exact ⟨⟨x.1,by simpa only [S,Metric.mem_sphere,dist_zero_right] using x.2⟩⟩
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  have hn (i : ℕ) : ‖(s i).1‖ = 1 := by
    simpa only [S,Metric.mem_sphere,dist_zero_right] using (s i).2
  let F (n : ℕ) (z : EuclideanSpace ℝ (Fin N × Fin m)) :=
    prefixMinimum (fun i => ‖gaussianPatternEuclideanOperator z (s i).1‖) n
  have hlim (z : EuclideanSpace ℝ (Fin N × Fin m)) :
      Tendsto (fun n => F n z) atTop (𝓝 (gaussianPatternSingularMin z)) := by
    exact dense_prefixMinimum_tendsto s hs (fun x => ‖gaussianPatternEuclideanOperator z x.1‖)
      (by fun_prop) ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hbound (n : ℕ) (z : EuclideanSpace ℝ (Fin N × Fin m)) : |F n z| ≤ ‖z‖ := by
    obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin (n+1) => ‖gaussianPatternEuclideanOperator z (s i).1‖)
    change |Finset.univ.inf' Finset.univ_nonempty _| ≤ _
    rw [he,abs_of_nonneg (norm_nonneg _)]
    have h := gaussianPatternEuclideanOperator_bound z (s i).1
    simpa only [hn,mul_one] using h
  have hint := tendsto_integral_of_dominated_convergence (μ := stdGaussian _) norm
    (fun n => (show Continuous (F n) from
      Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ =>
        (continuous_gaussianPattern_apply (s i).1).norm)).aestronglyMeasurable)
    ((finiteGaussian_lipschitz_memLp_two
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : EuclideanSpace ℝ (Fin N × Fin m) → ℝ))).integrable
      (by norm_num))
    (fun n => ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbound n z))
    (ae_of_all _ hlim)
  have hb (n : ℕ) : Real.sqrt ((N : ℝ)-1)-Real.sqrt m ≤ ∫ z, F n z ∂stdGaussian _ := by
    have hc := gaussian_finite_column_minimum hN (fun i : Fin (n+1) => (s i).1)
      (fun i => hn i)
    have hl := gaussianNorm_lower_mean (ι := Fin N)
    simp only [Fintype.card_fin] at hl
    exact (sub_le_sub_right hl (Real.sqrt m)).trans hc
  exact ge_of_tendsto hint (Filter.Eventually.of_forall hb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTranspose
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transposition preserves the actual standard Gaussian array law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma gaussianPatternTranspose_hasLaw {N m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : HasLaw Z (stdGaussian _) P) :
    HasLaw (fun ω => gaussianPatternTranspose N m (Z ω)) (stdGaussian _) P := by
  have hT : HasLaw (gaussianPatternTranspose N m)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin N)))
      (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) :=
    ⟨(gaussianPatternTranspose N m).continuous.measurable.aemeasurable,
      stdGaussian_map (gaussianPatternTranspose N m)⟩
  exact hT.comp hZ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTransposeLowerEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower singular edge of the transposed physical Gaussian array. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternCount_sub_one_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => ((gaussianPatternCount α (k+1) : ℝ)-1)/(k+1)) atTop (𝓝 α) := by
  have h := (gaussianPatternCount_ratio_tendsto hα).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_zero,sub_div] using h

theorem gaussianPatternTranspose_lower_edge_oai {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => max (Real.sqrt α-1-
      gaussianPatternSingularMin (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1))
        (Z (k+1) ω))/Real.sqrt (k+1)) 0) atTop (fun _ => 0) := by
  let T (k : ℕ) (ω : Ω) :=
    gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1)) (Z (k+1) ω)
  let M (k : ℕ) := ∫ z : EuclideanSpace ℝ (Fin (gaussianPatternCount α (k+1)) × Fin (k+1)),
    gaussianPatternSingularMin z ∂stdGaussian _
  let B (k : ℕ) := Real.sqrt (((gaussianPatternCount α (k+1) : ℝ)-1)/(k+1))-1
  have hB : Tendsto B atTop (𝓝 (Real.sqrt α-1)) :=
    ((Real.continuous_sqrt.tendsto α).comp (gaussianPatternCount_sub_one_ratio_tendsto hα.le)).sub_const 1
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < gaussianPatternCount α (k+1) := by
    filter_upwards [(tendsto_order.1 (gaussianPatternCount_ratio_tendsto hα.le)).1 0 hα] with k hk
    have hp : (0 : ℝ) < (gaussianPatternCount α (k+1) : ℝ) :=
      (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < k+1)).mp hk
    exact_mod_cast hp
  have hM : ∀ᶠ k : ℕ in atTop, B k ≤ M k/Real.sqrt (k+1) := by
    filter_upwards [hpos] with k hk
    have hh := gaussianPatternSingularMin_mean_ge hk (Nat.succ_pos k)
    have hs : 0 < Real.sqrt (k+1 : ℝ) := by positivity
    have hc : (0 : ℝ) ≤ (gaussianPatternCount α (k+1) : ℝ)-1 := by
      have hc' : (1 : ℝ) ≤ (gaussianPatternCount α (k+1) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hk)
      linarith
    have hd := div_le_div_of_nonneg_right hh hs.le
    dsimp only [B,M]
    rw [Real.sqrt_div hc]
    simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_one,sub_div,div_self hs.ne'] using hd
  have hT (k : ℕ) : HasLaw (T k) (stdGaussian _) P := gaussianPatternTranspose_hasLaw P _ (hZ (k+1))
  have hcent := finiteGaussian_centered_tendsto (fun k =>
      gaussianPatternSingularMin (N := gaussianPatternCount α (k+1)) (m := k+1))
    (fun k => gaussianPatternSingularMin_lipschitz _ _ (Nat.succ_pos k)) P T hT
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => max (Real.sqrt α-1-gaussianPatternSingularMin (T k ω)/Real.sqrt (k+1)) 0) P := by
    have h : Measurable (fun z : EuclideanSpace ℝ
        (Fin (gaussianPatternCount α (k+1)) × Fin (k+1)) =>
        max (Real.sqrt α-1-gaussianPatternSingularMin z/Real.sqrt (k+1)) 0) := by
      have hc := (gaussianPatternSingularMin_lipschitz (gaussianPatternCount α (k+1)) (k+1)
        (Nat.succ_pos k)).continuous
      fun_prop
    exact (h.aemeasurable.comp_aemeasurable (hT k).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hcu⟩ := (hcent.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [hcu] with ω hω
  have hc : Tendsto (fun k => (gaussianPatternSingularMin (T (ns (u k)) ω)-M (ns (u k)))/
      Real.sqrt (ns (u k)+1)) atTop (𝓝 0) := hω
  have hb := hB.comp (hns.comp hu).tendsto_atTop
  have ht := ((hc.neg.add (tendsto_const_nhds (x := Real.sqrt α-1))).sub hb).max
    (tendsto_const_nhds (x := (0 : ℝ)))
  have ht' : Tendsto (fun k => max
      (-(gaussianPatternSingularMin (T (ns (u k)) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1) +
        (Real.sqrt α-1)-B (ns (u k))) 0) atTop (𝓝 0) := by
    simpa only [neg_zero,zero_add,sub_self,max_self,neg_div,Function.comp_def] using ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => le_max_right _ _)) _ ht'
  filter_upwards [(hns.comp hu).tendsto_atTop.eventually hM] with k hk
  dsimp only [Function.comp_def] at hk
  apply max_le_max _ le_rfl
  rw [neg_div,sub_div]
  linarith

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.gaussianPatternTranspose_lower_edge_oai.{u_1} := @OAI.InvariantIsing.gaussianPatternTranspose_lower_edge_oai.{u_1}
