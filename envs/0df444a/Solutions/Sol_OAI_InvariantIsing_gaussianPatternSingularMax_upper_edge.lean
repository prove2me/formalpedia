-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:25.155788+00:00
-- url     : https://prove2.me/submissions/2e0c9a3d-bc2b-4cf6-81ba-c717389af973

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
import Theorems.Thm_OAI_InvariantIsing_finiteGaussian_centered_tendsto

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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma continuous_gaussianGibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (x : S) :
    Continuous (fun g => gaussianGibbs w B C g x) := by
  unfold gaussianGibbs finiteGibbs
  apply Continuous.div
  · unfold linearGaussian; fun_prop
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

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

lemma hasDerivAt_gaussianGibbs_insert {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => gaussianGibbs w B C (i.insertNth y g) x)
      (gaussianGibbs w B C (i.insertNth t g) x *
        (C x i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i)) t := by
  apply hasDerivAt_finiteGibbs hw
  intro z
  exact (hasDerivAt_linearGaussian_insert C i g z t).const_add (B z)

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

lemma replicaGibbs_nonneg {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    0 ≤ replicaGibbs w B C g σ :=
  Finset.prod_nonneg (fun l _ => finiteGibbs_nonneg hw _ (σ l))

lemma replicaGibbs_le_one {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    replicaGibbs w B C g σ ≤ 1 := by
  exact Finset.prod_le_one (fun replica _ => finiteGibbs_nonneg hw _ (σ replica))
    (fun l _ => finiteGibbs_le_one hw _ (σ l))

lemma continuous_replicaGibbs {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (σ : Fin r → S) :
    Continuous (fun g => replicaGibbs w B C g σ) := by
  exact continuous_finsetProd _ (fun l _ => continuous_gaussianGibbs hw B C (σ l))

lemma hasDerivAt_replicaGibbs_insert {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (σ : Fin r → S) (t : ℝ) :
    HasDerivAt (fun y => replicaGibbs w B C (i.insertNth y g) σ)
      (replicaGibbs w B C (i.insertNth t g) σ *
        (∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i))) t := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun l _ => hasDerivAt_gaussianGibbs_insert hw B C i g (σ l) t)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← mul_assoc, Finset.prod_erase_mul _ _ hl]
  rfl

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

lemma gaussian_replica_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) (σ : Fin r → S) :
    (∫ g, linearGaussian A g x * replicaGibbs w B C g σ
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, replicaGibbs w B C g σ *
      (∑ l, (gaussianCross A C x (σ l) -
        ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hd := gaussian_pi_linear_insertion (A x) (continuous_replicaGibbs hw B C σ).measurable
    (F' := fun i g => replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i))
    (fun i => ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).measurable)
    (fun i g t => hasDerivAt_replicaGibbs_insert hw B C i g σ t)
    (K := 1) (K' := fun i => ∑ l, (|C (σ l) i| + ∑ z, |C z i|))
    (fun g => by rw [abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)];
                 exact replicaGibbs_le_one hw B C g σ)
  have hb i g : |replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i)| ≤
      ∑ l, (|C (σ l) i| + ∑ z, |C z i|) := by
    rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    apply (mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)).trans
    rw [one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro l _
    exact (abs_sub _ _).trans (add_le_add le_rfl
      (finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
        (fun z => C z i) (fun z => Finset.single_le_sum (fun y _ => abs_nonneg (C y i))
          (Finset.mem_univ z))))
  rw [show linearGaussian A = fun g x => ∑ i, A x i * g i from rfl, hd hb]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [gaussianCross, Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    ring

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

lemma log_finitePartition_lipschitz {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, |H x - J x| ≤ K) :
    |Real.log (finitePartition w H) - Real.log (finitePartition w J)| ≤ K := by
  apply abs_le.mpr
  constructor
  · have hh := log_finitePartition_le_add hw (H := J) (J := H) (K := K)
      (fun x => by have := (abs_le.mp (h x)).1; linarith)
    linarith
  · have hh := log_finitePartition_le_add hw (H := H) (J := J) (K := K)
      (fun x => by have := (abs_le.mp (h x)).2; linarith)
    linarith

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

lemma continuous_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Continuous (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x))) := by
  apply Continuous.log
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

lemma integrable_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Integrable (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi : Integrable (fun g => |Real.log (finitePartition w B)| +
      |t| * ∑ x, |linearGaussian A g x|)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (integrable_const _).add ((integrable_finsetSum _
      (fun x _ => (integrable_linearGaussian A x).abs)).const_mul _)
  apply hi.mono' (continuous_log_finitePartition hw B A t).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  have hh := log_finitePartition_lipschitz hw (H := fun x => B x + t * linearGaussian A g x)
    (J := B) (K := |t| * ∑ x, |linearGaussian A g x|) (fun x => by
      simp only [add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
        (abs_nonneg t))
  have := abs_le.mp hh
  have hz := abs_le.mp (le_refl |Real.log (finitePartition w B)|)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype S] in
lemma linearGaussian_scale {n : ℕ} (A : S → Fin n → ℝ) (t : ℝ) (g : Fin n → ℝ) (x : S) :
    linearGaussian (fun y i => t * A y i) g x = t * linearGaussian A g x := by
  simp only [linearGaussian, Finset.mul_sum, mul_assoc]

lemma gaussian_gibbs_insertion {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) :
    (∫ g, linearGaussian A g x * gaussianGibbs w B C g x
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, gaussianGibbs w B C g x *
      (gaussianCross A C x x - ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  simpa [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
    gaussian_replica_insertion (r := 1) hw B A C x (fun _ => x)

lemma integrable_linearGaussian_mul_gibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x y : S) :
    Integrable (fun g => linearGaussian A g x * gaussianGibbs w B C g y)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_gaussianGibbs hw B C y).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianGibbs w B C g y from finiteGibbs_nonneg hw _ y)]
  exact finiteGibbs_le_one hw _ y

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

lemma cavityPenaltyCurve_hasDerivAt {X : Type*} (H V : X → ℝ) (c t : ℝ) (x : X) :
    HasDerivAt (fun s => cavityPenaltyCurve H V c s x)
      (4 * c * Real.sin t * Real.cos t * V x) t := by
  have h := (hasDerivAt_const t (H x)).sub
    ((((Real.hasDerivAt_cos t).pow 2).const_mul (2 * c)).mul_const (V x))
  change HasDerivAt (fun s => H x - 2 * c * Real.cos s ^ 2 * V x) _ t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianCurveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the finite Gaussian interpolation while removing the
nonuniform cavity penalty. The derivative is nonnegative under the
pointwise covariance-error bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

omit [Fintype X] in
lemma cavityPenaltyCurve_derivative_bound (V : X → ℝ) (c t : ℝ) (x : X) :
    |4 * c * Real.sin t * Real.cos t * V x| ≤ 4 * |c| * |V x| := by
  have hsc : |Real.sin t| * |Real.cos t| ≤ 1 := by
    exact (mul_le_mul (Real.abs_sin_le_one t) (Real.abs_cos_le_one t)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  calc
    _ = (4 * |c| * |V x|) * (|Real.sin t| * |Real.cos t|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      ring
    _ ≤ (4 * |c| * |V x|) * 1 := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = _ := mul_one _

lemma cavityGaussianCurveMean_hasDerivAt {d : ℕ} {w : X → ℝ}
    (hw : GibbsReference w) (H V : X → ℝ) (c : ℝ) (C A : X → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (cavityGaussianCurveMean w H V c C A)
      (cavityGaussianCurveSlope w H V c C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let B := fun g : Fin d → ℝ => ∑ x,
    (4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c s x + linearGaussian (cavityGaussianCurve C A s) g x))) μ := by
    simpa only [one_mul] using
      (continuous_log_finitePartition hw (cavityPenaltyCurve H V c s)
        (cavityGaussianCurve C A s) 1).aestronglyMeasurable
  have hi : Integrable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c t x + linearGaussian (cavityGaussianCurve C A t) g x))) μ := by
    simpa only [one_mul] using
      integrable_log_finitePartition hw (cavityPenaltyCurve H V c t) (cavityGaussianCurve C A t) 1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x,
      gaussianGibbs w (cavityPenaltyCurve H V c s) (cavityGaussianCurve C A s) g x *
      (4 * c * Real.sin s * Real.cos s * V x + linearGaussian (cavityGaussianCurveDerivative C A s) g x))
    (bound := B) Filter.univ_mem (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro x _
    exact (continuous_gaussianGibbs hw _ _ x).mul
      (continuous_const.add (by unfold linearGaussian; fun_prop))
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    apply finiteGibbs_average_bound hw
    intro x
    calc
      _ ≤ |4 * c * Real.sin s * Real.cos s * V x| +
          |linearGaussian (cavityGaussianCurveDerivative C A s) g x| := abs_add_le _ _
      _ ≤ 4 * |c| * |V x| + (|linearGaussian C g x| + |linearGaussian A g x|) :=
        add_le_add (cavityPenaltyCurve_derivative_bound V c s x)
          (cavityGaussianCurveDerivative_bound C A s g x)
      _ ≤ B g := by
        simpa only [B, add_assoc] using Finset.single_le_sum
          (f := fun x => 4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
          (fun _ _ => by positivity) (Finset.mem_univ x)
  · exact integrable_finsetSum _ (fun x _ =>
      ((integrable_const _).add (integrable_linearGaussian C x).abs).add
        (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    apply hasDerivAt_log_finitePartition hw
    intro x
    exact (cavityPenaltyCurve_hasDerivAt H V c s x).add (cavityGaussianCurve_hasDerivAt C A s g x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianComparisonSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance order gives the finite Gaussian log-partition comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X]

lemma gaussian_gibbs_linear_mean_nonneg {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (A C : X → Fin (d+1) → ℝ)
    (hK : ∀ x y, gaussianCross A C x y ≤ gaussianCross A C x x) :
    0 ≤ ∫ g, ∑ x, gaussianGibbs w H C g x * linearGaussian A g x
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hi x : Integrable (fun g => gaussianGibbs w H C g x * linearGaussian A g x)
      (Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) := by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x
  rw [integral_finsetSum _ (fun x _ => hi x)]
  apply Finset.sum_nonneg
  intro x _
  have he := gaussian_gibbs_insertion hw H A C x
  simp only [mul_comm (gaussianGibbs w H C _ x)]
  rw [he]
  apply integral_nonneg
  intro g
  apply mul_nonneg (finiteGibbs_nonneg hw _ x)
  apply sub_nonneg.mpr
  calc
    _ ≤ ∑ y, gaussianGibbs w H C g y * gaussianCross A C x x := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hK x y) (finiteGibbs_nonneg hw _ y)
    _ = gaussianCross A C x x := by
      rw [← Finset.sum_mul]
      change (∑ y, finiteGibbs w _ y) * _ = _
      rw [finiteGibbs_sum hw,one_mul]

theorem finite_gaussian_log_comparison {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hdiag : ∀ x, gaussianCross A A x x = gaussianCross C C x x)
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, Real.log (finitePartition w (fun x => H x+linearGaussian C g x))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
    ∫ g, Real.log (finitePartition w (fun x => H x+linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := cavityGaussianCurveMean_hasDerivAt hw H (fun _ => 0) 0 C A s
  have hs (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi/2)) :
      0 ≤ cavityGaussianCurveSlope w H (fun _ => 0) 0 C A s := by
    have hsc : 0 ≤ Real.sin s * Real.cos s := mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,Real.pi_pos],hs.2⟩)
    have hcross : ∀ x y,
        gaussianCross (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s) x y ≤
        gaussianCross (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s) x x := by
      intro x y
      rw [cavityGaussianCurve_cross C A s x y hCA,cavityGaussianCurve_cross C A s x x hCA,
        hdiag x,sub_self,mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hsc (sub_nonpos.mpr (hoff x y))
    have h := gaussian_gibbs_linear_mean_nonneg hw H (cavityGaussianCurveDerivative C A s)
      (cavityGaussianCurve C A s) hcross
    have hp : cavityPenaltyCurve H (fun _ => 0) 0 s = H := by
      funext x
      simp only [cavityPenaltyCurve,mul_zero,zero_mul,sub_zero]
    simpa only [cavityGaussianCurveSlope,hp,zero_mul,mul_zero,zero_add] using h
  have hm : MonotoneOn (cavityGaussianCurveMean w H (fun _ => 0) 0 C A)
      (Set.Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs'
    exact hs s (interior_subset hs')
  have hp : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have he := hm ⟨le_rfl,hp⟩ ⟨hp,le_rfl⟩ hp
  simpa only [cavityGaussianCurveMean,cavityPenaltyCurve,linearGaussian,cavityGaussianCurve,
    Real.cos_zero,Real.sin_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,
    one_mul,zero_mul,mul_zero,sub_zero,zero_add,add_zero] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteGaussianMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian maxima and their log-sum-exp approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X]

lemma finiteGaussianMaximum_integrable {d : ℕ} (C : X → Fin d → ℝ) :
    Integrable (finiteGaussianMaximum C) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (finiteGaussianMaximum C) := by
    have hc := Finset.measurable_sup' (s := (Finset.univ : Finset X)) Finset.univ_nonempty
      (fun x _ => show Measurable (fun g => linearGaussian C g x) from by unfold linearGaussian; fun_prop)
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    funext g
    rw [Finset.sup'_apply]
    rfl
  apply (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => linearGaussian C g x)
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [he,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) hx

lemma finiteGaussianMaximum_log_bounds {d : ℕ} (C : X → Fin d → ℝ)
    (g : Fin d → ℝ) (β : ℝ) (hβ : 0 < β) :
    β * finiteGaussianMaximum C g ≤
        Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x)) ∧
    Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x)) ≤
      β * finiteGaussianMaximum C g + Real.log (Fintype.card X) := by
  have hw : GibbsReference (fun _ : X => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one,⟨Classical.choice ‹Nonempty X›,zero_lt_one⟩⟩
  constructor
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => linearGaussian C g x)
    have hs : Real.exp (β * finiteGaussianMaximum C g) ≤
        finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x) := by
      unfold finiteGaussianMaximum
      rw [he]
      simpa only [finitePartition,one_mul] using
        Finset.single_le_sum (fun y _ => (Real.exp_pos (β*linearGaussian C g y)).le) hx
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hs
  · have hb (x : X) : β*linearGaussian C g x ≤ 0+β*finiteGaussianMaximum C g := by
      simpa only [zero_add,finiteGaussianMaximum] using mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun x => linearGaussian C g x) (Finset.mem_univ x)) hβ.le
    have he := log_finitePartition_le_add hw hb
    simpa only [finitePartition,Real.exp_zero,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_one,add_comm] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_DenseFiniteMaximum
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

theorem gaussianPatternSingularMax_lipschitz (N m : ℕ) :
    LipschitzWith 1 (gaussianPatternSingularMax (N := N) (m := m)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,gaussianPatternSingularMax]
  calc
    _ ≤ ‖gaussianPatternEuclideanOperator z-gaussianPatternEuclideanOperator w‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖gaussianPatternEuclideanOperator (z-w)‖ := by rw [gaussianPatternEuclideanOperator_sub]
    _ ≤ ‖z-w‖ := gaussianPatternEuclideanOperator_norm_le _

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

theorem finite_gaussian_maximum_comparison {d : ℕ} (C A : X → Fin (d+1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hdiag : ∀ x, gaussianCross A A x x = gaussianCross C C x x)
    (hoff : ∀ x y, gaussianCross A A x y ≤ gaussianCross C C x y) :
    (∫ g, finiteGaussianMaximum C g ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) ≤
      ∫ g, finiteGaussianMaximum A g ∂Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)
  let MC := ∫ g, finiteGaussianMaximum C g ∂μ
  let MA := ∫ g, finiteGaussianMaximum A g ∂μ
  let K := Real.log (Fintype.card X)
  have hw : GibbsReference (fun _ : X => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one,⟨Classical.choice ‹Nonempty X›,zero_lt_one⟩⟩
  have hbound (β : ℝ) (hβ : 0 < β) : β*MC ≤ β*MA+K := by
    let LC := fun g : Fin (d+1) → ℝ =>
      Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x))
    let LA := fun g : Fin (d+1) → ℝ =>
      Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian A g x))
    have hiC : Integrable LC μ := by
      simpa only [zero_add] using integrable_log_finitePartition hw (fun _ => 0) C β
    have hiA : Integrable LA μ := by
      simpa only [zero_add] using integrable_log_finitePartition hw (fun _ => 0) A β
    have hlow : β*MC ≤ ∫ g, LC g ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono ((finiteGaussianMaximum_integrable C).const_mul β) hiC
        (fun g => (finiteGaussianMaximum_log_bounds C g β hβ).1)
    have hupp : (∫ g, LA g ∂μ) ≤ β*MA+K := by
      have hconst : (∫ _ : Fin (d+1) → ℝ, K ∂μ) = K := by simp
      rw [← integral_const_mul,← hconst,← integral_add]
      · exact integral_mono hiA (((finiteGaussianMaximum_integrable A).const_mul β).add (integrable_const K))
          (fun g => (finiteGaussianMaximum_log_bounds A g β hβ).2)
      · exact (finiteGaussianMaximum_integrable A).const_mul β
      · exact integrable_const K
    have hmid : (∫ g, LC g ∂μ) ≤ ∫ g, LA g ∂μ := by
      have h := finite_gaussian_log_comparison hw (fun _ => 0)
        (fun x i => β*C x i) (fun x i => β*A x i)
        (fun x y => by rw [gaussianCross_scale_both,hCA x y,mul_zero])
        (fun x => by rw [gaussianCross_scale_both,gaussianCross_scale_both,hdiag x])
        (fun x y => by
          rw [gaussianCross_scale_both,gaussianCross_scale_both]
          exact mul_le_mul_of_nonneg_left (hoff x y) (sq_nonneg β))
      simpa only [linearGaussian_scale,zero_add] using h
    exact hlow.trans (hmid.trans hupp)
  change MC ≤ MA
  by_contra h
  have hpos : 0 < MC-MA := sub_pos.mpr (lt_of_not_ge h)
  let β := (|K|+1)/(MC-MA)
  have hβ : 0 < β := div_pos (by positivity) hpos
  have he : β*(MC-MA) = |K|+1 := div_mul_cancel₀ _ hpos.ne'
  have hh := hbound β hβ
  have hk := le_abs_self K
  nlinarith

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

lemma indexedGaussianMaximum_reindex {n : ℕ} (e : Fin n ≃ ι) (C : X → ι → ℝ) :
    (∫ g, indexedGaussianMaximum C g ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ g, finiteGaussianMaximum (fun x j => C x (e j)) g
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp : MeasurePreserving E
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [← hp.hasLaw.integral_comp (measurable_indexedGaussianMaximum C).aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  unfold indexedGaussianMaximum finiteGaussianMaximum
  dsimp only [Function.comp_def]
  congr 1
  funext x
  have heq (i : ι) : E g i = g (e.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ι => ℝ) e g (e.symm i))
  simp only [heq]
  have hs := e.sum_comp (fun i => C x i*g (e.symm i))
  simpa only [linearGaussian,Equiv.symm_apply_apply] using hs.symm

theorem indexed_gaussian_maximum_comparison [Nonempty ι] (C A : X → ι → ℝ)
    (hCA : ∀ x y, (∑ i, C x i*A y i) = 0)
    (hdiag : ∀ x, (∑ i, A x i*A x i) = ∑ i, C x i*C x i)
    (hoff : ∀ x y, (∑ i, A x i*A y i) ≤ ∑ i, C x i*C y i) :
    (∫ g, indexedGaussianMaximum C g ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
    ∫ g, indexedGaussianMaximum A g ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let d := Fintype.card ι-1
  have hc : Fintype.card ι = d+1 := by
    have := Fintype.card_pos (α := ι)
    dsimp [d]
    omega
  let e : Fin (d+1) ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  rw [indexedGaussianMaximum_reindex e C,indexedGaussianMaximum_reindex e A]
  apply finite_gaussian_maximum_comparison
  · intro x y
    change (∑ j, C x (e j)*A y (e j)) = 0
    rw [e.sum_comp (fun i => C x i*A y i)]
    exact hCA x y
  · intro x
    change (∑ j, A x (e j)*A x (e j)) = ∑ j, C x (e j)*C x (e j)
    rw [e.sum_comp (fun i => A x i*A x i),e.sum_comp (fun i => C x i*C x i)]
    exact hdiag x
  · intro x y
    change (∑ j, A x (e j)*A y (e j)) ≤ ∑ j, C x (e j)*C y (e j)
    rw [e.sum_comp (fun i => A x i*A y i),e.sum_comp (fun i => C x i*C y i)]
    exact hoff x y

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

theorem bilinear_gaussian_maximum_comparison {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1) :
    (∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)) ≤
    ∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g
      ∂Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1) := by
  apply indexed_gaussian_maximum_comparison
  · intro x y
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,bilinearVectorCoefficient,
      mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  · intro x
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    simp only [real_inner_self_eq_norm_sq,hu,hv,one_pow,one_mul]
  · intro x y
    rw [bilinearVector_covariance,bilinearMatrix_covariance]
    have ha : ⟪u x,u y⟫ ≤ 1 := by
      simpa only [hu,mul_one] using real_inner_le_norm (u x) (u y)
    have hb : ⟪v x,v y⟫ ≤ 1 := by
      simpa only [hv,mul_one] using real_inner_le_norm (v x) (v y)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSingularFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

theorem gaussianPatternSingularMax_centered_tendsto (m : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (Fin (k+1) × Fin (m k)))
    (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω =>
      (gaussianPatternSingularMax (Z k ω) -
        (∫ x : EuclideanSpace ℝ (Fin (k+1) × Fin (m k)), gaussianPatternSingularMax x ∂stdGaussian _)) /
      Real.sqrt (k+1)) atTop (fun _ => 0) :=
  finiteGaussian_centered_tendsto (fun _ => gaussianPatternSingularMax)
    (fun k => gaussianPatternSingularMax_lipschitz (k+1) (m k)) P Z hZ

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

lemma indexedGaussianMaximum_add_constant (C : X → ι → ℝ) (g : ι → ℝ) (a : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun x => (∑ i, C x i*g i)+a) =
      indexedGaussianMaximum C g+a := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    exact add_le_add (Finset.le_sup' (fun x => ∑ i, C x i*g i) (Finset.mem_univ x)) (le_refl a)
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)
    unfold indexedGaussianMaximum
    rw [he]
    exact Finset.le_sup' (fun x => (∑ i, C x i*g i)+a) hx

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp expected maximum estimate for every finite family of unit bilinear tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ}

lemma bilinearMatrix_maximum_eq
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (g : BilinearGaussianIndex N m → ℝ) :
    indexedGaussianMaximum (bilinearMatrixCoefficient u v) g =
      indexedGaussianMaximum (fun x (ij : Fin N × Fin m) => u x ij.1*v x ij.2)
        (fun ij => g (.inl (.inl ij))) + g (.inl (.inr ())) := by
  unfold indexedGaussianMaximum
  simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,zero_mul,
    one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
  exact indexedGaussianMaximum_add_constant _ _ _

theorem bilinear_gaussian_mean_le
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1) :
    (∫ g, indexedGaussianMaximum (fun x (ij : Fin N × Fin m) => u x ij.1*v x ij.2) g
      ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)) ≤
      Real.sqrt N + Real.sqrt m := by
  let μ := Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
  let e : Fin N × Fin m → BilinearGaussianIndex N m := fun ij => .inl (.inl ij)
  let D : X → (Fin N × Fin m) → ℝ := fun x ij => u x ij.1*v x ij.2
  have he : Function.Injective e := fun _ _ h => Sum.inl.inj (Sum.inl.inj h)
  have hD := indexedGaussianMaximum_integrable D
  have hR := iidGaussian_restrict_hasLaw e he
  have hc : Integrable (fun g : BilinearGaussianIndex N m → ℝ => g (.inl (.inr ()))) μ :=
    (gaussianCoordinate_memLp _).integrable (by norm_num)
  have hzero : (∫ g : BilinearGaussianIndex N m → ℝ, g (.inl (.inr ())) ∂μ) = 0 := by
    simpa only [μ,integral_id_gaussianReal] using
      (measurePreserving_eval (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
        (.inl (.inr ()))).hasLaw.integral_eq
  have hleft : (∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g ∂μ) =
      ∫ g, indexedGaussianMaximum D g ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
    simp_rw [bilinearMatrix_maximum_eq]
    change (∫ g, (indexedGaussianMaximum D ∘ (fun g : BilinearGaussianIndex N m → ℝ =>
      fun j => g (e j))) g + g (.inl (.inr ())) ∂μ) = _
    rw [integral_add (hR.integrable_comp hD) hc,hzero,add_zero]
    exact hR.integral_comp hD.aestronglyMeasurable
  let eu : Fin N → BilinearGaussianIndex N m := fun i => .inr (.inl i)
  let ev : Fin m → BilinearGaussianIndex N m := fun j => .inr (.inr j)
  have hub := ((gaussianCoordinateVector_memLp eu).integrable (by norm_num)).norm
  have hvb := ((gaussianCoordinateVector_memLp ev).integrable (by norm_num)).norm
  have hright : (∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g ∂μ) ≤
      (∫ g, ‖gaussianCoordinateVector eu g‖ ∂μ) +
        ∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ := by
    rw [← integral_add hub hvb]
    apply integral_mono (indexedGaussianMaximum_integrable _) (hub.add hvb)
    intro g
    apply Finset.sup'_le
    intro x _
    have hu' := real_inner_le_norm (u x) (gaussianCoordinateVector eu g)
    have hv' := real_inner_le_norm (v x) (gaussianCoordinateVector ev g)
    rw [hu,one_mul] at hu'
    rw [hv,one_mul] at hv'
    convert add_le_add hu' hv' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,
      Finset.sum_const_zero,zero_add,EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct,star_trivial,gaussianCoordinateVector,eu,ev,mul_comm]
  calc
    _ = ∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g ∂μ := hleft.symm
    _ ≤ ∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g ∂μ :=
      bilinear_gaussian_maximum_comparison u v hu hv
    _ ≤ _ := hright
    _ ≤ Real.sqrt N + Real.sqrt m := by
      simpa only [Fintype.card_fin] using add_le_add
        (gaussianCoordinateVector_norm_integral_le eu) (gaussianCoordinateVector_norm_integral_le ev)

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

lemma unitBilinear_le_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F)
    (p : UnitVector F × UnitVector E) : ⟪p.1.1,T p.2.1⟫ ≤ ‖T‖ := by
  calc
    _ ≤ ‖p.1.1‖*‖T p.2.1‖ := real_inner_le_norm _ _
    _ = ‖T p.2.1‖ := by rw [p.1.2,one_mul]
    _ ≤ ‖T‖*‖p.2.1‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [p.2.2,mul_one]

theorem norm_eq_iSup_unitBilinear {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Nonempty (UnitVector E)] [Nonempty (UnitVector F)] (T : E →L[ℝ] F) :
    ‖T‖ = ⨆ p : UnitVector F × UnitVector E, ⟪p.1.1,T p.2.1⟫ := by
  let f := fun p : UnitVector F × UnitVector E => ⟪p.1.1,T p.2.1⟫
  have hb : BddAbove (range f) := ⟨‖T‖,fun _ ⟨p,hp⟩ => hp ▸ unitBilinear_le_norm T p⟩
  have hnonneg : 0 ≤ ⨆ p, f p := by
    let u : UnitVector F := Classical.choice inferInstance
    let v : UnitVector E := Classical.choice inferInstance
    let un : UnitVector F := ⟨-u.1,by simp only [norm_neg,u.2]⟩
    have h₁ := le_ciSup hb (u,v)
    have h₂ := le_ciSup hb (un,v)
    change ⟪u.1,T v.1⟫ ≤ _ at h₁
    change ⟪-u.1,T v.1⟫ ≤ _ at h₂
    rw [inner_neg_left] at h₂
    linarith
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
    intro v hv
    by_cases hz : T v = 0
    · simpa only [hz,norm_zero] using hnonneg
    have hn : ‖T v‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let u : UnitVector F := ⟨‖T v‖⁻¹ • T v,by simp [norm_smul,hn]⟩
    have hh := le_ciSup hb (u,⟨v,hv⟩)
    change ⟪‖T v‖⁻¹ • T v,T v⟫ ≤ _ at hh
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_mul_norm,
      ← mul_assoc,inv_mul_cancel₀ hn,one_mul] using hh
  · exact ciSup_le (unitBilinear_le_norm T)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianOperatorMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp finite-dimensional upper mean bound for a rectangular Gaussian matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology
namespace InvariantIsing

theorem gaussianPatternSingularMax_mean_le_pos {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z ∂stdGaussian _) ≤
      Real.sqrt N + Real.sqrt m := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin N))) := unitVector_nonempty _
  let : Nonempty (UnitVector (EuclideanSpace ℝ (Fin m))) := unitVector_nonempty _
  let S := UnitVector (EuclideanSpace ℝ (Fin N)) × UnitVector (EuclideanSpace ℝ (Fin m))
  let s : ℕ → S := TopologicalSpace.denseSeq S
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  let A (n : ℕ) (g : (Fin N × Fin m) → ℝ) : ℝ :=
    indexedGaussianMaximum (fun i : Fin (n+1) => fun ij =>
      (s i).1.1 ij.1*(s i).2.1 ij.2) g
  let Z (g : (Fin N × Fin m) → ℝ) : EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 g
  let μ := Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)
  have hZ : HasLaw Z (stdGaussian _) μ :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  have hA (n : ℕ) (g : (Fin N × Fin m) → ℝ) :
      A n g = prefixMaximum
        (fun i => ⟪(s i).1.1,gaussianPatternEuclideanOperator (Z g) (s i).2.1⟫) n := by
    unfold A indexedGaussianMaximum prefixMaximum
    congr 1
    funext i
    exact (gaussianPattern_unitBilinear (Z g) (s i).1.1 (s i).2.1).symm
  have hlim (g : (Fin N × Fin m) → ℝ) :
      Tendsto (fun n => A n g) atTop (𝓝 (gaussianPatternSingularMax (Z g))) := by
    simp_rw [hA]
    have hc : Continuous (fun p : S =>
        ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫) := by
      dsimp [S]
      fun_prop
    have hb : BddAbove (range (fun p : S =>
        ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫)) :=
      ⟨‖gaussianPatternEuclideanOperator (Z g)‖,by
        rintro _ ⟨p,rfl⟩
        exact unitBilinear_le_norm _ p⟩
    have ht := dense_prefixMaximum_tendsto s hs _ hc hb
    have hn := norm_eq_iSup_unitBilinear (gaussianPatternEuclideanOperator (Z g))
    change ‖gaussianPatternEuclideanOperator (Z g)‖ =
      (⨆ p : S, ⟪p.1.1,gaussianPatternEuclideanOperator (Z g) p.2.1⟫) at hn
    rw [← hn] at ht
    exact ht
  have hbound (n : ℕ) (g : (Fin N × Fin m) → ℝ) : |A n g| ≤ ‖Z g‖ := by
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n+1) => ∑ ij, (s i).1.1 ij.1*(s i).2.1 ij.2*g ij)
    change |Finset.univ.sup' Finset.univ_nonempty _| ≤ _
    rw [he,← gaussianPattern_unitBilinear (Z g) (s i).1.1 (s i).2.1]
    calc
      _ ≤ ‖(s i).1.1‖*‖gaussianPatternEuclideanOperator (Z g) (s i).2.1‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖gaussianPatternEuclideanOperator (Z g) (s i).2.1‖ := by rw [(s i).1.2,one_mul]
      _ ≤ ‖gaussianPatternEuclideanOperator (Z g)‖*‖(s i).2.1‖ :=
        (gaussianPatternEuclideanOperator (Z g)).le_opNorm _
      _ ≤ ‖Z g‖ := by rw [(s i).2.2,mul_one]; exact gaussianPatternEuclideanOperator_norm_le _
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun g => ‖Z g‖)
    (fun n => (measurable_indexedGaussianMaximum _).aestronglyMeasurable)
    (((gaussianCoordinateVector_memLp (id : (Fin N × Fin m) → (Fin N × Fin m))).integrable
      (by norm_num)).norm)
    (fun n => ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hbound n g))
    (ae_of_all _ hlim)
  have hb (n : ℕ) : (∫ g, A n g ∂μ) ≤ Real.sqrt N + Real.sqrt m :=
    bilinear_gaussian_mean_le (fun i : Fin (n+1) => (s i).1.1)
      (fun i : Fin (n+1) => (s i).2.1) (fun i => (s i).1.2) (fun i => (s i).2.2)
  have he : (∫ g, gaussianPatternSingularMax (Z g) ∂μ) =
      ∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMax z ∂stdGaussian _ := by
    simpa only [Function.comp_def] using hZ.integral_comp
      (gaussianPatternSingularMax_lipschitz N m).continuous.aestronglyMeasurable
  rw [← he]
  exact le_of_tendsto ht (Filter.Eventually.of_forall hb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianNormMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact variance gives the second-moment upper bound needed for Gaussian Gram tails. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

theorem gaussianPatternSingularMax_mean_le (N m : ℕ) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z ∂stdGaussian _) ≤
      Real.sqrt N + Real.sqrt m := by
  by_cases hN : N = 0
  · subst N
    have hz (z : EuclideanSpace ℝ (Fin 0 × Fin m)) : gaussianPatternSingularMax z = 0 := by
      unfold gaussianPatternSingularMax
      rw [Subsingleton.elim (gaussianPatternEuclideanOperator z) 0,norm_zero]
    simp only [hz,integral_zero,Nat.cast_zero,Real.sqrt_zero,zero_add]
    exact Real.sqrt_nonneg _
  by_cases hm : m = 0
  · subst m
    have hz (z : EuclideanSpace ℝ (Fin N × Fin 0)) : gaussianPatternSingularMax z = 0 := by
      unfold gaussianPatternSingularMax
      rw [Subsingleton.elim (gaussianPatternEuclideanOperator z) 0,norm_zero]
    simp only [hz,integral_zero,Nat.cast_zero,Real.sqrt_zero,add_zero]
    exact Real.sqrt_nonneg _
  exact gaussianPatternSingularMax_mean_le_pos (Nat.pos_of_ne_zero hN) (Nat.pos_of_ne_zero hm)

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

lemma gaussianPatternCount_sqrt_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => 1+Real.sqrt ((gaussianPatternCount α (k+1) : ℝ)/(k+1)))
      atTop (𝓝 (1+Real.sqrt α)) :=
  tendsto_const_nhds.add (Real.continuous_sqrt.tendsto α |>.comp (gaussianPatternCount_ratio_tendsto hα))

lemma gaussianPattern_mean_div_sqrt_le {N m : ℕ} (hN : 0 < N) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z
      ∂ProbabilityTheory.stdGaussian _)/Real.sqrt N ≤ 1+Real.sqrt ((m : ℝ)/N) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  calc
    _ ≤ (Real.sqrt N+Real.sqrt m)/Real.sqrt N :=
      div_le_div_of_nonneg_right (gaussianPatternSingularMax_mean_le N m) hs.le
    _ = _ := by rw [add_div,div_self hs.ne',Real.sqrt_div (Nat.cast_nonneg m)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSingularUpperEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp one-sided upper singular-value edge for the actual rectangular Gaussian model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem gaussianPatternSingularMax_upper_edge_oai {α : ℝ} (hα : 0 ≤ α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω =>
      max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1) - (1+Real.sqrt α)) 0)
      atTop (fun _ => 0) := by
  let M (k : ℕ) := ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
    gaussianPatternSingularMax z ∂stdGaussian _
  let B (k : ℕ) := 1+Real.sqrt ((gaussianPatternCount α (k+1) : ℝ)/(k+1))
  have hB : Tendsto B atTop (𝓝 (1+Real.sqrt α)) := gaussianPatternCount_sqrt_ratio_tendsto hα
  have hM (k : ℕ) : M k/Real.sqrt (k+1) ≤ B k := by
    simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      gaussianPattern_mean_div_sqrt_le (m := gaussianPatternCount α (k+1)) (Nat.succ_pos k)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1) -
        (1+Real.sqrt α)) 0) P := by
    have hc := (gaussianPatternSingularMax_lipschitz (k+1) (gaussianPatternCount α (k+1))).continuous
    have hm : Measurable (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        max (gaussianPatternSingularMax z/Real.sqrt (k+1)-(1+Real.sqrt α)) 0) := by fun_prop
    exact (hm.aemeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hcu⟩ := ((gaussianPatternSingularMax_centered_tendsto
    (fun k => gaussianPatternCount α (k+1)) P (fun k => Z (k+1))
    (fun k => hZ (k+1))).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [hcu] with ω hω
  have hc : Tendsto (fun k =>
      (gaussianPatternSingularMax (Z (ns (u k)+1) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1))
      atTop (𝓝 0) := hω
  have hb := hB.comp (hns.comp hu).tendsto_atTop
  have ht := ((hc.add hb).sub_const (1+Real.sqrt α)).max (tendsto_const_nhds (x := (0 : ℝ)))
  have ht' : Tendsto (fun k => max
      ((gaussianPatternSingularMax (Z (ns (u k)+1) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1) +
        B (ns (u k))-(1+Real.sqrt α)) 0) atTop (𝓝 0) := by
    simpa only [zero_add,sub_self,max_self,Function.comp_def] using ht
  apply squeeze_zero (fun _ => le_max_right _ _) _ ht'
  intro k
  apply max_le_max _ le_rfl
  have hm := hM (ns (u k))
  rw [sub_div]
  linarith

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge_oai.{u_1} := @OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge_oai.{u_1}
