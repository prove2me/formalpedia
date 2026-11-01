-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:57:22.513191+00:00
-- url     : https://prove2.me/submissions/1a4f9a43-7d1f-4046-af53-96d9401e268b

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_manufacturedSlab_residual_finite_rank_lower
import Theorems.Thm_OAI_ContinuumCoulomb_manufacturedSlab_test_lower

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Add
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma mass_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma Antisymmetric.add {n : ℕ} {ψ φ : H1Vector n}
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) : Antisymmetric (ψ.add φ) := by
  intro p s
  filter_upwards [hψ p s, hφ p s] with x hx hy
  change ψ.value (s ∘ p) (permute p x) + φ.value (s ∘ p) (permute p x) = _
  rw [hx, hy]
  exact (mul_add _ _ _).symm

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SobolevDensityInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Sobolev density input for conditional estimates

N. G. Meyers and J. Serrin, *H = W*, Proc. Natl. Acad. Sci. USA 51 (1964),
1055–1056, DOI 10.1073/pnas.51.6.1055, Theorem and the Lemma on p.1056.
We use only m=1, p=2 on the full Euclidean configuration space. The finite
spin index is handled componentwise. This is smooth approximation in the
value-and-weak-gradient norm; no compact support or Coulomb-form comparison
is included in the assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

/-- A convenient actual-H1 version, preserving the published input explicitly. -/
theorem exists_smooth_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨f, hf, hL2, hpartial, he⟩ := hpublished n u ε hε
  exact ⟨classicalH1State f (fun s => (hf s).of_le (by first | simp | exact_mod_cast le_top)) hL2 hpartial,
    hf, fun _ _ _ => rfl, he⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SmoothCutoffApproximation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs of actual smooth weak-H1 vectors. This is the cutoff
step needed after the published smooth-density theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem smoothCutoffState_gradient {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (smoothCutoffState u hu χ hχ hc).gradient s a x =
      (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) * u.value s x +
        (χ x : ℂ) * u.gradient s a x := by
  change fderiv ℝ (fun y => (χ y : ℂ) * u.value s y) x (EuclideanSpace.single a 1) = _
  have hfχ := Complex.ofRealCLM.hasFDerivAt.comp x
    (hχ.differentiable (by norm_num) x).hasFDerivAt
  have hf := hfχ.mul (hu s |>.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hf.fderiv
  calc
    _ = (χ x : ℂ) * u.gradient s a x +
        u.value s x * (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) := by
      simpa only [Pi.mul_def, Function.comp_def, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, hd] using he
    _ = _ := by ring

/-- Dominated convergence for the two terms in the cutoff product rule. -/
theorem cutoff_product_error_tendsto {n : ℕ}
    (f g : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2)
    (a b : ℕ → Configuration n → ℝ)
    (ha : ∀ k, Continuous (a k)) (hb : ∀ k, Continuous (b k))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : ∀ k x, |a k x| ≤ A ∧ |b k x| ≤ B)
    (hat : ∀ x, Tendsto (fun k => a k x) atTop (𝓝 0))
    (hbt : ∀ x, Tendsto (fun k => b k x) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖(a k x : ℂ) * f x + (b k x : ℂ) * g x‖^2)
      atTop (𝓝 0) := by
  have hfi : Integrable (fun x => ‖f x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi : Integrable (fun x => ‖g x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  suffices hlim : Tendsto
      (fun k => ∫ x, ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖^2)
      atTop (𝓝 (∫ _ : Configuration n, (0 : ℝ))) by
    simpa only [integral_zero] using hlim
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*A^2*‖f x‖^2 + 2*B^2*‖g x‖^2)
  · intro k
    exact ((((Complex.continuous_ofReal.comp (ha k)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).add
      ((Complex.continuous_ofReal.comp (hb k)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable)).norm.pow 2)
  · exact (hfi.const_mul (2*A^2)).add (hgi.const_mul (2*B^2))
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖ ≤ A*‖f x‖ + B*‖g x‖ := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hab k x).1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hab k x).2 (norm_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _)))).mpr he
    nlinarith [sq_nonneg (A*‖f x‖ - B*‖g x‖)]
  · filter_upwards [] with x
    have ht := (((Complex.continuous_ofReal.tendsto 0).comp (hat x)).mul_const (f x)).add
      (((Complex.continuous_ofReal.tendsto 0).comp (hbt x)).mul_const (g x))
    simpa using ht.norm.pow 2

theorem smoothCutoffState_error_tendsto {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : ℕ → Configuration n → ℝ) (hχ : ∀ k, ContDiff ℝ 1 (χ k))
    (hc : ∀ k, HasCompactSupport (χ k))
    (D : ℝ) (hb : ∀ k x, |χ k x| ≤ 1)
    (hdb : ∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D)
    (ht : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    (hdt : ∀ a x, Tendsto (fun k => fderiv ℝ (χ k) x (EuclideanSpace.single a 1))
      atTop (𝓝 0)) :
    Tendsto (fun k => h1GraphError u (smoothCutoffState u hu (χ k) (hχ k) (hc k)))
      atTop (𝓝 0) := by
  have hχb (k : ℕ) (x : Configuration n) : |χ k x - 1| ≤ 2 := by
    calc
      _ ≤ |χ k x| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by simpa only [abs_one] using (show |χ k x| + 1 ≤ 2 by linarith [hb k x])
  have hv (s : SpinConfiguration n) :
      Tendsto (fun k => ∫ x, ‖u.value s x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).value s x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.value s)
      (u.value_L2 s) (u.value_L2 s)
      (fun k x => χ k x - 1) (fun _ _ => 0)
      (fun k => (hχ k).continuous.sub continuous_const) (fun _ => continuous_const)
      2 0 (by norm_num) le_rfl (fun k x => ⟨hχb k x, by simp⟩)
      (fun x => by simpa using (ht x).sub_const 1) (fun _ => tendsto_const_nhds)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖u.value s x - (χ k x : ℂ)*u.value s x‖^2 = _
    rw [norm_sub_rev]
    congr 2
    push_cast
    ring
  have hg (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      Tendsto (fun k => ∫ x, ‖u.gradient s a x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).gradient s a x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.gradient s a)
      (u.value_L2 s) (u.partial_L2 s a)
      (fun k x => fderiv ℝ (χ k) x (EuclideanSpace.single a 1)) (fun k x => χ k x - 1)
      (fun k => ((hχ k).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (fun k => (hχ k).continuous.sub continuous_const)
      |D| 2 (abs_nonneg D) (by norm_num)
      (fun k x => ⟨(hdb k a x).trans (le_abs_self D), hχb k x⟩)
      (hdt a) (fun x => by simpa using (ht x).sub_const 1)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smoothCutoffState_gradient u hu hd, norm_sub_rev]
    congr 2
    push_cast
    ring
  simpa only [h1GraphError, Finset.sum_const_zero, zero_add] using
    (tendsto_finsetSum _ (fun s _ => hv s)).add
      (tendsto_finsetSum _ (fun s _ => tendsto_finsetSum _ (fun a _ => hg s a)))

/-- Every smooth actual H1 vector is the graph-norm limit of compactly
supported C1 vectors, using the existing full-space cutoff construction. -/
theorem exists_compact_approximation_of_smooth {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (u.value s))
    (hd : ∀ s a x, u.gradient s a x = fderiv ℝ (u.value s) x (EuclideanSpace.single a 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨χ, D, hχ, hc, hb, hdb, ht, hdt⟩ := Coulomb.exists_hardyCutoffs n
  have hu₁ : ∀ s, ContDiff ℝ 1 (u.value s) := fun s => (hu s).of_le (by first | simp | exact_mod_cast le_top)
  have hχ₁ : ∀ k, ContDiff ℝ 1 (χ k) := fun k => (hχ k).of_le (by first | simp | exact_mod_cast le_top)
  have he := smoothCutoffState_error_tendsto u hu₁ (fun s a x => (hd s a x).symm)
    χ hχ₁ hc D hb hdb ht hdt
  obtain ⟨k, hk⟩ := (he.eventually (gt_mem_nhds hε)).exists
  refine ⟨smoothCutoffState u hu₁ (χ k) (hχ₁ k) (hc k), fun s => ?_,
    fun _ _ _ => rfl, hk⟩
  exact ⟨(cutoff_complex_C1 _ (hχ₁ k)).mul (hu₁ s),
    ((hc k).comp_left Complex.ofReal_zero).mul_right⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSobolevCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported C1 approximation on the full declared weak-H1
configuration domain. Only the explicitly cited smooth-density input is
conditional; the compactification step is proved here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem integral_square_error_triangle {n : ℕ}
    (f g h : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) (hh : MemLp h 2) :
    (∫ x, ‖f x-h x‖^2) ≤ 2*(∫ x, ‖f x-g x‖^2) + 2*(∫ x, ‖g x-h x‖^2) := by
  have hi (v w : Configuration n → ℂ) (hv : MemLp v 2) (hw : MemLp w 2) :
      Integrable (fun x => ‖v x-w x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (hv.sub hw).aestronglyMeasurable).mp (hv.sub hw)
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2 := by
      apply integral_mono (hi f h hf hh) ((hi f g hf hg).const_mul 2 |>.add
        ((hi g h hg hh).const_mul 2))
      intro x
      change ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2
      have he : ‖f x-h x‖ ≤ ‖f x-g x‖ + ‖g x-h x‖ := by
        calc
          _ = ‖(f x-g x)+(g x-h x)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
      nlinarith [sq_nonneg (‖f x-g x‖ - ‖g x-h x‖)]
    _ = _ := by
      rw [integral_add ((hi f g hf hg).const_mul 2) ((hi g h hg hh).const_mul 2),
        integral_const_mul, integral_const_mul]

theorem h1GraphError_triangle {n : ℕ} (u v w : Coulomb.H1Vector n) :
    h1GraphError u w ≤ 2*h1GraphError u v + 2*h1GraphError v w := by
  have hv := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    integral_square_error_triangle (u.value s) (v.value s) (w.value s)
      (u.value_L2 s) (v.value_L2 s) (w.value_L2 s))
  have hg := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
      integral_square_error_triangle (u.gradient s a) (v.gradient s a) (w.gradient s a)
        (u.partial_L2 s a) (v.partial_L2 s a) (w.partial_L2 s a)))
  have h := add_le_add hv hg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold h1GraphError
  linarith

/-- The smooth-density theorem plus the proved cutoff step gives a compact
core for the actual full weak-H1 vectors, with no symmetry restriction. -/
theorem exists_compact_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨v, hv, hd, hve⟩ := exists_smooth_h1_approximation hpublished u
    (by linarith : (0 : ℝ) < ε/4)
  obtain ⟨w, hw, hwd, hwe⟩ := exists_compact_approximation_of_smooth v hv hd
    (by linarith : (0 : ℝ) < ε/4)
  refine ⟨w, hw, hwd, ?_⟩
  have h := h1GraphError_triangle u v w
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1GraphCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full weak-H1 graph as finitely many actual L2 coordinates. Compact
C1 states approximate every coordinate simultaneously, so continuous form
inequalities on this graph extend to the full weak-H1 domain. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem h1Coordinate_error {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 =
      ∫ x, ‖h1CoordinateFunction u a x-h1CoordinateFunction v a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (h1Coordinates u a) (h1Coordinates v a),
    (h1Coordinate_memLp u a).coeFn_toLp, (h1Coordinate_memLp v a).coeFn_toLp]
    with x hs hu hv
  rw [real_inner_self_eq_norm_sq]
  change ‖(h1Coordinates u a-h1Coordinates v a) x‖^2 = _
  rw [hs]
  change ‖h1Coordinates u a x-h1Coordinates v a x‖^2 = _
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  change h1Coordinates v a x = h1CoordinateFunction v a x at hv
  rw [hu, hv]

theorem h1GraphError_eq_sum {n : ℕ} (u v : Coulomb.H1Vector n) :
    h1GraphError u v = ∑ a : H1Index n, ‖h1Coordinates u a-h1Coordinates v a‖^2 := by
  simp only [h1Coordinate_error, Fintype.sum_sum_type, Fintype.sum_prod_type,
    h1CoordinateFunction, h1GraphError]

theorem h1Coordinate_error_le {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a-h1Coordinates v a‖^2 ≤ h1GraphError u v := by
  rw [h1GraphError_eq_sum]
  exact Finset.single_le_sum (fun (i : H1Index n) _ =>
    sq_nonneg ‖h1Coordinates u i-h1Coordinates v i‖) (Finset.mem_univ a)

/-- Compact C1 states converge to every actual weak-H1 state in the finite
product of value and derivative L2 spaces. -/
theorem exists_compact_h1_graph_sequence (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) :
    ∃ v : ℕ → Coulomb.H1Vector n,
      (∀ k s, ContDiff ℝ 1 ((v k).value s) ∧ HasCompactSupport ((v k).value s)) ∧
      (∀ k s a x, (v k).gradient s a x =
        fderiv ℝ ((v k).value s) x (EuclideanSpace.single a 1)) ∧
      Tendsto (fun k => h1Coordinates (v k)) atTop (𝓝 (h1Coordinates u)) := by
  have he (k : ℕ) := exists_compact_h1_approximation hpublished u
    (show (0 : ℝ) < 1/((k : ℝ)+1) by positivity)
  choose v hv hd herr using he
  refine ⟨v, hv, hd, ?_⟩
  apply tendsto_pi_nhds.2
  intro a
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun k => ‖h1Coordinates (v k) a-h1Coordinates u a‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro k
    rw [norm_sub_rev]
    exact (h1Coordinate_error_le u (v k) a).trans (herr k).le
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using ht

/-- Transfer a continuous inequality from compact classical states to the
full declared weak-H1 graph. -/
theorem h1_continuous_nonnegative_of_compact
    (hpublished : PublishedSobolevSmoothDensity) {n : ℕ}
    (F : (H1Index n → Lp ℂ 2 (volume : Measure (Configuration n))) → ℝ)
    (hF : Continuous F)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) → 0 ≤ F (h1Coordinates v))
    (u : Coulomb.H1Vector n) : 0 ≤ F (h1Coordinates u) := by
  obtain ⟨v, hv, hd, ht⟩ := exists_compact_h1_graph_sequence hpublished u
  exact ge_of_tendsto (hF.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall (fun k => hcompact (v k) (hv k) (hd k)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1BoundedForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous kinetic-plus-bounded-operator forms on the full H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1Coordinates_norm_sq {n : ℕ} (u : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a‖^2 = ∫ x, ‖h1CoordinateFunction u a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u a).coeFn_toLp] with x hx
  simpa only [real_inner_self_eq_norm_sq, h1Coordinates] using congrArg (fun z : ℂ => ‖z‖^2) hx

theorem mass_eq_graphMass {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.mass u = graphMass (h1Coordinates u) := by
  simp only [Coulomb.mass, graphMass, h1Coordinates_norm_sq, h1CoordinateFunction]

theorem kinetic_eq_graphKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u = graphKinetic (h1Coordinates u) := by
  simp only [Coulomb.kinetic, graphKinetic, h1Coordinates_norm_sq, h1CoordinateFunction]

theorem graphMass_continuous (n : ℕ) : Continuous (@graphMass n) :=
  continuous_finsetSum _ (fun s _ => (continuous_apply (Sum.inl s)).norm.pow 2)

theorem graphKinetic_continuous (n : ℕ) : Continuous (@graphKinetic n) :=
  continuous_const.mul (continuous_finsetSum _ (fun s _ =>
    continuous_finsetSum _ (fun a _ => (continuous_apply (Sum.inr (s,a))).norm.pow 2)))

theorem graphBoundedForm_continuous {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) : Continuous (graphBoundedForm A) :=
  (graphKinetic_continuous n).add (continuous_finsetSum _ (fun s _ =>
    (continuous_apply (Sum.inl s)).inner (A.continuous.comp (continuous_apply (Sum.inl s)))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedPotentialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded real multiplication potentials on the weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace BoundedPotential

variable {n : ℕ} (V : Configuration n → ℝ) (hV : Continuous V)
  (B : ℝ) (hB : ∀ x, |V x| ≤ B)

theorem operator_ae (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    operator V hV B hB u =ᵐ[volume] fun x => (V x : ℂ)*u x := value_ae V hV B hB u

theorem operator_pairing (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ u (operator V hV B hB u) = ∫ x, V x * ‖u x‖^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae V hV B hB u] with x hx
  rw [hx, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]

end BoundedPotential

theorem boundedPotentialForm_eq_graph {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    boundedPotentialForm V u =
      graphBoundedForm (BoundedPotential.operator V hV B hB) (h1Coordinates u) := by
  unfold boundedPotentialForm graphBoundedForm
  rw [kinetic_eq_graphKinetic]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [BoundedPotential.operator_pairing]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp] with x hx
  change h1Coordinates u (Sum.inl s) x = u.value s x at hx
  rw [hx]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_H1FiniteProjection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orbital penalties pass from compact tests to the complete weak-H1
domain without asking approximants to preserve exact orthogonality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem graphOrbitalMass_continuous {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) :
    Continuous (graphOrbitalMass ψ) :=
  continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun _i _ =>
    (continuous_const.inner (continuous_apply (Sum.inl s))).norm.pow 2))

theorem graphOrbitalMass_eq_zero {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n)
    (horth : ∀ s i, inner ℂ (ψ i) (f (Sum.inl s)) = 0) :
    graphOrbitalMass ψ f = 0 := by
  simp only [graphOrbitalMass, horth, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero]

/-- The finite projection term is continuous on the same graph as the
kinetic and bounded potential terms. -/
theorem boundedPotential_projection_lower_of_compact
    (hpublished : PublishedSobolevSmoothDensity) {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B)
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (E κ : ℝ)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) →
      E*Coulomb.mass v - κ*graphOrbitalMass ψ (h1Coordinates v) ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector n) :
    E*Coulomb.mass u - κ*graphOrbitalMass ψ (h1Coordinates u) ≤ boundedPotentialForm V u := by
  let A := BoundedPotential.operator V hV B hB
  let F : H1Coordinates n → ℝ := fun f =>
    graphBoundedForm A f - E*graphMass f + κ*graphOrbitalMass ψ f
  have hF : Continuous F :=
    ((graphBoundedForm_continuous A).sub
      (continuous_const.mul (graphMass_continuous n))).add
      (continuous_const.mul (graphOrbitalMass_continuous ψ))
  have h := h1_continuous_nonnegative_of_compact hpublished F hF
    (fun v hv hd => by
      dsimp [F, A]
      rw [← boundedPotentialForm_eq_graph V hV B hB, ← mass_eq_graphMass]
      linarith [hcompact v hv hd]) u
  dsimp [F, A] at h
  rw [← boundedPotentialForm_eq_graph V hV B hB, ← mass_eq_graphMass] at h
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_FermionicCoefficients
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

lemma FermionicCoefficients.norm_permute {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (p : Equiv.Perm (Fin n)) (b : Fin n → α) : ‖f (b ∘ p)‖ = ‖f b‖ := by
  rw [hf p b, norm_mul]
  have hsign : ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]
  rw [hsign, one_mul]

lemma permuteIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permuteIsometry p x = permute p x := by
  ext a
  rfl

lemma integral_permute {n : ℕ} (p : Equiv.Perm (Fin n))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Configuration n → E) :
    (∫ x, f (permute p x)) = ∫ x, f x := by
  have h := (permuteIsometry p).measurePreserving.integral_comp
    (permuteIsometry p).toHomeomorph.measurableEmbedding f
  simpa only [permuteIsometry_apply] using h

lemma sign_complex_norm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]

lemma position_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) (i : Fin n) :
    position (permute p x) i = position x (p i) := rfl

lemma tensorOrbital_permute {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) (p : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    tensorOrbital v (b ∘ p) (s ∘ p) (permute p x) = tensorOrbital v b s x := by
  unfold tensorOrbital
  simp only [Function.comp_apply, position_permute]
  exact Equiv.prod_comp p (fun i => v (b i) (position x i) (s i))

lemma orbitalCoefficient_antisymmetric {n : ℕ} {α : Type*} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (v : α → Space → Fin 2 → ℂ)
    (p : Equiv.Perm (Fin n)) (b : Fin n → α) :
    orbitalCoefficient ψ v (b ∘ p) = ((p.sign : ℤ) : ℂ) * orbitalCoefficient ψ v b := by
  unfold orbitalCoefficient
  rw [← (spinPermEquiv p).sum_comp (fun s =>
    ∫ x, star (tensorOrbital v (b ∘ p) s x) * ψ.value s x)]
  simp only [spinPermEquiv, Equiv.coe_fn_mk]
  have he : ∀ s, (∫ x, star (tensorOrbital v (b ∘ p) (s ∘ p) x) * ψ.value (s ∘ p) x) =
      ((p.sign : ℤ) : ℂ) * ∫ x, star (tensorOrbital v b s x) * ψ.value s x := by
    intro s
    rw [← integral_permute p (fun x =>
      star (tensorOrbital v (b ∘ p) (s ∘ p) x) * ψ.value (s ∘ p) x)]
    simp only [tensorOrbital_permute]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hψ p s] with x hx
    rw [hx]
    ring
  simp_rw [he]
  rw [Finset.mul_sum]

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

theorem configurationMeasurableEquiv_apply (n : ℕ) (x : Configuration n) (i : Fin n) :
    configurationMeasurableEquiv n x i = position x i := rfl

theorem tensorOrbital_inner_integral {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b c : Fin n → α) :
    (∑ s : Spins n, ∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  classical
  have hi : ∀ s : Spins n,
      (∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∫ y, star (v (b i) y (s i)) * v (c i) y (s i) := by
    intro s
    calc
      _ = ∫ x : Fin n → Space, ∏ i, star (v (b i) (x i) (s i)) * v (c i) (x i) (s i) := by
        rw [← (configurationMeasurableEquiv_measurePreserving n).integral_comp']
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [tensorOrbital, star_prod, Finset.prod_mul_distrib,
            configurationMeasurableEquiv_apply]
      _ = _ := integral_fintype_prod_volume_eq_prod
        (fun i (y : Space) => star (v (b i) y (s i)) * v (c i) y (s i))
  simp_rw [hi]
  exact (Fintype.prod_sum fun i (t : Fin 2) => ∫ y, star (v (b i) y t) * v (c i) y t).symm

lemma norm_toLp_sq_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (↑(‖hf.toLp f‖ ^ 2) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∫ x, star (f x) * f x ∂μ := inner_toLp_complex hf hf
    _ = ∫ x, (↑(‖f x‖ ^ 2) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [mul_comm, Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f x)

lemma tensorHilbert_inner {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b c : Fin n → α) :
    inner ℂ (tensorHilbert v hv b) (tensorHilbert v hv c) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  rw [PiLp.inner_apply]
  simp only [tensorHilbert, WithLp.ofLp_toLp, inner_toLp_complex]
  exact tensorOrbital_inner_integral v b c

lemma tensorHilbert_orthonormal {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t) * v c y t) =
      if a = c then (1 : ℂ) else 0) :
    Orthonormal ℂ (tensorHilbert (n := n) v hv) := by
  classical
  rw [orthonormal_iff_ite]
  intro b c
  rw [tensorHilbert_inner]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    have hi : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hi]

lemma orbitalCoefficient_eq_inner {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) :
    orbitalCoefficient ψ v b = inner ℂ (tensorHilbert v hv b) ψ.toHilbert := by
  rw [PiLp.inner_apply]
  simp only [tensorHilbert, H1Vector.toHilbert, WithLp.ofLp_toLp, inner_toLp_complex,
    orbitalCoefficient]

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma memLp_fiber_ae {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    ∀ᵐ b ∂ν, MemLp (fun a => f (b, a)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.norm.integrable_sq.prod_right_ae]
    with b hb hbi
  exact (memLp_two_iff_integrable_sq_norm hb).2 hbi

omit [SigmaFinite μ] in
lemma integralInner_sq_le {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ a, star (f a) * g a ∂μ‖ ^ 2 ≤
      (∫ a, ‖f a‖ ^ 2 ∂μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) := by
  rw [← inner_toLp_complex hf hg, ← norm_toLp_sq_complex hf, ← norm_toLp_sq_complex hg,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

lemma fiberContract_memLp {v : A → ℂ} {f : B × A → ℂ}
    (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (fiberContract (μ := μ) v f) 2 ν := by
  have hm : AEStronglyMeasurable (fiberContract (μ := μ) v f) ν :=
    (hv.aestronglyMeasurable.star.comp_snd.mul hf.aestronglyMeasurable).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply Integrable.mono' ((hf.norm.integrable_sq.integral_prod_left).const_mul
    (∫ a, ‖v a‖ ^ 2 ∂μ)) (hm.norm.pow 2)
  filter_upwards [memLp_fiber_ae hf] with b hb
  simpa only [fiberContract, Pi.pow_apply, Real.norm_eq_abs, abs_sq] using integralInner_sq_le hv hb

omit [SigmaFinite μ] [SigmaFinite ν] in

lemma tensorPair_memLp [SFinite μ] {w : B → ℂ} {v : A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) :
    MemLp (fun z : B × A => w z.1 * v z.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hw.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hw.norm.integrable_sq.mul_prod hv.norm.integrable_sq

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma integrable_star_mul {F : Type*} [MeasurableSpace F] {η : Measure F}
    {f g : F → ℂ} (hf : MemLp f 2 η) (hg : MemLp g 2 η) :
    Integrable (fun x => star (f x) * g x) η := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma integral_tensorPair {w : B → ℂ} {v : A → ℂ} {f : B × A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    (∫ z, star (w z.1 * v z.2) * f z ∂(ν.prod μ)) =
      ∫ b, star (w b) * fiberContract (μ := μ) v f b ∂ν := by
  rw [integral_prod _ (integrable_star_mul (tensorPair_memLp hw hv) hf)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    dsimp only [fiberContract]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      simp only [star_mul]
      ring

end FiberContraction

section CompleteProducts
variable {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    [Countable ι]

theorem completeOrbitals_tensorPair {v : ι → A → ℂ} {w : κ → B → ℂ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hw : ∀ j, MemLp (w j) 2 ν)
    (hc : CompleteOrbitals μ v) (hd : CompleteOrbitals ν w) :
    CompleteOrbitals (ν.prod μ) (fun ij : κ × ι => fun z => w ij.1 z.1 * v ij.2 z.2) := by
  intro f hf hz
  have hzero : ∀ i, fiberContract (μ := μ) (v i) f =ᵐ[ν] 0 := by
    intro i
    apply hd _ (fiberContract_memLp (hv i) hf)
    intro j
    rw [← integral_tensorPair (hw j) (hv i) hf]
    exact hz (j, i)
  have hslice : ∀ᵐ b ∂ν, (fun a => f (b, a)) =ᵐ[μ] 0 := by
    filter_upwards [memLp_fiber_ae hf, ae_all_iff.mpr hzero] with b hb hbi
    apply hc _ hb
    exact hbi
  have hi : (∫ z, ‖f z‖ ^ 2 ∂(ν.prod μ)) = 0 := by
    rw [integral_prod _ hf.norm.integrable_sq]
    apply integral_eq_zero_of_ae
    filter_upwards [hslice] with b hb
    apply integral_eq_zero_of_ae
    filter_upwards [hb] with a ha
    simp [ha]
  have hz' := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖)
    hf.norm.integrable_sq).1 hi
  filter_upwards [hz'] with z h
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using h

end CompleteProducts

theorem HilbertBasis_completeOrbitals {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} (v : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    CompleteOrbitals μ (fun i => v i) := by
  intro f hf hz
  have he : v.repr (hf.toLp f) = 0 := by
    apply lp.ext
    funext i
    rw [v.repr_apply_apply]
    change inner ℂ (v i) (hf.toLp f) = 0
    have hi := inner_toLp_complex (Lp.memLp (v i)) hf
    simp only [Lp.toLp_coeFn] at hi
    rw [hi, hz i]
  have hf0 : hf.toLp f = 0 := v.repr.injective (by simpa using he)
  exact hf.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).1 hf0)

theorem CompleteOrbitals.comp {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {v : ι → A → ℂ}
    (hc : CompleteOrbitals μ v) (e : B ≃ᵐ A) (he : MeasurePreserving e ν μ) :
    CompleteOrbitals ν (fun i b => v i (e b)) := by
  intro f hf hz
  have hs := hc (f ∘ e.symm) (hf.comp_measurePreserving (he.symm e)) (by
    intro i
    dsimp only [Function.comp_apply]
    rw [← he.integral_comp' (fun a => star (v i a) * f (e.symm a))]
    simpa using hz i)
  filter_upwards [he.quasiMeasurePreserving.ae hs] with b hb
  simpa using hb

theorem completeOrbitals_finPi {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] [Countable ι] (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hc : CompleteOrbitals μ v) (n : ℕ) :
    CompleteOrbitals (Measure.pi fun _ : Fin n => μ)
      (fun b : Fin n → ι => fun x => ∏ i, v (b i) (x i)) := by
  induction n with
  | zero =>
    intro f hf hz
    have h := hz (fun i => Fin.elim0 i)
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    have hcp : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) =
        f (fun i => Fin.elim0 i) := by
      rw [he]
      simp [Measure.real, Measure.pi_empty_univ]
    have hh : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) = 0 := by
      simpa only [Fin.prod_univ_zero, star_one, one_mul] using h
    rw [hcp] at hh
    filter_upwards with x
    have hx : x = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hx, Pi.zero_apply] using hh
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0
    have hp : MeasurePreserving e (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have ht := (completeOrbitals_tensorPair
      (fun (b : Fin n → ι) => scalarTensor_memLp v hv b) hv ih hc).comp e hp
    intro f hf hz
    apply ht f hf
    intro ib
    have hz' := hz (Fin.insertNth 0 ib.1 ib.2)
    convert hz' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    dsimp only
    congr 1
    rw [Fin.prod_univ_succAbove _ 0]
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.tail]

theorem orthonormal_subtype_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [SecondCountableTopology E] {s : Set E}
    (hs : Orthonormal ℂ (Subtype.val : s → E)) : Countable s := by
  have : DiscreteTopology s := DiscreteTopology.of_forall_le_dist (r := 1) (by norm_num) (by
    intro x y hxy
    have he : ‖(x : E) - y‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hs.1 x, hs.1 y, hs.inner_eq_zero hxy]
      norm_num
    change 1 ≤ dist (x : E) (y : E)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((x : E) - y)])
  exact countable_of_Lindelof_of_discrete

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_BlockIndex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb

lemma joinConfiguration_measurePreserving (m k : ℕ) :
    MeasurePreserving (joinConfiguration m k).toHomeomorph.toMeasurableEquiv
      (volume.prod volume) volume := by
  have h1 := WithLp.volume_preserving_toLp (Configuration m) (Configuration k)
  have h2 := (PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : (Fin m × Fin 3) ⊕ (Fin k × Fin 3) => ℝ)).symm.measurePreserving
  have h3 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).measurePreserving
  exact h3.comp (h2.comp h1)

lemma joinConfiguration_left (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin m) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.castAdd k i,b) = x (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right (m k : ℕ) (x : Configuration m) (y : Configuration k)
    (i : Fin k) (b : Fin 3) :
    joinConfiguration m k (x,y) (Fin.natAdd m i,b) = y (i,b) := by
  simp [joinConfiguration, blockIndex, EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

lemma joinConfiguration_right_single (m k : ℕ) (a : Fin k × Fin 3) :
    joinConfiguration m k (0, EuclideanSpace.single a 1) =
      EuclideanSpace.single (Fin.natAdd m a.1, a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [joinConfiguration_left]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (m+k) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
  · intro j
    rw [joinConfiguration_right]
    simp [PiLp.single_apply, Prod.ext_iff]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_OrbitalHilbertBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

theorem hilbertBasis_parseval {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : HilbertBasis ι ℂ E) (f : E) :
    (∑' i, ‖inner ℂ (b i) f‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (b.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h.symm

lemma orbitalHilbertBasis_apply {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (i : ι) :
    orbitalHilbertBasis v hv ho hc i = (hv i).toLp (v i) := by
  simp only [orbitalHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem completeOrbitals_parseval {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (f : A → ℂ) (hf : MemLp f 2 μ) :
    (∑' i, ‖∫ a, star (v i a) * f a ∂μ‖ ^ 2) = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have h := hilbertBasis_parseval (orbitalHilbertBasis v hv ho hc) (hf.toLp f)
  simpa only [orbitalHilbertBasis_apply, inner_toLp_complex, norm_toLp_sq_complex] using h

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma scalarTensor_inner_integral {n : ℕ} (v : ι → A → ℂ) (b c : Fin n → ι) :
    (∫ x : Fin n → A, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = ∏ i, ∫ a, star (v (b i) a) * v (c i) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i a => star (v (b i) a) * v (c i) a)

lemma scalarTensor_orthonormal {n : ℕ} (v : ι → A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    ∀ b c : Fin n → ι, (∫ x, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = if b = c then (1 : ℂ) else 0 := by
  intro b c
  rw [scalarTensor_inner_integral]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma scalarCoefficient_antisymmetric {n : ℕ} {f : (Fin n → A) → ℂ}
    (hf : ProductAntisymmetric (μ := μ) f) (v : ι → A → ℂ) :
    FermionicCoefficients (scalarCoefficient (μ := μ) f v) := by
  intro p b
  unfold scalarCoefficient
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) p.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ => A) p.symm :
      (Fin n → A) → (Fin n → A)) = fun x => x ∘ p := by
    funext x i
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => A) p.symm x (p i))
  rw [← hp.integral_comp' (fun x => star (∏ i, v ((b ∘ p) i) (x i)) * f x), he,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hf p] with x hx
  simp only [Function.comp_apply, hx]
  rw [Equiv.prod_comp p (fun i => v (b i) (x i))]
  ring

theorem scalarCoefficient_parseval [Countable ι] {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) :
    (∑' b : Fin n → ι, ‖scalarCoefficient (μ := μ) f v b‖^2) =
      ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have ht := completeOrbitals_parseval (μ := Measure.pi fun _ : Fin n => μ)
    (fun (b : Fin n → ι) (x : Fin n → A) => ∏ i, v (b i) (x i))
    (scalarTensor_memLp v hv) (by
      intro b c
      have h := scalarTensor_orthonormal (μ := μ) v ho b c
      by_cases he : b = c <;> simpa only [he, ite_true, if_true, ite_false, if_false] using h)
    (completeOrbitals_finPi v hv hc n) f hf
  simpa only [scalarCoefficient] using ht

lemma scalarCoefficient_summable {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    Summable (fun b : Fin n → ι => ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  have ho' : Orthonormal ℂ (fun b : Fin n → ι =>
      (scalarTensor_memLp v hv b).toLp (fun x : Fin n → A => ∏ i, v (b i) (x i))) := by
    rw [orthonormal_iff_ite]
    intro b c
    rw [inner_toLp_complex]
    exact scalarTensor_orthonormal v ho b c
  have hs := ho'.inner_products_summable (hf.toLp f)
  simpa only [inner_toLp_complex, scalarCoefficient] using hs

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_HilbertBasisContaining
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma scalarCoefficient_contract {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) (a : ι) (b : Fin n → ι) :
    scalarCoefficient (μ := μ) f v (Fin.cons a b) =
      scalarCoefficient (μ := μ)
        (fiberContract (μ := μ) (v a) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1))) v b := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans (Measure.measurePreserving_swap)
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  have hf' : MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
    simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)
  unfold scalarCoefficient
  rw [← (he.symm e).integral_comp']
  simp only [hcons]
  have hprod (z : (Fin n → A) × A) :
      (∏ i : Fin (n+1), v ((Fin.cons a b : Fin (n+1) → ι) i)
        ((Fin.cons z.2 z.1 : Fin (n+1) → A) i)) =
        (∏ i : Fin n, v (b i) (z.1 i)) * v a z.2 := by
    rw [Fin.prod_univ_succ]
    simp [mul_comm]
  simp only [hprod]
  exact integral_tensorPair (scalarTensor_memLp v hv b) (hv a) hf'

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_TsumFixed
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma tsum_fixed_zero {ι : Type*} {n : ℕ} (f : (Fin (n+1) → ι) → ℝ) (a : ι) :
    (∑' b : Fin (n+1) → ι, if b 0 = a then f b else 0) =
      ∑' c : Fin n → ι, f (Fin.cons a c) := by
  have hinj : Function.Injective (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro c d h
    funext i
    exact congrFun h i.succ
  have hs : Function.support (fun b : Fin (n+1) → ι => if b 0 = a then f b else 0) ⊆
      Set.range (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro b hb
    have ha : b 0 = a := by
      by_contra hh
      exact hb (ite_eq_right hh)
    exact ⟨Fin.tail b, by simpa only [← ha] using Fin.cons_self_tail b⟩
  simpa only [Fin.cons_zero, ite_true, if_true] using (hinj.tsum_eq hs).symm

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include ho in
lemma orbital_orthonormal : Orthonormal ℂ (fun i => (hv i).toLp (v i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_complex]
  exact ho i j

lemma orbital_sum_toLp (s : Finset ι) (c : ι → ℂ) :
    (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) =
      ∑ i ∈ s, c i • (hv i).toLp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    have he : (fun x => ∑ i ∈ insert a s, c i * v i x) =
        (fun x => c a * v a x) + (fun x => ∑ i ∈ s, c i * v i x) := by
      funext x
      simp [Finset.sum_insert ha]
    rw [show (orbital_sum_memLp v hv (insert a s) c).toLp _ =
      ((hv a).const_mul (c a)).toLp (fun x => c a * v a x) +
      (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) from by
        simpa only [he] using ((hv a).const_mul (c a)).toLp_add
          (orbital_sum_memLp v hv s c)]
    rw [ih, Finset.sum_insert ha]
    congr 1

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_ThomasFermi_FirstFiber
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma firstFiber_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ} (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    MemLp (firstFiber f) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  change MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2 _
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb
lemma measurePreserving_const_uncurry {I J A : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry I J A).symm
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  refine ⟨(MeasurableEquiv.curry I J A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(MeasurableEquiv.curry I J A).symm.map_apply]
  have he : (MeasurableEquiv.curry I J A).symm ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, MeasurableEquiv.curry_symm_apply]
    exact ⟨fun h i j => h (i,j), fun h p => h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

lemma measure_pi_count {I A : Type*} [Fintype I] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (Measure.pi fun _ : I => (Measure.count : Measure A)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_CoreSliceRegular
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma ae_all_zero_of_continuous {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (A : X → T → ℂ) (hc : ∀ x, Continuous (A x))
    (hz : ∀ t, ∀ᵐ x ∂μ, A x t = 0) : ∀ᵐ x ∂μ, ∀ t, A x t = 0 := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense T
  have hDz : ∀ᵐ x ∂μ, ∀ t ∈ D, A x t = 0 := (ae_ball_iff hD).mpr (fun t _ => hz t)
  filter_upwards [hDz] with x hx
  have he : A x = fun _ => 0 := Continuous.ext_on hdense (hc x) continuous_const hx
  intro t
  exact congrFun he t

section SmoothSlices
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compact_tensor_test {χ : E → ℝ} {φ : F → ℝ}
    (hχ : HasCompactSupport χ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z : E × F => χ z.1 * φ z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hχ.prod hφ)
  intro z hz
  simp only [Function.mem_support, mul_ne_zero_iff] at hz
  exact ⟨subset_tsupport _ hz.1, subset_tsupport _ hz.2⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma tensor_test_deriv {χ : E → ℝ} {φ : F → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : F) (z : E × F) :
    fderiv ℝ (fun z : E × F => χ z.1 * φ z.2) z (0, v) =
      χ z.1 * fderiv ℝ φ z.2 v := by
  have h1 := (hχ.differentiable (by simp) z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hφ.differentiable (by simp) z.2).hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ))
  change (fderiv ℝ ((χ ∘ Prod.fst) * (φ ∘ Prod.snd)) z) (0,v) = _
  rw [(h1.mul h2).fderiv]
  simp

omit [SigmaFinite (volume : Measure E)] in
lemma test_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hφC.comp_left (by simp))

omit [SigmaFinite (volume : Measure E)] in
lemma test_direction_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) (v : E) :
    MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))

lemma weak_slice_fixed_test {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume)))
    (φ : F → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    ∀ᵐ x ∂(volume : Measure E),
      (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  let dφ : F → ℂ := fun y => (fderiv ℝ φ y v : ℂ)
  let cφ : F → ℂ := fun y => (φ y : ℂ)
  have hd := test_direction_complex_memLp hφ hφC v
  have hc := test_complex_memLp hφ hφC
  let A := fiberContract (μ := volume) dφ u
  let B := fiberContract (μ := volume) cφ g
  have hA : MemLp A 2 volume := fiberContract_memLp hd hu
  have hB : MemLp B 2 volume := fiberContract_memLp hc hg
  have hzero : ∀ᵐ x ∂(volume : Measure E), (A + B) x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hA.add hB).locallyIntegrable (by norm_num))
    intro χ hχ hχC
    have hχL := test_complex_memLp hχ hχC
    have H := hw (fun z => χ z.1 * φ z.2)
      ((hχ.comp contDiff_fst).mul (hφ.comp contDiff_snd)) (compact_tensor_test hχC hφC)
    simp_rw [tensor_test_deriv hχ hφ v, Complex.ofReal_mul] at H
    have H1 := integral_tensorPair hχL hd hu
    have H2 := integral_tensorPair hχL hc hg
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal] at H1 H2
    have L1 : (∫ z, u z * ((χ z.1 : ℂ) * (fderiv ℝ φ z.2 v : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * A x := by
      simpa only [A, dφ, mul_comm] using H1
    have L2 : (∫ z, g z * ((χ z.1 : ℂ) * (φ z.2 : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * B x := by
      simpa only [B, cφ, mul_comm] using H2
    rw [L1, L2] at H
    change (∫ x, (χ x) • (A x + B x)) = 0
    simp_rw [Complex.real_smul, mul_add]
    have hIntA : Integrable (fun x => (χ x : ℂ) * A x) := hχL.integrable_mul hA
    have hIntB : Integrable (fun x => (χ x : ℂ) * B x) := hχL.integrable_mul hB
    rw [integral_add hIntA hIntB, H, neg_add_cancel]
  filter_upwards [hzero] with x hx
  simpa only [Pi.add_apply, A, B, fiberContract, dφ, cφ,
    Complex.star_def, Complex.conj_ofReal, mul_comm, add_eq_zero_iff_eq_neg] using hx

lemma weak_slice {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume))) :
    ∀ᵐ x ∂(volume : Measure E),
      MemLp (fun y => u (x,y)) 2 volume ∧ MemLp (fun y => g (x,y)) 2 volume ∧
      ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)) := ⟨by norm_num⟩
  have : SecondCountableTopology F :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm :
      F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ)).toHomeomorph.secondCountableTopology
  let Tests := {φ : F → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  let Q : Tests → Lp ℂ 2 (volume : Measure F) × Lp ℂ 2 (volume : Measure F) := fun φ =>
    ⟨(test_direction_complex_memLp φ.2.1 φ.2.2 v).toLp _,
      (test_complex_memLp φ.2.1 φ.2.2).toLp _⟩
  let T := Set.range Q
  let U : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => u (x,y)) 2 volume then h.toLp _ else 0
  let G : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => g (x,y)) 2 volume then h.toLp _ else 0
  let A : E → T → ℂ := fun x t => inner ℂ t.1.1 (U x) + inner ℂ t.1.2 (G x)
  have hAc (x : E) : Continuous (A x) :=
    ((continuous_fst.comp continuous_subtype_val).inner continuous_const).add
      ((continuous_snd.comp continuous_subtype_val).inner continuous_const)
  have hAQ (x : E) (hx : MemLp (fun y => u (x,y)) 2 volume)
      (hxg : MemLp (fun y => g (x,y)) 2 volume) (φ : Tests) :
      A x ⟨Q φ, mem_range_self _⟩ =
        (∫ y, u (x,y) * (fderiv ℝ φ.1 y v : ℂ)) + (∫ y, g (x,y) * (φ.1 y : ℂ)) := by
    dsimp only [A, Q]
    simp only [U, G, dite_eq_left hx, dite_eq_left hxg]
    rw [inner_toLp_complex, inner_toLp_complex]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]
  have hAz (t : T) : ∀ᵐ x ∂(volume : Measure E), A x t = 0 := by
    rcases t with ⟨_, φ, rfl⟩
    filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg,
      weak_slice_fixed_test hu hg v hw φ.1 φ.2.1 φ.2.2] with x hx hxg hweak
    rw [hAQ x hx hxg φ, hweak, neg_add_cancel]
  have hall := ae_all_zero_of_continuous A hAc hAz
  filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg, hall] with x hx hxg hall
  refine ⟨hx, hxg, ?_⟩
  intro φ hφ hφC
  have H := hall ⟨Q ⟨φ, hφ, hφC⟩, mem_range_self _⟩
  rw [hAQ x hx hxg] at H
  exact add_eq_zero_iff_eq_neg.mp H

end SmoothSlices
section LinearChange
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

lemma weak_directional_change {u g : F → ℂ} (L : E ≃L[ℝ] F)
    (hL : MeasurePreserving L.toHomeomorph.toMeasurableEquiv μ ν) (v : E)
    (hw : ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, u y * (fderiv ℝ φ y (L v) : ℂ) ∂ν) = -(∫ y, g y * (φ y : ℂ) ∂ν)) :
    ∀ (η : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x, u (L x) * (fderiv ℝ η x v : ℂ) ∂μ) =
        -(∫ x, g (L x) * (η x : ℂ) ∂μ) := by
  intro η hη hηC
  let Φ : F → ℝ := η ∘ L.symm
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hη.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hηC.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : F) : fderiv ℝ Φ y (L v) = fderiv ℝ η (L.symm y) v := by
    dsimp only [Φ]
    rw [fderiv_comp y (hη.differentiable (by simp)).differentiableAt L.symm.differentiableAt,
      show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearMap from
        L.symm.toContinuousLinearMap.fderiv]
    simp
  have H := hw Φ HΦ HC
  simp_rw [Hd] at H
  rw [← hL.integral_comp' (fun y => u y * (fderiv ℝ η (L.symm y) v : ℂ)),
    ← hL.integral_comp' (fun y => g y * (Φ y : ℂ))] at H
  simpa [Φ] using H
end LinearChange

lemma H1Vector.weak_partial_join {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins (m+k)) (a : Fin k × Fin 3) :
    ∀ (η : Configuration m × Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η →
      (∫ z, ψ.value s (joinConfiguration m k z) *
        (fderiv ℝ η z (0, EuclideanSpace.single a 1) : ℂ) ∂(volume.prod volume)) =
      -(∫ z, ψ.gradient s (Fin.natAdd m a.1, a.2) (joinConfiguration m k z) *
        (η z : ℂ) ∂(volume.prod volume)) := by
  apply weak_directional_change (joinConfiguration m k) (joinConfiguration_measurePreserving m k)
    (0, EuclideanSpace.single a 1)
  rw [joinConfiguration_right_single]
  exact ψ.weak_partial s (Fin.natAdd m a.1, a.2)

lemma H1Vector.core_slices_H1 {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂(volume : Measure (Configuration m)),
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ))) := by
  have hV (t : Spins k) := (ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)
  have hG (t : Spins k) (a : Fin k × Fin 3) :=
    (ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
      (joinConfiguration_measurePreserving m k)
  have hval : ∀ᵐ x ∂(volume : Measure (Configuration m)),
      ∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume :=
    ae_all_iff.mpr (fun t => memLp_fiber_ae
      (f := fun z : Configuration m × Configuration k =>
        ψ.value (Fin.append s t) (joinConfiguration m k z)) (hV t))
  have hgrad := fun (t : Spins k) (a : Fin k × Fin 3) =>
    weak_slice (hV t) (hG t a) (EuclideanSpace.single a 1)
      (ψ.weak_partial_join (Fin.append s t) a)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (hgrad t))
  filter_upwards [hval, hall] with x hx hall
  exact ⟨hx, fun t a => (hall t a).2⟩

lemma H1Vector.coreSliceRegular_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂volume, ψ.CoreSliceRegular s x := ψ.core_slices_H1 s

lemma H1Vector.coreSlice_value {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (y : Configuration k) :
    (ψ.coreSlice s x).value t y = ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma H1Vector.coreSlice_gradient {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (a : Fin k × Fin 3)
    (y : Configuration k) :
    (ψ.coreSlice s x).gradient t a y =
      ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma mass_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => mass (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [mass, ψ.coreSlice_value s hx]

lemma mass_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (mass_coreSlice_ae ψ s).symm
  apply integrable_finsetSum
  intro t _
  have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
  exact h.integral_prod_left

lemma integral_mass_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x)) = mass ψ := by
  calc
    _ = ∑ s : Spins m, ∑ t : Spins k, ∫ z, ‖ψ.value (Fin.append s t) z‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_congr_ae (mass_coreSlice_ae ψ s), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
        change Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at h
        rw [← integral_prod _ h]
        exact (joinConfiguration_measurePreserving m k).integral_comp'
          (fun z => ‖ψ.value (Fin.append s t) z‖^2)
      · intro t _
        exact (((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow
            (p := 2) (by decide)).integral_prod_left
    _ = mass ψ := by
      rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
        ∫ z, ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
      exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CorePerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma kinetic_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => kinetic (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ y, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [kinetic, ψ.coreSlice_gradient s hx]

lemma kinetic_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => kinetic (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (kinetic_coreSlice_ae ψ s).symm
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro a _
  exact (((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)).integral_prod_left

lemma integral_kinetic_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2 := by
  have hs (s : Spins m) : (∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2 := by
    rw [integral_congr_ae (kinetic_coreSlice_ae ψ s), integral_const_mul]
    congr 1
    have hi (t : Spins k) (a : Fin k × Fin 3) :
        Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k z)‖^2)
          (volume.prod volume) :=
      ((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
        (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun a _ => (hi t a).integral_prod_left))]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum _ (fun a _ => (hi t a).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_prod _ (hi t a)]
    exact (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2)
  simp_rw [hs]
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∑ a : Fin k × Fin 3, ∫ z, ‖ψ.gradient (Fin.append st.1 st.2) (Fin.natAdd m a.1,a.2) z‖^2)]
  congr 1
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Pullback
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace Coulomb

lemma mass_pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : mass (ψ.pullback L) = mass ψ := by
  unfold mass H1Vector.pullback
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp' (fun x => ‖ψ.value s x‖^2)

noncomputable section

lemma permutationIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permutationIsometry p x = permute p x := by
  ext ⟨i,b⟩
  simp [permutationIsometry, permute, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permutationIsometry_single {n : ℕ} (p : Equiv.Perm (Fin n)) (a : Fin n × Fin 3) :
    permutationIsometry p (EuclideanSpace.single a 1) =
      EuclideanSpace.single (p.symm a.1,a.2) 1 := by
  rw [permutationIsometry_apply]
  ext ⟨i,b⟩
  simp [permute, PiLp.single_apply, Prod.ext_iff, ← Equiv.eq_symm_apply]

lemma permutation_value {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    (u.permutation p).value s x = u.value (s ∘ p) (permute p x) := by
  simp [H1Vector.permutation, H1Vector.pullback, permutationIsometry_apply]

lemma permutation_gradient {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (a : Fin n × Fin 3) (x : Configuration n) :
    (u.permutation p).gradient s a x =
      u.gradient (s ∘ p) (p.symm a.1,a.2) (permute p x) := by
  change (∑ k, ((permutationIsometry p (EuclideanSpace.single a 1)) k : ℂ) *
    u.gradient (s ∘ p) k (permutationIsometry p x)) = _
  rw [permutationIsometry_single, permutationIsometry_apply]
  simp [PiLp.single_apply, apply_ite]

end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_WedgeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
lemma mass_permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    mass (u.permutation p) = mass u := by
  calc
    _ = mass (u.pullback (permutationIsometry p)) := by
      unfold mass
      change (∑ s, ∫ x, ‖(u.pullback (permutationIsometry p)).value (permutationSpins p s) x‖^2) = _
      exact Equiv.sum_comp (permutationSpins p) (fun s => ∫ x, ‖(u.pullback (permutationIsometry p)).value s x‖^2)
    _ = _ := mass_pullback _ _
lemma antisymmetric_scale {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u) (c : ℂ) :
    Antisymmetric (u.scale c) := by
  intro p s
  filter_upwards [hu p s] with x hx
  change c*u.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ)*(c*u.value s x)
  rw [hx]
  ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_CoreKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma potentialForm_coreSlice_parameter_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration m → Configuration k → ℝ) :
    (fun x => potentialForm (V x) (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V x y * ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.coreSlice_value s hx]

lemma potentialForm_coreSlice_parameter_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins m) (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)) :
    Integrable (fun x => potentialForm (V x) (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (potentialForm_coreSlice_parameter_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
    (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  change Integrable (fun z : Configuration m × Configuration k =>
    V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
        ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
  simp only [ContinuousLinearEquiv.symm_apply_apply] at H
  exact H.integral_prod_left

lemma integral_potentialForm_coreSlice_parameter {m k : ℕ} (ψ : H1Vector (m+k))
    (V : Configuration m → Configuration k → ℝ)
    (hV : ∀ st : Spins (m+k), Integrable (fun z =>
      V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ st : Spins (m+k), ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm (V x) (ψ.coreSlice s x)) =
      ∑ t : Spins k, ∫ z,
        V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
          ‖ψ.value (Fin.append s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_coreSlice_parameter_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.1 z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
        (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (Fin.append s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
        ‖ψ.value (Fin.append s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).1
          ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 *
      ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreOrbitalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the one-particle projection estimate over the other electron
coordinates. Slices belong to the full weak-H1 domain almost everywhere. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1_inner_orbital {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (φ : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℂ φ (h1Coordinates u (Sum.inl s)) =
      ∫ x, star (φ x)*u.value s x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp] with x hx
  change h1Coordinates u (Sum.inl s) x = u.value s x at hx
  rw [hx,RCLike.inner_apply]
  exact mul_comm _ _

theorem coreOrbitalCoefficient_memLp {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) :
    MemLp (coreOrbitalCoefficient u φ s t) 2 :=
  Coulomb.fiberContract_memLp (Lp.memLp φ)
    ((u.value_L2 (Fin.append s t)).comp_measurePreserving
      (Coulomb.joinConfiguration_measurePreserving n 1))

theorem core_graphOrbitalMass_ae {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) :
    (fun x => graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))) =ᵐ[volume]
      fun x => ∑ t, ∑ i, ‖coreOrbitalCoefficient u (φ i) s t x‖^2 := by
  filter_upwards [u.coreSliceRegular_ae s] with x hx
  simp only [graphOrbitalMass,h1_inner_orbital,u.coreSlice_value s hx,
    coreOrbitalCoefficient]

theorem core_graphOrbitalMass_integrable {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) :
    Integrable (fun x => graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))) := by
  apply Integrable.congr _ (core_graphOrbitalMass_ae u φ s).symm
  exact integrable_finsetSum _ (fun t _ => integrable_finsetSum _
    (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq))

theorem coreOrbitalMass_eq_coefficients {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass u φ = ∑ s, ∑ t, ∑ i, ∫ x, ‖coreOrbitalCoefficient u (φ i) s t x‖^2 := by
  unfold coreOrbitalMass
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_congr_ae (core_graphOrbitalMass_ae u φ s),
    integral_finsetSum _ (fun t _ => integrable_finsetSum _
      (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq))]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_finsetSum _
    (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq)

theorem bounded_state_potential_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B) (s : SpinConfiguration n) :
    Integrable (fun x => V x*‖u.value s x‖^2) := by
  apply ((u.value_L2 s).norm.integrable_sq.const_mul B).mono'
    (hV.aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  change ‖V x*‖u.value s x‖^2‖ ≤ B*‖u.value s x‖^2
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u.value s x‖)]
  exact mul_le_mul_of_nonneg_right (hB x) (sq_nonneg _)

theorem coreOneBody_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector (n+1)) :
    E*Coulomb.mass u-κ*coreOrbitalMass u φ ≤ Coulomb.coreKinetic u+
      Coulomb.potentialForm (fun z => V ((Coulomb.joinConfiguration n 1).symm z).2) u := by
  have hip (st : SpinConfiguration (n+1)) : Integrable
      (fun z => V ((Coulomb.joinConfiguration n 1).symm z).2*‖u.value st z‖^2) :=
    bounded_state_potential_integrable u _
      (hV.comp ((Coulomb.joinConfiguration n 1).symm.continuous.snd)) B (fun z => hB _) st
  have hp (s : SpinConfiguration n) :=
    Coulomb.potentialForm_coreSlice_parameter_integrable u s (fun _ y => V y)
      (fun t => hip (Fin.append s t))
  have hs (s : SpinConfiguration n) := integral_mono
    (((Coulomb.mass_coreSlice_integrable u s).const_mul E).sub
      ((core_graphOrbitalMass_integrable u φ s).const_mul κ))
    ((Coulomb.kinetic_coreSlice_integrable u s).add (hp s))
    (fun x => hbound (u.coreSlice s x))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs s)
  simp only [Pi.sub_apply,Pi.add_apply] at hh
  simp_rw [integral_sub ((Coulomb.mass_coreSlice_integrable u _).const_mul E)
    ((core_graphOrbitalMass_integrable u φ _).const_mul κ),integral_const_mul,
    integral_add (Coulomb.kinetic_coreSlice_integrable u _) (hp _)] at hh
  have hpot := Coulomb.integral_potentialForm_coreSlice_parameter u (fun _ y => V y) hip
  simp only [Coulomb.potentialForm] at hpot
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Coulomb.integral_mass_coreSlice,Coulomb.integral_kinetic_coreSlice,
    coreOrbitalMass,Coulomb.coreKinetic,Coulomb.potentialForm,hpot] using hh

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PairRegroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma integrable_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure E} (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) : Integrable f (Measure.count.prod μ) := by
  rw [Measure.prod, Measure.count,
    Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  simp only [Measure.dirac_bind (measurable_of_countable _)]
  refine integrable_sum_measure (fun spin => ?_) (hasSum_fintype _).summable
  exact (measurableEmbedding_prodMk_left spin).integrable_map_iff.mpr (hf spin)

lemma integral_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure E} [SFinite μ] (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) :
    (∫ sx, f sx ∂(Measure.count.prod μ)) = ∑ s, ∫ x, f (s,x) ∂μ := by
  rw [integral_prod _ (integrable_finite_count_prod f hf), integral_count]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma spinCubeEquiv_full_measurePreserving (n : ℕ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinSpaceMeasure)
      (Measure.count.prod volume) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => volume)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume : Measure ℝ))
  exact h2.comp h1

lemma H1Vector.spinSpace_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.value sx.1 (WithLp.toLp 2 sx.2)) 2 (Measure.count.prod volume) := by
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ => tensorPair_memLp (hi s)
    ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma H1Vector.cubeState_full_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinSpaceMeasure) :=
  ψ.spinSpace_memLp.comp_measurePreserving (spinCubeEquiv_full_measurePreserving n)

lemma cubeState_full_mass {n : ℕ} (ψ : H1Vector n) :
    (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ := by
  change (∫ z, ‖ψ.value ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)‖^2
    ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => ‖ψ.value sx.1 (WithLp.toLp 2 sx.2)‖^2)]
  rw [integral_prod _ ψ.spinSpace_memLp.norm.integrable_sq, integral_count]
  unfold mass
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.value s x‖^2)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_SmoothCompact
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma flatSpinOrbital_memLp (v : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume) :
    MemLp (flatSpinOrbital v) 2 spinSpaceMeasure := by
  change MemLp (flatSpinOrbital v) 2 (Measure.count.prod volume)
  have hi (s : Fin 2) : MemLp (fun t : Fin 2 => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Fin 2) _ => tensorPair_memLp (hi s)
    ((hv s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp [flatSpinOrbital, ite_mul]

lemma flatSpinOrbital_inner (v u : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume)
    (hu : ∀ s, MemLp (fun x => u x s) 2 volume) :
    (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂spinSpaceMeasure) =
      ∑ s : Fin 2, ∫ x : Space, star (v x s) * u x s := by
  have hI := (flatSpinOrbital_memLp v hv).star.integrable_mul (flatSpinOrbital_memLp u hu)
  change Integrable (fun a => star (flatSpinOrbital v a) * flatSpinOrbital u a)
    (Measure.count.prod volume) at hI
  change (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hI, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => star (v x s) * u x s)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_DensitySynthesis
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative continuous-density synthesis for the unit-charge construction

The density is the uniform slab plus `ΔV/(4π)`. Compact support of `V`
inside the slab makes its attractive Coulomb field exactly the slab field
plus `V`. A pointwise Laplacian bound makes the density nonnegative.
Only C² regularity is required, as the manuscript's manufactured well is
finitely smooth.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabDensity_integral (rho H S : ℝ) :
    (∫ x, slabDensity rho H S x) = volume.real (slabDomain H S) * rho := by
  exact integral_indicator_const rho (slabDomain_isClosed H S).measurableSet

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SpinConfigurationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinConfiguration_integral {n : ℕ} (F : Spins n → Configuration n → ℝ)
    (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_CorrectionDensity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem translated_kernel_indicator_eq (x : Position) (r : ℝ) :
    (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) =
      (fun y => (Metric.ball (0 : Position) r).indicator coulombKernel (x-y)) := by
  ext y
  have hh : x-y ∈ Metric.ball (0 : Position) r ↔ y ∈ Metric.ball x r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x r <;> simp [hh, hy]

theorem translated_kernel_indicator_integrable (x : Position) (r : ℝ) :
    Integrable ((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) := by
  rw [translated_kernel_indicator_eq]
  exact (integrable_comp_sub_left
    ((Metric.ball (0 : Position) r).indicator coulombKernel) x).mpr
      ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

theorem translated_kernel_indicator_integral (x : Position) (r : ℝ) :
    (∫ y, (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) y) =
      kernelBallMass r := by
  rw [translated_kernel_indicator_eq, integral_sub_left_eq_self,
    integral_indicator measurableSet_ball]
  rfl

theorem potential_integrable_and_bound {ρ : Position → ℝ} {x : Position} {r A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hr : 0 < r)
    (hloc : ∀ y ∈ Metric.ball x r, ρ y ≤ A) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ A*kernelBallMass r+r⁻¹*(∫ y, ρ y) := by
  let b : Position → ℝ := fun y =>
    A*((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) y+r⁻¹*ρ y
  have hb : Integrable b :=
    ((translated_kernel_indicator_integrable x r).const_mul A).add (hρ.const_mul r⁻¹)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ b y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · simp only [b, Set.indicator_of_mem hy]
      exact (mul_le_mul_of_nonneg_left (hloc y hy) (coulombKernel_nonneg _)).trans
        (by nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) (hpos y)])
    · simp only [b, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hd : r ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hd) (hpos y)
  have hprod : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi : Integrable (fun y => coulombKernel (x-y)*ρ y) := hb.mono' hprod
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
      exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  dsimp [b]
  rw [integral_add ((translated_kernel_indicator_integrable x r).const_mul A) (hρ.const_mul r⁻¹),
    integral_const_mul, integral_const_mul, translated_kernel_indicator_integral]

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSharpDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharp exponential rate for the actual planar resolvent mode. Gaussian
exponential tilting gives a polynomial prefactor and decay `exp (-|r|)`, as
needed to bracket the contact hoppings at lengths `(1±ε)D`. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_tilt {t : ℝ} (ht : 0 < t) (e b : PlanarPosition) :
    planarHeatKernel t b * Real.exp (inner ℝ e b) =
      Real.exp (t * ‖e‖ ^ 2) * planarHeatKernel t (b - (2 * t) • e) := by
  have he : -‖b‖ ^ 2 / (4 * t) + inner ℝ e b =
      t * ‖e‖ ^ 2 + -‖b - (2 * t) • e‖ ^ 2 / (4 * t) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm b e]
    field_simp
    ring
  unfold planarHeatKernel
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem planarForcing_exponential_bound (e s : PlanarPosition) :
    planarForcing s ≤ Real.exp (‖e‖ - inner ℝ e s) := by
  by_cases hf : planarForcing s = 0
  · rw [hf]
    exact (Real.exp_pos _).le
  have hs : ‖s‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (norm_nonneg e))
  exact (planarForcing_le_one s).trans (Real.one_le_exp (by linarith))

theorem planarHeatForcing_tilt_bound {t : ℝ} (ht : 0 < t) (e r b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
  calc
    _ ≤ planarHeatKernel t b * Real.exp (‖e‖ - inner ℝ e (r - b)) :=
      mul_le_mul_of_nonneg_left (planarForcing_exponential_bound e (r - b))
        (planarHeatKernel_positive ht b).le
    _ = Real.exp (‖e‖ - inner ℝ e r) *
        (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
      rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
        (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
      ring
    _ = _ := by rw [planarHeatKernel_tilt ht]; ring

theorem planarHeatAverage_tilt_bound {t : ℝ} (ht : 0 < t) (e r : PlanarPosition) :
    planarHeatAverage t r ≤
      Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2) := by
  have hi := ((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
    (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tilt_bound ht e r)
  simpa only [planarHeatAverage, integral_const_mul, integral_sub_right_eq_self,
    planarHeatKernel_integral ht, mul_one] using h

theorem planarResolventMode_tilt_bound (e r : PlanarPosition) (he : ‖e‖ < 1) :
    planarResolventMode r ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ Real.exp (-t) * (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatAverage_tilt_bound ht e r) (Real.exp_pos _).le
        _ = Real.exp (‖e‖ - inner ℝ e r) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
          rw [show -(1 - ‖e‖ ^ 2) * t = -t + t * ‖e‖ ^ 2 by ring, Real.exp_add]
          ring)
  have heval : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 - ‖e‖ ^ 2) * t)) =
      (1 - ‖e‖ ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi (by linarith : -(1 - ‖e‖ ^ 2) < 0)]
    simp
    rw [show ‖e‖ ^ 2 - 1 = -(1 - ‖e‖ ^ 2) by ring, div_neg]
    simp only [neg_div, neg_neg, one_div]
  simpa only [integral_const_mul, heval, div_eq_mul_inv] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarExponentialEnvelope
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global exponential envelopes at every fixed rate below one, and
integrability of their planar radial envelopes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < planarExponentialConstant a := div_pos (Real.exp_pos _) (by nlinarith)

theorem planarResolventMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) : planarResolventMode r ≤ planarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have hd : 0 < 1 - a ^ 2 := by nlinarith
  by_cases hr : r = 0
  · subst r
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one]
    apply (planarResolventMode_le_one 0).trans
    apply (le_div_iff₀ hd).mpr
    have h := Real.one_le_exp ha
    nlinarith [sq_nonneg a]
  have hnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr
  let e : PlanarPosition := (a / ‖r‖) • r
  have he : ‖e‖ = a := by
    dsimp [e]
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha hnorm.le)]
    field_simp
  have hi : inner ℝ e r = a * ‖r‖ := by
    dsimp [e]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h := planarResolventMode_tilt_bound e r (by rw [he]; exact ha₁)
  rw [he, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarExponentialConstant
  rw [show a - a * ‖r‖ = a + -a * ‖r‖ by ring, Real.exp_add]
  ring

theorem exponential_inverse_cubic_bound {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * t) ≤ (1 + 3 / c) ^ 3 / (1 + t) ^ 3 := by
  have hq : 0 < c / 3 := by positivity
  have he := Real.add_one_le_exp (c / 3 * t)
  have ht' : t ≤ (3 / c) * Real.exp (c / 3 * t) := by
    have h : t * c ≤ 3 * Real.exp (c / 3 * t) := by nlinarith only [he]
    calc
      _ ≤ (3 * Real.exp (c / 3 * t)) / c := (le_div_iff₀ hc).mpr h
      _ = _ := by ring
  have h₁ : 1 ≤ Real.exp (c / 3 * t) := Real.one_le_exp (mul_nonneg hq.le ht)
  have hb : 1 + t ≤ (1 + 3 / c) * Real.exp (c / 3 * t) := by nlinarith only [ht', h₁]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hb 3
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have harg : (3 : ℝ) * (c / 3 * t) = c * t := by ring
  rw [harg] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-c * t)).le
  have hexp : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound : Real.exp (-c * t) * (1 + t) ^ 3 ≤ (1 + 3 / c) ^ 3 := by
    calc
      _ ≤ Real.exp (-c * t) * ((1 + 3 / c) ^ 3 * Real.exp (c * t)) := hm
      _ = _ := by rw [mul_left_comm, hexp, mul_one]
  exact (le_div_iff₀ (pow_pos (by linarith : 0 < 1 + t) 3)).mpr hbound

theorem planar_exp_norm_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun r : PlanarPosition => Real.exp (-c * ‖r‖)) := by
  have hi : Integrable (fun r : PlanarPosition => (1 + ‖r‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [PlanarPosition])
  apply (hi.const_mul ((1 + 3 / c) ^ 3)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun r => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg (by positivity)]
    simpa only [Real.rpow_ofNat, div_eq_mul_inv] using exponential_inverse_cubic_bound hc (norm_nonneg r))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarOverlap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized planar orbitals have overlap bounded at rate 0.9,
uniformly over every pair of centers. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < normalizedPlanarExponentialConstant a :=
  div_pos (planarExponentialConstant_positive ha ha₁)
    (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

theorem normalizedPlanarMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) :
    normalizedPlanarMode r ≤ normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have h := div_le_div_of_nonneg_right (planarResolventMode_exponential_envelope ha ha₁ r)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  convert h using 1 <;> first | rfl | (unfold normalizedPlanarExponentialConstant; ring)

theorem planarModeOverlap_integrable (u v : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)).integrable_mul
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume v))

theorem planarModeOverlap_nonnegative (u v : PlanarPosition) : 0 ≤ planarModeOverlap u v :=
  integral_nonneg (fun _ => mul_nonneg (normalizedPlanarMode_positive _).le (normalizedPlanarMode_positive _).le)

theorem planarModeOverlap_diagonal (u : PlanarPosition) : planarModeOverlap u u = 1 := by
  unfold planarModeOverlap
  simp_rw [← pow_two]
  rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized]

theorem planarModeOverlap_envelope {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha₁ : a < 1)
    (u v : PlanarPosition) :
    planarModeOverlap u v ≤
      (normalizedPlanarExponentialConstant a ^ 2 *
        (∫ r : PlanarPosition, Real.exp (-(a - b) * ‖r‖))) * Real.exp (-b * ‖u - v‖) := by
  have ha : 0 ≤ a := le_trans hb hba.le
  have hC := (normalizedPlanarExponentialConstant_positive ha ha₁).le
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤
        (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖)) *
          Real.exp (-(a - b) * ‖r - u‖) := by
    have ht : ‖u - v‖ ≤ ‖r - u‖ + ‖r - v‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r v
    have hs := mul_le_mul_of_nonneg_left ht hb
    have he : -a * (‖r - u‖ + ‖r - v‖) ≤ -b * ‖u - v‖ + -(a - b) * ‖r - u‖ := by
      nlinarith [mul_nonneg (sub_pos.mpr hba).le (norm_nonneg (r - v))]
    calc
      _ ≤ (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - u‖)) *
          (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - v‖)) :=
        mul_le_mul (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
      _ = normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-a * (‖r - u‖ + ‖r - v‖)) := by
        rw [show -a * (‖r - u‖ + ‖r - v‖) = -a * ‖r - u‖ + -a * ‖r - v‖ by ring,
          Real.exp_add]
        ring
      _ ≤ normalizedPlanarExponentialConstant a ^ 2 *
          Real.exp (-b * ‖u - v‖ + -(a - b) * ‖r - u‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  have hi := ((planar_exp_norm_integrable (sub_pos.mpr hba)).comp_sub_right u).const_mul
    (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖))
  have h := integral_mono (planarModeOverlap_integrable u v) hi hpt
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(a - b) * ‖r‖)) u] at h
  exact h.trans_eq (by ring)

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem planarModeOverlap_decay (u v : PlanarPosition) :
    planarModeOverlap u v ≤ planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  have h := planarModeOverlap_envelope (a := 19 / 20) (b := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) u v
  norm_num only [show (19 / 20 : ℝ) - 9 / 10 = 1 / 20 by norm_num] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transition densities of localized three-dimensional modes
have normalized mass bounds and exponentially small off-site L1 mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedTransition_mass {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, localizedTransition freq u v x) = planarModeOverlap u v := by
  change (∫ x, localizedMode freq u (positionSplitCoordinates x) *
    localizedMode freq v (positionSplitCoordinates x)) = _
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p * localizedMode freq v p)]
  have he : (fun p : SplitPosition => localizedMode freq u p * localizedMode freq v p) =
      (fun p => (normalizedPlanarMode (p.1 - u) * normalizedPlanarMode (p.1 - v)) * verticalMode freq p.2 ^ 2) := by
    funext p
    unfold localizedMode
    ring
  rw [he, Measure.volume_eq_prod, integral_prod_mul
    (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v))
    (fun z => verticalMode freq z ^ 2)]
  rw [verticalMode_normalized hfreq, mul_one]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombGramApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the actual manufactured-well inequality on the planar
Sobolev graph. The bounded potential acts on actual L² classes, and the
form is continuous in the function-and-gradient norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

namespace PlanarSobolev

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition
theorem wellBound_nonnegative : 0 ≤ wellBound :=
  (norm_nonneg (manufacturedPlanarWell 0)).trans (wellBound_spec 0)

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the actual sum of manufactured wells. Site
pieces see exactly their own well; the exterior piece sees zero potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWellField
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact three-dimensional well field in the unit-charge
construction. Its coefficients are Coulomb counterterms. The cutoff only weakens the attractive uncorrected wells. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem slabWellCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    slabWellCutoff S z = 0 := by
  apply verticalCutoffBump.zero_of_le_dist
  change 2 ≤ dist ((2/S)*z) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*S = (2:ℝ) := by field_simp
  exact he.symm.le.trans hm

theorem manufacturedWellField_outer (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : S ≤ |(positionSplitCoordinates x).2|) :
    manufacturedWellField freq scale S u x = 0 := by
  simp only [manufacturedWellField, slabWellCutoff_outer hS hx, zero_mul]

theorem countertermWellSum_zero_far (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition)
    (hr : ∀ i, 1 ≤ ‖r-u i‖) : countertermWellSum freq scale u r = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [manufacturedPlanarWell_zero_of_norm_ge_one (hr i), mul_zero]

theorem manufacturedWellField_support (freq scale : ℝ) {S R : ℝ}
    (hS : 0 < S) (hR : 0 ≤ R) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆
      Metric.closedBall (0 : Position) (R+S+1) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hr : ‖(positionSplitCoordinates x).1‖ < R+1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i => ?_), mul_zero]
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i, le_of_not_gt hn]
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs := positionSplitCoordinates_norm_sq x
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ R+1)).mpr hr.le
  have hz2 := (sq_le_sq₀ (abs_nonneg _) hS.le).mpr hz.le
  rw [sq_abs] at hz2
  nlinarith [norm_nonneg x]

theorem manufacturedWellField_compact (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    HasCompactSupport (manufacturedWellField freq scale S u) := by
  let R : ℝ := ∑ i, ‖u i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hu (i : Fin m) : ‖u i‖ ≤ R :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact (isCompact_closedBall (0 : Position) (R+S+1)).of_isClosed_subset
    (isClosed_tsupport _) (manufacturedWellField_support freq scale hS hR u hu)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarCutoffTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual site cutoff changes its normalized ground mode by an
exponentially small L2 vector. This controls the rank-one terms in IMS. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarSiteTailConstant_nonnegative : 0 ≤ planarSiteTailConstant := by
  unfold planarSiteTailConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (integral_nonneg (fun _ => (Real.exp_pos _).le))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarMultiwellScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed planar excitation gap for exponentially many separated sites.
The scale is chosen once from the isolated-well gap, independently of the
number of sites and the input instance. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarSiteDerivativeBound_tendsto :
    Tendsto planarSiteDerivativeBound atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.const_mul (6 : ℝ)).const_mul (Real.pi / 2)
  have h' := h.mul_const PlanarSobolev.cutoffGradBound
  change Tendsto (fun D : ℝ => (Real.pi / 2 * (6 / D)) * PlanarSobolev.cutoffGradBound)
    atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero, zero_mul] using h'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOrbitalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized L2 orbitals form a well-conditioned independent
family whenever the exponentially small pair overlaps have a small row sum.
In particular their finite span has an actual orthonormal basis. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_upper {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, A i i ≤ a)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (∑ i, ∑ j, A i j * d i * d j) ≤ (a + m * delta) * ∑ i, d i ^ 2 := by
  have h := dualMatrix_quadratic_lower (fun i j => -A i j) hdelta
    (fun i => neg_le_neg (hdiag i)) (fun i j hij => by simpa only [abs_neg] using hoff i j hij) d
  simp only [neg_mul, Finset.sum_neg_distrib] at h
  linarith

theorem localizedOverlapBound_nonnegative (D : ℝ) : 0 ≤ localizedOverlapBound D :=
  mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le

theorem planarModeOverlap_offsite {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) (hij : i ≠ j) :
    |planarModeOverlap (u i) (u j)| ≤ localizedOverlapBound D := by
  rw [abs_of_nonneg (planarModeOverlap_nonnegative _ _)]
  exact (planarModeOverlap_decay _ _).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) planarOverlapConstant_nonnegative)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume- and kinetic-energy-preserving identification of one-electron
configuration space with physical three-dimensional space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronCoordinates_symm_single (a : Fin 3) :
    oneElectronCoordinates.symm (EuclideanSpace.single a (1:ℝ)) =
      EuclideanSpace.single (0,a) 1 := by
  apply oneElectronCoordinates.injective
  rw [LinearIsometryEquiv.apply_symm_apply,oneElectronCoordinates_single]

theorem oneElectronCoordinates_integral (f : Position → ℝ) :
    (∫ x : Configuration 1, f (oneElectronCoordinates x)) = ∫ y, f y :=
  oneElectronCoordinates.measurePreserving.integral_comp
    oneElectronCoordinates.toHomeomorph.measurableEmbedding f

theorem oneElectronCoordinates_integral_complex (f : Position → ℂ) :
    (∫ x : Configuration 1, f (oneElectronCoordinates x)) = ∫ y, f y :=
  oneElectronCoordinates.measurePreserving.integral_comp
    oneElectronCoordinates.toHomeomorph.measurableEmbedding f

theorem oneElectronPullback_contDiff {f : Configuration 1 → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (oneElectronPullback f) := hf.comp oneElectronCoordinates.symm.contDiff

theorem oneElectronPullback_compact {f : Configuration 1 → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (oneElectronPullback f) :=
  hc.comp_homeomorph oneElectronCoordinates.symm.toHomeomorph

theorem oneElectronPullback_partial {f : Configuration 1 → ℂ} (hf : ContDiff ℝ 1 f)
    (a : Fin 3) (y : Position) :
    fderiv ℝ (oneElectronPullback f) y (EuclideanSpace.single a 1) =
      fderiv ℝ f (oneElectronCoordinates.symm y) (EuclideanSpace.single (0,a) 1) := by
  have h := ((hf.differentiable (by norm_num)) (oneElectronCoordinates.symm y)).hasFDerivAt.comp y
    oneElectronCoordinates.symm.toContinuousLinearEquiv.hasFDerivAt
  have he := congrArg (fun L => L (EuclideanSpace.single a 1)) h.fderiv
  unfold oneElectronPullback
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.coe_coe,
    oneElectronCoordinates_symm_single] using he

theorem oneElectronPullback_integral (g : Configuration 1 → ℝ) :
    (∫ y, g (oneElectronCoordinates.symm y)) = ∫ x, g x := by
  rw [← oneElectronCoordinates_integral (fun y => g (oneElectronCoordinates.symm y))]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem oneElectronPullback_integral_complex (g : Configuration 1 → ℂ) :
    (∫ y, g (oneElectronCoordinates.symm y)) = ∫ x, g x := by
  rw [← oneElectronCoordinates_integral_complex (fun y => g (oneElectronCoordinates.symm y))]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem oneElectronPullback_form (V : Position → ℝ) {f : Configuration 1 → ℂ}
    (hf : ContDiff ℝ 1 f) :
    positionComplexForm V (oneElectronPullback f) =
      (1/2:ℝ)*(∑ a : Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2)+
      ∫ x, V (oneElectronCoordinates x)*‖f x‖^2 := by
  unfold positionComplexForm positionComplexKinetic
  simp_rw [oneElectronPullback_partial hf]
  have hi (a : Fin 3) : (∫ y, ‖fderiv ℝ f (oneElectronCoordinates.symm y)
      (EuclideanSpace.single (0,a) 1)‖^2) =
      ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2 :=
    oneElectronPullback_integral (fun x => ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2)
  simp_rw [hi]
  congr 1
  have h := oneElectronPullback_integral
    (fun x => V (oneElectronCoordinates x)*‖f x‖^2)
  simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ElectronSlotBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-electron finite-rank lower bound acts on every electron slot.
All coordinate changes preserve the full spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem sum_electronSlotKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    (∑ i, electronSlotKinetic u i) = Coulomb.kinetic u := by
  unfold electronSlotKinetic Coulomb.kinetic
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp only [Fintype.sum_prod_type]

theorem coreKinetic_permutation_one {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (p : Equiv.Perm (Fin (n+1))) :
    Coulomb.coreKinetic (u.permutation p) = electronSlotKinetic u (p.symm (Fin.last n)) := by
  unfold Coulomb.coreKinetic electronSlotKinetic
  simp only [Coulomb.permutation_gradient,Fintype.sum_prod_type,Fin.sum_univ_one]
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext rfl
  have he (s : SpinConfiguration (n+1)) (a : Fin 3) :
      (∫ x, ‖u.gradient (s ∘ p) (p.symm (Fin.natAdd n (0 : Fin 1)),a) (Coulomb.permute p x)‖^2) =
        ∫ x, ‖u.gradient (s ∘ p) (p.symm (Fin.last n),a) x‖^2 := by
    simpa only [Coulomb.permutationIsometry_apply,hlast] using
      (Coulomb.permutationIsometry p).measurePreserving.integral_comp
        (Coulomb.permutationIsometry p).toHomeomorph.measurableEmbedding
        (fun x => ‖u.gradient (s ∘ p) (p.symm (Fin.last n),a) x‖^2)
  simp_rw [he]
  congr 1
  exact Equiv.sum_comp (Coulomb.permutationSpins p)
    (fun s => ∑ a : Fin 3, ∫ x, ‖u.gradient s (p.symm (Fin.last n),a) x‖^2)

theorem oneElectronCoordinates_core {n : ℕ} (x : Configuration (n+1)) :
    oneElectronCoordinates ((Coulomb.joinConfiguration n 1).symm x).2 =
      Coulomb.position x (Fin.last n) := by
  ext a
  have h := Coulomb.joinConfiguration_right n 1
    ((Coulomb.joinConfiguration n 1).symm x).1
    ((Coulomb.joinConfiguration n 1).symm x).2 (0 : Fin 1) a
  change ((Coulomb.joinConfiguration n 1).symm x).2 (0,a) = x (Fin.last n,a)
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext rfl
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,hlast] using h.symm

theorem corePotential_permutation_one {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (p : Equiv.Perm (Fin (n+1))) (V : Position → ℝ) :
    Coulomb.potentialForm (fun z => V (oneElectronCoordinates
      ((Coulomb.joinConfiguration n 1).symm z).2)) (u.permutation p) =
        Coulomb.potentialForm (fun x => V (Coulomb.position x (p.symm (Fin.last n)))) u := by
  simp only [Coulomb.potentialForm,Coulomb.permutation_value,oneElectronCoordinates_core]
  have he (s : SpinConfiguration (n+1)) :
      (∫ x, V (Coulomb.position x (Fin.last n))*‖u.value (s ∘ p) (Coulomb.permute p x)‖^2) =
        ∫ x, V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value (s ∘ p) x‖^2 := by
    have h := (Coulomb.permutationIsometry p).measurePreserving.integral_comp
      (Coulomb.permutationIsometry p).toHomeomorph.measurableEmbedding
      (fun x => V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value (s ∘ p) x‖^2)
    simpa only [Coulomb.permutationIsometry_apply,Coulomb.position,Coulomb.permute,
      Equiv.apply_symm_apply] using h
  simp_rw [he]
  exact Equiv.sum_comp (Coulomb.permutationSpins p)
    (fun s => ∫ x, V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value s x‖^2)

theorem electronSlot_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤
        boundedPotentialForm (fun x => V (oneElectronCoordinates x)) v)
    (u : Coulomb.H1Vector (n+1)) (i : Fin (n+1)) :
    E*Coulomb.mass u-κ*electronSlotOrbitalMass u φ i ≤ electronSlotKinetic u i+
      Coulomb.potentialForm (fun x => V (Coulomb.position x i)) u := by
  have h := coreOneBody_projection_lower _ (hV.comp oneElectronCoordinates.continuous)
    B (fun x => hB _) φ E κ hbound (u.permutation (Equiv.swap (Fin.last n) i))
  simp only [Function.comp_apply] at h
  rw [Coulomb.mass_permutation,coreKinetic_permutation_one,corePotential_permutation_one] at h
  simpa only [Equiv.symm_swap,Equiv.swap_apply_left,electronSlotOrbitalMass] using h

theorem manyElectron_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤
        boundedPotentialForm (fun x => V (oneElectronCoordinates x)) v)
    (u : Coulomb.H1Vector (n+1)) :
    (n+1:ℕ)*E*Coulomb.mass u-κ*totalOrbitalMass u φ ≤
      boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) u := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => electronSlot_projection_lower V hV B hB φ E κ hbound u i)
  have hi (s : SpinConfiguration (n+1)) (i : Fin (n+1)) :
      Integrable (fun x => V (Coulomb.position x i)*‖u.value s x‖^2) :=
    bounded_state_potential_integrable u _ (hV.comp (Coulomb.positionCLM i).continuous)
      B (fun x => hB _) s
  have hp : (∑ i, Coulomb.potentialForm (fun x => V (Coulomb.position x i)) u) =
      Coulomb.potentialForm (fun x => ∑ i, V (Coulomb.position x i)) u := by
    unfold Coulomb.potentialForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.sum_mul]
    exact (integral_finsetSum _ (fun i _ => hi s i)).symm
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_electronSlotKinetic,hp] at h
  simpa only [Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,
    totalOrbitalMass,boundedPotentialForm,
    Coulomb.potentialForm,mul_assoc] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalComplementCount
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coefficient array orthogonal to all tensors of the chosen orbitals
has at least one particle outside them. This counts particles, not basis
configurations, and so introduces no exponential dimension factor. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem complement_coefficient_pointwise {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0) (b : Fin (n+1) → α) :
    (∑ i, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤ (n:ℝ)*‖c b‖^2 := by
  by_cases hz : c b = 0
  · simp [hz]
  obtain ⟨j,hj⟩ : ∃ j, b j ∉ S := by
    by_contra! hh
    exact hz (hzero b hh)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),ite_eq_right hj,add_zero]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.erase j, ‖c b‖^2 :=
      Finset.sum_le_sum (fun i _ => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _)
    _ = _ := by simp

theorem complement_coefficient_occupation_sum {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0)
    (hs : Summable (fun b => ‖c b‖^2)) :
    (∑ i, ∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤
      (n:ℝ)*(∑' b, ‖c b‖^2) := by
  have hi (i : Fin (n+1)) : Summable (fun b => if b i ∈ S then ‖c b‖^2 else (0:ℝ)) :=
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _) hs
  rw [← Summable.tsum_finsetSum (fun i _ => hi i),← tsum_mul_left]
  exact Summable.tsum_le_tsum (complement_coefficient_pointwise S c hzero)
    (summable_sum (fun i _ => hi i)) (hs.mul_left (n:ℝ))

theorem coefficient_set_occupation_eq {α : Type*} {n : ℕ}
    {c : (Fin n → α) → ℂ} (hc : Coulomb.FermionicCoefficients c)
    (S : Set α) (i j : Fin n) :
    (∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) =
      ∑' b, if b j ∈ S then ‖c b‖^2 else (0:ℝ) := by
  let p := Equiv.swap i j
  have he := (Coulomb.coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => if b i ∈ S then ‖c b‖^2 else (0:ℝ))
  change (∑' b, if (b ∘ p) i ∈ S then ‖c (b ∘ p)‖^2 else (0:ℝ)) = _ at he
  simpa only [Function.comp_apply,p,Equiv.swap_apply_left,hc.norm_permute] using he.symm

theorem complement_coefficient_single_occupation {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ) (hc : Coulomb.FermionicCoefficients c)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0)
    (hs : Summable (fun b => ‖c b‖^2)) (i : Fin (n+1)) :
    (n+1:ℕ)*(∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤
      (n:ℝ)*(∑' b, ‖c b‖^2) := by
  have h := complement_coefficient_occupation_sum S c hzero hs
  simp_rw [coefficient_set_occupation_eq hc S _ i] at h
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorComplementBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parseval identifies the coefficient occupation count with the actual
partial integrals of a many-electron wave function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem first_fiber_occupation_eq {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (hc : Coulomb.CompleteOrbitals μ v)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ)) (S : Finset ι) :
    (∑ a ∈ S, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) =
    ∑' b, if b 0 ∈ S then ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2 else (0:ℝ) := by
  have hs := Coulomb.scalarCoefficient_summable f hf v hv ho
  have hsingle (a : ι) :
      (∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
        ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑' b, if b 0 = a then ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2 else (0:ℝ) := by
    calc
      _ = ∑' b : Fin n → ι, ‖Coulomb.scalarCoefficient (μ := μ)
          (Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f)) v b‖^2 :=
        (Coulomb.scalarCoefficient_parseval _
          (Coulomb.fiberContract_memLp (hv a) (Coulomb.firstFiber_memLp hf)) v hv ho hc).symm
      _ = ∑' b : Fin n → ι, ‖Coulomb.scalarCoefficient (μ := μ) f v (Fin.cons a b)‖^2 := by
        apply tsum_congr
        intro b
        exact congrArg (fun z : ℂ => ‖z‖^2) (Coulomb.scalarCoefficient_contract f hf v hv a b).symm
      _ = _ := (Coulomb.tsum_fixed_zero (fun b => ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2) a).symm
  simp_rw [hsingle]
  rw [← Summable.tsum_finsetSum (fun a _ =>
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _) hs)]
  apply tsum_congr
  intro b
  simp

theorem first_fiber_complement_bound {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (hc : Coulomb.CompleteOrbitals μ v)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : Coulomb.ProductAntisymmetric (μ := μ) f) (S : Finset ι)
    (hzero : ∀ b, (∀ i, b i ∈ S) → Coulomb.scalarCoefficient (μ := μ) f v b = 0) :
    (n+1:ℕ)*(∑ a ∈ S, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) ≤
      (n:ℝ)*(∫ x, ‖f x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) := by
  rw [first_fiber_occupation_eq v hv ho hc f hf S,
    ← Coulomb.scalarCoefficient_parseval f hf v hv ho hc]
  simpa only [Finset.mem_coe] using complement_coefficient_single_occupation (S : Set ι)
    (Coulomb.scalarCoefficient (μ := μ) f v) (Coulomb.scalarCoefficient_antisymmetric ha v)
    hzero (Coulomb.scalarCoefficient_summable f hf v hv ho) 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalBasisExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending the finitely many chosen orbitals supplies Parseval for
arbitrary continuum states, including their orthogonal remainder. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem finite_orbitals_basis_extension {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SecondCountableTopology (Lp ℂ 2 μ)] {m : ℕ}
    (v : Fin m → Lp ℂ 2 μ) (hv : Orthonormal ℂ v) :
    ∃ (S : Set (Lp ℂ 2 μ)) (b : HilbertBasis S ℂ (Lp ℂ 2 μ)) (e : Fin m ↪ S),
      Countable S ∧ ∀ i, b (e i) = v i := by
  obtain ⟨S,b,hS,hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  let e : Fin m ↪ S :=
    ⟨fun i => ⟨v i,hS (Set.mem_range_self i)⟩,
      fun i j hij => hv.linearIndependent.injective (congrArg Subtype.val hij)⟩
  refine ⟨S,b,e,?_,?_⟩
  · exact Coulomb.orthonormal_subtype_countable (by simpa only [hb] using b.orthonormal)
  · intro i
    exact congrFun hb (e i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOrbitalComplement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement occupation bound for a finite family requires no choice
of ambient basis in its statement. The auxiliary basis is constructed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finite_orbital_complement_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {m n : ℕ}
    (v : Fin m → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x)*v j x ∂μ) = if i=j then (1:ℂ) else 0)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : Coulomb.ProductAntisymmetric (μ := μ) f)
    (hzero : ∀ b : Fin (n+1) → Fin m, Coulomb.scalarCoefficient (μ := μ) f v b = 0) :
    (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) ≤
      (n:ℝ)*(∫ x, ‖f x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) := by
  obtain ⟨J,b,e,hJ,he⟩ := finite_orbitals_basis_extension
    (fun i => (hv i).toLp (v i)) (Coulomb.orbital_orthonormal v hv (by
      intro i j
      by_cases hij : i=j <;> simpa only [hij,ite_true, if_true,ite_false, if_false] using ho i j))
  let : Countable J := hJ
  let w (j : J) : A → ℂ := b j
  have hw (j : J) : MemLp (w j) 2 μ := Lp.memLp (b j)
  have hwo (i j : J) : (∫ x, star (w i x)*w j x ∂μ) = if i=j then (1:ℂ) else 0 := by
    calc
      _ = inner ℂ (b i) (b j) := by
        simpa only [w,Lp.toLp_coeFn] using (Coulomb.inner_toLp_complex (hw i) (hw j)).symm
      _ = _ := (orthonormal_iff_ite.mp b.orthonormal) i j
  have hwc : Coulomb.CompleteOrbitals μ w := Coulomb.HilbertBasis_completeOrbitals b
  have heq (i : Fin m) : w (e i) =ᵐ[μ] v i := by
    change (b (e i) : A → ℂ) =ᵐ[μ] v i
    rw [he i]
    exact (hv i).coeFn_toLp
  let T := Finset.univ.image e
  have hz (q : Fin (n+1) → J) (hq : ∀ i, q i ∈ T) :
      Coulomb.scalarCoefficient (μ := μ) f w q = 0 := by
    have hpre (i : Fin (n+1)) : ∃ j, e j = q i := by
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hq i)
      exact ⟨j,hj⟩
    choose a ha' using hpre
    have hcoeff : Coulomb.scalarCoefficient (μ := μ) f w q =
        Coulomb.scalarCoefficient (μ := μ) f v a := by
      unfold Coulomb.scalarCoefficient
      apply integral_congr_ae
      have hp := Measure.ae_eq_pi (μ := fun _ : Fin (n+1) => μ)
        (fun i => show w (q i) =ᵐ[μ] v (a i) by rw [← ha' i]; exact heq (a i))
      filter_upwards [hp] with x hx
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      exact congrFun hx i
    rw [hcoeff,hzero a]
  have h := first_fiber_complement_bound w hw (by
    intro i j
    by_cases hij : i=j <;> simpa only [hij,ite_true, if_true,ite_false, if_false] using hwo i j) hwc f hf ha T hz
  have hfiber (a : Fin m) (y : Fin n → A) :
      Coulomb.fiberContract (μ := μ) (w (e a)) (Coulomb.firstFiber f) y =
      Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y := by
    unfold Coulomb.fiberContract
    apply integral_congr_ae
    filter_upwards [heq a] with x hx
    rw [hx]
  dsimp [T] at h
  rw [Finset.sum_image e.injective.injOn] at h
  simpa only [hfiber] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorState
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite products of the actual smooth orbitals lie in the full H1 domain.
Their synthesis agrees with the orthogonal L2 tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) :
    (finiteTensorState v hv hL2 hpartial c).toHilbert =
      ∑ p, c p • Coulomb.tensorHilbert v hL2 p := by
  apply PiLp.ext
  intro s
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    Coulomb.tensorHilbert,Coulomb.H1Vector.toHilbert,WithLp.ofLp_toLp]
  exact Coulomb.orbital_sum_toLp (fun p => Coulomb.tensorOrbital v p s)
    (fun p => Coulomb.tensorOrbital_memLp v hL2 p s) Finset.univ c

theorem finiteTensorProjection_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) :
    (finiteTensorProjection v hv hL2 hpartial u).toHilbert =
      ∑ p, inner ℂ (Coulomb.tensorHilbert v hL2 p) u.toHilbert •
        Coulomb.tensorHilbert v hL2 p := by
  simp only [finiteTensorProjection,finiteTensorState_toHilbert,
    Coulomb.orbitalCoefficient_eq_inner u v hL2]

theorem finiteTensorProjection_coefficients {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t)*v c y t) =
      if a = c then (1:ℂ) else 0) (u : Coulomb.H1Vector n) (p : Fin n → α) :
    Coulomb.orbitalCoefficient (finiteTensorProjection v hv hL2 hpartial u) v p =
      Coulomb.orbitalCoefficient u v p := by
  simp only [Coulomb.orbitalCoefficient_eq_inner _ v hL2,finiteTensorProjection_toHilbert]
  exact (Coulomb.tensorHilbert_orthonormal v hL2 ho).inner_right_sum _ (Finset.mem_univ p)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorProjection
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-orbital tensor projection and its genuine H1 remainder have
orthogonal L2 values. In particular their masses add exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1_toHilbert_add {n : ℕ} (u w : Coulomb.H1Vector n) :
    (u.add w).toHilbert = u.toHilbert+w.toHilbert := by
  apply PiLp.ext
  intro s
  rfl

theorem h1_toHilbert_scale {n : ℕ} (u : Coulomb.H1Vector n) (c : ℂ) :
    (Coulomb.H1Vector.scale c u).toHilbert = c • u.toHilbert := by
  apply PiLp.ext
  intro s
  rfl

theorem finiteTensorRemainder_toHilbert {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) :
    (finiteTensorRemainder v hv hL2 hpartial u).toHilbert =
      u.toHilbert-(finiteTensorProjection v hv hL2 hpartial u).toHilbert := by
  simp only [finiteTensorRemainder,h1_toHilbert_add,h1_toHilbert_scale,neg_smul,one_smul,sub_eq_add_neg]

theorem finiteTensorRemainder_orthogonal {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t)*v c y t) =
      if a = c then (1:ℂ) else 0) (u : Coulomb.H1Vector n) (p : Fin n → α) :
    inner ℂ (Coulomb.tensorHilbert v hL2 p)
      (finiteTensorRemainder v hv hL2 hpartial u).toHilbert = 0 := by
  rw [finiteTensorRemainder_toHilbert,inner_sub_right,
    ← Coulomb.orbitalCoefficient_eq_inner u v hL2,
    ← Coulomb.orbitalCoefficient_eq_inner (finiteTensorProjection v hv hL2 hpartial u) v hL2,
    finiteTensorProjection_coefficients v hv hL2 hpartial ho u p,sub_self]

theorem finiteTensorProjection_antisymmetric {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) (hu : Coulomb.Antisymmetric u) :
    Coulomb.Antisymmetric (finiteTensorProjection v hv hL2 hpartial u) := by
  intro p s
  filter_upwards [] with x
  change (∑ b, Coulomb.orbitalCoefficient u v b*Coulomb.tensorOrbital v b (s ∘ p)
      (Coulomb.permute p x)) =
    (((p.sign : ℤ):ℂ))*(∑ b, Coulomb.orbitalCoefficient u v b*Coulomb.tensorOrbital v b s x)
  let e : (Fin n → α) ≃ (Fin n → α) := Equiv.arrowCongr p (Equiv.refl α)
  have he (b : Fin n → α) : e.symm b = b ∘ p := rfl
  rw [← e.symm.sum_comp]
  simp only [he,Coulomb.orbitalCoefficient_antisymmetric hu v,
    Coulomb.tensorOrbital_permute,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GramCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative symmetric orthonormalization of a finite real Gram matrix.
The correction is the actual spectral inverse square root, with Euclidean
operator norm estimates independent of the ambient function space. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb.GramCorrection

variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

lemma eigenvalue_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta) (i : Fin m) :
    1 - m * delta ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ 1 + m * delta := by
  let v : Fin m → ℝ := hG.eigenvectorBasis i
  have hnorm : ∑ j, v j ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) (hG.eigenvectorBasis.orthonormal.1 i)
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
  have hval : hG.eigenvalues i = ∑ j, ∑ k, G j k * v j * v k := by
    rw [hG.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    ring
  rw [hval]
  have hlo := dualMatrix_quadratic_lower G hdelta (fun j => (hdiag j).ge) hoff v
  have hhi := dualMatrix_quadratic_upper G hdelta (fun j => (hdiag j).le) hoff v
  rw [hnorm, mul_one] at hlo hhi
  exact ⟨hlo, hhi⟩

lemma correction_isHermitian (hG : G.IsHermitian) : (correction hG).IsHermitian := by
  rw [correction, ← hG.cfc_eq]
  exact (IsSelfAdjoint.cfc : IsSelfAdjoint (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G))

lemma correction_transpose (hG : G.IsHermitian) : (correction hG)ᵀ = correction hG := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    correction_isHermitian hG

lemma correction_gram (hG : G.IsHermitian) (hpos : ∀ i, 0 < hG.eigenvalues i) :
    (correction hG)ᵀ * G * correction hG = 1 := by
  rw [correction_transpose]
  conv_lhs => arg 1; arg 2; rw [hG.spectral_theorem]
  unfold correction Matrix.IsHermitian.cfc
  rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hdiag : Matrix.diagonal (fun i =>
      (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    have hscalar (i : Fin m) : (Real.sqrt (hG.eigenvalues i))⁻¹ * hG.eigenvalues i *
        (Real.sqrt (hG.eigenvalues i))⁻¹ = 1 := by
      have hs : Real.sqrt (hG.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
      calc
        _ = (Real.sqrt (hG.eigenvalues i))⁻¹ * Real.sqrt (hG.eigenvalues i) ^ 2 *
            (Real.sqrt (hG.eigenvalues i))⁻¹ := by rw [Real.sq_sqrt (hpos i).le]
        _ = 1 := by field_simp
    simp only [hscalar, Matrix.diagonal_one]
  simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using
    congrArg (Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary) hdiag |>.trans (map_one _)

end ContinuumCoulomb.GramCorrection

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite linear combinations of localized orbitals. Their
classical partials remain L2, and their integral Gram matrix is the
corresponding finite congruence of the actual overlap matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedLinearOrbital_inner {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) :
    (∫ x, localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x) =
      ∑ j, ∑ k, (a j * b k) * planarModeOverlap (u j) (u k) := by
  have hi (j k : Fin m) : Integrable (fun x => (a j * b k) *
      localizedTransition freq (u j) (u k) x) :=
    (localizedTransition_integrable hfreq (u j) (u k)).const_mul _
  have he (x : Position) : localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x =
      ∑ j, ∑ k, (a j * b k) * localizedTransition freq (u j) (u k) x := by
    unfold localizedLinearOrbital
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold localizedTransition
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hi j k)]
  simp only [integral_const_mul, localizedTransition_mass hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealSpinOrbitals
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin lifting of real C1 orbitals into the actual fermionic weak-H1
domain. Any injective list of occupied orthonormal spatial/spin modes
gives a normalized antisymmetric state on the full configuration space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem realSpinOrbital_inner (f g : Position → ℝ) (σ τ : Fin 2) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s) =
      if σ = τ then (↑(∫ x, f x * g x) : ℂ) else 0 := by
  by_cases h : σ = τ
  · subst τ
    have hp (s : Fin 2) :
        (∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g σ x s) =
          if s=σ then (↑(∫ x, f x*g x) : ℂ) else 0 := by
      by_cases hs : s=σ
      · subst s
        simp only [realSpinOrbital, ite_true, if_true, Complex.star_def, Complex.conj_ofReal,
          ← Complex.ofReal_mul, integral_complex_ofReal]
      · simp [realSpinOrbital, hs]
    simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  · have hz (s : Fin 2) (x : Position) : star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s = 0 := by
      by_cases hs : s = σ
      · subst s
        simp [realSpinOrbital, h]
      · simp [realSpinOrbital, hs]
    simp only [hz, integral_zero, Finset.sum_const_zero, h, ite_false, if_false]

theorem selectedRealSpinOrbitals_orthonormal {α : Type*} {n : ℕ}
    (f : α → Position → ℝ)
    (ho : ∀ i j, (∫ x, f i x * f j x) = if i = j then (1 : ℝ) else 0)
    (p : Fin n → α × Fin 2) (hp : Function.Injective p) (i j : Fin n) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital (f (p i).1) (p i).2 x s) *
      realSpinOrbital (f (p j).1) (p j).2 x s) = if i = j then (1 : ℂ) else 0 := by
  classical
  rw [realSpinOrbital_inner, ho]
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hs : (p i).2 = (p j).2
    · have hf : (p i).1 ≠ (p j).1 := by
        intro hf
        exact hij (hp (Prod.ext hf hs))
      simp only [hs, hf, hij, ite_true, if_true, ite_false, if_false, Complex.ofReal_zero]
    · simp only [hs, hij, ite_false, if_false]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral inverse-square-root correction applied to the
manufactured orbitals. These are C1 decaying orthonormal spatial functions;
injectively occupied spatial/spin modes give actual normalized fermions. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb

theorem correctedLocalizedCoefficients_gram {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) :
    correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ = 1 := by
  have hpos (i : Fin m) : 0 < (localizedModeGram_isHermitian u).eigenvalues i := by
    have h := (GramCorrection.eigenvalue_bounds (localizedModeGram_isHermitian u)
      (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
      (planarModeOverlap_offsite u hsep) i).1
    linarith
  have h := GramCorrection.correction_gram (localizedModeGram_isHermitian u) hpos
  rw [GramCorrection.correction_transpose] at h
  simpa only [correctedLocalizedCoefficients, GramCorrection.correction_transpose] using h

theorem correctedLocalizedMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    (∫ x, correctedLocalizedMode freq u i x * correctedLocalizedMode freq u j x) =
      if i=j then (1 : ℝ) else 0 := by
  rw [correctedLocalizedMode, correctedLocalizedMode, localizedLinearOrbital_inner hfreq]
  have he : (∑ p, ∑ q, (correctedLocalizedCoefficients u i p * correctedLocalizedCoefficients u j q) *
      planarModeOverlap (u p) (u q)) =
      (correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, localizedModeGram]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he, correctedLocalizedCoefficients_gram u hsep hs, Matrix.one_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreOrbitalCongruence
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The core occupation depends only on the L2 state. A global phase and
fermionic coordinate permutations preserve it. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem coreOrbitalCoefficient_phase_ae {n : ℕ} (u v : Coulomb.H1Vector (n+1))
    (c : ℂ) (h : ∀ s, u.value s =ᵐ[volume] fun x => c*v.value s x)
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) :
    coreOrbitalCoefficient u φ s t =ᵐ[volume]
      fun x => c*coreOrbitalCoefficient v φ s t x := by
  have hp := (Coulomb.joinConfiguration_measurePreserving n 1).quasiMeasurePreserving.ae
    (h (Fin.append s t))
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with x hx
  unfold coreOrbitalCoefficient
  calc
    _ = ∫ y, c*(star (φ y)*v.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y))) := by
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      change u.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y)) =
        c*v.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y)) at hy
      rw [hy]
      ring
    _ = _ := integral_const_mul _ _

theorem coreOrbitalMass_phase {n : ℕ} {ι : Type*} [Fintype ι]
    (u v : Coulomb.H1Vector (n+1)) (c : ℂ) (hc : ‖c‖=1)
    (h : ∀ s, u.value s =ᵐ[volume] fun x => c*v.value s x)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass u φ = coreOrbitalMass v φ := by
  rw [coreOrbitalMass_eq_coefficients,coreOrbitalMass_eq_coefficients]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [coreOrbitalCoefficient_phase_ae u v c h (φ i) s t] with x hx
  rw [hx,norm_mul,hc,one_mul]

theorem coreOrbitalMass_permutation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (p : Equiv.Perm (Fin (n+1)))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass (u.permutation p) φ = coreOrbitalMass u φ := by
  apply coreOrbitalMass_phase _ _ ((p.sign : ℤ):ℂ) (Coulomb.sign_complex_norm p)
  intro s
  filter_upwards [hu p s] with x hx
  rw [Coulomb.permutation_value,hx]

theorem totalOrbitalMass_antisymmetric {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    totalOrbitalMass u φ = (n+1:ℕ)*coreOrbitalMass u φ := by
  unfold totalOrbitalMass electronSlotOrbitalMass
  simp_rw [coreOrbitalMass_permutation u hu]
  simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_FullSpinTensorCoefficients
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full spin-space coordinates preserve the actual tensor coefficients
and antisymmetry. No restriction to a fixed spin sector is made. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem spinConfiguration_complex_integral {n : ℕ}
    (F : SpinConfiguration n → Configuration n → ℂ) (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((Coulomb.spinCubeEquiv n) z).1 (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(Coulomb.spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [Coulomb.integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

theorem fullSpin_scalarCoefficient {n : ℕ} {α : Type*}
    (u : Coulomb.H1Vector n) (v : α → Position → Fin 2 → ℂ)
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2) (b : Fin n → α) :
    Coulomb.scalarCoefficient (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u)
      (fun a => Coulomb.flatSpinOrbital (v a)) b = Coulomb.orbitalCoefficient u v b := by
  have h := spinConfiguration_complex_integral
    (fun s x => star (Coulomb.tensorOrbital v b s x)*u.value s x)
    (fun s => (Coulomb.tensorOrbital_memLp v hL2 b s).star.integrable_mul (u.value_L2 s))
  exact h

theorem fullSpin_antisymmetric {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : Coulomb.Antisymmetric u) :
    Coulomb.ProductAntisymmetric (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u) := by
  intro p
  have hs (s : SpinConfiguration n) : ∀ᵐ x ∂volume,
      u.value (s ∘ p) (Coulomb.permute p (WithLp.toLp 2 x)) =
        ((p.sign : ℤ):ℂ)*u.value s (WithLp.toLp 2 x) :=
    (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae (hu p s)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (Measure.count : Measure (SpinConfiguration n)))).ae (ae_all_iff.mpr hs)
  have ht := (Coulomb.spinCubeEquiv_full_measurePreserving n).quasiMeasurePreserving.ae hp
  filter_upwards [ht] with z hz
  exact hz (fun i => (z i).1)

theorem finiteTensorRemainder_antisymmetric {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) (hu : Coulomb.Antisymmetric u) :
    Coulomb.Antisymmetric (finiteTensorRemainder v hv hL2 hpartial u) :=
  hu.add (Coulomb.antisymmetric_scale _ (finiteTensorProjection_antisymmetric v hv hL2 hpartial u hu) _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the physical one-electron estimate to the full spinful weak-H1
form domain. The only approximation input is the published H=W density result. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1_inner_real_orbital {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (φ : Configuration n → ℝ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.ofReal.toLp (fun x => (φ x : ℂ))) (h1Coordinates u (Sum.inl s)) =
      ∫ x, u.value s x*(φ x : ℂ) := by
  have hcφ : MemLp (fun x => (φ x : ℂ)) 2 := hφ.ofReal
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hcφ.coeFn_toLp,(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp]
    with x hφx hux
  change inner ℂ (hφ.ofReal.toLp (fun x => (φ x : ℂ)) x)
    (h1Coordinates u (Sum.inl s) x) = _
  change h1Coordinates u (Sum.inl s) x = u.value s x at hux
  rw [hφx,hux,RCLike.inner_apply]
  simp only [Complex.conj_ofReal]

theorem oneElectron_inner_real_orbital (u : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) (φ : Position → ℝ) (hφ : MemLp φ 2) :
    inner ℂ (oneElectronOrbitalLp φ hφ) (h1Coordinates u (Sum.inl s)) =
      ∫ x, u.value s x*(φ (oneElectronCoordinates x) : ℂ) :=
  h1_inner_real_orbital u s (fun x => φ (oneElectronCoordinates x))
    (hφ.comp_measurePreserving oneElectronCoordinates.measurePreserving)

theorem oneElectron_graphOrbitalMass {ι : Type*} [Fintype ι]
    (φ : ι → Position → ℝ) (hφ : ∀ i, MemLp (φ i) 2) (u : Coulomb.H1Vector 1) :
    graphOrbitalMass (fun i => oneElectronOrbitalLp (φ i) (hφ i)) (h1Coordinates u) =
      ∑ s, ∑ i, ‖∫ x, u.value s x*(φ i (oneElectronCoordinates x) : ℂ)‖^2 := by
  unfold graphOrbitalMass
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℂ => ‖z‖^2)
    (h1_inner_real_orbital u s (fun x => φ i (oneElectronCoordinates x))
      ((hφ i).comp_measurePreserving oneElectronCoordinates.measurePreserving))

theorem oneElectron_weakH1_lower
    (hdensity : PublishedSobolevSmoothDensity)
    {ι : Type*} [Fintype ι] (V : Position → ℝ) (hV : Continuous V)
    (B : ℝ) (hB : ∀ x, |V x| ≤ B) (φ : ι → Position → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2) (E κ : ℝ)
    (hphysical : ∀ f : Position → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      E*(∫ x, ‖f x‖^2)-κ*(∑ i, ‖∫ x, f x*(φ i x : ℂ)‖^2) ≤ positionComplexForm V f)
    (u : Coulomb.H1Vector 1) :
    E*Coulomb.mass u-κ*graphOrbitalMass (fun i => oneElectronOrbitalLp (φ i) (hφ i))
      (h1Coordinates u) ≤ boundedPotentialForm (fun x => V (oneElectronCoordinates x)) u := by
  apply boundedPotential_projection_lower_of_compact hdensity _
    (hV.comp oneElectronCoordinates.continuous) B (fun x => hB _) _ E κ ?_ u
  intro v hv hd
  have hs (s : SpinConfiguration 1) := hphysical (oneElectronPullback (v.value s))
    (oneElectronPullback_contDiff (hv s).1) (oneElectronPullback_compact (hv s).2)
  have hm (s : SpinConfiguration 1) : (∫ x, ‖oneElectronPullback (v.value s) x‖^2) =
      ∫ x, ‖v.value s x‖^2 := oneElectronPullback_integral (fun x => ‖v.value s x‖^2)
  have ho (s : SpinConfiguration 1) (i : ι) :
      (∫ x, oneElectronPullback (v.value s) x*(φ i x : ℂ)) =
        ∫ x, v.value s x*(φ i (oneElectronCoordinates x) : ℂ) := by
    have h := oneElectronPullback_integral_complex
      (fun x => v.value s x*(φ i (oneElectronCoordinates x) : ℂ))
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using h
  have hs' (s : SpinConfiguration 1) :
      E*(∫ x, ‖v.value s x‖^2)-κ*(∑ i, ‖∫ x, v.value s x*(φ i (oneElectronCoordinates x) : ℂ)‖^2) ≤
      (1/2:ℝ)*(∑ a : Fin 3, ∫ x, ‖fderiv ℝ (v.value s) x (EuclideanSpace.single (0,a) 1)‖^2)+
      ∫ x, V (oneElectronCoordinates x)*‖v.value s x‖^2 := by
    simpa only [hm,ho,oneElectronPullback_form V (hv s).1] using hs s
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs' s)
  rw [oneElectron_graphOrbitalMass]
  unfold Coulomb.mass boundedPotentialForm Coulomb.kinetic
  simp_rw [hd,Fintype.sum_prod_type,Fin.sum_univ_one]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Function.comp_apply] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_LastTensorFiber
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the contracted electron from the first to the last coordinate
preserves occupation for an antisymmetric full-product wave function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem last_first_fiber_norm_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (ha : Coulomb.ProductAntisymmetric (μ := μ) f)
    (v : A → ℂ) :
    (∫ y, ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) =
    ∫ y, ‖Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons (z : (Fin n → A) × A) : e.symm z = Fin.cons z.2 z.1 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm]
  have hp := (he.symm e).quasiMeasurePreserving.ae (ha Fin.revPerm)
  have hc : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev)‖^2 =
        ‖Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y‖^2 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hp] with y hy
    have hcontract : Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev) =
        (((Fin.revPerm : Equiv.Perm (Fin (n+1))).sign : ℤ):ℂ)*
          Coulomb.fiberContract (μ := μ) v (Coulomb.firstFiber f) y := by
      unfold Coulomb.fiberContract
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hy] with z hz
      simp only [hcons] at hz
      change f (Fin.cons z y ∘ Fin.rev) = _ at hz
      rw [Fin.cons_comp_rev] at hz
      change star (v z)*f (Fin.snoc (y ∘ Fin.rev) z) =
        _*(star (v z)*f (Fin.cons z y))
      rw [hz]
      ring
    rw [hcontract,norm_mul,Coulomb.sign_complex_norm,one_mul]
  have hr := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) Fin.revPerm).integral_comp'
    (fun y => ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) y‖^2)
  have hrev (y : Fin n → A) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => A) Fin.revPerm) y = y ∘ Fin.rev := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => A) Fin.revPerm y i.rev
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => A) Fin.revPerm) y i.rev.rev = y i.rev at h
    simpa only [Fin.rev_rev,Function.comp_apply] using h
  simp only [hrev] at hr
  calc
    _ = ∫ y, ‖Coulomb.fiberContract (μ := μ) v (lastTensorFiber f) (y ∘ Fin.rev)‖^2
        ∂(Measure.pi fun _ : Fin n => μ) := hr.symm
    _ = _ := integral_congr_ae hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreTensorFiber
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-coordinate contraction in full spin space is exactly the
core-slice orbital coefficient used by the many-electron energy bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem spinConfigurationPoint_coordinates {n : ℕ}
    (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    spinConfigurationPoint ((Coulomb.spinCubeEquiv n) z).1
      (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2) = z := by
  rfl

theorem cubeState_snoc {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (s : SpinConfiguration n) (x : Configuration n) (t : Fin 2) (y : Configuration 1) :
    Coulomb.cubeState u (Fin.snoc (spinConfigurationPoint s x)
      (t,fun a => y (0,a))) =
    u.value (Fin.append s (fun _ => t)) (Coulomb.joinConfiguration n 1 (x,y)) := by
  unfold Coulomb.cubeState
  congr 1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.append_right_eq_snoc]
    · simp [Fin.append_right_eq_snoc,spinConfigurationPoint]
  · apply PiLp.ext
    intro a
    obtain ⟨i,b⟩ := a
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      change y (0,b) = Coulomb.joinConfiguration n 1 (x,y) (Fin.last n,b)
      simpa only [show Fin.natAdd n (0:Fin 1) = Fin.last n from Fin.ext rfl] using
        (Coulomb.joinConfiguration_right n 1 x y (0:Fin 1) b).symm
    · simp only [Fin.snoc_castSucc]
      change x (j,b) = Coulomb.joinConfiguration n 1 (x,y) (j.castSucc,b)
      simpa only [show Fin.castAdd 1 j = j.castSucc from Fin.ext rfl] using
        (Coulomb.joinConfiguration_left n 1 x y j b).symm

theorem lastTensorFiber_coreSlice {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x)
    (z : Fin 2 × (Fin 3 → ℝ)) :
    lastTensorFiber (Coulomb.cubeState u) (spinConfigurationPoint s x,z) =
      Coulomb.flatSpinOrbital (fun y t => (u.coreSlice s x).value (fun _ => t)
        (oneElectronCoordinates.symm y)) z := by
  change Coulomb.cubeState u (Fin.snoc (spinConfigurationPoint s x) z) =
    (u.coreSlice s x).value (fun _ => z.1) (oneElectronCoordinates.symm (WithLp.toLp 2 z.2))
  rw [u.coreSlice_value s hx]
  have hz : (z.1,fun a => oneElectronCoordinates.symm (WithLp.toLp 2 z.2) (0,a)) = z := by
    exact Prod.ext rfl rfl
  simpa only [hz] using cubeState_snoc u s x z.1
    (oneElectronCoordinates.symm (WithLp.toLp 2 z.2))

theorem coreOrbitalCoefficient_slice {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x)
    (t : SpinConfiguration 1) :
    coreOrbitalCoefficient u φ s t x =
      inner ℂ φ (h1Coordinates (u.coreSlice s x) (Sum.inl t)) := by
  rw [h1_inner_orbital]
  simp only [u.coreSlice_value s hx,coreOrbitalCoefficient]

theorem lastTensorFiber_realOrbital_core {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2)
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x) :
    Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u))
      (spinConfigurationPoint s x) =
    coreOrbitalCoefficient u (oneElectronOrbitalLp f hf) s (fun _ => σ) x := by
  let w (y : Position) (t : Fin 2) :=
    (u.coreSlice s x).value (fun _ => t) (oneElectronCoordinates.symm y)
  have hw (t : Fin 2) : MemLp (fun y => w y t) 2 :=
    ((u.coreSlice s x).value_L2 (fun _ => t)).comp_measurePreserving
      oneElectronCoordinates.symm.measurePreserving
  have he : Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u))
        (spinConfigurationPoint s x) =
      ∫ z, star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*Coulomb.flatSpinOrbital w z
        ∂Coulomb.spinSpaceMeasure := by
    unfold Coulomb.fiberContract
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => congrArg (fun c =>
      star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*c)
        (lastTensorFiber_coreSlice u s x hx z))
  rw [he,Coulomb.flatSpinOrbital_inner _ w (realSpinOrbital_memLp f hf σ) hw]
  have hsum : (∑ t : Fin 2, ∫ y, star (realSpinOrbital f σ y t)*w y t) =
      ∫ y, (f y:ℂ)*w y σ := by
    have hpoint (t : Fin 2) : (∫ y, star (realSpinOrbital f σ y t)*w y t) =
        if t=σ then (∫ y, (f y:ℂ)*w y σ) else 0 := by
      by_cases ht : t=σ
      · subst t
        simp only [realSpinOrbital,ite_true, if_true,Complex.star_def,Complex.conj_ofReal]
      · simp only [realSpinOrbital,ht,ite_false, if_false,star_zero,zero_mul,integral_zero]
    simp only [hpoint]
    simp
  rw [hsum,coreOrbitalCoefficient_slice u _ s x hx,oneElectron_inner_real_orbital]
  rw [← oneElectronCoordinates_integral_complex (fun y => (f y:ℂ)*w y σ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp [w]
    rw [LinearIsometryEquiv.symm_apply_apply]
    ring)

theorem lastTensorFiber_realOrbital_integral {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2) :
    (∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) =
    ∑ s, ∫ x, ‖coreOrbitalCoefficient u (oneElectronOrbitalLp f hf) s (fun _ => σ) x‖^2 := by
  have hs (s : SpinConfiguration n) :=
    (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae
      (u.coreSliceRegular_ae s)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (Measure.count : Measure (SpinConfiguration n)))).ae (ae_all_iff.mpr hs)
  have ht := (Coulomb.spinCubeEquiv_full_measurePreserving n).quasiMeasurePreserving.ae hp
  have he : (fun y => ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2) =ᵐ[
        Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure]
      fun y => ‖coreOrbitalCoefficient u (oneElectronOrbitalLp f hf)
        ((Coulomb.spinCubeEquiv n) y).1 (fun _ => σ)
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) y).2)‖^2 := by
    filter_upwards [ht] with y hy
    have h := lastTensorFiber_realOrbital_core u f hf σ
      ((Coulomb.spinCubeEquiv n) y).1 (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) y).2)
      (hy ((Coulomb.spinCubeEquiv n) y).1)
    rw [spinConfigurationPoint_coordinates] at h
    exact congrArg (fun z : ℂ => ‖z‖^2) h
  rw [integral_congr_ae he]
  exact Coulomb.spinConfiguration_integral _ (fun s =>
    (coreOrbitalCoefficient_memLp u (oneElectronOrbitalLp f hf) s (fun _ => σ)).norm.integrable_sq)

theorem coreOrbitalMass_last_occupation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2) :
    coreOrbitalMass u (fun i => oneElectronOrbitalLp (f i) (hf i)) =
    ∑ i, ∑ σ : Fin 2, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f i) σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  rw [coreOrbitalMass_eq_coefficients]
  have he (i : ι) (σ : Fin 2) := lastTensorFiber_realOrbital_integral u (f i) (hf i) σ
  simp_rw [he]
  symm
  calc
    _ = ∑ i, ∑ s, ∑ σ : Fin 2, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ σ : Fin 2, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 :=
      Finset.sum_comm
    _ = ∑ s, ∑ σ : Fin 2, ∑ i, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp
        (fun t : SpinConfiguration 1 => ∑ i, ∫ x,
          ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s t x‖^2)

theorem coreOrbitalMass_first_occupation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2) :
    coreOrbitalMass u (fun i => oneElectronOrbitalLp (f i) (hf i)) =
    ∑ i, ∑ σ : Fin 2, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f i) σ)) (Coulomb.firstFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  rw [coreOrbitalMass_last_occupation u f hf]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro σ _
  exact last_first_fiber_norm_integral _ (fullSpin_antisymmetric u hu) _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_FullTensorComplement
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual antisymmetric H1 remainder has a missing orbital occupation
on the full spin-space product measure. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace ContinuumCoulomb

theorem finiteTensorRemainder_flat_occupation {m n : ℕ}
    (v : Fin m → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u) :
    let q := finiteTensorRemainder v hv hL2 hpartial u
    (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) ≤ (n:ℝ)*Coulomb.mass q := by
  let : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let q := finiteTensorRemainder v hv hL2 hpartial u
  have hflat (a b : Fin m) :
      (∫ x, star (Coulomb.flatSpinOrbital (v a) x)*Coulomb.flatSpinOrbital (v b) x
        ∂Coulomb.spinSpaceMeasure) = if a=b then (1:ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
    exact ho a b
  have hz (b : Fin (n+1) → Fin m) :
      Coulomb.scalarCoefficient (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState q)
        (fun a => Coulomb.flatSpinOrbital (v a)) b = 0 := by
    rw [fullSpin_scalarCoefficient q v hL2 b,Coulomb.orbitalCoefficient_eq_inner q v hL2 b]
    exact finiteTensorRemainder_orthogonal v hv hL2 hpartial (by
      intro i j
      by_cases hij : i=j <;> simpa only [hij,ite_true, if_true,ite_false, if_false] using ho i j) u b
  have h := finite_orbital_complement_bound (fun a => Coulomb.flatSpinOrbital (v a))
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) hflat (Coulomb.cubeState q)
    q.cubeState_full_memLp (fullSpin_antisymmetric q (finiteTensorRemainder_antisymmetric v hv hL2 hpartial u hu)) hz
  simpa only [Coulomb.cubeState_full_mass] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorComplementGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tensor-complement occupation deficit gives a full many-electron
gap once the proved one-body finite-rank estimate is supplied. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorRemainder_totalOccupation {m n : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin m → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0)
    (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2)
    (e : Fin m ≃ ι × Fin 2) (he : ∀ a, v a = realSpinOrbital (f (e a).1) (e a).2)
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u) :
    let q := finiteTensorRemainder v hv hL2 hpartial u
    totalOrbitalMass q (fun i => oneElectronOrbitalLp (f i) (hf i)) ≤ (n:ℝ)*Coulomb.mass q := by
  let q := finiteTensorRemainder v hv hL2 hpartial u
  have hq : Coulomb.Antisymmetric q := finiteTensorRemainder_antisymmetric v hv hL2 hpartial u hu
  have h := finiteTensorRemainder_flat_occupation v hv hL2 hpartial ho u hu
  change (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
    (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) ≤ (n:ℝ)*Coulomb.mass q at h
  have hs : (∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
    (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) =
      coreOrbitalMass q (fun i => oneElectronOrbitalLp (f i) (hf i)) := by
    rw [coreOrbitalMass_first_occupation q hq f hf]
    simp_rw [he]
    let F (a : ι × Fin 2) : ℝ := ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f a.1) a.2))
      (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)
    exact (e.sum_comp F).trans (Fintype.sum_prod_type F)
  rw [hs,← totalOrbitalMass_antisymmetric q hq] at h
  exact h

theorem tensorComplement_energy_gap {n : ℕ} {ι : Type*} [Fintype ι]
    (q : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (E τ b Q : ℝ) (hτ : 0 ≤ τ) (hb : 0 ≤ b)
    (hocc : totalOrbitalMass q φ ≤ (n:ℝ)*Coulomb.mass q)
    (hform : (n+1:ℕ)*(E+τ)*Coulomb.mass q -
      (τ+b)*totalOrbitalMass q φ ≤ Q)
    (herr : (n:ℝ)*b ≤ τ/2) :
    ((n+1:ℕ)*E+τ/2)*Coulomb.mass q ≤ Q := by
  have hm : 0 ≤ Coulomb.mass q := Coulomb.mass_nonneg q
  have hprod := mul_le_mul_of_nonneg_left hocc (add_nonneg hτ hb)
  have he := mul_le_mul_of_nonneg_right herr hm
  push_cast at hform ⊢
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and global boundedness of the actual slab field, including
its discontinuous density at the slab boundary. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabPotential rho H S x| ≤
      rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho := by
  have hb := (NeutralAtom.potential_integrable_and_bound
    (slabDensity_integrable hH hS rho) (slabDensity_nonnegative hrho H S)
    (by norm_num : (0:ℝ)<1) (fun y _ => slabDensity_le hrho H S y) (x := x)).2
  rw [slabDensity_integral] at hb
  rw [slabPotential_eq_negativePotentialOf, abs_neg,
    abs_of_nonneg (NeutralAtom.potentialOf_nonneg (slabDensity_nonnegative hrho H S) x)]
  simpa only [inv_one, one_mul] using hb

theorem manufacturedSlabPotential_bounded {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 < S) (freq scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    ∃ B : ℝ, ∀ x, |manufacturedSlabPotential rho H S freq scale u x| ≤ B := by
  obtain ⟨C,hC⟩ := (manufacturedWellField_C7 freq scale S u).continuous.bounded_above_of_compact_support
    (manufacturedWellField_compact freq scale hS u)
  let A := rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho
  refine ⟨2*A+C,fun x => ?_⟩
  have hx := slabPotential_abs_bound hrho hH hS.le x
  have h0 := slabPotential_abs_bound hrho hH hS.le 0
  have hw := hC x
  change |manufacturedWellField freq scale S u x| ≤ C at hw
  unfold manufacturedSlabPotential
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add hx h0)) hw).trans_eq (by dsimp [A]; ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Gram correction preserves the actual orbital span and hence its
orthogonal complement. The inverse coefficients are obtained from the proved
Gram identity, without adding a spectral hypothesis. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ContinuumCoulomb

theorem correctedLocalizedCoefficients_leftInverse {D : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) :
    (localizedModeGram u*correctedLocalizedCoefficients u)*
      correctedLocalizedCoefficients u = 1 := by
  have h := correctedLocalizedCoefficients_gram u hsep hs
  have ht : (correctedLocalizedCoefficients u)ᵀ = correctedLocalizedCoefficients u :=
    GramCorrection.correction_transpose (localizedModeGram_isHermitian u)
  rw [ht, Matrix.mul_assoc] at h
  exact mul_eq_one_comm.mp h

theorem continuumLocalizedMode_expand_corrected {D : ℝ} {m : ℕ} (freq : ℝ)
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (i : Fin m) (x : Position) :
    continuumLocalizedMode freq (u i) x =
      ∑ j, (localizedModeGram u*correctedLocalizedCoefficients u) i j *
        correctedLocalizedMode freq u j x := by
  symm
  unfold correctedLocalizedMode localizedLinearOrbital
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← Matrix.mul_apply]
  rw [correctedLocalizedCoefficients_leftInverse u hsep hs]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem corrected_orthogonal_implies_raw {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2)
    (f : Position → ℂ) (hf : MemLp f 2)
    (ho : ∀ j, (∫ x, f x*(correctedLocalizedMode freq u j x : ℂ)) = 0)
    (i : Fin m) : (∫ x, f x*(continuumLocalizedMode freq (u i) x : ℂ)) = 0 := by
  have hi (j : Fin m) : Integrable (fun x =>
      ((localizedModeGram u*correctedLocalizedCoefficients u) i j : ℂ)*
        (f x*(correctedLocalizedMode freq u j x : ℂ))) :=
    (hf.integrable_mul (correctedLocalizedMode_memLp hfreq u j).ofReal).const_mul _
  have he (x : Position) : f x*(continuumLocalizedMode freq (u i) x : ℂ) =
      ∑ j, ((localizedModeGram u*correctedLocalizedCoefficients u) i j : ℂ)*
        (f x*(correctedLocalizedMode freq u j x : ℂ)) := by
    rw [continuumLocalizedMode_expand_corrected freq u hsep hs]
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_const_mul,ho,mul_zero,Finset.sum_const_zero]

theorem corrected_graph_orthogonal_implies_raw {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (v : Coulomb.H1Vector 1)
    (ho : ∀ s i, inner ℂ
      (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) :
    graphOrbitalMass (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
      (continuumLocalizedMode_memLp hfreq (u i))) (h1Coordinates v) = 0 := by
  apply graphOrbitalMass_eq_zero
  intro s i
  rw [oneElectron_inner_real_orbital]
  have hf : MemLp (oneElectronPullback (v.value s)) 2 :=
    (v.value_L2 s).comp_measurePreserving oneElectronCoordinates.symm.measurePreserving
  have hh (j : Fin m) :
      (∫ x, oneElectronPullback (v.value s) x*(correctedLocalizedMode freq u j x : ℂ)) = 0 := by
    have h := ho s j
    rw [oneElectron_inner_real_orbital] at h
    have he := oneElectronPullback_integral_complex
      (fun x => v.value s x*(correctedLocalizedMode freq u j (oneElectronCoordinates x) : ℂ))
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using he.trans h
  have h := corrected_orthogonal_implies_raw hfreq u hsep hs _ hf hh i
  have he := oneElectronPullback_integral_complex
    (fun x => v.value s x*(continuumLocalizedMode freq (u i) (oneElectronCoordinates x) : ℂ))
  have he' : (∫ x, oneElectronPullback (v.value s) x*(continuumLocalizedMode freq (u i) x : ℂ)) =
      ∫ x, v.value s x*(continuumLocalizedMode freq (u i) (oneElectronCoordinates x) : ℂ) := by
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using he
  exact he'.symm.trans h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFockStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every state of the actual full half-filled Fock space is realized by
an antisymmetric weak-H1 continuum state in the corrected localized modes.
The continuum mass is exactly the finite occupation norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedSpinMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1 : ℕ) * localizedOverlapBound D ≤ 1/2) (i j : Fin ((2*m+1)+1)) :
    (∑ s : Fin 2, ∫ x, star (localizedSpinMode freq u i x s) * localizedSpinMode freq u j x s) =
      if i=j then (1 : ℂ) else 0 := by
  exact selectedRealSpinOrbitals_orthonormal (correctedLocalizedMode freq u) (by
    intro a b
    by_cases hab : a=b
    · simpa only [hab, ite_true, if_true] using correctedLocalizedMode_inner hfreq u hsep hs a b
    · simpa only [hab, ite_false, if_false] using correctedLocalizedMode_inner hfreq u hsep hs a b)
    (siteModes m).symm (siteModes m).symm.injective i j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOneElectronGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manufactured field's finite-rank lower estimate holds on the entire
spinful weak-H1 domain. No smoothness, compact support, or reality condition is
imposed on the state in this theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedSlab_weakH1_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap)
    (hdensity : PublishedSobolevSmoothDensity) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → ∀ hfreq : 0 < freq, 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ v : Coulomb.H1Vector 1,
      manufacturedSpectralLevel γ m D η freq S rho H δ*Coulomb.mass v-
        γ*(1+η)*graphOrbitalMass
          (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
            (continuumLocalizedMode_memLp hfreq (u i))) (h1Coordinates v) ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  obtain ⟨γ,hγ,hsmall,hphysical⟩ := manufacturedSlab_test_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom v => ?_⟩
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  exact oneElectron_weakH1_lower hdensity _
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u) B hB
    (fun i => continuumLocalizedMode freq (u i))
    (fun i => continuumLocalizedMode_memLp hfreq (u i)) _ _
    (hphysical m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
      hrelation hbarrier u hsep hcoeff hdom) v

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manufactured field has a positive gap above its one-orbital energy
on the complement of the actual orthonormalized modes. All localization losses
are retained explicitly; they are not charged to the final energy precision. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedSpectralLevel_eq (γ : ℝ) (m : ℕ) (D η freq S rho H δ : ℝ) :
    manufacturedSpectralLevel γ m D η freq S rho H δ =
      -1/2+freq/2+γ-manufacturedSpectralLoss γ m D η freq S rho H δ := by
  unfold manufacturedSpectralLevel manufacturedSpectralLoss planarSpectralLevel verticalSpectralLevel
  ring

theorem manufacturedSpectralLevel_lower {γ D η freq S rho H δ : ℝ} {m : ℕ}
    (hloss : manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2) :
    -1/2+freq/2+γ/2 ≤ manufacturedSpectralLevel γ m D η freq S rho H δ := by
  rw [manufacturedSpectralLevel_eq]
  linarith

theorem manufacturedSlab_corrected_complement_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → ∀ hfreq : 0 < freq, 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      m*localizedOverlapBound D ≤ 1/2 →
      manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2 →
      ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) →
      (-1/2+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := manufacturedSlab_weakH1_lower hp hv hdensity
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom hover hloss v ho => ?_⟩
  have hb := hbound m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom v
  rw [corrected_graph_orthogonal_implies_raw hfreq u hsep hover v ho,
    mul_zero,sub_zero] at hb
  have hm : 0 ≤ Coulomb.mass v :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right (manufacturedSpectralLevel_lower hloss) hm).trans hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCappedScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed slab width threshold makes both actual transverse cutoff
losses smaller than half the oscillator gap. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem verticalCutoffDerivativeBound_tendsto :
    Tendsto verticalCutoffDerivativeBound atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.const_mul (2:ℝ)).const_mul (Real.pi/2)
  have h' := h.mul_const verticalCutoffDerivativeConstant
  change Tendsto (fun S : ℝ => (Real.pi/2*(2/S))*verticalCutoffDerivativeConstant) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, zero_mul, mul_zero] using h'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGapScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed localization parameters for the manufactured one-electron gap.
The number of sites enters only through the proved exponential count bound. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planar_projection_loss_threshold {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ D : ℝ, R ≤ D → ∀ m : ℕ,
      (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      planarSiteDerivativeBound D^2+
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)) ≤ ε := by
  have hexp : Tendsto (fun D : ℝ => Real.exp (-(19/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<19/320))
  have hl : Tendsto (fun D : ℝ => planarSiteDerivativeBound D^2+
      γ*(1+η⁻¹)*planarSiteTailConstant*Real.exp (-(19/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa using (planarSiteDerivativeBound_tendsto.pow 2).add
      (hexp.const_mul (γ*(1+η⁻¹)*planarSiteTailConstant))
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 (hl.eventually (gt_mem_nhds hε))
  refine ⟨max 8 R,le_max_left _ _,fun D hD m hm => ?_⟩
  have hC : 0 ≤ γ*(1+η⁻¹)*planarSiteTailConstant := by
    exact mul_nonneg (mul_nonneg hγ.le (by positivity)) planarSiteTailConstant_nonnegative
  have ht : γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)) ≤
      γ*(1+η⁻¹)*planarSiteTailConstant*Real.exp (-(19/320:ℝ)*D) := by
    calc
      _ = (γ*(1+η⁻¹)*planarSiteTailConstant)*
        ((m:ℝ)*Real.exp (-(19/20:ℝ)*(D/8))) := by ring
      _ ≤ (γ*(1+η⁻¹)*planarSiteTailConstant)*
        (Real.exp ((19/320:ℝ)*D)*Real.exp (-(19/20:ℝ)*(D/8))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) hC
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  exact (add_le_add le_rfl ht).trans (hR D ((le_max_right _ _).trans hD)).le

theorem vertical_projection_loss_tendsto {freq : ℝ} (hfreq : 0 < freq) (η : ℝ) :
    Tendsto (fun S : ℝ => verticalCutoffDerivativeBound S^2/2+
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
  have harg : Tendsto (fun S : ℝ => (freq/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq/8)
  have he : Tendsto (fun S : ℝ => Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp harg using 1
    all_goals try with_reducible_and_instances rfl
    ext S
    congr 1
    ring
  simpa using ((verticalCutoffDerivativeBound_tendsto.pow 2).div_const 2).add
    (he.const_mul (freq*(1+η⁻¹)*verticalCutoffTailConstant freq))

theorem vertical_projection_loss_threshold {freq ε : ℝ}
    (hfreq : 0 < freq) (η : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ S : ℝ, R ≤ S →
      3*freq/2 ≤ freq^2*S^2/8 ∧
      verticalCutoffDerivativeBound S^2/2+
        freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8) ≤ ε := by
  have hbar : Tendsto (fun S : ℝ => (freq^2/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq^2/8)
  have hb : ∀ᶠ S : ℝ in atTop, 3*freq/2 ≤ freq^2*S^2/8 := by
    filter_upwards [hbar.eventually (eventually_ge_atTop (3*freq/2))] with S hS
    convert hS using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hl := (vertical_projection_loss_tendsto hfreq η).eventually (gt_mem_nhds hε)
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 (hb.and hl)
  refine ⟨max 1 R,le_max_left _ _,fun S hS => ?_⟩
  obtain ⟨hb,hl⟩ := hR S ((le_max_right _ _).trans hS)
  exact ⟨hb,hl.le⟩

theorem manufactured_gap_parameter_bounds {γ freq : ℝ}
    (hγ : 0 < γ) (hsmall : γ ≤ 1/4) (hfreq : 1 ≤ freq) :
    0 < γ/(16*freq) ∧ freq*(γ/(16*freq)) = γ/16 ∧
      ∀ t : ℝ, t ≤ 1/2 →
        γ*(1+γ/(16*freq))*(1+t) ≤ freq*(1+γ/(16*freq)) := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  have hη : 0 < γ/(16*freq) := by positivity
  refine ⟨hη,by field_simp,fun t ht => ?_⟩
  have hgt : γ*(1+t) ≤ freq := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hgt (show 0 ≤ 1+γ/(16*freq) by positivity)
  nlinarith only [hh]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedUniformGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single positive complementary gap for every admissible manufactured
configuration. Localization widths and error tolerances are selected before
the instance and before the number of wells. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem localizedOverlap_row_threshold :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ D : ℝ, R ≤ D → ∀ m : ℕ,
      (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) → m*localizedOverlapBound D ≤ 1/2 := by
  have he : Tendsto (fun D : ℝ => Real.exp (-(269/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<269/320))
  have hl : Tendsto (fun D : ℝ => planarOverlapConstant*Real.exp (-(269/320:ℝ)*D))
      atTop (𝓝 0) := by simpa using he.const_mul planarOverlapConstant
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1
    (hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max 8 R,le_max_left _ _,fun D hD m hm => ?_⟩
  have hb : (m:ℝ)*localizedOverlapBound D ≤
      planarOverlapConstant*Real.exp (-(269/320:ℝ)*D) := by
    unfold localizedOverlapBound
    calc
      _ ≤ Real.exp ((19/320:ℝ)*D)*(planarOverlapConstant*Real.exp (-(9/10:ℝ)*D)) :=
        mul_le_mul_of_nonneg_right hm
          (mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le)
      _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring
  exact hb.trans (hR D ((le_max_right _ _).trans hD)).le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGrowingGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary gap remains uniform when the slab thickness grows
to obtain the required orbital residual accuracy. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_growing_complement_gap
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → ∀ u : Fin m → PlanarPosition,
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp (lt_of_lt_of_le zero_lt_one hfreq) u i))
          (h1Coordinates v (Sum.inl s)) = 0) →
      (-1/2+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,hγ,hsmall,hbound⟩ := manufacturedSlab_corrected_complement_lower hp hv hdensity
  let η := γ/(16*freq)
  obtain ⟨hη,hfreqη,hdom⟩ := manufactured_gap_parameter_bounds hγ hsmall hfreq
  obtain ⟨R₁,hR₁,hplanar⟩ := planar_projection_loss_threshold hγ hη (by positivity : 0 < γ/16)
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  obtain ⟨S₀,hS₀,hvertical⟩ := vertical_projection_loss_threshold hf η (by positivity : 0 < γ/16)
  let δ := γ/(16*(PlanarSobolev.wellBound+1))
  let C := max 1 (96*Real.pi*rho/γ)
  have hw := PlanarSobolev.wellBound_nonnegative
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨γ,max R₁ R₂,S₀,δ,C,hγ,hsmall,hR₁.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale hD hm hS hH hCH hscale u hsep hcoeff v ho => ?_⟩
  have hD₁ : R₁ ≤ D := (le_max_left _ _).trans hD
  have hD₂ : R₂ ≤ D := (le_max_right _ _).trans hD
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hδloss : δ*PlanarSobolev.wellBound ≤ γ/16 := by
    have hid : δ*(PlanarSobolev.wellBound+1) = γ/16 := by
      dsimp [δ]
      field_simp
    exact (mul_le_mul_of_nonneg_left (by linarith :
      PlanarSobolev.wellBound ≤ PlanarSobolev.wellBound+1) hδ.le).trans_eq hid
  have hslab : 6*Real.pi*rho*S^3/H ≤ γ/16 := by
    have hh : 96*Real.pi*rho*S^3/γ ≤ H := by
      calc
        _ = (96*Real.pi*rho/γ)*S^3 := by ring
        _ ≤ C*S^3 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hSpos.le _)
        _ ≤ H := hCH
    have hh' := (div_le_iff₀ hγ).mp hh
    apply (div_le_iff₀ hHpos).mpr
    nlinarith only [hh']
  have hloss : manufacturedSpectralLoss γ m D η freq S rho H δ ≤ γ/2 := by
    have hp' := hplanar D hD₁ m hm
    have hv' := (hvertical S hS).2
    unfold manufacturedSpectralLoss
    dsimp [η] at hv' ⊢
    linarith [hfreqη]
  exact hbound m D η freq S rho H scale δ (hR₁.trans hD₁) hη hf hSpos hrho hHpos
    hscale hδ.le hrelation (hvertical S hS).1 u hsep hcoeff
    (hdom _ (hover D hD₂ m hm)) (hover D hD₂ m hm) hloss v ho

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedPreciseResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform spectral gap uses a fixed threshold, while residual precision
uses the actual, smaller counterterm ratio chosen by the reduction. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_precise_manyElectron_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m : ℕ) (D S H scale r ε η : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H → 0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      ∀ (n : ℕ) (v : Coulomb.H1Vector (n+1)),
      (n+1:ℕ)*((-1/2:ℝ)+freq/2+γ/4)*Coulomb.mass v-
        (γ/4+ε+ε^2/(γ/4))*totalOrbitalMass v
          (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
            (correctedLocalizedMode_memLp (lt_of_lt_of_le zero_lt_one hfreq) u i)) ≤
        boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
          (Coulomb.position x i)) v := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_growing_complement_gap hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr n v => ?_⟩
  have hs := hover D ((le_max_right _ _).trans hD) m hm
  have hbound := manufacturedSlab_residual_finite_rank_lower hdensity hrho
    (lt_of_lt_of_le zero_lt_one hH) (lt_of_lt_of_le zero_lt_one (hS₀.trans hS))
    hf hrelation hr hrH hrS hγ scale u hsep hs hη hcoeff hε herr
    (hgap m D S H scale ((le_max_left _ _).trans hD) hm hS hH hCH hscale u hsep (fun i => ⟨(hcoeff i).1,(hcoeff i).2.trans hηδ⟩))
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hHpos.le hSpos freq scale u
  exact manyElectron_projection_lower _
    (manufacturedSlabPotential_continuous hrho hHpos.le hSpos.le freq scale u)
    B hB _ _ _ hbound v


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedTensorGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive gap on the actual full-domain tensor complement.
The only analytic inputs are the published planar, oscillator and density
statements; the finite tensor projection and its occupation deficit are proved. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_tensorComplement_gap_oai
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ v : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric v →
      let hf := lt_of_lt_of_le zero_lt_one hfreq
      let q := finiteTensorRemainder (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) v
      ((n+1:ℕ)*((-1/2:ℝ)+freq/2)+γ/8)*Coulomb.mass q ≤
        boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
          (Coulomb.position x i)) q := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hbound⟩ :=
    manufacturedSlab_uniform_precise_manyElectron_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,
    fun m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall v ha => ?_⟩
  let q := finiteTensorRemainder (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) v
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hocc := finiteTensorRemainder_totalOccupation (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs)
    (correctedLocalizedMode freq u) (correctedLocalizedMode_memLp hf u)
    (HubbardGlobal.siteModes m).symm (fun _ => rfl) v ha
  have he := hbound (m+1) D S H scale r ε η ((le_max_left _ _).trans hD) hm
    hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr n q
  have hg := tensorComplement_energy_gap q
    (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hf u i))
    ((-1/2:ℝ)+freq/2) (γ/4) (ε+ε^2/(γ/4)) _
    (by positivity) (by positivity) hocc (by simpa only [add_assoc] using he)
      (by convert hsmall using 1; ring)
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap_oai := @OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap_oai
