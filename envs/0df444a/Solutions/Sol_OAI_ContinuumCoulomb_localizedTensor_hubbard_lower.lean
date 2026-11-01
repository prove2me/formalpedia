-- Prove2me | solution 1 for OAI.ContinuumCoulomb.localizedTensor_hubbard_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:56:36.24341+00:00
-- url     : https://prove2.me/submissions/911dc69a-ad4f-4074-82d3-647d67c0d85c

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_finiteTensorState_form_approximation

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ChargePenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charge-transfer penalty at half filling

The diagonal part of the finite fermion model keeps long-range direct
Coulomb interactions. A symmetric interaction matrix with bounded absolute
row sums gives a gap against every nonsingly occupied configuration.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

/-- The direct Coulomb term and the compensating diagonal one-body term
are exactly the charge penalty minus its fixed scalar shift. Here `V i i=0`
is the physical off-site convention; the algebraic identity needs only
symmetry and conservation of total particle number. -/
theorem chargePenalty_offset_identity {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Fin m → Fin 3) (hsymm : ∀ i j, V i j = V j i)
    (hfill : ∑ i, (occupation i : ℕ) = m) :
    U / 2 * (∑ i, ((occupation i : ℕ) : ℝ) * (((occupation i : ℕ) : ℝ) - 1)) +
        (1 / 2 : ℝ) * (∑ i, ∑ j,
          V i j * ((occupation i : ℕ) : ℝ) * ((occupation j : ℕ) : ℝ)) -
        (∑ i, (∑ j, V i j) * ((occupation i : ℕ) : ℝ)) =
      chargePenalty U V occupation - (1 / 2 : ℝ) * ∑ i, ∑ j, V i j := by
  let x : Fin m → ℝ := fun i => (occupation i : ℕ)
  have hfillR : (∑ i, x i) = (m : ℝ) := by
    dsimp [x]
    exact_mod_cast hfill
  have hlinear : (∑ i, (x i - 1)) = 0 := by
    simp [Finset.sum_sub_distrib, hfillR]
  have honsite : (∑ i, x i * (x i - 1)) = ∑ i, (x i - 1) ^ 2 := by
    have h : (∑ i, x i * (x i - 1)) =
        (∑ i, (x i - 1) ^ 2) + ∑ i, (x i - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h, hlinear, add_zero]
  have hcross : (∑ i, ∑ j, V i j * x j) = ∑ i, ∑ j, V i j * x i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hquadratic : (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) =
      (∑ i, ∑ j, V i j * x i * x j) -
        2 * (∑ i, ∑ j, V i j * x i) + ∑ i, ∑ j, V i j := by
    have hexpand : (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) =
        (∑ i, ∑ j, V i j * x i * x j) - (∑ i, ∑ j, V i j * x i) -
          (∑ i, ∑ j, V i j * x j) + ∑ i, ∑ j, V i j := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexpand, hcross]
    ring
  change U / 2 * (∑ i, x i * (x i - 1)) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * x i * x j) -
    (∑ i, (∑ j, V i j) * x i) = _
  simp only [chargePenalty, occupationDeviation]
  change _ = U / 2 * (∑ i, (x i - 1) ^ 2) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) -
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j)
  rw [honsite, hquadratic]
  simp only [Finset.sum_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PairRegroup
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
lemma pairRegroup_measurePreserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μa : Measure A) (μb : Measure B)
    (μc : Measure C) (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (pairRegroup : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

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
lemma count_prod_count {S T : Type*} [Countable S] [Countable T] [MeasurableSpace S]
    [MeasurableSpace T] [MeasurableSingletonClass S] [MeasurableSingletonClass T] :
    (Measure.count : Measure S).prod (Measure.count : Measure T) = Measure.count := by
  apply Measure.ext_of_singleton
  intro st
  rw [← singleton_prod_singleton, Measure.prod_prod]
  simp
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

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

lemma H1Vector.toHilbert_norm_sq {n : ℕ} (ψ : H1Vector n) :
    ‖ψ.toHilbert‖ ^ 2 = mass ψ := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun s _ => norm_toLp_sq_complex (ψ.value_L2 s)

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

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

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
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
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
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_C1 {phi : PlanarPosition → ℝ} (hphi : ContDiff ℝ 2 phi)
    (e : PlanarPosition) : ContDiff ℝ 1 (planarPartial phi e) :=
  (hphi.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatLimit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian change of scale and the actual time-zero limit of the heat
average. The bound by the normalized time-one Gaussian permits dominated
convergence even though the Gaussian has noncompact support. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatKernel_sqrt_scale {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatKernel t (Real.sqrt t • r) = t⁻¹ * planarHeatKernel 1 r := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rw [planarHeatKernel, planarHeatKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
  have he : -(t * ‖r‖ ^ 2) / (4 * t) = -‖r‖ ^ 2 / (4 * 1) := by
    field_simp
  rw [he]
  ring

theorem planarHeatAverage_scaled {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b) := by
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure PlanarPosition)
    (fun b => planarHeatKernel t b * planarForcing (r - b)) (Real.sqrt t)
    (hR := Real.sqrt_nonneg t)
  simp only [finrank_euclideanSpace_fin, Real.sq_sqrt ht.le, smul_eq_mul,
    planarHeatKernel_sqrt_scale ht] at hi
  simp_rw [mul_assoc] at hi
  rw [integral_const_mul] at hi
  exact (mul_left_cancel₀ (inv_ne_zero ht.ne') hi).symm

theorem planarScaledHeatIntegrand_measurable (t : ℝ) (r : PlanarPosition) :
    AEStronglyMeasurable (fun b => planarHeatKernel 1 b *
      planarForcing (r - Real.sqrt t • b)) := by
  have hc : Continuous (fun b : PlanarPosition => r - Real.sqrt t • b) := by fun_prop
  exact ((planarHeatKernel_continuous 1).mul
    (planarForcing_C7.continuous.comp hc)).aestronglyMeasurable

theorem planarScaledHeatIntegrand_bound (t : ℝ) (r b : PlanarPosition) :
    ‖planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b)‖ ≤ planarHeatKernel 1 b := by
  have hk : 0 < planarHeatKernel 1 b := planarHeatKernel_positive (by norm_num) b
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.le (planarForcing_nonnegative _))]
  exact mul_le_of_le_one_right hk.le (planarForcing_le_one _)

theorem planarScaledHeatIntegrand_tendsto (r b : PlanarPosition) :
    Tendsto (fun t : ℝ => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (planarHeatKernel 1 b * planarForcing r)) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • b) (𝓝[>] 0) (𝓝 (0 : PlanarPosition)) := by
    have hs0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa only [Real.sqrt_zero, zero_smul] using
      (hs0.mono_left nhdsWithin_le_nhds).smul_const b
  have hr : Tendsto (fun t : ℝ => r - Real.sqrt t • b) (𝓝[>] 0) (𝓝 r) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hs
  exact tendsto_const_nhds.mul (planarForcing_C7.continuous.continuousAt.tendsto.comp hr)

theorem planarHeatAverage_tendsto_zero (r : PlanarPosition) :
    Tendsto (fun t => planarHeatAverage t r) (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by
  have hconv : Tendsto
      (fun t : ℝ => ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ b, planarHeatKernel 1 b * planarForcing r)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (F := fun t b => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (f := fun b => planarHeatKernel 1 b * planarForcing r)
      (bound := planarHeatKernel 1)
    · exact Eventually.of_forall (fun t => planarScaledHeatIntegrand_measurable t r)
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun b =>
        planarScaledHeatIntegrand_bound t r b))
    · exact planarHeatKernel_integrable (by norm_num)
    · exact Eventually.of_forall (planarScaledHeatIntegrand_tendsto r)
  have hv : (∫ b, planarHeatKernel 1 b * planarForcing r) = planarForcing r := by
    rw [integral_mul_const, planarHeatKernel_integral (by norm_num), one_mul]
  rw [hv] at hconv
  apply hconv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (planarHeatAverage_scaled ht r).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise differential identities for the actual two-dimensional Gaussian
kernel. Its time derivative is its coordinate Laplacian. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace ContinuumCoulomb

theorem planarHeatKernel_C2 (t : ℝ) : ContDiff ℝ 2 (planarHeatKernel t) := by
  unfold planarHeatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

theorem planarHeatKernel_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatKernel s r) (planarHeatTimeDerivative t r) t := by
  have hi := hasDerivAt_inv ht.ne'
  have h := (hi.const_mul ((4 * Real.pi)⁻¹)).mul
    ((hi.const_mul (-‖r‖ ^ 2 / 4)).exp)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · beta_reduce
    change planarHeatKernel s r = (4 * Real.pi)⁻¹ * s⁻¹ * Real.exp (-‖r‖ ^ 2 / 4 * s⁻¹)
    unfold planarHeatKernel
    congr 1 <;> ring_nf
  · dsimp [planarHeatTimeDerivative, planarHeatKernel]
    have he : -‖r‖ ^ 2 / (4 * t) = -‖r‖ ^ 2 / 4 * t⁻¹ := by ring
    rw [he]
    field_simp
    ring

theorem planarHeatKernel_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarHeatKernel t) e r =
      (-inner ℝ e r / (2 * t)) * planarHeatKernel t r := by
  have hd := ((((hasStrictFDerivAt_norm_sq r).hasFDerivAt.neg).mul_const (4 * t)⁻¹).exp).const_mul
    ((4 * Real.pi * t)⁻¹)
  change fderiv ℝ (planarHeatKernel t) r e = _
  rw [show fderiv ℝ (planarHeatKernel t) r = _ from hd.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply,
    innerSL_apply_apply, planarHeatKernel]
  rw [real_inner_comm r e]
  ring_nf

theorem planarHeatKernel_partial_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarPartial (planarHeatKernel t) e) e r =
      ((inner ℝ e r) ^ 2 / (4 * t ^ 2) - ‖e‖ ^ 2 / (2 * t)) * planarHeatKernel t r := by
  have hlin : ContDiff ℝ 1 (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) :=
    ((innerSL ℝ e).contDiff.neg).div_const _
  have heq : planarPartial (planarHeatKernel t) e =
      fun s => (-inner ℝ e s / (2 * t)) * planarHeatKernel t s :=
    funext (planarHeatKernel_partial t e)
  rw [heq, planarPartial_mul _ _ hlin ((planarHeatKernel_C2 t).of_le (by norm_num)),
    planarHeatKernel_partial]
  have hpart : planarPartial (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) e r =
      -‖e‖ ^ 2 / (2 * t) := by
    have hd := ((innerSL ℝ e).hasFDerivAt (x := r)).neg.mul_const (2 * t)⁻¹
    have hd' : HasFDerivAt (fun s : PlanarPosition => -inner ℝ e s / (2 * t))
        ((2 * t)⁻¹ • -(innerSL ℝ e)) r := by
      simpa only [Pi.neg_apply, innerSL_apply_apply, div_eq_mul_inv] using hd
    change fderiv ℝ (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) r e = _
    rw [hd'.fderiv]
    simp only [smul_apply, smul_eq_mul, neg_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq]
    ring
  rw [hpart]
  ring

theorem planarHeatKernel_laplacian (t : ℝ) (r : PlanarPosition) :
    planarLaplacian (planarHeatKernel t) r = planarHeatTimeDerivative t r := by
  have hn : ‖r‖ ^ 2 = ∑ a : Fin 2, (r a) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq r
  have ha (a : Fin 2) : inner ℝ (planarAxis a) r = r a := by
    simp [planarAxis, EuclideanSpace.inner_single_left]
  have he (a : Fin 2) : ‖planarAxis a‖ ^ 2 = 1 := by simp [planarAxis]
  simp only [planarLaplacian, planarHeatKernel_partial_partial, ha, he,
    planarHeatTimeDerivative, hn, Fin.sum_univ_two]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in time of the actual heat average. The compact forcing
allows a fixed compact dominating set on every positive time neighborhood. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatAverage_flip (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel t (r - b) * planarForcing b := by
  unfold planarHeatAverage
  rw [← integral_sub_left_eq_self _ volume r]
  simp only [sub_sub_self]

theorem planarHeatTimeDerivative_forcing_continuous (t : ℝ) (r : PlanarPosition) :
    Continuous (fun b => planarHeatTimeDerivative t (r - b) * planarForcing b) := by
  have hg : Continuous (fun b : PlanarPosition => planarHeatTimeDerivative t (r - b)) := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  exact hg.mul planarForcing_C7.continuous

theorem planarHeatTimeDerivative_forcing_joint_continuousAt (r : PlanarPosition)
    {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition =>
      planarHeatTimeDerivative q.1 (r - q.2) * planarForcing q.2) p := by
  have h4 : 4 * p.1 ≠ 0 := by positivity
  have h42 : 4 * p.1 ^ 2 ≠ 0 := by positivity
  have hpi : 4 * Real.pi * p.1 ≠ 0 := by positivity
  have hne : p.1 ≠ 0 := hp.ne'
  have hcomp : ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatTimeDerivative q.1 (r - q.2)) p := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  have hf : Continuous (fun q : ℝ × PlanarPosition => planarForcing q.2) :=
    planarForcing_C7.continuous.comp continuous_snd
  exact hcomp.mul hf.continuousAt

theorem planarHeatTimeDerivative_local_bound {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    ∃ bound : PlanarPosition → ℝ, Integrable bound ∧
      ∀ b s, s ∈ Set.Ioo (t / 2) (3 * t / 2) →
        ‖planarHeatTimeDerivative s (r - b) * planarForcing b‖ ≤ bound b := by
  let S : Set (ℝ × PlanarPosition) := Set.Icc (t / 2) (3 * t / 2) ×ˢ tsupport planarForcing
  let F : ℝ × PlanarPosition → ℝ := fun p =>
    planarHeatTimeDerivative p.1 (r - p.2) * planarForcing p.2
  have hS : IsCompact S := isCompact_Icc.prod planarForcing_hasCompactSupport
  have hF : ContinuousOn F S := by
    intro p hp
    have hpos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp.1.1
    exact (planarHeatTimeDerivative_forcing_joint_continuousAt r hpos).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.bddAbove_image hF.norm
  let bound : PlanarPosition → ℝ := (tsupport planarForcing).indicator (fun _ => max 0 C)
  refine ⟨bound, ?_, ?_⟩
  · exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr
      (integrableOn_const planarForcing_hasCompactSupport.measure_ne_top)
  · intro b s hs
    by_cases hb : b ∈ tsupport planarForcing
    · have hf : ‖F (s, b)‖ ≤ C := hC ⟨(s, b), ⟨⟨hs.1.le, hs.2.le⟩, hb⟩, rfl⟩
      simpa only [bound, Set.indicator_of_mem hb] using hf.trans (le_max_right 0 C)
    · simp only [bound, Set.indicator_of_notMem hb, image_eq_zero_of_notMem_tsupport hb,
        mul_zero, norm_zero, le_refl]

theorem planarHeatAverage_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) t := by
  obtain ⟨bound, hbi, hb⟩ := planarHeatTimeDerivative_local_bound ht r
  have hn : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hi : Integrable (fun b => planarHeatKernel t (r - b) * planarForcing b) :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub continuous_id)
      |>.mul planarForcing_C7.continuous).integrable_of_hasCompactSupport
      planarForcing_hasCompactSupport.mul_left
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun b => planarHeatKernel s (r - b) * planarForcing b) :=
    Eventually.of_forall (fun s => ((planarHeatKernel_continuous s).comp
      (continuous_const.sub continuous_id) |>.mul planarForcing_C7.continuous).aestronglyMeasurable)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s b => planarHeatKernel s (r - b) * planarForcing b)
    (F' := fun s b => planarHeatTimeDerivative s (r - b) * planarForcing b)
    hn hmeas hi (planarHeatTimeDerivative_forcing_continuous t r).aestronglyMeasurable
    (Eventually.of_forall hb) hbi
    (Eventually.of_forall (fun b s hs => (planarHeatKernel_hasDerivAt
      (by linarith [hs.1] : 0 < s) (r - b)).mul_const (planarForcing b)))
  simpa only [← planarHeatAverage_flip] using hd.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLaplaceIBP
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two integrations by parts transfer the planar Laplacian from the
Gaussian kernel to the compact forcing. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r e x : PlanarPosition) :
    planarPartial (fun y => f (r - y)) e x = -planarPartial f e (r - x) := by
  have hd := ((hf.differentiable (by norm_num) (r - x)).hasFDerivAt).comp x
    ((hasFDerivAt_const r x).sub (hasFDerivAt_id x))
  change fderiv ℝ (fun y => f (r - y)) x e = -(fderiv ℝ f (r - x) e)
  rw [show fderiv ℝ (fun y => f (r - y)) x = _ from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem planarPartial_neg {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (e x : PlanarPosition) :
    planarPartial (fun y => -f y) e x = -planarPartial f e x := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.neg
  change fderiv ℝ (fun y => -f y) x e = -(fderiv ℝ f x e)
  rw [show fderiv ℝ (fun y => -f y) x = _ from hd.fderiv]
  simp only [neg_apply]

theorem planarLaplacian_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (r x : PlanarPosition) :
    planarLaplacian (fun y => f (r - y)) x = planarLaplacian f (r - x) := by
  apply Finset.sum_congr rfl
  intro a _
  have hp := planarPartial_C1 hf (planarAxis a)
  have hpr : ContDiff ℝ 1 (fun y => planarPartial f (planarAxis a) (r - y)) :=
    hp.comp (contDiff_const.sub contDiff_id)
  rw [show planarPartial (fun y => f (r - y)) (planarAxis a) =
      fun y => -planarPartial f (planarAxis a) (r - y) from
    funext (planarPartial_reflect (hf.of_le (by norm_num)) r (planarAxis a)),
    planarPartial_neg hpr, planarPartial_reflect hp, neg_neg]

theorem planar_integral_mul_laplacian_C2 (f phi : PlanarPosition → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * planarLaplacian phi x) = ∫ x, planarLaplacian f x * phi x := by
  have hp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      ContDiff ℝ 1 (planarPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      Continuous (planarPartial (planarPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : PlanarPosition) : HasCompactSupport (planarPartial phi v) :=
    hc.fderiv_apply ℝ v
  have hppc (v : PlanarPosition) : HasCompactSupport (planarPartial (planarPartial phi v) v) :=
    (hpc v).fderiv_apply ℝ v
  have hleft (v : PlanarPosition) : Integrable (fun x => f x * planarPartial (planarPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : PlanarPosition) : Integrable (fun x => planarPartial (planarPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * planarPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : PlanarPosition) : Integrable (fun x => f x * planarPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : PlanarPosition) :
      (∫ x, f x * planarPartial (planarPartial phi v) v x) =
        ∫ x, planarPartial (planarPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, planarPartial f v x * planarPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, planarPartial f v x * planarPartial phi v x) =
            -(∫ x, planarPartial (planarPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  simp_rw [planarLaplacian, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (planarAxis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (planarAxis a))]
  simp_rw [Finset.sum_mul]

theorem planarLaplacian_continuous {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (planarLaplacian f) :=
  continuous_finsetSum _ (fun a _ =>
    planarPartial_continuous (planarPartial_C1 hf (planarAxis a)) (planarAxis a))

theorem planarLaplacian_hasCompactSupport {f : PlanarPosition → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planarLaplacian f) := by
  change HasCompactSupport (fun x => ∑ a : Fin 2,
    fderiv ℝ (fun y => fderiv ℝ f y (planarAxis a)) x (planarAxis a))
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => (hc.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ (planarAxis a))
  simpa only [Finset.sum_fn] using h

theorem planarHeatAverage_hasDerivAt_laplacian {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) t := by
  have hf2 : ContDiff ℝ 2 planarForcing := planarForcing_C7.of_le (by norm_num)
  have hr : ContDiff ℝ 2 (fun b : PlanarPosition => planarForcing (r - b)) :=
    hf2.comp (contDiff_const.sub contDiff_id)
  have hrc : HasCompactSupport (fun b : PlanarPosition => planarForcing (r - b)) :=
    planarForcing_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft r)
  have heq : (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) =
      ∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b) := by
    calc
      _ = ∫ b, planarHeatTimeDerivative t b * planarForcing (r - b) := by
        rw [← integral_sub_left_eq_self _ volume r]
        simp only [sub_sub_self]
      _ = ∫ b, planarLaplacian (planarHeatKernel t) b * planarForcing (r - b) := by
        simp only [planarHeatKernel_laplacian]
      _ = ∫ b, planarHeatKernel t b * planarLaplacian (fun y => planarForcing (r - y)) b :=
        (planar_integral_mul_laplacian_C2 _ _ (planarHeatKernel_C2 t) hr hrc).symm
      _ = _ := by simp only [planarLaplacian_reflect hf2]
  rw [← heq]
  exact planarHeatAverage_hasDerivAt ht r

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDerivatives
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first and second directional derivatives of the resolvent mode.
Differentiation is transferred to the compact forcing, which also gives
finite L¹ and L² derivatives without differentiating the singular kernel. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventMode_partial_partial (e v r : PlanarPosition) :
    planarPartial (planarPartial planarResolventMode e) v r =
      planarResolventOf (planarPartial (planarPartial planarForcing e) v) r := by
  rw [show planarPartial planarResolventMode e =
    planarResolventOf (planarPartial planarForcing e) from funext (planarResolventMode_partial e)]
  exact planarResolventOf_partial
    (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e) v r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventEquation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarResolvent_joint_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  apply planarResolventIntegrand_integrable.mul_bdd
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖g (r - p.2)‖ ≤ B
    exact hB _)

theorem planarResolventOf_heat_representation {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_joint_integrable hg hc r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planarResolventOf_heat_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b))
      (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_joint_integrable hg hc r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul] using h

theorem planarResolventMode_laplacian_integral (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventOf (planarLaplacian planarForcing) r := by
  have hi (a : Fin 2) : Integrable (fun b => planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) :=
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ
      (planarAxis a)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      planarResolventKernel_integrable.locallyIntegrable
      (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) _) _) r
  unfold planarLaplacian
  simp_rw [planarResolventMode_partial_partial]
  change (∑ a : Fin 2, ∫ b, planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) =
    ∫ b, planarResolventKernel b * ∑ a : Fin 2,
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp only [Finset.mul_sum]

theorem planarHeatResolventPrimitive_hasDerivAt (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (planarHeatResolventPrimitive r) (planarHeatResolventDerivative r t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using (hasDerivAt_id t).neg.exp
  have hd := he.mul (planarHeatAverage_hasDerivAt_laplacian ht r)
  have hd' : HasDerivAt (fun s => Real.exp (-s) * planarHeatAverage s r)
      (planarHeatResolventDerivative r t) t := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [planarHeatResolventDerivative]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [planarHeatResolventPrimitive, ite_eq_right (show s ≠ 0 from (show 0 < s from hs).ne')]

theorem planarHeatResolventPrimitive_continuousWithinAt (r : PlanarPosition) :
    ContinuousWithinAt (planarHeatResolventPrimitive r) (Set.Ici (0 : ℝ)) 0 := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have he0 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto
    simpa only [neg_zero, Real.exp_zero] using
      he0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlim := he.mul (planarHeatAverage_tendsto_zero r)
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto _ _ (𝓝 (planarHeatResolventPrimitive r 0))
  rw [planarHeatResolventPrimitive_zero]
  have hlim' : Tendsto (fun t => Real.exp (-t) * planarHeatAverage t r)
      (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by simpa only [one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarHeatResolventDerivative_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventDerivative r) (Set.Ioi (0 : ℝ)) :=
  (planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r).sub
    (planarResolventMode_heat_integrable r)

theorem planarHeatResolventPrimitive_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventPrimitive r) (Set.Ioi (0 : ℝ)) := by
  apply (planarResolventMode_heat_integrable r).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarResolventMode_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventMode r - planarForcing r := by
  have hd := fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => planarHeatResolventPrimitive_hasDerivAt r ht
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (planarHeatResolventDerivative_integrable r) (planarHeatResolventPrimitive_integrable r)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (planarHeatResolventPrimitive_continuousWithinAt r) hd
    (planarHeatResolventDerivative_integrable r) hzero
  have hL := planarResolventOf_heat_representation
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  have hLi := planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  simp only [planarHeatResolventDerivative, planarHeatResolventPrimitive_zero, zero_sub,
    integral_sub hLi (planarResolventMode_heat_integrable r), ← hL,
    ← planarResolventMode_heat_representation, ← planarResolventMode_laplacian_integral] at hFTC
  linarith

theorem manufacturedPlanarWell_eigen_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r =
      (2 * manufacturedPlanarWell r + 1) * planarResolventMode r := by
  rw [planarResolventMode_equation]
  unfold manufacturedPlanarWell
  field_simp [(planarResolventMode_positive r).ne']
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalized
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic identities for the actual normalized planar mode. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarLaplacian_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (r : PlanarPosition) :
    planarLaplacian (fun x => c * f x) r = c * planarLaplacian f r := by
  have h (e : PlanarPosition) : planarPartial (fun x => c * f x) e =
      fun x => c * planarPartial f e x :=
    funext (planarPartial_const_mul (hf.of_le (by norm_num)) c e)
  simp only [planarLaplacian]
  simp_rw [h]
  simp_rw [planarPartial_const_mul (planarPartial_C1 hf _)]
  exact (Finset.mul_sum _ _ _).symm

theorem normalizedPlanarMode_eigen_equation (r : PlanarPosition) :
    planarLaplacian normalizedPlanarMode r =
      (2 * manufacturedPlanarWell r + 1) * normalizedPlanarMode r := by
  rw [normalizedPlanarMode_eq_const_mul,
    planarLaplacian_const_mul (planarResolventMode_C7.of_le (by norm_num)),
    manufacturedPlanarWell_eigen_equation]
  ring

theorem planarPartial_translate (f : PlanarPosition → ℝ) (u e r : PlanarPosition) :
    planarPartial (fun x => f (x - u)) e r = planarPartial f e (r - u) := by
  simp only [planarPartial, fderiv_comp_sub]

theorem planarLaplacian_translate (f : PlanarPosition → ℝ) (u r : PlanarPosition) :
    planarLaplacian (fun x => f (x - u)) r = planarLaplacian f (r - u) := by
  have h (e : PlanarPosition) : planarPartial (fun x => f (x - u)) e =
      fun x => planarPartial f e (x - u) := funext (planarPartial_translate f u e)
  simp only [planarLaplacian]
  simp_rw [h, planarPartial_translate]

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

theorem verticalMode_second_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (verticalMode freq))
      ((freq ^ 2 * z ^ 2 - freq) * verticalMode freq z) z := by
  rw [show deriv (verticalMode freq) = (fun x => -freq * x * verticalMode freq x)
    from funext (verticalMode_deriv freq)]
  refine (((hasDerivAt_id z).const_mul (-freq)).mul (verticalMode_hasDerivAt freq z)).congr_deriv ?_
  · simp only [id_eq]
    ring

theorem verticalMode_second_deriv (freq z : ℝ) :
    deriv (deriv (verticalMode freq)) z = (freq ^ 2 * z ^ 2 - freq) * verticalMode freq z :=
  (verticalMode_second_hasDerivAt freq z).deriv

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

theorem localizedMode_planar_laplacian (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    planarLaplacian (fun r => localizedMode freq u (r, p.2)) p.1 =
      (2 * manufacturedPlanarWell (p.1 - u) + 1) * localizedMode freq u p := by
  have hc : ContDiff ℝ 2 (fun r => normalizedPlanarMode (r - u)) :=
    (normalizedPlanarMode_C7.comp (contDiff_id.sub contDiff_const)).of_le (by norm_num)
  change planarLaplacian (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) p.1 = _
  rw [show (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) =
    (fun r => verticalMode freq p.2 * normalizedPlanarMode (r - u))
    from funext (fun r => mul_comm _ _), planarLaplacian_const_mul hc,
    planarLaplacian_translate, normalizedPlanarMode_eigen_equation]
  simp only [localizedMode]
  ring

theorem localizedMode_vertical_second (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    deriv (deriv (fun z => localizedMode freq u (p.1, z))) p.2 =
      (freq ^ 2 * p.2 ^ 2 - freq) * localizedMode freq u p := by
  simp only [localizedMode, deriv_const_mul_field', deriv_const_mul_field,
    verticalMode_second_deriv]
  ring

theorem localizedMode_eigen_equation (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    -(1 / 2 : ℝ) * splitLaplacian (localizedMode freq u) p +
      localizedPotential freq u p * localizedMode freq u p =
        ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq u p := by
  simp only [splitLaplacian, localizedMode_planar_laplacian,
    localizedMode_vertical_second, localizedPotential]
  ring

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

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global Coulomb pairing for the bounded integrable packets used in
the mode construction. Existing Gaussian-kernel positivity applies directly
once the elementary bounded-density estimate supplies joint integrability. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

namespace CoulombPacket

theorem joint_integrable (f g : CoulombPacket) :
    Integrable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) := by
  have hg (x : Position) := NeutralAtom.bounded_density_convolution
    NeutralAtom.measurable_coulombKernel NeutralAtom.coulombKernel_nonneg
    (NeutralAtom.coulombKernel_integrableOn_ball 1) (fun _ => NeutralAtom.coulombKernel_le_one)
    g.integrable.norm (fun _ => norm_nonneg _) g.bound_spec x
  let C := g.bound * NeutralAtom.kernelBallMass 1 + ∫ y, ‖g y‖
  have hm : Measurable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) :=
    ((f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => by
      have hi := (hg x).1.const_mul ‖f x‖
      apply hi.mono' ((hm.comp ((measurable_const : Measurable (fun _ : Position => x)).prodMk
        measurable_id)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [Function.comp_def, Prod.fst, Prod.snd, id_eq]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
        change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ ≤ ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
        ring_nf
        exact le_rfl))
  · apply (f.integrable.norm.const_mul C).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      have he : (∫ y, ‖f x * g y * Coulomb.coulombKernel (x - y)‖) =
          ‖f x‖ * ∫ y, NeutralAtom.coulombKernel (x - y) * ‖g y‖ := by
        have hp (y : Position) : ‖f x * g y * Coulomb.coulombKernel (x - y)‖ =
            ‖f x‖ * (NeutralAtom.coulombKernel (x - y) * ‖g y‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
          change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ = ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
          ring
        simp_rw [hp, integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
      calc
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hg x).2 (norm_nonneg (f x))
        _ = _ := mul_comm _ _)

theorem pair_symmetric (f g : CoulombPacket) : pair f g = pair g f := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f g),
    integral_prod _ (joint_integrable g f), integral_integral_swap (joint_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Coulomb.coulombKernel, norm_sub_rev x y]
  ring

theorem pair_add_left (f g h : CoulombPacket) : pair (add f g) h = pair f h + pair g h := by
  unfold pair
  change (∫ p : Position × Position, (f p.1 + g p.1) * h p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [add_mul]
  exact integral_add (joint_integrable f h) (joint_integrable g h)

theorem pair_smul_left (t : ℝ) (f g : CoulombPacket) : pair (smul t f) g = t * pair f g := by
  unfold pair
  change (∫ p : Position × Position, (t * f p.1) * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [mul_assoc]
  exact integral_const_mul t _

end CoulombPacket
end ContinuumCoulomb

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
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem localizedTransition_mass_le_one {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, localizedTransition freq u v x) ≤ 1 := by
  have hi := ((localizedDensity_integrable hfreq u).add (localizedDensity_integrable hfreq v)).div_const 2
  have h := integral_mono (localizedTransition_integrable hfreq u v) hi (fun x => by
    simp only [Pi.add_apply, localizedTransition, localizedDensity]
    nlinarith [sq_nonneg (continuumLocalizedMode freq u x - continuumLocalizedMode freq v x)])
  simp only [Pi.add_apply] at h
  rw [integral_div, integral_add (localizedDensity_integrable hfreq u) (localizedDensity_integrable hfreq v),
    localizedDensity_mass hfreq u, localizedDensity_mass hfreq v] at h
  norm_num at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFourIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-index Coulomb integrals of the actual localized orbitals. Each
unequal-index pair gives exponentially small Coulomb coefficients, uniformly
in the other pair. Diagonal pairs recover the actual direct interaction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedTransition_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedTransition freq u v y) ∧
      NeutralAtom.potentialOf (localizedTransition freq u v) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedTransition_integrable hfreq u v)
    (localizedTransition_nonnegative hfreq u v) (localizedTransition_bound hfreq u v) x
  refine ⟨h.1, h.2.trans ?_⟩
  exact add_le_add_right (localizedTransition_mass_le_one hfreq u v) _

theorem localizedTransition_potential_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedTransition freq u v) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedTransition_nonnegative hfreq u v _))

theorem localizedTransition_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedTransition freq u v)) :=
  NeutralAtom.potentialOf_continuous (localizedTransition_integrable hfreq u v)
    (localizedTransition_nonnegative hfreq u v) (localizedTransition_bound hfreq u v)

theorem localizedFourIndex_integrable {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    Integrable (fun x => localizedTransition freq u v x *
      NeutralAtom.potentialOf (localizedTransition freq w z) x) := by
  apply (localizedTransition_integrable hfreq u v).mul_bdd (c := localizedPotentialBound freq)
    (localizedTransition_potential_continuous hfreq w z).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedTransition_potential_nonnegative hfreq w z x)]
    exact (localizedTransition_coulomb_integrable_bound hfreq w z x).2)

theorem localizedFourIndex_nonnegative {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    0 ≤ localizedFourIndex freq u v w z :=
  integral_nonneg (fun _ => mul_nonneg (localizedTransition_nonnegative hfreq u v _)
    (localizedTransition_potential_nonnegative hfreq w z _))

theorem localizedTransitionPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    CoulombPacket.pair (localizedTransitionPacket hfreq u v) (localizedTransitionPacket hfreq w z) =
      localizedFourIndex freq u v w z := by
  unfold CoulombPacket.pair localizedFourIndex NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedTransition freq u v x * localizedTransition freq w z y * ‖x - y‖⁻¹ =
    localizedTransition freq u v x * (‖x - y‖⁻¹ * localizedTransition freq w z y)
  ring

theorem localizedFourIndex_symmetric {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    localizedFourIndex freq u v w z = localizedFourIndex freq w z u v := by
  rw [← localizedTransitionPacket_pair hfreq, CoulombPacket.pair_symmetric,
    localizedTransitionPacket_pair hfreq]

theorem localizedFourIndex_diagonal (freq : ℝ) (u v : PlanarPosition) :
    localizedFourIndex freq u u v v = localizedCoulombCoeff freq u v := by
  have he (w : PlanarPosition) : localizedTransition freq w w = localizedDensity freq w := by
    funext x
    exact (pow_two _).symm
  simp only [localizedFourIndex, localizedCoulombCoeff, he]

theorem localizedFourIndex_le_overlap {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    localizedFourIndex freq u v w z ≤ localizedPotentialBound freq * planarModeOverlap u v := by
  have h := integral_mono (localizedFourIndex_integrable hfreq u v w z)
    ((localizedTransition_integrable hfreq u v).mul_const (localizedPotentialBound freq))
    (fun x => mul_le_mul_of_nonneg_left (localizedTransition_coulomb_integrable_bound hfreq w z x).2
      (localizedTransition_nonnegative hfreq u v x))
  rw [integral_mul_const, localizedTransition_mass hfreq] at h
  exact h.trans_eq (mul_comm _ _)

theorem localizedFourIndexConstant_nonnegative (freq : ℝ) : 0 ≤ localizedFourIndexConstant freq :=
  mul_nonneg (localizedPotentialBound_nonnegative freq) planarOverlapConstant_nonnegative

theorem localizedFourIndex_decay_left {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    |localizedFourIndex freq u v w z| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  rw [abs_of_nonneg (localizedFourIndex_nonnegative hfreq u v w z)]
  calc
    _ ≤ localizedPotentialBound freq * planarModeOverlap u v := localizedFourIndex_le_overlap hfreq u v w z
    _ ≤ localizedPotentialBound freq * (planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖)) :=
      mul_le_mul_of_nonneg_left (planarModeOverlap_decay u v) (localizedPotentialBound_nonnegative freq)
    _ = _ := (mul_assoc _ _ _).symm

theorem localizedFourIndex_decay_right {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    |localizedFourIndex freq u v w z| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * ‖w - z‖) := by
  rw [localizedFourIndex_symmetric hfreq]
  exact localizedFourIndex_decay_left hfreq w z u v

theorem localizedFourIndex_offsite {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j k l : Fin m) (hoff : i ≠ j ∨ k ≠ l) :
    |localizedFourIndex freq (u i) (u j) (u k) (u l)| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * D) := by
  rcases hoff with hij | hkl
  · exact (localizedFourIndex_decay_left hfreq _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep i j hij]))
        (localizedFourIndexConstant_nonnegative freq))
  · exact (localizedFourIndex_decay_right hfreq _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep k l hkl]))
        (localizedFourIndexConstant_nonnegative freq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteCoefficientCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise perturbation bounds needed when applying the actual symmetric
Gram correction to the two- and four-index orbital coefficients. Polynomial
site-count losses suffice for the logarithmic spacing used here. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem product_two_perturb {a b c d eta : ℝ}
    (hb : |b| ≤ 2) (hc : |c| ≤ 2)
    (he : 0 ≤ eta) (hac : |a - c| ≤ eta) (hbd : |b - d| ≤ eta) :
    |a * b - c * d| ≤ 4 * eta := by
  have hid : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hid]
  calc
    _ ≤ |a - c| * |b| + |c| * |b - d| := by simpa only [abs_mul] using abs_add_le ((a-c)*b) (c*(b-d))
    _ ≤ eta * 2 + 2 * eta := add_le_add
      (mul_le_mul hac hb (abs_nonneg _) he)
      (mul_le_mul hc hbd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem product_four_perturb {a b c d a' b' c' d' eta : ℝ}
    (hb : |b| ≤ 2) (hc : |c| ≤ 2) (hd : |d| ≤ 2)
    (ha' : |a'| ≤ 2) (hb' : |b'| ≤ 2) (hc' : |c'| ≤ 2)
    (he : 0 ≤ eta) (haa : |a-a'| ≤ eta) (hbb : |b-b'| ≤ eta)
    (hcc : |c-c'| ≤ eta) (hdd : |d-d'| ≤ eta) :
    |(a*b)*(c*d) - (a'*b')*(c'*d')| ≤ 32 * eta := by
  have hab := product_two_perturb hb ha' he haa hbb
  have hcd := product_two_perturb hd hc' he hcc hdd
  have hcd4 : |c*d| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hc hd (abs_nonneg d) (by norm_num : (0:ℝ) ≤ 2)]
  have hab4 : |a'*b'| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha' hb' (abs_nonneg b') (by norm_num : (0:ℝ) ≤ 2)]
  have hid : (a*b)*(c*d) - (a'*b')*(c'*d') =
      (a*b-a'*b')*(c*d) + (a'*b')*(c*d-c'*d') := by ring
  rw [hid]
  calc
    _ ≤ |a*b-a'*b'| * |c*d| + |a'*b'| * |c*d-c'*d'| := by
      simpa only [abs_mul] using abs_add_le ((a*b-a'*b')*(c*d)) ((a'*b')*(c*d-c'*d'))
    _ ≤ (4*eta)*4 + 4*(4*eta) := add_le_add
      (mul_le_mul hab hcd4 (abs_nonneg _) (by positivity))
      (mul_le_mul hab4 hcd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem finiteFourIndexChange_identity {m : ℕ}
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) :
    finiteFourIndexChange (fun a b => if a = b then 1 else 0) F i j k l = F i j k l := by
  classical
  simp only [finiteFourIndexChange, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem finiteFourIndexChange_bound {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) {eta B : ℝ}
    (he : 0 ≤ eta) (_hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i = j then 1 else 0| ≤ eta)
    (hF : ∀ i j k l, |F i j k l| ≤ B) (i j k l : Fin m) :
    |finiteFourIndexChange A F i j k l - F i j k l| ≤ (m : ℝ)^4 * (32 * eta * B) := by
  classical
  let I : Fin m → Fin m → ℝ := fun a b => if a = b then 1 else 0
  have hI (a b : Fin m) : |I a b| ≤ 2 := by dsimp [I]; split_ifs <;> norm_num
  have hc (p q r s : Fin m) :
      |((A i p*A j q)*(A k r*A l s) - (I i p*I j q)*(I k r*I l s)) * F p q r s| ≤ 32*eta*B := by
    rw [abs_mul]
    exact mul_le_mul
      (product_four_perturb (hA j q) (hA k r) (hA l s)
        (hI i p) (hI j q) (hI k r) he
        (hnear i p) (hnear j q) (hnear k r) (hnear l s))
      (hF p q r s) (abs_nonneg _) (by positivity)
  rw [← finiteFourIndexChange_identity F i j k l]
  change |finiteFourIndexChange A F i j k l - finiteFourIndexChange I F i j k l| ≤ _
  unfold finiteFourIndexChange
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ p, ∑ q, ∑ r, ∑ s,
        |((A i p*A j q)*(A k r*A l s) - (I i p*I j q)*(I k r*I l s)) * F p q r s| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, ∑ _r : Fin m, ∑ _s : Fin m, 32*eta*B :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ =>
        Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => hc p q r s))))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketTests
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet combinations and the exact global Poisson duality for
smooth compact tests. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem pair_zero_left (f : CoulombPacket) : pair zero f = 0 := by
  simp [pair, zero]

theorem pair_sumList_left (fs : List CoulombPacket) (g : CoulombPacket) :
    pair (sumList fs) g = (fs.map (fun f => pair f g)).sum := by
  induction fs with
  | nil => exact pair_zero_left g
  | cons f fs ih => simp only [sumList, pair_add_left, ih, List.map_cons, List.sum_cons]

theorem pair_combination_left {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ)
    (g : CoulombPacket) : pair (combination f d) g = ∑ i, d i * pair (f i) g := by
  rw [combination, pair_sumList_left, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, pair_smul_left]

theorem pair_combination_right {m : ℕ} (f : CoulombPacket) (g : Fin m → CoulombPacket)
    (d : Fin m → ℝ) : pair f (combination g d) = ∑ j, d j * pair f (g j) := by
  calc
    _ = pair (combination g d) f := pair_symmetric _ _
    _ = ∑ j, d j * pair (g j) f := pair_combination_left g d f
    _ = _ := Finset.sum_congr rfl (fun j _ => congrArg (fun a => d j * a) (pair_symmetric (g j) f))

end ContinuumCoulomb.CoulombPacket

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombSymmetry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual strict positivity and symmetry of the direct Coulomb coefficients. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedCoulomb_product_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun p : Position × Position => localizedDensity freq u p.1 *
      (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Position × Position => localizedDensity freq u p.1 *
        (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) :=
    (((localizedDensity_continuous freq u).measurable.comp measurable_fst).mul
      ((NeutralAtom.measurable_coulombKernel.comp (measurable_fst.sub measurable_snd)).mul
        ((localizedDensity_continuous freq v).measurable.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x =>
      (localizedDensity_coulomb_integrable_bound hfreq v x).1.const_mul
        (localizedDensity freq u x))
  · have hn (x y : Position) :
        ‖localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y)‖ =
        localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y) :=
      Real.norm_of_nonneg (mul_nonneg (localizedDensity_nonnegative freq u x)
        (mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
          (localizedDensity_nonnegative freq v y)))
    simp_rw [hn, integral_const_mul]
    exact localizedCoulombCoeff_integrable hfreq u v

theorem localizedCoulombCoeff_symmetric {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : localizedCoulombCoeff freq u v = localizedCoulombCoeff freq v u := by
  unfold localizedCoulombCoeff NeutralAtom.potentialOf
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (localizedCoulomb_product_integrable hfreq u v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [NeutralAtom.coulombKernel, norm_sub_rev x y]
      ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCenter_norm (u : PlanarPosition) : ‖planarCenter u‖ = ‖u‖ := by
  have h := positionSplitCoordinates_norm_sq (planarCenter u)
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem planarCenter_sub (u v : PlanarPosition) : planarCenter (u - v) = planarCenter u - planarCenter v := by
  change positionSplitCoordinates.symm (u - v, 0) =
    positionSplitCoordinates.symm (u, 0) - positionSplitCoordinates.symm (v, 0)
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_self]

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

theorem localizedDensity_potential_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq u) x =
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) := by
  unfold NeutralAtom.potentialOf
  rw [← integral_add_right_eq_self
    (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [localizedDensity_translate freq u, add_sub_cancel_right]
    congr 2
    abel)

theorem localizedCoulombProfileAt_eq (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombCoeff freq 0 u := by
  unfold localizedCoulombProfileAt localizedCoulombCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

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

theorem planarWellSum_continuous {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) :
    Continuous (planarWellSum u) :=
  continuous_finsetSum _ (fun i _ => manufacturedPlanarWell_C7.continuous.comp
    (continuous_id.sub (continuous_const : Continuous (fun _ : PlanarPosition => u i))))

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth transverse cutoff. Its formula uses only the fixed
smooth transition function, so rational approximation can use the actual
exponential formula instead of a classically selected bump function. -/

noncomputable section
namespace ContinuumCoulomb

namespace verticalCutoffBump

theorem nonneg {z : ℝ} : 0 ≤ verticalCutoffBump z :=
  Real.smoothTransition.nonneg _

theorem le_one {z : ℝ} : verticalCutoffBump z ≤ 1 :=
  Real.smoothTransition.le_one _

end verticalCutoffBump
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

theorem slabWellCutoff_bounds (S z : ℝ) :
    0 ≤ slabWellCutoff S z ∧ slabWellCutoff S z ≤ 1 :=
  ⟨verticalCutoffBump.nonneg, verticalCutoffBump.le_one⟩

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

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitPullback
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kinetic-energy pullback between physical Euclidean space and
planar/transverse product coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem splitCoordinate_planar_axis (a : Fin 2) :
    positionSplitCoordinates.symm (planarAxis a,0) =
      EuclideanSpace.single (Fin.castSucc a) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> fin_cases a <;>
      simp [planarAxis, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    fin_cases a <;> simp

theorem splitCoordinate_vertical_axis :
    positionSplitCoordinates.symm (0,1) = EuclideanSpace.single (2:Fin 3) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakH1Laplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak kinetic pairing with a C2 orbital only requires its Laplacian,
not each second partial separately, to belong to L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem configurationRealPartial_C1 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationRealPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOrbitalLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear combinations commute with the actual weak-form coordinate
Laplacian. These identities are used only for Gram-corrected orbitals. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem configurationRealLaplacian_sum {m : ℕ} (c : Fin m → ℝ)
    (f : Fin m → Configuration 1 → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationRealLaplacian (f j) x := by
  have hfirst (a : Fin 1 × Fin 3) :
      configurationRealPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationRealPartial (f j) a y) :=
    funext (configurationRealPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationRealLaplacian
  simp_rw [hfirst,configurationRealPartial_sum c _ (fun j => configurationRealPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorNorm
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficient norms for finite tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_mass {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (c : (Fin n → α) → ℂ) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) = ∑ b, ‖c b‖^2 := by
  rw [← Coulomb.H1Vector.toHilbert_norm_sq,finiteTensorState_toHilbert]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ b, c b • Coulomb.tensorHilbert v hL2 b‖^2) : ℂ) =
        inner ℂ (∑ b, c b • Coulomb.tensorHilbert v hL2 b)
          (∑ b, c b • Coulomb.tensorHilbert v hL2 b) := by
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    _ = ∑ b, (starRingEnd ℂ) (c b)*c b :=
      (Coulomb.tensorHilbert_orthonormal v hL2 ho).inner_sum c c Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' (c b)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_CAR
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q)) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

theorem create_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    create i * create j + create j * create i = 0 := by
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

theorem create_sq {Q : ℕ} (i : Fin (Q+1)) : create i * create i = 0 := by
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

theorem normal_order_entry {Q : ℕ} (P R : Module.End ℂ (Space Q))
    (i j k l : Fin (Q+1)) :
    (P * create j * annihilate i) * (create k * annihilate l * R) =
      delta i k • (P * create j * annihilate l * R) -
        P * create j * create k * annihilate i * annihilate l * R := by
  calc
    _ = P * create j * (annihilate i * create k) * annihilate l * R := by
      noncomm_ring
    _ = _ := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global finite-fermion identities for the Hubbard reduction

These are identities of actual creation and contraction operators on
the finite exterior algebra.  They retain every spectator mode and
therefore do not assume transition signs from the two-site calculation.
-/

noncomputable section

namespace ContinuumCoulomb.HubbardGlobal

open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem transfer_mul (i j k l : Fin (Q + 1)) :
    transfer i j * transfer k l = delta j k • transfer i l -
      create i * create k * annihilate j * annihilate l := by
  simpa only [transfer, one_mul, mul_one] using
    normal_order_entry (1 : Module.End ℂ (Space Q)) 1 j i k l

theorem number_idempotent (i : Fin (Q + 1)) : number i * number i = number i := by
  unfold number
  rw [transfer_mul]
  simp [delta, create_sq]

theorem quartic_number (i j : Fin (Q + 1)) (hij : i ≠ j) :
    create i * create j * annihilate j * annihilate i = number i * number j := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute i j)
  calc
    _ = -((create i * create j) * (annihilate i * annihilate j)) := by
      rw [ha]
      ext x
      simp
    _ = _ := by
      rw [number, number, transfer_mul]
      simp only [delta, ite_eq_right hij, zero_smul, zero_sub]
      noncomm_ring

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardOccupation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-basis diagonal action for the global Hubbard model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators
variable {Q : ℕ}

theorem annihilate_unoccupied_wedge (i : Fin (Q + 1)) (n : ℕ)
    (w : Fin n → Fin (Q + 1)) (hi : ∀ k, w k ≠ i) :
    annihilate i (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k))) = 0 := by
  induction n with
  | zero => simp [annihilate]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode (w 0)) *
        ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hmode : (LinearMap.proj i : Orbital Q →ₗ[ℂ] ℂ) (mode (w 0)) = 0 := by
      simp [LinearMap.proj, mode, Ne.symm (hi 0)]
    have htail := ih (fun k => w k.succ) (fun k => hi k.succ)
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0 at htail
    rw [hmode, htail]
    simp

theorem annihilate_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (fockBasis Q A) = 0 := by
  let S : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hn (k : Fin A.card) : Set.powersetCard.ofFinEmbEquiv.symm S k ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨k, rfl⟩
  have h := annihilate_unoccupied_wedge i A.card
    (Set.powersetCard.ofFinEmbEquiv.symm S) hn
  change annihilate i ((Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val) = 0
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simpa only [ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem fockBasis_singleton (i : Fin (Q + 1)) :
    fockBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm S 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S
      (Set.powersetCard.ofFinEmbEquiv.symm S 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : create i (fockBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q + 1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin (Q + 1)))
    (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q + 1)) 1)
    (⟨A, rfl⟩ : Set.powersetCard (Fin (Q + 1)) A.card) hd
  change fockBasis Q {i} * fockBasis Q A = 0 at h
  rw [fockBasis_singleton] at h
  exact h

/-- Each actual number operator is diagonal in the full occupation
basis, including every spectator mode. -/
theorem number_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    number i (fockBasis Q A) = if i ∈ A then fockBasis Q A else 0 := by
  by_cases hi : i ∈ A
  · have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
    change annihilate i (create i (fockBasis Q A)) +
      create i (annihilate i (fockBasis Q A)) =
        (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
    simpa [hi, create_occupied_basis i A hi, number, transfer] using h
  · simpa [hi, number, transfer] using
      congrArg (create i) (annihilate_unoccupied_basis i A hi)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardSpin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the singly occupied exterior sector with the spin model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem wedgeModes_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1)) :
    wedgeModes (n + 1) v = create (v 0) (wedgeModes n (fun k => v k.succ)) := by
  simp [wedgeModes, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, create, Function.comp_def]

theorem wedgeModes_replace_zero (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) :
    wedgeModes (n + 1) (fun a => if a = 0 then i else v a) =
      create i (wedgeModes n (fun a => v a.succ)) := by
  simp [wedgeModes_succ]

theorem wedgeModes_replace_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) (k : Fin n) :
    wedgeModes (n + 1) (fun a => if a = k.succ then i else v a) =
      create (v 0) (wedgeModes n (fun a => if a = k then i else v a.succ)) := by
  have h : (0 : Fin (n + 1)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
  simp [wedgeModes_succ, h]

/-- Even fermion bilinears pass a spectator creator without a sign. -/
theorem transfer_create (i j k : Fin (Q + 1)) :
    transfer i j * create k =
      delta j k • create i + create k * transfer i j := by
  have hc := eq_neg_of_add_eq_zero_left (create_anticommute i k)
  calc
    _ = create i * (annihilate j * create k) := by rw [transfer, mul_assoc]
    _ = delta j k • create i - (create i * create k) * annihilate j := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one, mul_assoc]
    _ = _ := by rw [hc]; ext x; simp [transfer]

/-- The action of a bilinear on an arbitrary wedge is the sum of its
one-particle replacements, with all CAR signs derived. -/
theorem transfer_wedgeModes (i j : Fin (Q + 1)) (n : ℕ)
    (v : Fin n → Fin (Q + 1)) :
    transfer i j (wedgeModes n v) =
      ∑ k, delta j (v k) • wedgeModes n (fun a => if a = k then i else v a) := by
  induction n with
  | zero => simp [wedgeModes, transfer, annihilate]
  | succ n ih =>
    rw [wedgeModes_succ]
    have h := LinearMap.congr_fun (transfer_create i j (v 0))
      (wedgeModes n (fun k => v k.succ))
    change transfer i j (create (v 0) (wedgeModes n (fun k => v k.succ))) =
      delta j (v 0) • create i (wedgeModes n (fun k => v k.succ)) +
        create (v 0) (transfer i j (wedgeModes n (fun k => v k.succ))) at h
    rw [h, ih, map_sum, Fin.sum_univ_succ, wedgeModes_replace_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, wedgeModes_replace_succ]

theorem siteMode_eq_iff (m : ℕ) (i j : Fin (m + 1)) (σ τ : Fin 2) :
    siteMode m i σ = siteMode m j τ ↔ i = j ∧ σ = τ := by
  rw [siteMode, siteMode, Equiv.apply_eq_iff_eq]
  exact Prod.mk_inj

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardExcitation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-diagonal inverse and charge-selection rules. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem fockDiagonal_basis (f : Finset (Fin (Q + 1)) → ℂ)
    (A : Finset (Fin (Q + 1))) :
    fockDiagonal f (fockBasis Q A) = f A • fockBasis Q A :=
  (fockBasis Q).constr_basis ℂ _ A

theorem fockDiagonal_coordinate (f : Finset (Fin (Q + 1)) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (fockDiagonal f x) A = f A * (fockBasis Q).repr x A := by
  have h : ((fockBasis Q).coord A).comp (fockDiagonal f) =
      f A • (fockBasis Q).coord A := by
    apply (fockBasis Q).ext
    intro S
    change (fockBasis Q).repr (fockDiagonal f (fockBasis Q S)) A =
      f A * (fockBasis Q).repr (fockBasis Q S) A
    rw [fockDiagonal_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hSA : S = A
    · subst S
      simp
    · simp [Module.Basis.repr_self, hSA]
  exact LinearMap.congr_fun h x

theorem siteNumber_basis (m : ℕ) (i : Fin (m + 1))
    (A : Finset (Fin ((2 * m + 1) + 1))) :
    siteNumber m i (fockBasis (2 * m + 1) A) =
      ((occupationAt m A i : ℕ) : ℂ) • fockBasis (2 * m + 1) A := by
  simp only [siteNumber, LinearMap.add_apply, number_basis, occupationAt]
  split_ifs <;> simp [two_smul]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial operator bounds from the actual exterior occupation basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Q : ℕ}

theorem fockCoordinates_norm_sq (x : Space Q) :
    ‖fockCoordinates Q x‖ ^ 2 = fockMass x := by
  simp only [EuclideanSpace.norm_sq_eq, fockCoordinates_apply,
    Complex.normSq_eq_norm_sq, fockMass]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockDensityTensor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation-diagonal Coulomb tensors are density interactions with the
self term removed, as follows directly from the CAR. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem twoBodyOperator_density {Q : ℕ} (V : Fin (Q+1) → Fin (Q+1) → ℂ) :
    twoBodyOperator (fun a b c d => if a=c ∧ b=d then V a b else 0) =
      (2:ℂ)⁻¹ • densityInteraction (fun a b => if a=b then 0 else V a b) := by
  unfold twoBodyOperator densityInteraction
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hi (c d : Fin (Q+1)) : (if a=c ∧ b=d then V a b else 0) =
      (if c=a then (if d=b then V a b else 0) else 0) := by
    by_cases hca : c=a <;> by_cases hdb : d=b <;> simp_all [eq_comm]
  simp only [hi,ite_smul,zero_smul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  by_cases hab : a=b
  · subst b
    simp [create_sq]
  · simp only [hab,ite_false, if_false,quartic_number a b hab]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HalfFilledSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled occupation basis splits into spins and charge defects. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

/-- The sum of actual local particle counts is the cardinality of the
occupied-mode set, including doubly occupied sites. -/
theorem occupationAt_sum (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∑ i, (occupationAt m A i : ℕ)) = A.card := by
  have hlocal (i : Fin (m + 1)) :
      (occupationAt m A i : ℕ) = ∑ σ : Fin 2,
        if siteMode m i σ ∈ A then 1 else 0 := by
    rw [Fin.sum_univ_two]
    rfl
  simp_rw [hlocal]
  rw [← Fintype.sum_prod_type (fun p : Fin (m + 1) × Fin 2 =>
    if siteMode m p.1 p.2 ∈ A then (1 : ℕ) else 0)]
  have h := (siteModes m).sum_comp
    (fun k => if k ∈ A then (1 : ℕ) else 0)
  change (∑ p : Fin (m + 1) × Fin 2,
      if siteModes m p ∈ A then 1 else 0) = A.card
  rw [h]
  simp

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-particle support and the true low/high Fock projections. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

variable {Q : ℕ}

theorem totalNumber_basis (A : Finset (Fin (Q + 1))) :
    totalNumber Q (fockBasis Q A) = (A.card : ℂ) • fockBasis Q A := by
  simp only [totalNumber, LinearMap.sum_apply, number_basis]
  have hpoint (i : Fin (Q + 1)) :
      (if i ∈ A then fockBasis Q A else 0) =
        (if i ∈ A then (1 : ℂ) else 0) • fockBasis Q A := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_smul]
  simp

theorem totalNumber_eq_diagonal (Q : ℕ) :
    totalNumber Q = fockDiagonal (fun A => (A.card : ℂ)) := by
  apply (fockBasis Q).ext
  intro A
  rw [totalNumber_basis, fockDiagonal_basis]

theorem totalNumber_eigen_coordinate_zero (N : ℕ) (x : Space Q)
    (hx : totalNumber Q x = (N : ℂ) • x) (A : Finset (Fin (Q + 1)))
    (hA : A.card ≠ N) : (fockBasis Q).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis Q).repr y A) hx
  rw [totalNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hne : (A.card : ℂ) ≠ (N : ℂ) := by exact_mod_cast hA
  have hz : ((A.card : ℂ) - N) * (fockBasis Q).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockChargePolynomial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density interaction and its counterterm on the full half-filled
Fock sector, including the scalar off-site Coulomb shift. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem siteChargeOperator_basis (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ)
    (A : Finset (Fin ((2*m+1)+1))) :
    siteChargeOperator m U V (fockBasis (2*m+1) A) =
      (directChargeValue U V (occupationAt m A) : ℂ) • fockBasis (2*m+1) A := by
  simp only [siteChargeOperator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply,
    siteNumber_basis, map_smul, smul_smul, ← Finset.sum_smul,
    ← sub_smul, ← add_smul]
  congr 1
  simp only [directChargeValue, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_one]
  congr 2
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem siteChargeOperator_eq_diagonal (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) :
    siteChargeOperator m U V =
      occupationDiagonal m (fun o => (directChargeValue U V o : ℂ)) := by
  apply (fockBasis (2*m+1)).ext
  intro A
  change siteChargeOperator m U V (fockBasis (2*m+1) A) =
    fockDiagonal (fun B => (directChargeValue U V (occupationAt m B):ℂ)) (fockBasis (2*m+1) A)
  rw [siteChargeOperator_basis,fockDiagonal_basis]

/-- The manuscript's scalar shift holds for every half-filled vector,
including charge defects and arbitrary spectator spins. -/
theorem siteChargeOperator_halfFilled (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j = V j i)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    siteChargeOperator m U V x = chargePenaltyFock m U V x -
      (((1 / 2 : ℝ) * ∑ i, ∑ j, V i j : ℝ) : ℂ) • x := by
  rw [siteChargeOperator_eq_diagonal]
  apply (fockBasis (2*m+1)).repr.injective
  ext A
  simp only [occupationDiagonal, chargePenaltyFock, fockDiagonal_coordinate,
    map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : A.card = m+1
  · have hfill : ∑ i, (occupationAt m A i : ℕ) = m+1 :=
      (occupationAt_sum m A).trans hA
    have h := chargePenalty_offset_identity U V (occupationAt m A) hsymm hfill
    change directChargeValue U V (occupationAt m A) = _ at h
    rw [h, Complex.ofReal_sub, sub_mul]
  · rw [hx A hA]
    simp

theorem oneBodyOperator_siteDiagonal (m : ℕ) (f : Fin (m+1) → ℂ) :
    oneBodyOperator (fun a b => if a=b then f (modeSite m a) else 0) =
      ∑ i, f i • siteNumber m i := by
  unfold oneBodyOperator
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type, modeSite, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [siteNumber, smul_add, number, siteMode]

theorem densityInteraction_site (m : ℕ) (C : Fin (m+1) → Fin (m+1) → ℂ) :
    densityInteraction (fun a b => C (modeSite m a) (modeSite m b)) =
      ∑ i, ∑ j, C i j • (siteNumber m i * siteNumber m j) := by
  unfold densityInteraction
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ σ : Fin 2, ∑ j : Fin (m+1), ∑ τ : Fin 2,
        C i j • (number (siteMode m i σ) * number (siteMode m j τ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← (siteModes m).sum_comp]
      simp only [Fintype.sum_prod_type, modeSite, Equiv.symm_apply_apply, siteMode]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.sum_univ_two, siteNumber, add_mul, mul_add, smul_add]
      abel

theorem densityInteraction_remove_self {Q : ℕ}
    (C : Fin (Q+1) → Fin (Q+1) → ℂ) :
    densityInteraction (fun a b => if a=b then 0 else C a b) =
      densityInteraction C - ∑ a, C a a • number a := by
  unfold densityInteraction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hterm (b : Fin (Q+1)) :
      (if a=b then (0:ℂ) else C a b) • (number a * number b) =
        C a b • (number a * number b) -
          (if b=a then C a a • number a else 0) := by
    by_cases hab : a=b
    · subst b
      simp [number_idempotent]
    · simp [hab, Ne.symm hab]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, if_true]

theorem densityInteraction_siteCoulomb (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i = 0) :
    densityInteraction (fun a b => siteCoulombCoefficient U V (modeSite m a) (modeSite m b)) =
      (U:ℂ) • (∑ i, siteNumber m i * siteNumber m i) +
        ∑ i, ∑ j, (V i j:ℂ) • (siteNumber m i * siteNumber m j) := by
  rw [densityInteraction_site]
  have hC (i j : Fin (m+1)) : siteCoulombCoefficient U V i j =
      (if i=j then (U:ℂ) else 0) + (V i j:ℂ) := by
    by_cases hij : i=j
    · subst j
      simp [siteCoulombCoefficient,hdiag]
    · simp [siteCoulombCoefficient,hij]
  simp only [hC, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.smul_sum]

theorem sum_siteCoulomb_self (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) :
    (∑ a, siteCoulombCoefficient U V (modeSite m a) (modeSite m a) • number a) =
      (U:ℂ) • ∑ i, siteNumber m i := by
  simp only [siteCoulombCoefficient, ite_true, if_true]
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.smul_sum, siteNumber,
    smul_add, siteMode]

/-- The actual diagonal Coulomb CAR tensor and compensating one-body
matrix are the site-charge polynomial, before restricting particle number. -/
theorem directCoulomb_operator (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i = 0) :
    oneBodyOperator (fun a b => if a=b then
        -((∑ j, V (modeSite m a) j : ℝ):ℂ) else 0) +
      twoBodyOperator (fun a b c d => if a=c ∧ b=d then
        siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0) =
      siteChargeOperator m U V := by
  rw [oneBodyOperator_siteDiagonal m (fun i => -((∑ j, V i j : ℝ):ℂ)), twoBodyOperator_density,
    densityInteraction_remove_self, densityInteraction_siteCoulomb m U V hdiag,
    sum_siteCoulomb_self]
  have hneg : (∑ i, (-((∑ j, V i j : ℝ):ℂ)) • siteNumber m i) =
      -(∑ i, ((∑ j, V i j : ℝ):ℂ) • siteNumber m i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact neg_smul (((∑ j, V i j : ℝ):ℂ)) (siteNumber m i)
  rw [hneg]
  simp only [siteChargeOperator, Finset.sum_sub_distrib,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  module

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_Scaling
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_ScalingWedge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_product (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    (∏ a : Fin n, d (Set.powersetCard.ofFinEmbEquiv.symm A a)) = ∏ i ∈ A.val, d i := by
  apply Finset.prod_bij (fun a _ => Set.powersetCard.ofFinEmbEquiv.symm A a)
  · intro a ha
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A _).mp ⟨a,rfl⟩
  · intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm A).injective hab
  · intro b hb
    obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A b).mpr hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a ha
    rfl

theorem exteriorScaling_occupation_sector (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    exteriorScaling Q d (occupationBasis Q A.val) =
      (∏ i ∈ A.val, d i) • occupationBasis Q A.val := by
  have h := exteriorScaling_wedge Q n d (Set.powersetCard.ofFinEmbEquiv.symm A)
  rw [occupation_product Q n d A] at h
  simpa only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem exteriorScaling_occupation (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Finset (Fin (Q+1))) :
    exteriorScaling Q d (occupationBasis Q A) = (∏ i ∈ A, d i) • occupationBasis Q A := by
  exact exteriorScaling_occupation_sector Q A.card d ⟨A,rfl⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Creation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) : annihilate i (occupationBasis Q A) = 0 := by
  let d : Fin (Q+1) → ℂ := fun j => if j = i then 0 else 1
  have hd : (∏ j ∈ A, d j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [d, show j ≠ i by intro h; subst j; exact hi hj]
  have h := annihilate_scaling Q d i (occupationBasis Q A)
  rw [exteriorScaling_occupation,hd,one_smul] at h
  simpa [d] using h

theorem create_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) : create i (occupationBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q+1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint
    (Pi.basisFun ℂ (Fin (Q+1)))
    (⟨{i},Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q+1)) 1)
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) hd
  change occupationBasis Q {i} * occupationBasis Q A = 0 at h
  rw [occupation_singleton] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Annihilation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

theorem insertionSign_sq (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A * insertionSign Q i A = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    create i (occupationBasis Q A) = insertionSign Q i A • occupationBasis Q (insert i A) := by
  simpa [insertionSign,hi] using (create_unoccupied_sign Q i A hi).choose_spec.2

theorem annihilate_insert (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    annihilate i (occupationBasis Q (insert i A)) = insertionSign Q i A • occupationBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (occupationBasis Q A)
  change annihilate i (create i (occupationBasis Q A)) +
    create i (annihilate i (occupationBasis Q A)) = (if i = i then (1 : ℂ) else 0) • occupationBasis Q A at h
  rw [create_unoccupied Q i A hi, map_smul, annihilate_unoccupied Q i A hi, map_zero] at h
  simp only [add_zero, ite_true, if_true, one_smul] at h
  have he := congrArg (fun x => insertionSign Q i A • x) h
  simpa only [smul_smul, insertionSign_sq, one_smul] using he

theorem annihilate_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) :
    annihilate i (occupationBasis Q A) =
      insertionSign Q i (A.erase i) • occupationBasis Q (A.erase i) := by
  simpa only [Finset.insert_erase hi] using
    annihilate_insert Q i (A.erase i) (Finset.notMem_erase i A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Coordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (annihilate i x) A =
      if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A) := by
  let e : ℂ := if i ∈ A then 0 else insertionSign Q i A
  have h : ((occupationBasis Q).coord A).comp (annihilate i) =
      e • (occupationBasis Q).coord (insert i A) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (annihilate i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (insert i A)
    by_cases hiB : i ∈ B
    · rw [annihilate_occupied Q i B hiB, map_smul, Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · have hBA : B.erase i ≠ A := by intro h; rw [← h] at hiA; exact Finset.notMem_erase i B hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hBA]
      · by_cases hBA : B = insert i A
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have herase : B.erase i ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.insert_erase hiB]
          simp [e,hiA,Module.Basis.repr_self,herase,hBA]
    · rw [annihilate_unoccupied Q i B hiB]
      have hBA : B ≠ insert i A := by intro h; subst B; simp at hiB
      simp [e,Module.Basis.repr_self,hBA]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

theorem create_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (create i x) A =
      if i ∈ A then insertionSign Q i (A.erase i) * (occupationBasis Q).repr x (A.erase i) else 0 := by
  let e : ℂ := if i ∈ A then insertionSign Q i (A.erase i) else 0
  have h : ((occupationBasis Q).coord A).comp (create i) =
      e • (occupationBasis Q).coord (A.erase i) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (create i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (A.erase i)
    by_cases hiB : i ∈ B
    · rw [create_occupied Q i B hiB]
      have hBA : B ≠ A.erase i := by intro h; rw [h] at hiB; exact Finset.notMem_erase i A hiB
      simp [e,Module.Basis.repr_self,hBA]
    · rw [create_unoccupied Q i B hiB,map_smul,Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · by_cases hBA : B = A.erase i
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have hins : insert i B ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.erase_insert hiB]
          simp [e,hiA,Module.Basis.repr_self,hBA,hins]
      · have hins : insert i B ≠ A := by intro h; rw [← h] at hiA; simp at hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hins]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_ContractionBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Adjoint
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem insertionSign_star (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    star (insertionSign Q i A) = insertionSign Q i A := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_annihilate_adjoint (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q (create i x) y = occupationInner Q x (annihilate i y) := by
  let f : Finset (Fin (Q+1)) → ℂ := fun A =>
    insertionSign Q i (A.erase i) *
      (star ((occupationBasis Q).repr x (A.erase i)) * (occupationBasis Q).repr y A)
  have hl : occupationInner Q (create i x) y =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
    rw [Finset.sum_filter]
    unfold occupationInner
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hi : i ∈ A <;>
      simp only [f, create_coordinate, hi, ite_true, if_true, ite_false, if_false, star_mul,
        insertionSign_star, star_zero, zero_mul, mul_comm, mul_left_comm]
  rw [hl, ← sum_unoccupied_insert i f, Finset.sum_filter]
  unfold occupationInner
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hi : i ∈ A <;>
    simp only [f, hi, annihilate_coordinate, not_true_eq_false, not_false_eq_true,
      ite_true, if_true, ite_false, if_false, Finset.erase_insert, zero_mul, mul_assoc, mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Inner
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_Bidegree
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_empty (Q : ℕ) : occupationBasis Q ∅ = (1 : Space Q) := by
  let A : Set.powersetCard (Fin (Q+1)) 0 := ⟨∅,rfl⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_zero_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Fock_PairNormalization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_vacuum {Q : ℕ} (i : Fin (Q+1)) : annihilate i (1 : Space Q) = 0 := by
  simp [annihilate]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_FourBody_CARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_apply (Q : ℕ) (a b : Fin (Q+1)) (x : Space Q) :
    annihilate a (create b x) = delta a b • x - create b (annihilate a x) := by
  have h := LinearMap.congr_fun (annihilate_create a b) x
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_Antisymmetry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem antisymmetric_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (a : Configuration N Q) :
    ψ (a ∘ σ) = σ.sign • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' generalizing a with
  | one => simp
  | mul_swap σ i j hij ih =>
    change ψ ((a ∘ σ) ∘ Equiv.swap i j) = _
    rw [hψ i j hij, ih]
    simp [map_mul, Equiv.Perm.sign_swap hij]

theorem antisymmetric_insertNth {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (k : Fin (n+1)) (i : Fin (Q+1)) (a : Configuration n Q) :
    ψ (k.insertNth i a) = (-1 : ℂ)^k.val * ψ (Fin.cons i a) := by
  rw [← Fin.cons_comp_cycleRange, antisymmetric_perm hψ]
  simp [Units.smul_def]

theorem antisymmetric_cons {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    Antisymmetric (fun a : Configuration n Q => ψ (Fin.cons i a)) := by
  intro j k hjk a
  change ψ (Fin.cons i (a ∘ Equiv.swap j k)) = _
  rw [show Fin.cons i (a ∘ Equiv.swap j k) =
    Fin.cons i a ∘ Equiv.swap j.succ k.succ from Matrix.cons_swap i a j k]
  exact hψ j.succ k.succ (by simpa using hjk) (Fin.cons i a)

theorem sum_config_insert {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (k : Fin (n+1)) (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (k.insertNth i b) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => Fin (Q+1)) k).sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_config_cons {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (Fin.cons i b) := by
  simpa using sum_config_insert (0 : Fin (n+1)) f

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_ExteriorContraction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem orderedWedge_cons {n Q : ℕ} (i : Fin (Q+1)) (a : Configuration n Q) :
    orderedWedge (Fin.cons i a) = create i (orderedWedge a) := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

theorem orderedWedge_head {n Q : ℕ} (a : Configuration (n+1) Q) :
    orderedWedge a = create (a 0) (orderedWedge (fun j => a j.succ)) := by
  rw [← orderedWedge_cons]
  congr 1
  exact (Fin.cons_self_tail a).symm

theorem annihilate_orderedWedge (n Q : ℕ) (i : Fin (Q+1))
    (a : Configuration (n+1) Q) :
    annihilate i (orderedWedge a) =
      ∑ k : Fin (n+1), ((-1 : ℂ)^k.val * delta i (a k)) •
        orderedWedge (k.removeNth a) := by
  induction n with
  | zero =>
    rw [orderedWedge_head, annihilate_create_apply]
    simp [orderedWedge, ExteriorAlgebra.ιMulti_zero_apply, annihilate_vacuum]
  | succ n ih =>
    rw [orderedWedge_head, annihilate_create_apply, ih, map_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ,
      map_smul]
    have h0 : (0 : Fin (n+2)).removeNth a = fun j => a j.succ := by rfl
    rw [h0]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hw : orderedWedge (k.succ.removeNth a) =
        create (a 0) (orderedWedge (k.removeNth (fun j => a j.succ))) := by
      rw [← orderedWedge_cons]
      congr 1
      have h := Fin.cons_comp_succ_succAbove (a 0) (fun j => a j.succ) k
      have ha : Fin.cons (a 0) (fun j => a j.succ) = a := Fin.cons_self_tail a
      rw [ha] at h
      exact h
    rw [hw]
    simp only [mul_neg_one, neg_mul, neg_smul]

theorem tensorExterior_cons (n Q : ℕ) (ψ : State (n+1) Q) :
    tensorExterior (n+1) Q ψ =
      ∑ i : Fin (Q+1), create i (tensorExterior n Q (fun a => ψ (Fin.cons i a))) := by
  change (∑ a, ψ a • orderedWedge a) = _
  rw [sum_config_cons]
  change (∑ i, ∑ b, ψ (Fin.cons i b) • orderedWedge (Fin.cons i b)) = _
  simp only [orderedWedge_cons,tensorExterior,map_sum,map_smul]
  rfl

theorem annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+1) Q)
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    annihilate i (tensorExterior (n+1) Q ψ) =
      (n+1 : ℂ) • tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
  change annihilate i (∑ a, ψ a • orderedWedge a) = _
  simp only [map_sum,map_smul,annihilate_orderedWedge,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  have hs (k : Fin (n+1)) :
      (∑ a : Configuration (n+1) Q,
        (ψ a * ((-1 : ℂ)^k.val * delta i (a k))) • orderedWedge (k.removeNth a)) =
        tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
    rw [sum_config_insert k]
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      antisymmetric_insertNth hψ]
    have he (x : Fin (Q+1)) (b : Configuration n Q) :
        ((-1 : ℂ)^k.val * ψ (Fin.cons x b) * ((-1 : ℂ)^k.val * delta i x)) =
          delta i x * ψ (Fin.cons x b) := by
      have hpow : ((-1 : ℂ)^k.val)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      calc
        _ = ((-1 : ℂ)^k.val)^2 * (delta i x * ψ (Fin.cons x b)) := by ring
        _ = _ := by rw [hpow,one_mul]
    simp only [he]
    simp [delta,tensorExterior,orderedWedge]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_ExteriorIsometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem tensorExterior_inner (n Q : ℕ) (ψ φ : State n Q) (hφ : Antisymmetric φ) :
    occupationInner Q (tensorExterior n Q ψ) (tensorExterior n Q φ) =
      (n.factorial : ℂ) * ∑ a, star (ψ a) * φ a := by
  induction n with
  | zero =>
    simp only [tensorExterior, ExteriorAlgebra.ιMulti_zero_apply]
    simp only [occupationInner_sum_left,occupationInner_sum_right]
    simp only [occupationInner_smul_left,occupationInner_smul_right]
    have h1 : occupationInner Q 1 1 = 1 := by
      rw [← occupation_empty]
      simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]
    simp [h1,mul_comm]
  | succ n ih =>
    rw [tensorExterior_cons,occupationInner_sum_left]
    simp only [create_annihilate_adjoint,annihilate_tensorExterior n Q φ hφ,
      occupationInner_smul_right]
    simp_rw [ih _ _ (antisymmetric_cons hφ _)]
    rw [sum_config_cons]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Finset.mul_sum]
    ring_nf

theorem normalizedTensorExterior_inner (n Q : ℕ) (ψ φ : State n Q)
    (hφ : Antisymmetric φ) :
    occupationInner Q (normalizedTensorExterior n Q ψ) (normalizedTensorExterior n Q φ) =
      ∑ a, star (ψ a)*φ a := by
  have hp : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he : ((Real.sqrt (n.factorial : ℝ) : ℂ))^2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hp)
  simp only [normalizedTensorExterior,occupationInner_smul_left,occupationInner_smul_right,
    tensorExterior_inner n Q ψ φ hφ]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have hsc : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [← he]
  field_simp

theorem normalizedTensorExterior_norm (n Q : ℕ) (ψ : State n Q)
    (hψ : Antisymmetric ψ) :
    occupationNormSq Q (normalizedTensorExterior n Q ψ) = ∑ a, ‖ψ a‖^2 := by
  have h := normalizedTensorExterior_inner n Q ψ ψ hψ
  rw [occupationInner_self] at h
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  simp only [he,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockEnergyError
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator errors control every normalized occupation-sector energy with
polynomial mode dependence. The tensor and exterior norms are identified. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock HubbardGlobal

theorem occupationInner_fockCoordinates {Q : ℕ} (x y : Space Q) :
    occupationInner Q x y = inner ℂ (fockCoordinates Q x) (fockCoordinates Q y) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply',fockCoordinates_apply,
    occupationInner,occupationBasis,fockBasis,starRingEnd_apply]

theorem occupationNormSq_fockCoordinates {Q : ℕ} (x : Space Q) :
    occupationNormSq Q x = ‖fockCoordinates Q x‖^2 := by
  simp only [fockCoordinates_norm_sq,occupationNormSq,fockMass,occupationBasis,fockBasis,
    Complex.normSq_eq_norm_sq]

theorem occupationInner_operator_error {Q : ℕ} (T U : Module.End ℂ (Space Q))
    (ε : ℝ) (hε : ‖fockOperator (T-U)‖ ≤ ε) (x : Space Q) :
    |(occupationInner Q x (T x)).re-(occupationInner Q x (U x)).re| ≤
      ε*occupationNormSq Q x := by
  rw [occupationInner_fockCoordinates,occupationInner_fockCoordinates,
    ← Complex.sub_re,← inner_sub_right,← map_sub,← LinearMap.sub_apply,
    ← fockOperator_coordinates]
  calc
    _ ≤ ‖inner ℂ (fockCoordinates Q x) (fockOperator (T-U) (fockCoordinates Q x))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖fockCoordinates Q x‖*‖fockOperator (T-U) (fockCoordinates Q x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖fockCoordinates Q x‖*(ε*‖fockCoordinates Q x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((fockOperator (T-U)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
    _ = _ := by rw [occupationNormSq_fockCoordinates]; ring

theorem finiteTensorState_occupationMass {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State n Q) (hc : Laughlin.Antisymmetric c) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) =
      occupationNormSq Q (normalizedTensorExterior n Q c) := by
  rw [finiteTensorState_mass v hv hL2 hpartial (fun a b => by
    split_ifs with h <;> simpa only [h,ite_true, if_true,ite_false, if_false] using ho a b) c,
    normalizedTensorExterior_norm n Q c hc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSiteOneBody
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial one-body matrix acts on both conserved spin modes and
agrees with the actual graph hopping operator. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem oneBodyOperator_spinLift (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ) :
    oneBodyOperator (spinLift m K) = siteOneBody m K := by
  unfold oneBodyOperator siteOneBody
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ σ : Fin 2, ∑ j : Fin (m+1),
        K i j • transfer (siteMode m i σ) (siteMode m j σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← (siteModes m).sum_comp]
      simp only [Fintype.sum_prod_type, spinLift, modeSite, Equiv.symm_apply_apply,
        ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, siteMode]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.sum_univ_two, siteBilinear, smul_add]

theorem siteOneBody_add (m : ℕ) (K L : Fin (m+1) → Fin (m+1) → ℂ) :
    siteOneBody m (fun i j => K i j + L i j) = siteOneBody m K + siteOneBody m L := by
  simp only [siteOneBody, add_smul, Finset.sum_add_distrib]

theorem siteOneBody_sum {I : Type*} [Fintype I] (m : ℕ)
    (K : I → Fin (m+1) → Fin (m+1) → ℂ) :
    siteOneBody m (fun i j => ∑ e, K e i j) = ∑ e, siteOneBody m (K e) := by
  unfold siteOneBody
  simp only [Finset.sum_smul]
  calc
    _ = ∑ i, ∑ e, ∑ j, K e i j • siteBilinear m i j :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem siteOneBody_single (m : ℕ) (i j : Fin (m+1)) (z : ℂ) :
    siteOneBody m (fun k l => if k=i ∧ l=j then z else 0) =
      z • siteBilinear m i j := by
  have h (k l : Fin (m+1)) : (if k=i ∧ l=j then z else 0) =
      if k=i then (if l=j then z else 0) else 0 := by
    by_cases hki : k=i <;> by_cases hlj : l=j <;> simp [hki,hlj]
  simp only [siteOneBody,h,ite_smul,zero_smul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]

theorem oneBodyOperator_graphHopping {Edge : Type*} [Fintype Edge] (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) :
    oneBodyOperator (spinLift m (graphHoppingMatrix m left right t)) =
      graphHopping m left right t := by
  rw [oneBodyOperator_spinLift]
  unfold graphHoppingMatrix
  rw [siteOneBody_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [siteOneBody_add,siteOneBody_single,siteOneBody_single]
  simp only [siteBilinear,siteHopping,twoSiteHopping,bondTransfer,smul_add]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardEnergyLower
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled Hubbard variational bottom bounds every sector
vector, including unnormalized projections of continuum states. -/

noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem hubbardFermionForm_occupation (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    hubbardFermionForm m U V left right t x =
      (occupationInner (2*m+1) x
        ((chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))) x)).re := by
  rw [hubbardFermionForm,euclidean_real_inner,occupationInner_fockCoordinates]

theorem hubbardFermionForm_abs_bound (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    |hubbardFermionForm m U V left right t x| ≤
      ‖fockOperator (chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ)))‖*
        fockMass x := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have he := occupationInner_operator_error T 0 ‖fockOperator T‖ (by simp) x
  have hm := occupationNormSq_fockCoordinates x
  rw [fockCoordinates_norm_sq] at hm
  have hz : occupationInner (2*m+1) x 0 = 0 := by simp [occupationInner]
  rw [hubbardFermionForm_occupation]
  simpa only [LinearMap.zero_apply,hz,Complex.zero_re,sub_zero,hm] using he

theorem hubbardFermionBottom_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    hubbardFermionBottom m U V left right t*fockMass x ≤
      hubbardFermionForm m U V left right t x := by
  have hb : BddBelow {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} := by
    refine ⟨-‖fockOperator (chargePenaltyFock m U V+
      graphHopping m left right (fun e => (t e:ℂ)))‖,?_⟩
    rintro e ⟨y,_hy,hpos,rfl⟩
    apply (le_div_iff₀ hpos).mpr
    have he := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith
  have hm : 0 ≤ fockMass x := by rw [← fockCoordinates_norm_sq]; positivity
  rcases eq_or_lt_of_le hm with hz | hpos
  · have hnorm : ‖fockCoordinates (2*m+1) x‖ = 0 := by
      have h := fockCoordinates_norm_sq x
      rw [← hz] at h
      nlinarith [norm_nonneg (fockCoordinates (2*m+1) x)]
    have hzero : x=0 := (fockCoordinates (2*m+1)).injective (by simpa using norm_eq_zero.mp hnorm)
    subst x
    simp [hubbardFermionForm,fockMass]
  · exact (le_div_iff₀ hpos).mp (csInf_le hb ⟨x,hx,hpos,rfl⟩)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockHubbardForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the compressed Coulomb CAR Hamiltonian
with the full half-filled Hubbard variational problem. -/

noncomputable section
open scoped BigOperators Classical InnerProductSpace
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

variable {Edge : Type*} [Fintype Edge]

theorem hubbardOneBodyMatrix_split (m : ℕ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    hubbardOneBodyMatrix m V left right t = fun a b =>
      spinLift m (graphHoppingMatrix m left right (fun e => (t e:ℂ))) a b +
        if a=b then -((∑ j, V (modeSite m a) j : ℝ):ℂ) else 0 := by
  funext a b
  obtain ⟨⟨i,σ⟩,rfl⟩ := (siteModes m).surjective a
  obtain ⟨⟨j,τ⟩,rfl⟩ := (siteModes m).surjective b
  change _ = _ + if siteMode m i σ=siteMode m j τ then _ else 0
  simp only [hubbardOneBodyMatrix,spinLift,modeSite,Equiv.symm_apply_apply,
    siteMode_eq_iff]
  by_cases hij : i=j <;> by_cases hστ : σ=τ <;> simp [hij,hστ,sub_eq_add_neg]

theorem hubbardCAR_operator (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i=0)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
      twoBodyOperator (hubbardCoulombTensor m U V) =
        siteChargeOperator m U V + graphHopping m left right (fun e => (t e:ℂ)) := by
  rw [hubbardOneBodyMatrix_split]
  have hadd {Q : ℕ} (K L : Fin (Q+1) → Fin (Q+1) → ℂ) :
      oneBodyOperator (fun a b => K a b+L a b) = oneBodyOperator K+oneBodyOperator L := by
    simp only [oneBodyOperator,add_smul,Finset.sum_add_distrib]
  rw [hadd,oneBodyOperator_graphHopping]
  have hd := directCoulomb_operator m U V hdiag
  change _ + twoBodyOperator (fun a b c d => if a=c ∧ b=d then
    siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0) = _
  rw [← hd]
  abel

theorem hubbardCAR_halfFilled (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
      twoBodyOperator (hubbardCoulombTensor m U V)) x =
        (chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))) x -
          (((1/2:ℝ)*∑ i, ∑ j, V i j : ℝ):ℂ) • x := by
  rw [hubbardCAR_operator m U V hdiag,LinearMap.add_apply,
    siteChargeOperator_halfFilled m U V hsymm x hx,LinearMap.add_apply]
  abel

theorem hubbardCAR_form (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (occupationInner (2*m+1) x
      ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
        twoBodyOperator (hubbardCoulombTensor m U V)) x)).re =
      hubbardFermionForm m U V left right t x -
        ((1/2:ℝ)*∑ i, ∑ j, V i j)*fockMass x := by
  rw [hubbardCAR_halfFilled m U V hsymm hdiag left right t x hx,
    occupationInner_fockCoordinates,map_sub,map_smul,inner_sub_right,inner_smul_right]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rw [← euclidean_real_inner,← hubbardFermionForm,inner_self_eq_norm_sq_to_K]
  have hreal (r : ℝ) : ((r:ℂ)^2).re = r^2 := by
    rw [pow_two,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  change hubbardFermionForm m U V left right t x -
    ((1/2:ℝ)*∑ i, ∑ j, V i j)*((‖fockCoordinates (2*m+1) x‖:ℂ)^2).re = _
  rw [hreal,fockCoordinates_norm_sq]

theorem hubbardCAR_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    (hubbardFermionBottom m U V left right t-(1/2:ℝ)*∑ i, ∑ j, V i j)*fockMass x ≤
      (occupationInner (2*m+1) x
        ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
          twoBodyOperator (hubbardCoulombTensor m U V)) x)).re := by
  rw [hubbardCAR_form m U V hsymm hdiag left right t x hx,sub_mul]
  exact sub_le_sub_right (hubbardFermionBottom_lower m U V left right t x hx) _

theorem hubbardCAR_approximation_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j=V j i)
    (hdiag : ∀ i, V i i=0) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) (energy error : ℝ)
    (herr : |energy-(occupationInner (2*m+1) x
      ((oneBodyOperator (hubbardOneBodyMatrix m V left right t) +
        twoBodyOperator (hubbardCoulombTensor m U V)) x)).re| ≤ error*fockMass x) :
    (hubbardFermionBottom m U V left right t-(1/2:ℝ)*∑ i, ∑ j, V i j-error)*
      fockMass x ≤ energy := by
  have h := hubbardCAR_lower m U V hsymm hdiag left right t x hx
  have he := (abs_le.mp herr).1
  nlinarith

end ContinuumCoulomb.HubbardGlobal

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

lemma inverseSqrt_bounds {a x : ℝ} (_ha : 0 ≤ a) (has : a ≤ 1 / 2)
    (hx : 1 - a ≤ x ∧ x ≤ 1 + a) :
    (Real.sqrt x)⁻¹ ≤ 2 ∧ |(Real.sqrt x)⁻¹ - 1| ≤ 2 * a := by
  have hxp : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsq := Real.sq_sqrt hxp.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hinv : (Real.sqrt x)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs).mpr
    linarith
  refine ⟨hinv, ?_⟩
  have hid : ((Real.sqrt x)⁻¹ - 1) *
      (Real.sqrt x * (Real.sqrt x + 1)) = 1 - x := by
    calc
      _ = ((Real.sqrt x)⁻¹ * Real.sqrt x - Real.sqrt x) * (Real.sqrt x + 1) := by ring
      _ = (1 - Real.sqrt x) * (Real.sqrt x + 1) := by rw [inv_mul_cancel₀ hs.ne']
      _ = 1 - x := by nlinarith
  have hden : (1 / 2 : ℝ) ≤ Real.sqrt x * (Real.sqrt x + 1) := by
    nlinarith
  have habs : |1 - x| ≤ a := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hm : |(Real.sqrt x)⁻¹ - 1| * (Real.sqrt x * (Real.sqrt x + 1)) ≤ a := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x * (Real.sqrt x + 1)), ← abs_mul, hid]
    exact habs
  nlinarith [mul_nonneg (abs_nonneg ((Real.sqrt x)⁻¹ - 1)) (sub_nonneg.mpr hden)]

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

lemma correction_norm_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) :
    ‖correction hG‖ ≤ 2 ∧ ‖correction hG - 1‖ ≤ 2 * m * delta := by
  have ha : 0 ≤ (m : ℝ) * delta := mul_nonneg (Nat.cast_nonneg _) hdelta
  have hb (i : Fin m) := inverseSqrt_bounds ha hsmall (eigenvalue_bounds hG hdelta hdiag hoff i)
  have hnorm : ‖correction hG‖ ≤ 2 := by
    rw [correction, ← hG.cfc_eq]
    apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 2)
    intro x hx
    rw [hG.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (hb i).1
  refine ⟨hnorm, ?_⟩
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  rw [correction, ← hG.cfc_eq, ← cfc_const_one ℝ G, ← cfc_sub _ _ G hc continuousOn_const]
  apply norm_cfc_le (by positivity : (0 : ℝ) ≤ 2 * m * delta)
  intro x hx
  rw [hG.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  simpa only [Real.norm_eq_abs, mul_assoc] using (hb i).2

lemma entry_abs_le_norm (B : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) : |B i j| ≤ ‖B‖ := by
  let v : EuclideanSpace ℝ (Fin m) := PiLp.single 2 j 1
  let y : EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B v
  have hy : y i = B i j := by
    change (B *ᵥ Pi.single j (1 : ℝ)) i = B i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    |B i j| = ‖y i‖ := by rw [hy, Real.norm_eq_abs]
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B‖ * ‖v‖ := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B).le_opNorm v
    _ = ‖B‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]; simp only [v, PiLp.norm_single, norm_one, mul_one]

lemma correction_entry_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) (i j : Fin m) :
    |correction hG i j - if i = j then 1 else 0| ≤ 2 * m * delta ∧
      |correction hG i j| ≤ 2 := by
  have hb := correction_norm_bounds hG hdelta hdiag hoff hsmall
  constructor
  · simpa only [Matrix.sub_apply, Matrix.one_apply] using
      (entry_abs_le_norm (correction hG - 1) i j).trans hb.2
  · exact (entry_abs_le_norm (correction hG) i j).trans hb.1

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

theorem correctedLocalizedCoefficients_entries {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    |correctedLocalizedCoefficients u i j - if i=j then 1 else 0| ≤ 2*m*localizedOverlapBound D ∧
      |correctedLocalizedCoefficients u i j| ≤ 2 :=
  GramCorrection.correction_entry_bounds (localizedModeGram_isHermitian u)
    (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
    (planarModeOverlap_offsite u hsep) hs i j

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_PairSpinOrbitals
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin selection rules for the actual Coulomb four-index integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

private theorem realPairIntegrand_eq (f g h k : Position → ℝ) (σ τ κ χ s t : Fin 2)
    (x y : Fin 3 → ℝ) : realPairIntegrand f g h k σ τ κ χ ((s,x),(t,y)) =
      if s=σ ∧ s=κ ∧ t=τ ∧ t=χ then
        ((Coulomb.coulombKernel (WithLp.toLp 2 x-WithLp.toLp 2 y)*
          ((f (WithLp.toLp 2 x)*h (WithLp.toLp 2 x))*
            (g (WithLp.toLp 2 y)*k (WithLp.toLp 2 y))):ℝ):ℂ) else 0 := by
  by_cases h₁ : s=σ <;> by_cases h₂ : s=κ <;> by_cases h₃ : t=τ <;> by_cases h₄ : t=χ <;>
    simp_all [realPairIntegrand,flatPairCoulomb,Coulomb.flatSpinOrbital,realSpinOrbital,
      Complex.ofReal_mul]

private theorem realPairIntegrand_section_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2)
    (st : Fin 2 × Fin 2) :
    Integrable (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      realPairIntegrand f g h k σ τ κ χ ((st.1,z.1),(st.2,z.2))) (volume.prod volume) := by
  simp_rw [realPairIntegrand_eq]
  split_ifs
  · have hm : MeasurePreserving
        ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
          (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) (volume.prod volume) (volume.prod volume) :=
      (PiLp.volume_preserving_toLp (Fin 3)).prod (PiLp.volume_preserving_toLp (Fin 3))
    exact hm.integrable_comp_of_integrable hI.ofReal
  · exact integrable_zero _ _ _

private theorem realPairIntegrand_regroup_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    Integrable (fun z : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      realPairIntegrand f g h k σ τ κ χ ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      (Measure.count.prod (volume.prod volume)) :=
  Coulomb.integrable_finite_count_prod _ (realPairIntegrand_section_integrable f g h k hI σ τ κ χ)

theorem realSpin_coulomb_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    Integrable (realPairIntegrand f g h k σ τ κ χ)
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure) := by
  have hm := Coulomb.pairRegroup_measurePreserving
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [Coulomb.count_prod_count] at hm
  exact hm.integrable_comp_of_integrable
    (realPairIntegrand_regroup_integrable f g h k hI σ τ κ χ)

theorem realSpin_coulomb_integral (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    (∫ z, realPairIntegrand f g h k σ τ κ χ z
      ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)) =
      if σ=κ ∧ τ=χ then
        ((∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
          ((f z.1*h z.1)*(g z.2*k z.2)) ∂(volume.prod volume):ℝ):ℂ) else 0 := by
  have hm := Coulomb.pairRegroup_measurePreserving
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [Coulomb.count_prod_count] at hm
  let F (z : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :=
    realPairIntegrand f g h k σ τ κ χ ((z.1.1,z.2.1),(z.1.2,z.2.2))
  have he := hm.integral_comp' F
  change (∫ z, realPairIntegrand f g h k σ τ κ χ z
    ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)) = _ at he
  rw [he,Coulomb.integral_finite_count_prod F
    (realPairIntegrand_section_integrable f g h k hI σ τ κ χ)]
  have hp : MeasurePreserving
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) (volume.prod volume) (volume.prod volume) :=
    (PiLp.volume_preserving_toLp (Fin 3)).prod (PiLp.volume_preserving_toLp (Fin 3))
  have hsection (s t : Fin 2) :
      (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
        realPairIntegrand f g h k σ τ κ χ ((s,z.1),(t,z.2)) ∂(volume.prod volume)) =
      if s=σ ∧ s=κ ∧ t=τ ∧ t=χ then
        ((∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
          ((f z.1*h z.1)*(g z.2*k z.2)) ∂(volume.prod volume):ℝ):ℂ) else 0 := by
    simp_rw [realPairIntegrand_eq]
    split_ifs
    · exact (hp.integral_comp' (fun z : Position × Position =>
        Complex.ofReal (Coulomb.coulombKernel (z.1-z.2)*((f z.1*h z.1)*(g z.2*k z.2))))).trans
          integral_complex_ofReal
    · simp only [integral_zero]
  dsimp only [F]
  simp only [Fintype.sum_prod_type,hsection]
  fin_cases σ <;> fin_cases τ <;> fin_cases κ <;> fin_cases χ <;> norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate derivatives of tensor products. Cross-coordinate
factors remain constant when differentiating a second time in one slot. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem positionComplexPartial_C1 (f : Position → ℂ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    ContDiff ℝ 1 (positionComplexPartial f b) :=
  (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorOccupationSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every antisymmetric coefficient tensor lies in the complete fixed-particle
occupation sector, including tensors obtained by continuum projection. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock HubbardGlobal

theorem totalNumber_wedgeModes {Q n : ℕ} (v : Fin n → Fin (Q+1)) :
    totalNumber Q (wedgeModes n v) = (n:ℂ) • wedgeModes n v := by
  simp only [totalNumber,LinearMap.sum_apply,number,transfer_wedgeModes]
  rw [Finset.sum_comm]
  have hi (k : Fin n) :
      (∑ i : Fin (Q+1), delta i (v k) •
        wedgeModes n (fun a => if a=k then i else v a)) = wedgeModes n v := by
    simp only [delta,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    congr 1
    funext a
    split_ifs with h
    · subst a
      rfl
    · rfl
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem totalNumber_normalizedTensorExterior {Q n : ℕ} (ψ : Laughlin.State n Q) :
    totalNumber Q (normalizedTensorExterior n Q ψ) =
      (n:ℂ) • normalizedTensorExterior n Q ψ := by
  simp only [normalizedTensorExterior,tensorExterior,map_smul,map_sum]
  have he (a : Laughlin.Configuration n Q) :
      totalNumber Q (ExteriorAlgebra.ιMulti ℂ n (fun i => mode (a i))) =
        (n:ℂ) • ExteriorAlgebra.ιMulti ℂ n (fun i => mode (a i)) :=
    totalNumber_wedgeModes a
  simp only [he,Finset.smul_sum,smul_smul]
  congr 1
  funext a
  congr 1
  ring

theorem normalizedTensorExterior_occupationSupport {Q n : ℕ} (ψ : Laughlin.State n Q)
    (A : Finset (Fin (Q+1))) (hA : A.card ≠ n) :
    (fockBasis Q).repr (normalizedTensorExterior n Q ψ) A = 0 :=
  totalNumber_eigen_coordinate_zero n _ (totalNumber_normalizedTensorExterior ψ) A hA

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHigherMoments
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial moments needed to control the finite-slab
operator residual. All moments refer to the actual normalized orbital density. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem polynomial_exponential_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t^k*Real.exp (-t/2) ≤ (2:ℝ)^k*(k.factorial:ℝ) := by
  have hf : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have he := Real.pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) k
  have hid : ((t/2)^k/(k.factorial:ℝ))*((2:ℝ)^k*(k.factorial:ℝ)) = t^k := by
    rw [div_pow]
    field_simp
  have h := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (2:ℝ)^k*(k.factorial:ℝ) by positivity)
  rw [hid] at h
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t/2)).le
  have hc : (Real.exp (t/2)*((2:ℝ)^k*(k.factorial:ℝ)))*Real.exp (-t/2) =
      (2:ℝ)^k*(k.factorial:ℝ) := by
    rw [mul_right_comm,← Real.exp_add]
    rw [show t/2 + -t/2 = 0 by ring, Real.exp_zero, one_mul]
  exact h'.trans_eq hc

theorem normalizedPlanarMode_norm_moment_integrable (k : ℕ) :
    Integrable (fun r : PlanarPosition => ‖r‖^k*normalizedPlanarMode r^2) := by
  let C := planarExponentialConstant (1/2)^2*((2:ℝ)^k*(k.factorial:ℝ))
  have hmajor := (planar_exp_norm_integrable (by norm_num : (0:ℝ)<1/2)).const_mul C
  have hraw : Integrable (fun r : PlanarPosition => ‖r‖^k*planarResolventMode r^2) := by
    apply hmajor.mono'
      ((continuous_norm.pow k).mul (planarResolventMode_C7.continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with r
    change ‖‖r‖^k*planarResolventMode r^2‖ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖)
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
    have hm := pow_le_pow_left₀ (planarResolventMode_positive r).le
      (planarResolventMode_exponential_envelope (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1) r) 2
    rw [mul_pow] at hm
    have hex : Real.exp (-(1/2:ℝ)*‖r‖)^2 =
        Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖) := by
      rw [pow_two]
      congr 1
      congr 1
      ring
    rw [hex] at hm
    calc
      _ ≤ ‖r‖^k*(planarExponentialConstant (1/2)^2*
          (Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖))) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (norm_nonneg _) _)
      _ = (planarExponentialConstant (1/2)^2*(‖r‖^k*Real.exp (-‖r‖/2)))*
          Real.exp (-(1/2:ℝ)*‖r‖) := by ring
      _ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (polynomial_exponential_bound k (norm_nonneg r))
            (sq_nonneg _)) (Real.exp_pos _).le
  simp_rw [normalizedPlanarMode,div_pow,← mul_div_assoc]
  exact hraw.div_const _

private theorem localizedDensity_even_moment_integrable {freq : ℝ} (hfreq : 0 < freq)
    (k : ℕ) : Integrable (fun x : Position => ‖x‖^(2*k)*localizedDensity freq 0 x) := by
  have hp := (normalizedPlanarMode_norm_moment_integrable (2*k)).mul_prod (verticalMode_square_integrable hfreq)
  have hz := normalizedPlanarMode_square_integrable.mul_prod (verticalMode_moment_integrable hfreq (2*k))
  have hi : Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2) := by
    apply ((hp.add hz).const_mul ((2:ℝ)^(k-1))).mono'
      ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
        ((localizedMode_C7 freq 0).continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖(‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
    have h : (‖p.1‖^2+p.2^2)^k ≤ (2:ℝ)^(k-1)*(‖p.1‖^(2*k)+p.2^(2*k)) := by
      simpa only [← pow_mul] using add_pow_le (sq_nonneg ‖p.1‖) (sq_nonneg p.2) k
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (localizedMode freq 0 p))
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [localizedMode,sub_zero,mul_pow,Pi.add_apply]
    ring
  have ht := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,localizedDensity,continuumLocalizedMode]
  rw [pow_mul, positionSplitCoordinates_norm_sq]

theorem localizedDensity_fourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMomentTail
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated fourth/eighth moments and the weighted tails used in the
finite-slab operator estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem translated_moment {freq : ℝ} (hfreq : 0 < freq) (k : ℕ)
    (hk : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq 0 x))
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) ∧
      localizedDensityMoment freq u k ≤
        (2:ℝ)^(k-1)*(localizedDensityMoment freq 0 k+‖u‖^k) := by
  let c := planarCenter u
  let F (x : Position) := ‖x‖^k*localizedDensity freq 0 x+
    ‖c‖^k*localizedDensity freq 0 x
  have hF : Integrable F := hk.add ((localizedDensity_integrable hfreq 0).const_mul _)
  have hmajor : Integrable (fun x => (2:ℝ)^(k-1)*F (x-c)) :=
    (hF.comp_sub_right c).const_mul _
  have hp (x : Position) : ‖x‖^k*localizedDensity freq u x ≤ (2:ℝ)^(k-1)*F (x-c) := by
    have hn : ‖x‖ ≤ ‖x-c‖+‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-c) c
    have hb := (pow_le_pow_left₀ (norm_nonneg x) hn k).trans
      (add_pow_le (norm_nonneg (x-c)) (norm_nonneg c) k)
    have hm := mul_le_mul_of_nonneg_right hb (localizedDensity_nonnegative freq 0 (x-c))
    rw [localizedDensity_translate]
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F, c]
    ring
  have hi : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) := by
    apply hmajor.mono' ((continuous_norm.pow k).mul (localizedDensity_continuous freq u)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖x‖^k*localizedDensity freq u x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) k)
      (localizedDensity_nonnegative freq u x))]
    exact hp x
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hp
  change localizedDensityMoment freq u k ≤ _ at h
  rw [integral_const_mul, integral_sub_right_eq_self] at h
  dsimp [F] at h
  rw [integral_add hk ((localizedDensity_integrable hfreq 0).const_mul _),
    integral_const_mul, localizedDensity_mass hfreq 0, mul_one] at h
  simpa only [c, planarCenter_norm, localizedDensityMoment] using h

theorem localizedDensity_fourth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 4 ≤ 8*(localizedDensityMoment freq 0 4+‖u‖^4) := by
  convert translated_moment hfreq 4 (localizedDensity_fourth_moment_integrable hfreq) u using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slab's actual harmonic-oscillator residual on a localized
orbital. Interior accuracy and weighted tails are kept separately. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabResidualMultiplier_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabResidualMultiplier rho H S x| ≤
      2*slabUniformBound rho H S+(2*Real.pi*rho)*‖x‖^2 := by
  have hx := slabPotential_abs_bound hrho hH hS x
  have h0 := slabPotential_abs_bound hrho hH hS 0
  have hn : (x 2)^2 ≤ ‖x‖^2 := by
    have h := PiLp.norm_apply_le x 2
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  have hc : 0 ≤ 2*Real.pi*rho := by positivity
  unfold slabResidualMultiplier
  calc
    _ ≤ |slabPotential rho H S x-slabPotential rho H S 0|+
        |2*Real.pi*rho*(x 2)^2| := abs_sub _ _
    _ ≤ 2*slabUniformBound rho H S+(2*Real.pi*rho)*(x 2)^2 := by
      rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg _))]
      have h := (abs_sub (slabPotential rho H S x) (slabPotential rho H S 0)).trans
        (add_le_add hx h0)
      dsimp [slabUniformBound]
      linarith
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hc)

private theorem square_times_density_bound {f : ℝ} {A B t d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hf : |f| ≤ A+B*t) : f^2*d ≤ 2*A^2*d+2*B^2*t^2*d := by
  have hs := (sq_le_sq₀ (abs_nonneg f) (by positivity : 0 ≤ A+B*t)).mpr hf
  rw [sq_abs] at hs
  have hq : f^2 ≤ 2*A^2+2*B^2*t^2 := by nlinarith [sq_nonneg (A-B*t)]
  nlinarith [mul_le_mul_of_nonneg_right hq hd]

theorem slabOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => slabOrbitalResidual rho H S freq u x^2) := by
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : Integrable (fun x : Position =>
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x)) :=
    ((localizedDensity_integrable hfreq u).const_mul _).add
      ((localizedDensity_fourth_moment_translate hfreq u).1.const_mul _)
  apply hmajor.mono'
    ((((slabPotential_continuous hrho hH hS).sub continuous_const).sub
      (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
      (continuumLocalizedMode_C7 freq u).continuous |>.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖slabOrbitalResidual rho H S freq u x^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
    (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH hS x)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoordinateLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate identities for the actual three-dimensional Laplacian. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem directionalSecond_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (c : F) (e x : E) :
    directionalSecond (fun y => f (L y+c)) e x = directionalSecond f (L e) (L x+c) := by
  have hfirst (y : E) : fderiv ℝ (fun z => f (L z+c)) y e =
      fderiv ℝ f (L y+c) (L e) := by
    exact congrArg (fun M : E →L[ℝ] ℝ => M e)
      (((hf.differentiable (by norm_num) _).hasFDerivAt).comp y
        (L.hasFDerivAt.add_const c)).fderiv
  have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y (L e)) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const
  unfold directionalSecond
  simp_rw [hfirst]
  exact congrArg (fun M : E →L[ℝ] ℝ => M e)
    (((hd.differentiable (by norm_num) _).hasFDerivAt).comp x
      (L.hasFDerivAt.add_const c)).fderiv

private theorem split_planar_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (a : Fin 2) (p : SplitPosition) :
    planarPartial (planarPartial (fun r => f (r,p.2)) (planarAxis a)) (planarAxis a) p.1 =
      directionalSecond f (planarAxis a,0) p := by
  change directionalSecond (fun r => f (r,p.2)) (planarAxis a) p.1 = _
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inl ℝ PlanarPosition ℝ) (0,p.2) (planarAxis a) p.1
  simpa only [ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

private theorem split_vertical_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (p : SplitPosition) :
    deriv (deriv (fun z => f (p.1,z))) p.2 = directionalSecond f (0,1) p := by
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inr ℝ PlanarPosition ℝ) (p.1,0) 1 p.2
  simpa only [directionalSecond, fderiv_apply_one_eq_deriv, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

theorem oneElectron_split_laplacian (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => f (positionSplitCoordinates (oneElectronCoordinates y))) x =
      splitLaplacian f (positionSplitCoordinates (oneElectronCoordinates x)) := by
  let L : Configuration 1 →L[ℝ] SplitPosition :=
    positionSplitCoordinates.toContinuousLinearMap.comp oneElectronCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  have hs (a : Fin 3) :
      directionalSecond (fun y => f (positionSplitCoordinates (oneElectronCoordinates y)))
        (EuclideanSpace.single (0,a) 1) x =
      directionalSecond f (positionSplitCoordinates (EuclideanSpace.single a 1))
        (positionSplitCoordinates (oneElectronCoordinates x)) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, oneElectronCoordinates_single, add_zero, L] using
      directionalSecond_affine f hf L 0 (EuclideanSpace.single (0,a) 1) x
  have hp (a : Fin 2) : positionSplitCoordinates (EuclideanSpace.single (Fin.castSucc a) 1) =
      (planarAxis a,0) := by
    rw [← splitCoordinate_planar_axis, ContinuousLinearEquiv.apply_symm_apply]
  have hz : positionSplitCoordinates (EuclideanSpace.single (2:Fin 3) 1) = (0,1) := by
    rw [← splitCoordinate_vertical_axis, ContinuousLinearEquiv.apply_symm_apply]
  unfold configurationRealLaplacian configurationRealPartial
  change (∑ a : Fin 1 × Fin 3, directionalSecond _ (EuclideanSpace.single a 1) x) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp_rw [hs]
  change positionSplitCoordinates (EuclideanSpace.single (Fin.last 2) 1) = (0,1) at hz
  rw [Fin.sum_univ_castSucc (n := 2),hz]
  simp_rw [hp]
  unfold splitLaplacian planarLaplacian
  simp_rw [split_planar_second f hf, split_vertical_second f hf]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOneBody
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual differential action of the full multiwell operator on the
localized modes. Subtraction of the common ground energy leaves exactly the
sum of other wells, so its matrix is the checked hopping matrix plus the
explicit two-tail error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem multiwellAction_localizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (j : Fin m) (p : SplitPosition) :
    multiwellAction freq u (localizedMode freq (u j)) p - ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
  classical
  have hs : (∑ k, manufacturedPlanarWell (p.1 - u k)) =
      manufacturedPlanarWell (p.1 - u j) + (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) := by
    calc
      _ = ∑ k, ((if k = j then manufacturedPlanarWell (p.1 - u j) else 0) +
          (if k = j then 0 else manufacturedPlanarWell (p.1 - u k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j <;> simp [hk]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he := localizedMode_eigen_equation freq (u j) p
  unfold localizedPotential at he
  unfold multiwellAction multiwellPotential
  rw [hs]
  have hm : (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp only [zero_mul]
  rw [← hm]
  nlinarith only [he]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellResidual
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual other-well residual has exponentially small L2 mass.
The square of a nonpositive bounded well is controlled by its negative
well matrix element, so the checked two-tail estimate applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedWellAction_continuous (freq : ℝ) (u w : PlanarPosition) :
    Continuous (localizedWellAction freq u w) :=
  (manufacturedPlanarWell_C7.continuous.comp
    ((positionSplitCoordinates.continuous.fst).sub continuous_const)).mul
      (continuumLocalizedMode_C7 freq u).continuous

theorem localizedWellAction_memLp {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    MemLp (localizedWellAction freq u w) 2 := by
  apply (continuumLocalizedMode_memLp hfreq u).of_le_mul
    (c := PlanarSobolev.wellBound) (localizedWellAction_continuous freq u w).aestronglyMeasurable
  filter_upwards [] with x
  rw [localizedWellAction, norm_mul]
  exact mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec _) (norm_nonneg _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L2 bounds on the actual differential residuals of the localized modes.
The estimate is polynomial in the number of wells; it does not sum over a
many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedMultiwellResidual_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    localizedMultiwellResidual freq u j x =
      multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
        ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [show continuumLocalizedMode freq (u j) x =
    localizedMode freq (u j) (positionSplitCoordinates x) from rfl,
    multiwellAction_localizedMode]
  rfl

theorem localizedMultiwellResidual_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    MemLp (localizedMultiwellResidual freq u j) 2 := by
  classical
  apply memLp_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true, if_true]
    exact MemLp.zero
  · simp only [hk, ite_false, if_false]
    exact localizedWellAction_memLp hfreq _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellFieldOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cutoff and depth-counterterm contribution to the actual localized
one-particle residual. The estimate uses polynomially many spatial modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_abs_bound {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    |planarWellSum u r| ≤ (m : ℝ)*PlanarSobolev.wellBound := by
  unfold planarWellSum
  calc
    _ ≤ ∑ i, |manufacturedPlanarWell (r-u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, PlanarSobolev.wellBound := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
    _ = _ := by simp

theorem countertermWellSum_sub_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r-planarWellSum u r =
      ∑ i, (localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
  unfold countertermWellSum planarWellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem countertermWellSum_sub_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r-planarWellSum u r| ≤
      (m : ℝ)*δ*PlanarSobolev.wellBound := by
  rw [countertermWellSum_sub_eq]
  calc
    _ ≤ ∑ i, |(localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, δ*PlanarSobolev.wellBound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hcoeff i).1]
      exact mul_le_mul (hcoeff i).2 (by
        simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
        (abs_nonneg _) ((hcoeff i).1.trans (hcoeff i).2)
    _ = _ := by simp [mul_assoc]

theorem manufacturedWellField_sub_abs_bound (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (x : Position) :
    |manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1| ≤
      (m : ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  let t := slabWellCutoff S (positionSplitCoordinates x).2
  let a := countertermWellSum freq scale u (positionSplitCoordinates x).1
  let b := planarWellSum u (positionSplitCoordinates x).1
  have ht : 0 ≤ t ∧ t ≤ 1 := slabWellCutoff_bounds _ _
  have hdiff := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
  have hb := planarWellSum_abs_bound u (positionSplitCoordinates x).1
  have h1 : |t-1| ≤ 1 := by rw [abs_of_nonpos (by linarith : t-1 ≤ 0)]; linarith
  have he : t*a-b = t*(a-b)+(t-1)*b := by ring
  change |t*a-b| ≤ _
  rw [he]
  calc
    _ ≤ |t*(a-b)|+|(t-1)*b| := abs_add_le _ _
    _ ≤ (m : ℝ)*δ*PlanarSobolev.wellBound+(m : ℝ)*PlanarSobolev.wellBound := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff))
        ((mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans (by simpa only [one_mul] using hb))
    _ = _ := by ring

theorem wellFieldOrbitalResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => wellFieldOrbitalResidual freq scale S u j x^2) := by
  have hm : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 := by
    apply (continuumLocalizedMode_memLp hfreq (u j)).of_le_mul
      (c := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound)
      ((((manufacturedWellField_C7 freq scale S u).continuous.sub
        ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
        (continuumLocalizedMode_C7 freq (u j)).continuous).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
      continuumLocalizedMode freq (u j) x‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x)
      (norm_nonneg _)
  exact hm.integrable_sq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual for the actual manufactured one-body operator is the sum
of the checked off-site, finite-slab, and cutoff/counterterm residuals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufacturedOrbitalResidual_eq {rho freq : ℝ} (hfreq : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    manufacturedOrbitalResidual rho H S freq scale u j x =
      -(1/2 : ℝ)*splitLaplacian (localizedMode freq (u j)) (positionSplitCoordinates x)+
      manufacturedSlabPotential rho H S freq scale u x*continuumLocalizedMode freq (u j) x-
      ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [manufacturedOrbitalResidual, localizedMultiwellResidual_eq]
  unfold multiwellAction multiwellPotential slabOrbitalResidual slabResidualMultiplier
    wellFieldOrbitalResidual manufacturedSlabPotential planarWellSum
  rw [hfreq]
  simp only [continuumLocalizedMode, positionSplitCoordinates_snd]
  ring

private theorem slab_residual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

private theorem well_residual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (wellFieldOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
    (continuumLocalizedMode_C7 freq (u j)).continuous

theorem manufacturedOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    MemLp (manufacturedOrbitalResidual rho H S freq scale u j) 2 := by
  have hs : MemLp (slabOrbitalResidual rho H S freq (u j)) 2 :=
    (memLp_two_iff_integrable_sq (slab_residual_continuous hrho hH hS freq (u j)).aestronglyMeasurable).mpr
      (slabOrbitalResidual_square_integrable hrho hH hS hfreq (u j))
  have hw : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 :=
    (memLp_two_iff_integrable_sq (well_residual_continuous freq scale S u j).aestronglyMeasurable).mpr
      (wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j)
  exact ((localizedMultiwellResidual_memLp hfreq u j).add hs).add hw

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedManufacturedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram correction preserves a polynomial residual bound: it sums over
spatial modes, independently of the many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem correctedManufacturedResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m) :
    MemLp (correctedManufacturedResidual rho H S freq scale u i) 2 :=
  memLp_finsetSum Finset.univ (fun j _ =>
    (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j).const_mul _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWeakResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential residual is an actual weak-H1 kinetic/potential
pairing identity. This is the bridge used for the off-diagonal form bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronLocalizedMode_laplacian (freq : ℝ) (u : PlanarPosition) (x : Configuration 1) :
    configurationRealLaplacian (oneElectronLocalizedMode freq u) x =
      splitLaplacian (localizedMode freq u) (positionSplitCoordinates (oneElectronCoordinates x)) :=
  oneElectron_split_laplacian _ ((localizedMode_C7 freq u).of_le (by norm_num)) x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedResidualPairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected-orbital mixed forms inherit the manufactured residual
bound on every state in the full one-electron weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronCorrectedMode_C2 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i : Fin m) : ContDiff ℝ 2 (oneElectronCorrectedMode freq u i) :=
  ((localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)).comp oneElectronCoordinates.contDiff

theorem correctedManufacturedResidual_eq {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Configuration 1) :
    correctedManufacturedResidual rho H S freq scale u i (oneElectronCoordinates x) =
      -(1/2:ℝ)*configurationRealLaplacian (oneElectronCorrectedMode freq u i) x+
      manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
        oneElectronCorrectedMode freq u i x-
      ((-1/2:ℝ)+freq/2)*oneElectronCorrectedMode freq u i x := by
  have hlap := configurationRealLaplacian_sum (correctedLocalizedCoefficients u i)
    (fun j => oneElectronLocalizedMode freq (u j)) (fun j => oneElectronLocalizedMode_C2 freq (u j)) x
  have he (j : Fin m) := manufacturedOrbitalResidual_eq hrelation H S scale u j (oneElectronCoordinates x)
  simp_rw [← oneElectronLocalizedMode_laplacian] at he
  change (∑ j, correctedLocalizedCoefficients u i j*
    manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x)) = _
  change configurationRealLaplacian (oneElectronCorrectedMode freq u i) x = _ at hlap
  rw [hlap]
  change _ = -(1/2:ℝ)*(∑ j, correctedLocalizedCoefficients u i j*
    configurationRealLaplacian (oneElectronLocalizedMode freq (u j)) x)+
    manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
      (∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)-
    ((-1/2:ℝ)+freq/2)*(∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j]
  simp only [oneElectronLocalizedMode]
  ring

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coulomb integrals of actual linear combinations of the localized
orbitals. Bounded-L1 packets make the full four-index change of basis an
exact identity, with joint singular-kernel integrability. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace CoulombPacket

theorem sumList_apply (fs : List CoulombPacket) (x : Position) :
    sumList fs x = (fs.map (fun f => f x)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [sumList, add, List.map_cons, List.sum_cons] using congrArg (fun t => f x + t) ih

theorem combination_apply {m : ℕ} (f : Fin m → CoulombPacket) (a : Fin m → ℝ) (x : Position) :
    combination f a x = ∑ j, a j * f j x := by
  rw [combination, sumList_apply, List.map_ofFn, List.sum_ofFn]
  rfl

end CoulombPacket

theorem localizedLinearTransitionPacket_apply {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) (x : Position) :
    localizedLinearTransitionPacket hfreq u a b x =
      localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x := by
  simp only [localizedLinearTransitionPacket, CoulombPacket.combination_apply, one_mul,
    localizedTransitionPacket, localizedTransition, localizedLinearOrbital, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem localizedLinearFourIndex_integrable {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    Integrable (fun p : Position × Position =>
      (localizedLinearOrbital freq u a p.1 * localizedLinearOrbital freq u b p.1) *
      (localizedLinearOrbital freq u c p.2 * localizedLinearOrbital freq u d p.2) *
      Coulomb.coulombKernel (p.1 - p.2)) := by
  simpa only [localizedLinearTransitionPacket_apply] using
    CoulombPacket.joint_integrable (localizedLinearTransitionPacket hfreq u a b)
      (localizedLinearTransitionPacket hfreq u c d)

theorem localizedLinearFourIndex_integral {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    localizedLinearFourIndex hfreq u a b c d =
      ∫ p : Position × Position,
        (localizedLinearOrbital freq u a p.1 * localizedLinearOrbital freq u b p.1) *
        (localizedLinearOrbital freq u c p.2 * localizedLinearOrbital freq u d p.2) *
        Coulomb.coulombKernel (p.1 - p.2) := by
  simp only [localizedLinearFourIndex, CoulombPacket.pair, localizedLinearTransitionPacket_apply]

theorem localizedLinearFourIndex_eq {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    localizedLinearFourIndex hfreq u a b c d =
      ∑ j, ∑ k, ∑ l, ∑ r,
        ((a j * b k) * (c l * d r)) * localizedFourIndex freq (u j) (u k) (u l) (u r) := by
  unfold localizedLinearFourIndex localizedLinearTransitionPacket
  rw [CoulombPacket.pair_combination_left]
  simp_rw [CoulombPacket.pair_combination_left, CoulombPacket.pair_combination_right,
    localizedTransitionPacket_pair hfreq, Finset.mul_sum, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem localizedLinearFourIndex_correction {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (A : Fin m → Fin m → ℝ) {eta : ℝ}
    (he : 0 ≤ eta) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) (i j k l : Fin m) :
    |localizedLinearFourIndex hfreq u (A i) (A j) (A k) (A l) -
      localizedFourIndex freq (u i) (u j) (u k) (u l)| ≤
      (m : ℝ)^4 * (32 * eta * localizedPotentialBound freq) := by
  have hF (p q r s : Fin m) :
      |localizedFourIndex freq (u p) (u q) (u r) (u s)| ≤ localizedPotentialBound freq := by
    rw [abs_of_nonneg (localizedFourIndex_nonnegative hfreq _ _ _ _)]
    have hov : planarModeOverlap (u p) (u q) ≤ 1 := by
      rw [← localizedTransition_mass hfreq]
      exact localizedTransition_mass_le_one hfreq _ _
    exact (localizedFourIndex_le_overlap hfreq _ _ _ _).trans
      ((mul_le_mul_of_nonneg_left hov (localizedPotentialBound_nonnegative freq)).trans_eq (mul_one _))
  rw [localizedLinearFourIndex_eq]
  exact finiteFourIndexChange_bound A (fun p q r s => localizedFourIndex freq (u p) (u q) (u r) (u s))
    he (localizedPotentialBound_nonnegative freq) hA hnear hF i j k l

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual corrected spatial-spin Coulomb tensor differs from its
occupation-diagonal density interaction by the Gram and off-site errors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem correctedLocalizedFourIndex_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (i j k l : Fin m) :
    |localizedLinearFourIndex hf u (correctedLocalizedCoefficients u i)
        (correctedLocalizedCoefficients u k) (correctedLocalizedCoefficients u j)
        (correctedLocalizedCoefficients u l)-
      (if i=k ∧ j=l then localizedFourIndex freq (u i) (u i) (u j) (u j) else 0)| ≤
      (m:ℝ)^4*(32*(2*m*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  have hg := localizedLinearFourIndex_correction hf u (correctedLocalizedCoefficients u)
    (show 0 ≤ 2*(m:ℝ)*localizedOverlapBound D by
      exact mul_nonneg (by positivity) (localizedOverlapBound_nonnegative D))
    (fun a b => (correctedLocalizedCoefficients_entries u hsep hs a b).2)
    (fun a b => (correctedLocalizedCoefficients_entries u hsep hs a b).1) i k j l
  have hb : 0 ≤ localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) :=
    mul_nonneg (localizedFourIndexConstant_nonnegative freq) (Real.exp_pos _).le
  by_cases h : i=k ∧ j=l
  · obtain ⟨rfl,rfl⟩ := h
    simpa only [and_self,ite_true, if_true] using hg.trans (le_add_of_nonneg_right hb)
  · have ho : i ≠ k ∨ j ≠ l := by tauto
    have he := localizedFourIndex_offsite hf u hsep i k j l ho
    simp only [h,ite_false, if_false,sub_zero]
    have ht := abs_add_le
      (localizedLinearFourIndex hf u (correctedLocalizedCoefficients u i)
        (correctedLocalizedCoefficients u k) (correctedLocalizedCoefficients u j)
        (correctedLocalizedCoefficients u l)-localizedFourIndex freq (u i) (u k) (u j) (u l))
      (localizedFourIndex freq (u i) (u k) (u j) (u l))
    simp only [sub_add_cancel] at ht
    exact ht.trans (add_le_add hg he)

theorem localizedSpinMode_coulomb_integrable {freq : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition) (a b c d : Fin ((2*m+1)+1)) :
    Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z.1)*
        Coulomb.flatSpinOrbital (localizedSpinMode freq u c) z.1)*
        (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z.2)*
          Coulomb.flatSpinOrbital (localizedSpinMode freq u d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure) := by
  let p := (HubbardGlobal.siteModes m).symm
  apply realSpin_coulomb_integrable
  convert localizedLinearFourIndex_integrable hf u
    (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
    (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  dsimp only [correctedLocalizedMode,p]
  ring

theorem localizedSpinMode_coulomb_tensor {freq : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition) (a b c d : Fin ((2*m+1)+1)) :
    flatCoulombTensor (localizedSpinMode freq u) a b c d =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then
        (localizedLinearFourIndex hf u (correctedLocalizedCoefficients u (p a).1)
          (correctedLocalizedCoefficients u (p c).1) (correctedLocalizedCoefficients u (p b).1)
          (correctedLocalizedCoefficients u (p d).1):ℂ) else 0 := by
  let p := (HubbardGlobal.siteModes m).symm
  have hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((correctedLocalizedMode freq u (p a).1 z.1*correctedLocalizedMode freq u (p c).1 z.1)*
        (correctedLocalizedMode freq u (p b).1 z.2*correctedLocalizedMode freq u (p d).1 z.2)))
      (volume.prod volume) := by
    convert localizedLinearFourIndex_integrable hf u
      (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
      (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    dsimp only [correctedLocalizedMode]
    ring
  have he : (∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
      ((correctedLocalizedMode freq u (p a).1 z.1*correctedLocalizedMode freq u (p c).1 z.1)*
        (correctedLocalizedMode freq u (p b).1 z.2*correctedLocalizedMode freq u (p d).1 z.2))
      ∂(volume.prod volume)) = localizedLinearFourIndex hf u
        (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
        (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) := by
    rw [localizedLinearFourIndex_integral hf u]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [correctedLocalizedMode]
    ring
  have h := realSpin_coulomb_integral _ _ _ _ hI (p a).2 (p b).2 (p c).2 (p d).2
  change flatCoulombTensor (localizedSpinMode freq u) a b c d = _ at h
  change flatCoulombTensor (localizedSpinMode freq u) a b c d =
    if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then _ else 0
  simpa only [he] using h

theorem localizedSpinMode_coulomb_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
    (a b c d : Fin ((2*m+1)+1)) :
    ‖flatCoulombTensor (localizedSpinMode freq u) a b c d-localizedDensityTensor freq u a b c d‖ ≤
      (m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  let p := (HubbardGlobal.siteModes m).symm
  have he := correctedLocalizedFourIndex_error hf u hsep hs (p a).1 (p b).1 (p c).1 (p d).1
  rw [localizedSpinMode_coulomb_tensor hf]
  change ‖(if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then _ else 0)-_‖ ≤ _
  by_cases hspin : (p a).2=(p c).2 ∧ (p b).2=(p d).2
  · have heq : ((p a).1=(p c).1 ∧ (p b).1=(p d).1) ↔ (a=c ∧ b=d) := by
      constructor
      · rintro ⟨hac,hbd⟩
        exact ⟨p.injective (Prod.ext hac hspin.1),p.injective (Prod.ext hbd hspin.2)⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨rfl,rfl⟩
    rw [ite_eq_left hspin]
    dsimp only [localizedDensityTensor]
    simp only [heq] at he
    split_ifs at he ⊢ <;> simpa only [← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,Complex.ofReal_zero,sub_zero,Nat.cast_add,Nat.cast_one] using he
  · have hne : ¬(a=c ∧ b=d) := by rintro ⟨rfl,rfl⟩; exact hspin ⟨rfl,rfl⟩
    rw [ite_eq_right hspin]
    simp only [localizedDensityTensor,ite_eq_right hne,sub_self,norm_zero]
    have hp := localizedPotentialBound_nonnegative freq
    have hov := localizedOverlapBound_nonnegative D
    exact add_nonneg (by positivity)
      (mul_nonneg (localizedFourIndexConstant_nonnegative freq) (Real.exp_pos _).le)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbard
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized direct Coulomb matrix satisfies the full charge
penalty condition used by the complete half-filled Hubbard comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedOffsiteCoulomb_diagonal {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedOffsiteCoulomb freq u i i = 0 := by simp [localizedOffsiteCoulomb]

theorem localizedOffsiteCoulomb_symmetric {m : ℕ} {freq : ℝ} (hfreq : 0 < freq)
    (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOffsiteCoulomb freq u i j = localizedOffsiteCoulomb freq u j i := by
  simp only [localizedOffsiteCoulomb, eq_comm]
  rw [localizedCoulombCoeff_symmetric hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbardTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized direct-Coulomb tensor has exactly the on-site
and off-site coefficients of the Hubbard charge operator. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedDensityTensor_hubbard (freq : ℝ) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) :
    localizedDensityTensor freq u = hubbardCoulombTensor m
      (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) := by
  funext a b c d
  by_cases h : a=c ∧ b=d
  · simp only [localizedDensityTensor,hubbardCoulombTensor,ite_eq_left h]
    rw [localizedFourIndex_diagonal]
    by_cases hs : modeSite m a = modeSite m b
    · simp only [siteCoulombCoefficient,ite_eq_left hs]
      change (localizedCoulombCoeff freq (u (modeSite m a))
        (u (modeSite m b)) : ℂ) = _
      rw [hs,localizedCoulombCoeff_distance,sub_self,norm_zero]
    · change (localizedCoulombCoeff freq (u (modeSite m a))
        (u (modeSite m b)) : ℂ) = _
      simp only [siteCoulombCoefficient,ite_eq_right hs,localizedOffsiteCoulomb]
  · simp only [localizedDensityTensor,hubbardCoulombTensor,ite_eq_right h]

theorem localizedSpinMode_hubbard_tensor_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
    (a b c d : Fin ((2*m+1)+1)) :
    ‖flatCoulombTensor (localizedSpinMode freq u) a b c d-
      hubbardCoulombTensor m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) a b c d‖ ≤
      (m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  rw [← localizedDensityTensor_hubbard]
  exact localizedSpinMode_coulomb_error hf u hsep hs a b c d

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTensorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual corrected manufactured orbital residuals, lifted to both spin
components and all electron coordinates, satisfy a polynomial L2 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (j : Fin ((2*m+1)+1)) (s : Fin 2) :
    MemLp (fun x => localizedSpinResidual rho H S freq scale u j x s) 2 :=
  realSpinOrbital_memLp _
    (correctedManufacturedResidual_memLp hrho hH hS hfreq scale u hη hcoeff _) _ s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronComplexLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-electron coordinate isometry identifies the physical complex
Laplacian with the Laplacian already used for the manufactured real orbitals. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem configurationComplexPartial_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 1 f) (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => (f y:ℂ)) a x =
      (configurationRealPartial f a x:ℂ) := by
  exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1))
    (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem configurationComplexLaplacian_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Configuration n) :
    configurationComplexLaplacian (fun y => (f y:ℂ)) x =
      (configurationRealLaplacian f x:ℂ) := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => (f y:ℂ)) a =
        (fun y => (configurationRealPartial f a y:ℂ)) :=
    funext (configurationComplexPartial_ofReal f (hf.of_le (by norm_num)) a)
  simp only [configurationComplexLaplacian,hfirst,
    configurationComplexPartial_ofReal _ (configurationRealPartial_C1 hf _),
    configurationRealLaplacian,Complex.ofReal_sum]

theorem oneElectron_complex_partial (f : Position → ℂ) (hf : ContDiff ℝ 1 f)
    (b : Fin 3) (x : Configuration 1) :
    configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) x =
      positionComplexPartial f b (oneElectronCoordinates x) := by
  have h := (hf.differentiable (by norm_num) (oneElectronCoordinates x)).hasFDerivAt.comp x
    oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  simpa only [configurationComplexPartial,positionComplexPartial,Function.comp_def,
    ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,oneElectronCoordinates_single] using
      congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (EuclideanSpace.single (0,b) 1)) h.fderiv

theorem oneElectron_complex_laplacian (f : Position → ℂ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationComplexLaplacian (fun y => f (oneElectronCoordinates y)) x =
      positionComplexLaplacian f (oneElectronCoordinates x) := by
  have hfirst (b : Fin 3) :
      configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) =
        (fun y => positionComplexPartial f b (oneElectronCoordinates y)) :=
    funext (oneElectron_complex_partial f (hf.of_le (by norm_num)) b)
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type,Fin.sum_univ_one]
  simp only [hfirst,oneElectron_complex_partial _ (positionComplexPartial_C1 f hf _),
    positionComplexLaplacian]

theorem correctedManufacturedResidual_complex_laplacian {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Position) :
    (correctedManufacturedResidual rho H S freq scale u i x:ℂ) =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => (correctedLocalizedMode freq u i y:ℂ)) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*(correctedLocalizedMode freq u i x:ℂ)-
      (((-1/2:ℝ)+freq/2):ℂ)*(correctedLocalizedMode freq u i x:ℂ) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u i) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)
  have hx := correctedManufacturedResidual_eq hrelation H S scale u i (oneElectronCoordinates.symm x)
  have hL := oneElectron_complex_laplacian (fun y => (correctedLocalizedMode freq u i y:ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (oneElectronCoordinates.symm x)
  change configurationComplexLaplacian (fun y => (oneElectronCorrectedMode freq u i y:ℂ))
    (oneElectronCoordinates.symm x) = _ at hL
  rw [configurationComplexLaplacian_ofReal _ (oneElectronCorrectedMode_C2 freq u i)] at hL
  simp only [LinearIsometryEquiv.apply_symm_apply] at hx hL
  rw [← hL, hx]
  simp only [oneElectronCorrectedMode,LinearIsometryEquiv.apply_symm_apply]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedSpinOperator
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-body differential residual of each corrected spatial-spin mode. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinMode_C2 (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) : ContDiff ℝ 2 (fun x => localizedSpinMode freq u j x s) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u ((HubbardGlobal.siteModes m).symm j).1) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u _)).of_le (by norm_num)
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_true, if_true,Function.comp_def,
      Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hf
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_false, if_false] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : Position => (0:ℂ)))

theorem localizedSpinResidual_operator {rho freq : ℝ} (hrelation : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) (x : Position) :
    localizedSpinResidual rho H S freq scale u j x s =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => localizedSpinMode freq u j y s) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*localizedSpinMode freq u j x s-
      (((-1/2:ℝ)+freq/2):ℂ)*localizedSpinMode freq u j x s := by
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,ite_true, if_true] using
      correctedManufacturedResidual_complex_laplacian hrelation H S scale u
        ((HubbardGlobal.siteModes m).symm j).1 x
  · simp [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,
      positionComplexLaplacian,positionComplexPartial]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbardForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured continuum form on its localized tensor space
is controlled by the full half-filled Hubbard variational problem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal Laughlin.Fock

section LocalizedForm
variable (hdensity : PublishedSobolevSmoothDensity)
variable {Edge : Type*} [Fintype Edge]
variable {n m : ℕ} {rho H S freq scale δ D ε : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hf : 0 < freq)
variable (hrelation : freq^2 = 4*Real.pi*rho) (hscale : 0 < scale)
variable (u : Fin (m+1) → PlanarPosition)
variable (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
variable (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
variable (hδ : 0 ≤ δ)
variable (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
  localizedCounterterm freq u i/scale ≤ δ)
variable (F : Position → ℝ)
variable (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
  (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
    Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure)
variable (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
variable (hK : ∀ a b, ‖(scale:ℂ)*
  (flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b+
    flatNuclearMatrix (localizedSpinMode freq u) F a b)-
  hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ ε)
variable (c : Laughlin.State (n+2) (2*m+1)) (hc : Laughlin.Antisymmetric c)
variable (hI : nuclearFormIntegrable F (finiteTensorState (localizedSpinMode freq u)
  (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
  (localizedSpinMode_partial_memLp hf u) c))

include hdensity hrho hH hS hf hrelation hscale hsep hs hδ hcoeff hN hK hc hI

theorem localizedTensor_hubbard_form_error :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
    let x := normalizedTensorExterior (n+2) (2*m+1) c
    |scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p-
        (n+2:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)-
      (occupationInner (2*m+1) x
        ((oneBodyOperator (hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t)+
          twoBodyOperator (hubbardCoulombTensor m (localizedCoulombProfile freq 0)
            (localizedOffsiteCoulomb freq u))) x)).re| ≤
      localizedHubbardFormError m freq D ε*Coulomb.mass p := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hsum (z : Configuration (n+2)) :
      |∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position z i)| ≤
        (n+2:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_ofNat] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => hB (Coulomb.position z i))
  have he := finiteTensorState_form_approximation (n := n) (Q := 2*m+1) hdensity
    (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_C2 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hf scale u hδ hcoeff)
    (localizedSpinMode_inner hf u hsep hs)
    (manufacturedSlabPotential rho H S freq scale u)
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u)
    ((-1/2:ℝ)+freq/2) ((n+2:ℝ)*B) scale⁻¹ hsum
    (fun a s x => by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
        Complex.ofReal_one,Complex.ofReal_ofNat] using
        localizedSpinResidual_operator hrelation H S scale u a s x)
    F hN (localizedSpinMode_coulomb_integrable hf u) c hc hI scale ε
    ((m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
      localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D))
    (hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t)
    (hubbardCoulombTensor m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)) hK
    (fun a b c d => by
      rw [← Complex.ofReal_mul,mul_inv_cancel₀ (ne_of_gt hscale),Complex.ofReal_one,one_mul]
      exact localizedSpinMode_hubbard_tensor_error hf u hsep hs a b c d)
  simpa only [localizedHubbardFormError,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using he

theorem localizedTensor_hubbard_lower_oai (hNelec : n+2=m+1) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
    (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+
      hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
      localizedHubbardFormError m freq D ε)*Coulomb.mass p ≤
      scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p) := by
  let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
  let x := normalizedTensorExterior (n+2) (2*m+1) c
  have hx : IsHalfFilled m x := by
    intro A hA
    exact normalizedTensorExterior_occupationSupport c A (by omega)
  have hm := finiteTensorState_occupationMass (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs) c hc
  rw [occupationNormSq_fockCoordinates,fockCoordinates_norm_sq] at hm
  have he := localizedTensor_hubbard_form_error hdensity hrho hH hS hf hrelation hscale u hsep hs
    hδ hcoeff F hN left right t hK c hc hI
  have hl := hubbardCAR_approximation_lower m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) (localizedOffsiteCoulomb_symmetric hf u)
    (localizedOffsiteCoulomb_diagonal freq u) left right t x hx
    (scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
      (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p-
      (n+2:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)) (localizedHubbardFormError m freq D ε) (by
        change Coulomb.mass p = fockMass x at hm
        rw [← hm]
        exact he)
  change Coulomb.mass p = fockMass x at hm
  rw [← hm] at hl
  dsimp only
  nlinarith only [hl]

end LocalizedForm

end ContinuumCoulomb

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ContinuumCoulomb.localizedTensor_hubbard_lower_oai.{u_1} := @OAI.ContinuumCoulomb.localizedTensor_hubbard_lower_oai.{u_1}
