-- Prove2me | solution 1 for OAI.ContinuumCoulomb.finiteTensorState_form_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:57:54.64038+00:00
-- url     : https://prove2.me/submissions/85c0c87d-0ebe-4cf3-81e2-c91080d0a3c6

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
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.RCLike.Basic
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A007

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_HardyMollifier
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
open ContinuousLinearMap
open scoped Convolution

lemma hardyCoulomb_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : 0 ≤ hardyCoulomb i R x := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma quadratic_young_reciprocal (t : ℝ) {η : ℝ} (hη : 0 < η) :
    t ≤ η * t^2 + 1 / (4 * η) := by
  calc
    t ≤ (4 * η^2 * t^2 + 1) / (4 * η) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η)).mpr
      nlinarith [sq_nonneg (2 * η * t - 1)]
    _ = η * t^2 + 1 / (4 * η) := by field_simp

lemma H1Vector.coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) ∧
    (∫ x, hardyCoulomb i R x * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  have hH := ψ.hardy s i R
  have hρ : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (ψ.value_L2 s).aestronglyMeasurable).mp (ψ.value_L2 s)
  have hB : Integrable (fun x => η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2) :=
    (hH.1.const_mul η).add (hρ.const_mul (1 / (4 * η)))
  have hpoint : ∀ x, hardyCoulomb i R x * ‖ψ.value s x‖^2 ≤
      η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2 := by
    intro x
    have ht := mul_le_mul_of_nonneg_right
      (quadratic_young_reciprocal (hardyCoulomb i R x) hη) (sq_nonneg ‖ψ.value s x‖)
    simpa only [hardyCoulomb_sq, add_mul, mul_assoc] using ht
  have hI : Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) := by
    apply hB.mono' ((measurable_hardyCoulomb i R).aestronglyMeasurable.mul
      ((ψ.value_L2 s).aestronglyMeasurable.norm.pow 2))
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hardyCoulomb_nonneg i R x) (sq_nonneg _))] using hpoint x
  refine ⟨hI, ?_⟩
  have hm := integral_mono hI hB hpoint
  rw [integral_add (hH.1.const_mul η) (hρ.const_mul (1 / (4 * η))),
    integral_const_mul, integral_const_mul] at hm
  have hhard := mul_le_mul_of_nonneg_left hH.2 hη.le
  nlinarith

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Add
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
open ContinuousLinearMap
open scoped Convolution

lemma H1Vector.pair_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i j : Fin n) (hij : i ≠ j) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_pair] using
    ψ.coulomb_integrable_bound s i (pairHardyCoordinates i j hij) hη

lemma H1Vector.pair_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n) :
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n,
      if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖^2) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0 : ℝ) < 1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

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

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] [SigmaFinite ν] in

lemma tensorPair_memLp [SFinite μ] {w : B → ℂ} {v : A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) :
    MemLp (fun z : B × A => w z.1 * v z.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hw.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hw.norm.integrable_sq.mul_prod hv.norm.integrable_sq

end FiberContraction

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_DeterminantWave
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
namespace Coulomb

lemma tensor_weight_factor {A : Type*} {n : ℕ} (f : Fin n → A → ℂ)
    (w : A → ℂ) (i : Fin n) (x : Fin n → A) :
    w (x i) * ∏ j, f j (x j) =
      ∏ j, (if j = i then w (x j) * f j (x j) else f j (x j)) := by
  calc
    w (x i) * ∏ j, f j (x j) =
        (w (x i) * f i (x i)) * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)]
      ring
    _ = (if i = i then w (x i) * f i (x i) else f i (x i)) *
        ∏ j ∈ Finset.univ.erase i, if j = i then w (x j) * f j (x j) else f j (x j) := by
      simp only [ite_true, if_true]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact (ite_eq_right (Finset.mem_erase.mp hj).1).symm
    _ = _ := Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then w (x j) * f j (x j) else f j (x j)) (Finset.mem_univ i)

lemma weighted_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n)
    (hf : ∀ j, Integrable (f j) μ) (hwi : Integrable (fun a => w a * f i a) μ) :
    Integrable (fun x : Fin n → A => w (x i) * ∏ j, f j (x j))
      (Measure.pi fun _ => μ) := by
  simp_rw [tensor_weight_factor]
  apply Integrable.fintype_prod (f := fun j a => if j = i then w a * f j a else f j a)
  intro j
  by_cases h : j = i
  · subst j; simpa only [ite_true, if_true] using hwi
  · simpa only [ite_eq_right h] using hf j

lemma weighted_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) * ∏ j, f j (x j) ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * f i a ∂μ) * ∏ j ∈ Finset.univ.erase i, ∫ a, f j a ∂μ := by
  simp_rw [tensor_weight_factor]
  rw [integral_fintype_prod_eq_prod (f := fun j a => if j = i then w a * f j a else f j a) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
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

theorem kinetic_eq_graphKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u = graphKinetic (h1Coordinates u) := by
  simp only [Coulomb.kinetic, graphKinetic, h1Coordinates_norm_sq, h1CoordinateFunction]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_BoundedFormCross
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization of the actual bounded-potential quadratic form on the
full weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb


theorem Lp_real_inner_eq_re {n : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def,L2.inner_def]
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re) = (∫ x, inner ℂ (f x) (g x)).re at hr
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [] with x
  exact real_inner_eq_re_inner ℂ (f x) (g x)

private theorem re_finite_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i, z i).re = ∑ i, (z i).re :=
  map_sum Complex.reLm z Finset.univ

theorem graphBoundedCross_eq_re {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) :
    graphBoundedCross A f g = (graphComplexCross A f g).re := by
  simp only [graphBoundedCross,graphComplexCross,Lp_real_inner_eq_re,Complex.add_re,
    Complex.mul_re,re_finite_sum]
  norm_num

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo
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
namespace Coulomb

lemma pairSplit_first {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.1 = x i := by
  change x ((pairIndexEquiv i j hij) 0).1 = x i
  simp [pairIndexEquiv]

lemma pairSplit_second {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.2 = x j := by
  change x ((pairIndexEquiv i j hij) 1).1 = x j
  simp [pairIndexEquiv]

lemma pairSplit_rest {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) (k : {k : I // ¬ (k = i ∨ k = j)}) :
    ((pairSplit i j hij) x).2 k = x k := rfl

lemma pairSplit_measurePreserving {I A : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] (i j : I) (hij : i ≠ j) :
    MeasurePreserving (pairSplit (A := A) i j hij) (Measure.pi fun _ => μ)
      ((μ.prod μ).prod (Measure.pi fun _ => μ)) := by
  have hp : MeasurePreserving (pairSelectedEquiv (A := A) i j hij)
      (Measure.pi fun _ => μ) (μ.prod μ) :=
    (measurePreserving_finTwoArrow μ).comp
      ((measurePreserving_piCongrLeft (fun _ => μ) (pairIndexEquiv i j hij)).symm)
  exact (hp.prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (fun k => k = i ∨ k = j))

lemma prod_erase_pair {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j)
    (f : I → ℂ) :
    (∏ k, f k) = (f i * f j) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    ← mul_assoc]
  congr 1
  exact Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) f

lemma pair_weight_tensor_integrable {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) (hf : ∀ k, Integrable (f k) μ)
    (hw : Integrable (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2)) (μ.prod μ)) :
    Integrable (fun x : I → A => w (x i) (x j) * ∏ k, f k (x k)) (Measure.pi fun _ => μ) := by
  have hR : Integrable (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (x k))
      (Measure.pi fun _ => μ) := Integrable.fintype_prod (fun k => hf k)
  have h := (pairSplit_measurePreserving μ i j hij).integrable_comp_of_integrable (hw.mul_prod hR)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply, pairSplit_first, pairSplit_second, pairSplit_rest,
    prod_erase_pair i j hij]
  ring

lemma pair_weight_tensor_integral {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) :
    (∫ x : I → A, w (x i) (x j) * ∏ k, f k (x k) ∂(Measure.pi fun _ => μ)) =
      (∫ ab : A × A, w ab.1 ab.2 * (f i ab.1 * f j ab.2) ∂(μ.prod μ)) *
        ∏ k ∈ (Finset.univ.erase i).erase j, ∫ a, f k a ∂μ := by
  have he (x : I → A) : w (x i) (x j) * ∏ k, f k (x k) =
      (w ((pairSplit i j hij) x).1.1 ((pairSplit i j hij) x).1.2 *
        (f i ((pairSplit i j hij) x).1.1 * f j ((pairSplit i j hij) x).1.2)) *
          ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (((pairSplit i j hij) x).2 k) := by
    simp only [pairSplit_first, pairSplit_second, pairSplit_rest, prod_erase_pair i j hij]
    ring
  simp_rw [he]
  rw [(pairSplit_measurePreserving μ i j hij).integral_comp'
    (fun z => (w z.1.1 z.1.2 * (f i z.1.1 * f j z.1.2)) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (z.2 k)),
    integral_prod_mul (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2))
      (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k, f k.1 (x k)),
    integral_fintype_prod_eq_prod]
  congr 1
  exact (Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) (fun k => ∫ a, f k a ∂μ)).symm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakH1Pairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts against a noncompact square-integrable C1 function
on the actual weak-H1 graph. Compact approximation is used only through the
explicit published Sobolev density input. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem complex_C1_compact_test_ibp {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (a : Configuration n) :
    (∫ x, f x*fderiv ℝ g x a) = -(∫ x, fderiv ℝ f x a*g x) := by
  have hf' : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x a) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hf'.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hf.continuous.mul hg').integrable_of_hasCompactSupport (hc.fderiv_apply ℝ a).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorFirstReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing one orbital in a finite tensor expansion costs the squared
L2 size of the replacement family, without an exponential dimension factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorCoefficientSlice_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) (a : ι) :
    MemLp (tensorCoefficientSlice v c a) 2 (Measure.pi fun _ : Fin n => μ) := by
  unfold tensorCoefficientSlice
  exact memLp_finsetSum Finset.univ (fun b _ =>
    (Coulomb.scalarTensor_memLp v hv b).const_mul (c a b))

theorem tensorFirstReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) :
    MemLp (tensorFirstReplacement v r c) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  unfold tensorFirstReplacement
  exact memLp_finsetSum Finset.univ (fun a _ =>
    Coulomb.tensorPair_memLp (tensorCoefficientSlice_memLp v hv c a) (hr a))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorSlotReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual in any electron coordinate has the same polynomial bound.
The regrouping is an exact measure-preserving separation of that coordinate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorSlotReplacement_regroup {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin (n+1) → ι) → ℂ)
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    tensorSlotReplacement v r c i x =
      tensorFirstReplacement v r (fun a b => c (i.insertNth a b)) (i.removeNth x,x i) := by
  unfold tensorSlotReplacement
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => ι) i).sum_comp
    (fun b => c b * ∏ j, if j=i then r (b j) (x j) else v (b j) (x j))]
  rw [Fintype.sum_prod_type]
  unfold tensorFirstReplacement tensorCoefficientSlice
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNthEquiv_apply,Fin.insertNth_apply_same,ite_true, if_true,
    Fin.succAbove_ne,ite_false, if_false,Fin.insertNth_apply_succAbove]
  change c (i.insertNth a b) * (r a (x i) * ∏ j, v (b j) (x (i.succAbove j))) =
    (c (i.insertNth a b) * ∏ j, v (b j) (x (i.succAbove j))) * r a (x i)
  ring

theorem separateTensorSlot_apply {A : Type*} [MeasurableSpace A] {n : ℕ}
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    separateTensorSlot i x = (i.removeNth x,x i) := rfl

theorem separateTensorSlot_measurePreserving {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (separateTensorSlot i)
      (Measure.pi fun _ : Fin (n+1) => μ) ((Measure.pi fun _ : Fin n => μ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) i)

theorem tensorSlotReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    MemLp (tensorSlotReplacement v r c i) 2 (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (tensorFirstReplacement_memLp v r hv hr (fun a b => c (i.insertNth a b))).comp_measurePreserving
    (separateTensorSlot_measurePreserving (μ := μ) i)
  simpa only [Function.comp_def,separateTensorSlot_apply,← tensorSlotReplacement_regroup] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_FullSpinTensorCoefficients
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakComplexLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for a complex C2 orbital against the full weak-H1
space. Only the sum of its second derivatives is required to lie in L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem configurationComplexPartial_C1 {n : ℕ} {φ : Configuration n → ℂ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationComplexPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem h1_inner_complex_coordinate {n : ℕ} (u : Coulomb.H1Vector n)
    (a : H1Index n) (φ : Configuration n → ℂ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.toLp φ) (h1Coordinates u a) =
      ∫ x, star (φ x)*h1CoordinateFunction u a x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp,(h1Coordinate_memLp u a).coeFn_toLp] with x hp hu
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  rw [hp,hu,RCLike.inner_apply]
  exact mul_comm _ _

theorem weakH1_complex_laplacian_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hpartial : ∀ a, MemLp (configurationComplexPartial φ a) 2)
    (hlap : MemLp (configurationComplexLaplacian φ) 2)
    (v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    (∑ a, ∫ x, star (configurationComplexPartial φ a x)*v.gradient s a x) =
      -(∫ x, star (configurationComplexLaplacian φ x)*v.value s x) := by
  let G (a : Fin n × Fin 3) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hpartial a).toLp (configurationComplexPartial φ a)
  let L : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    hlap.toLp (configurationComplexLaplacian φ)
  have hpair (w : Coulomb.H1Vector n) (a : Fin n × Fin 3) :
      inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a))) =
        ∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x :=
    h1_inner_complex_coordinate w (Sum.inr (s,a)) _ (hpartial a)
  have hlpair (w : Coulomb.H1Vector n) :
      inner ℂ L (h1Coordinates w (Sum.inl s)) =
        ∫ x, star (configurationComplexLaplacian φ x)*w.value s x :=
    h1_inner_complex_coordinate w (Sum.inl s) _ hlap
  have hcompact (w : Coulomb.H1Vector n)
      (hw : ∀ t, ContDiff ℝ 1 (w.value t) ∧ HasCompactSupport (w.value t))
      (hd : ∀ t a x, w.gradient t a x =
        fderiv ℝ (w.value t) x (EuclideanSpace.single a 1)) :
      (∑ a, inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a)))) =
        -inner ℂ L (h1Coordinates w (Sum.inl s)) := by
    have hi (a : Fin n × Fin 3) : Integrable (fun x =>
        star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) :=
      (((configurationComplexPartial_C1 hφ a).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).star.mul (hw s).1.continuous |>.integrable_of_hasCompactSupport (hw s).2.mul_left
    have he (a : Fin n × Fin 3) :
        (∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x) =
          -(∫ x, star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) := by
      have hc := configurationComplexPartial_C1 hφ a
      have hstar (x : Configuration n) :
          fderiv ℝ (fun y => star (configurationComplexPartial φ a y)) x
            (EuclideanSpace.single a 1) =
          star (configurationComplexPartial (configurationComplexPartial φ a) a x) := by
        exact congrArg (fun B : Configuration n →L[ℝ] ℂ => B (EuclideanSpace.single a 1))
          (Complex.conjCLE.hasFDerivAt.comp x (hc.differentiable (by norm_num) x).hasFDerivAt).fderiv
      have hh := complex_C1_compact_test_ibp (fun x => star (configurationComplexPartial φ a x))
        (w.value s) (Complex.conjCLE.contDiff.comp hc) (hw s).1 (hw s).2
          (EuclideanSpace.single a 1)
      simpa only [hd,hstar] using hh
    simp only [hpair,hlpair]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [configurationComplexLaplacian,star_sum,Finset.sum_mul]
  obtain ⟨w,hw,hd,ht⟩ := exists_compact_h1_graph_sequence hdensity v
  have hcG : Continuous (fun f : H1Coordinates n =>
      ∑ a, inner ℂ (G a) (f (Sum.inr (s,a)))) :=
    continuous_finsetSum _ (fun a _ => continuous_const.inner (continuous_apply _))
  have hcL : Continuous (fun f : H1Coordinates n => -inner ℂ L (f (Sum.inl s))) :=
    (continuous_const.inner (continuous_apply _)).neg
  have heq := tendsto_nhds_unique (hcG.continuousAt.tendsto.comp ht)
    ((hcL.continuousAt.tendsto.comp ht).congr' (Filter.Eventually.of_forall
      (fun k => (hcompact (w k) (hw k) (hd k)).symm)))
  simpa only [hpair,hlpair] using heq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem coordinateProduct_C2 {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (coordinateProduct f) := by
  apply contDiff_prod
  intro i _
  exact (hf i).comp (Coulomb.positionCLM i).contDiff

theorem coordinateProduct_partial {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (coordinateProduct f) (i,b) x =
      positionComplexPartial (f i) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  exact tensorOrbital_C1_fderiv (fun j y _ => f j y) (fun j _ => hf j) id
    (fun _ => 0) x i b

theorem coordinateProduct_partial_product {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) :
    configurationComplexPartial (coordinateProduct f) (i,b) =
      coordinateProduct (fun j y => if j=i then positionComplexPartial (f j) b y else f j y) := by
  funext x
  rw [coordinateProduct_partial f hf i b x]
  change _ = Coulomb.slotTensor f (fun j => positionComplexPartial (f j) b) 1 i
    (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem positionComplexPartial_C1 (f : Position → ℂ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    ContDiff ℝ 1 (positionComplexPartial f b) :=
  (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem coordinateProduct_second {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (configurationComplexPartial (coordinateProduct f) (i,b)) (i,b) x =
      positionComplexPartial (positionComplexPartial (f i) b) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  let g : Fin n → Position → ℂ := fun j y => if j=i then positionComplexPartial (f j) b y else f j y
  have hg (j : Fin n) : ContDiff ℝ 1 (g j) := by
    by_cases hj : j=i
    · simpa only [g,hj,ite_true, if_true] using positionComplexPartial_C1 (f j) (hf j) b
    · simpa only [g,hj,ite_false, if_false] using (hf j).of_le (by norm_num)
  rw [coordinateProduct_partial_product f (fun j => (hf j).of_le (by norm_num)) i b]
  rw [coordinateProduct_partial _ hg i b x]
  change positionComplexPartial (g i) b (Coulomb.position x i)*_ = _
  have hgi : g i = positionComplexPartial (f i) b := by funext y; simp only [g,ite_true, if_true]
  rw [hgi]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [g,ite_eq_right (Finset.mem_erase.mp hj).1]

theorem coordinateProduct_laplacian {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : Configuration n) :
    configurationComplexLaplacian (coordinateProduct f) x =
      ∑ i, positionComplexLaplacian (f i) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type]
  simp_rw [coordinateProduct_second f hf]
  simp only [positionComplexLaplacian,Finset.sum_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorOperatorResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential one-body residual of a product is the sum of the
one-orbital residuals in its electron slots. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorOrbital_operator_residual {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (b : Fin n → α) (s : SpinConfiguration n) (x : Configuration n) :
    (-1/2:ℂ)*configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*Coulomb.tensorOrbital v b s x-
      ((n:ℝ)*E:ℝ)*Coulomb.tensorOrbital v b s x = tensorOrbitalResidual v r b s x := by
  have hL := coordinateProduct_laplacian (fun i y => v (b i) y (s i))
    (fun i => hv (b i) (s i)) x
  change configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x = _ at hL
  have hf (i : Fin n) : v (b i) (Coulomb.position x i) (s i)*
      (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      Coulomb.tensorOrbital v b s x :=
    Finset.mul_prod_erase Finset.univ
      (fun j => v (b j) (Coulomb.position x j) (s j)) (Finset.mem_univ i)
  have hR : tensorOrbitalResidual v r b s x =
      ∑ i, ((-1/2:ℂ)*
        (positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
          ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
        (V (Coulomb.position x i):ℂ)*Coulomb.tensorOrbital v b s x-
        (E:ℂ)*Coulomb.tensorOrbital v b s x) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [heq]
    rw [show ((-1/2:ℂ)*positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)+
        (V (Coulomb.position x i):ℂ)*v (b i) (Coulomb.position x i) (s i)-
        (E:ℂ)*v (b i) (Coulomb.position x i) (s i))*
        (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      (-1/2:ℂ)*(positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
      (V (Coulomb.position x i):ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))-
      (E:ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) by ring]
    rw [hf]
  rw [hR,hL]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
  ring

theorem configurationComplexPartial_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => ∑ j, c j*f j y) a x =
      ∑ j, c j*configurationComplexPartial (f j) a x := by
  unfold configurationComplexPartial
  have hd (j : α) := (hf j).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (c j))]
  simp only [sum_apply,fderiv_const_mul (hd _),smul_apply,smul_eq_mul]

theorem configurationComplexLaplacian_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration n) :
    configurationComplexLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationComplexLaplacian (f j) x := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationComplexPartial (f j) a y) :=
    funext (configurationComplexPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationComplexLaplacian
  simp_rw [hfirst,configurationComplexPartial_sum c _
    (fun j => configurationComplexPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreTensorFiber
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial tensor residual is the actual differential residual of
finite tensor synthesis in the full physical spin space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorOrbitalResidual_memLp {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (b : Fin n → α) (s : SpinConfiguration n) :
    MemLp (tensorOrbitalResidual v r b s) 2 := by
  apply memLp_finsetSum Finset.univ
  intro i _
  have h := (Coulomb.slotTensor_memLp (fun j y => v (b j) y (s j))
    (fun j y => r (b j) y (s j)) (fun j => hv (b j) (s j)) (fun j => hr (b j) (s j)) 1 i).comp_measurePreserving
    (Coulomb.configurationMeasurableEquiv_measurePreserving n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorResidualValue_memLp {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    MemLp (finiteTensorResidualValue v r c s) 2 :=
  memLp_finsetSum Finset.univ (fun b _ => (tensorOrbitalResidual_memLp v r hv hr b s).const_mul (c b))

theorem finiteTensorResidualValue_eq_flat {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (x : Configuration n) :
    finiteTensorResidualValue v r c s x =
      tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
        (fun a => Coulomb.flatSpinOrbital (r a)) c (spinConfigurationPoint s x) := by
  unfold finiteTensorResidualValue tensorOrbitalResidual tensorTotalReplacement tensorSlotReplacement
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  change c b*(r (b i) (Coulomb.position x i) (s i)*
    ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      c b*Coulomb.slotTensor (fun j y => v (b j) y (s j))
        (fun j y => r (b j) y (s j)) 1 i (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorState_value_C2 {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    ContDiff ℝ 2 ((finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c).value s) := by
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul (coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i)))

theorem finiteTensorState_gradient_classical {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (finiteTensorState v hv hL2 hpartial c).gradient s a x =
      configurationComplexPartial ((finiteTensorState v hv hL2 hpartial c).value s) a x := by
  have h := configurationComplexPartial_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => tensorOrbital_C1 v hv b s) a x
  exact h.symm

theorem finiteTensorState_operator_residual {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) (x : Configuration n) :
    let p := finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c
    finiteTensorResidualValue v r c s x =
      (-1/2:ℂ)*configurationComplexLaplacian (p.value s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*p.value s x-((n:ℝ)*E:ℝ)*p.value s x := by
  dsimp only
  change (∑ b, c b*tensorOrbitalResidual v r b s x) =
    (-1/2:ℂ)*configurationComplexLaplacian (fun y => ∑ b, c b*Coulomb.tensorOrbital v b s y) x+
    ((∑ i, V (Coulomb.position x i)):ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)-
    ((n:ℝ)*E:ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)
  rw [configurationComplexLaplacian_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i))) x]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← tensorOrbital_operator_residual v r hv V E heq b s x]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ClassicalResidualPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual differential residual controls the mixed bounded-potential
form against every weak-H1 state, without restricting its smoothness. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1Coordinates_complex_inner {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    inner ℂ (h1Coordinates u a) (h1Coordinates v a) =
      ∫ x, star (h1CoordinateFunction u a x)*h1CoordinateFunction v a x :=
  h1_inner_complex_coordinate v a _ (h1Coordinate_memLp u a)

theorem h1Coordinates_complex_mass_inner {n : ℕ} (u v : Coulomb.H1Vector n) :
    (∑ s, inner ℂ (h1Coordinates u (Sum.inl s)) (h1Coordinates v (Sum.inl s))) =
      inner ℂ u.toHilbert v.toHilbert := by
  rw [PiLp.inner_apply]
  rfl

theorem boundedPotential_complex_pairing {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (s : SpinConfiguration n) :
    inner ℂ (h1Coordinates u (Sum.inl s))
      (BoundedPotential.operator V hV B hB (h1Coordinates v (Sum.inl s))) =
      ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp,
    BoundedPotential.operator_ae V hV B hB (h1Coordinates v (Sum.inl s))] with x hu hv hA
  change h1Coordinates u (Sum.inl s) x = u.value s x at hu
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hA,hu,hv,RCLike.inner_apply]
  exact mul_comm _ _

theorem classical_residual_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B)
    (R : SpinConfiguration n → Configuration n → ℂ)
    (hR : ∀ s, MemLp (R s) 2)
    (hu : ∀ s, ContDiff ℝ 2 (u.value s))
    (hdu : ∀ s a x, u.gradient s a x = configurationComplexPartial (u.value s) a x)
    (heq : ∀ s x, R s x = (-1/2:ℂ)*configurationComplexLaplacian (u.value s) x+
      (V x:ℂ)*u.value s x-(E:ℂ)*u.value s x) :
    graphComplexCross (BoundedPotential.operator V hV B hB) (h1Coordinates u) (h1Coordinates v)-
      (E:ℂ)*inner ℂ u.toHilbert v.toHilbert =
      ∑ s, ∫ x, star (R s x)*v.value s x := by
  have hm (s : SpinConfiguration n) : MemLp (fun x => (V x:ℂ)*u.value s x) 2 := by
    apply (u.value_L2 s).of_le_mul (c := B)
      ((Complex.continuous_ofReal.comp hV).aestronglyMeasurable.mul (u.value_L2 s).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(V x:ℂ)*u.value s x‖ ≤ B*‖u.value s x‖
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hLap (s : SpinConfiguration n) : MemLp (configurationComplexLaplacian (u.value s)) 2 := by
    have hfun : configurationComplexLaplacian (u.value s) =
        (fun x => (2:ℂ)*((V x:ℂ)*u.value s x-(E:ℂ)*u.value s x-R s x)) := by
      funext x
      linear_combination 2*(heq s x)
    rw [hfun]
    exact ((hm s).sub ((u.value_L2 s).const_mul (E:ℂ)) |>.sub (hR s)).const_mul 2
  have hp (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      MemLp (configurationComplexPartial (u.value s) a) 2 :=
    (memLp_congr_ae (Filter.Eventually.of_forall (hdu s a))).mp (u.partial_L2 s a)
  have hkin (s : SpinConfiguration n) := weakH1_complex_laplacian_pairing hdensity
    (u.value s) (hu s) (hp s) (hLap s) v s
  have hpoint (s : SpinConfiguration n) :
      (1/2:ℂ)*(∑ a, ∫ x, star (u.gradient s a x)*v.gradient s a x)+
        (∫ x, star (u.value s x)*((V x:ℂ)*v.value s x))-
        (E:ℂ)*(∫ x, star (u.value s x)*v.value s x) =
        ∫ x, star (R s x)*v.value s x := by
    have hLI := (hLap s).star.integrable_mul (v.value_L2 s)
    have hVI := (hm s).star.integrable_mul (v.value_L2 s)
    have hUI := (u.value_L2 s).star.integrable_mul (v.value_L2 s)
    have hhalf : star (-1/2:ℂ) = (-1/2:ℂ) := by
      change (starRingEnd ℂ) (-1/2) = (-1/2:ℂ)
      simp only [map_div₀,map_neg,map_one,map_ofNat]
    have hE : star (E:ℂ) = (E:ℂ) := Complex.conj_ofReal E
    have hprod (x : Configuration n) : star (R s x)*v.value s x =
        (-1/2:ℂ)*(star (configurationComplexLaplacian (u.value s) x)*v.value s x)+
          star ((V x:ℂ)*u.value s x)*v.value s x-
          (E:ℂ)*(star (u.value s x)*v.value s x) := by
      rw [heq]
      simp only [star_sub,star_add,star_mul,hhalf,hE]
      ring
    simp_rw [hprod]
    have hsub := integral_sub ((hLI.const_mul (-1/2:ℂ)).add hVI) (hUI.const_mul (E:ℂ))
    have hadd := integral_add (hLI.const_mul (-1/2:ℂ)) hVI
    simp only [Pi.add_apply,Pi.mul_apply,Pi.star_apply] at hsub hadd
    rw [hsub,hadd,integral_const_mul,integral_const_mul]
    simp_rw [← hdu] at hkin
    rw [hkin]
    have hvprod : (∫ x, star ((V x:ℂ)*u.value s x)*v.value s x) =
        ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
      congr 1
      funext x
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    rw [hvprod]
    ring
  rw [← h1Coordinates_complex_mass_inner]
  simp only [graphComplexCross,h1Coordinates_complex_inner,boundedPotential_complex_pairing,
    h1CoordinateFunction]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun s _ => by simpa only [Finset.mul_sum] using hpoint s)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential residual also controls the compressed diagonal energy.
This estimate retains polynomial dependence on the number of particles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem graphBoundedCross_self {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates u) (h1Coordinates u) = boundedPotentialForm V u := by
  rw [boundedPotentialForm_eq_graph V hV B hB]
  simp only [graphBoundedCross,graphBoundedForm,graphKinetic,real_inner_self_eq_norm_sq]

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

end Laughlin.Fock

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

/-- A creator sends an unoccupied canonical basis vector to the inserted
occupation with its actual exterior permutation sign. -/
theorem create_unoccupied_basis_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      create i (fockBasis Q A) = c • fockBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hd : Disjoint S.val T.val := by simpa only [S, T, Finset.disjoint_singleton_left]
  have h := ExteriorAlgebra.basis_mul_of_disjoint
    (Pi.basisFun ℂ (Fin (Q + 1))) S T hd
  have hset : (Set.powersetCard.disjUnion hd).val = insert i A := by
    ext k
    simp [Set.powersetCard.disjUnion, S, T]
  change fockBasis Q {i} * fockBasis Q A =
    (Set.powersetCard.permOfDisjoint hd).sign •
      fockBasis Q (Set.powersetCard.disjUnion hd).val at h
  rw [fockBasis_singleton, hset] at h
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [hs, one_smul, create, LinearMap.coe_mk, AddHom.coe_mk] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [hs, Units.neg_smul, one_smul, neg_smul,
      create, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem creationCoefficient_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    creationCoefficient i A = 1 ∨ creationCoefficient i A = -1 := by
  obtain ⟨c, hc, h⟩ := create_unoccupied_basis_signed i A hi
  have heq : creationCoefficient i A = c := by
    simp [creationCoefficient, h]
  simpa only [heq] using hc

theorem creationCoefficient_occupied (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : creationCoefficient i A = 0 := by
  simp [creationCoefficient, create_occupied_basis i A hi]

theorem create_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    create i (fockBasis Q A) = creationCoefficient i A • fockBasis Q (insert i A) := by
  by_cases hi : i ∈ A
  · simp [create_occupied_basis i A hi, creationCoefficient_occupied i A hi]
  · obtain ⟨c, _, hc⟩ := create_unoccupied_basis_signed i A hi
    have heq : creationCoefficient i A = c := by simp [creationCoefficient, hc]
    rw [heq, hc]

theorem annihilate_create_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (create i (fockBasis Q A)) = fockBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
  change annihilate i (create i (fockBasis Q A)) +
    number i (fockBasis Q A) = (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
  simpa [number_basis, hi] using h

theorem annihilate_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) :
    annihilate i (fockBasis Q A) =
      creationCoefficient i (A.erase i) • fockBasis Q (A.erase i) := by
  have h := annihilate_create_unoccupied_basis i (A.erase i) (Finset.notMem_erase _ _)
  rw [create_basis, Finset.insert_erase hi, map_smul] at h
  have hc : creationCoefficient i (A.erase i) * creationCoefficient i (A.erase i) = 1 := by
    rcases creationCoefficient_signed i (A.erase i) (Finset.notMem_erase _ _) with hc | hc
    all_goals simp [hc]
  calc
    _ = creationCoefficient i (A.erase i) •
        (creationCoefficient i (A.erase i) • annihilate i (fockBasis Q A)) := by
      rw [smul_smul, hc, one_smul]
    _ = _ := congrArg (fun x => creationCoefficient i (A.erase i) • x) h

theorem create_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (create i x) B =
      if i ∈ B then creationCoefficient i (B.erase i) * (fockBasis Q).repr x (B.erase i)
      else 0 := by
  classical
  have h : create i x = ∑ A, (fockBasis Q).repr x A • create i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  simp only [create_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ B
  · rw [ite_eq_left hi, Finset.sum_eq_single (B.erase i)]
    · simp [Finset.insert_erase hi, mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · simp [creationCoefficient_occupied i A hiA]
      · have hne : insert i A ≠ B := by
          intro hAB
          apply hA
          have he := congrArg (Finset.erase · i) hAB
          simpa only [Finset.erase_insert hiA] using he
        simp [Module.Basis.repr_self, hne]
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro A _
    have hne : insert i A ≠ B := by
      intro hAB
      exact hi (hAB ▸ Finset.mem_insert_self i A)
    simp [Module.Basis.repr_self, hne]

theorem annihilate_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (annihilate i x) B =
      if i ∉ B then creationCoefficient i B * (fockBasis Q).repr x (insert i B)
      else 0 := by
  classical
  have h : annihilate i x =
      ∑ A, (fockBasis Q).repr x A • annihilate i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  by_cases hi : i ∈ B
  · rw [ite_eq_right (not_not.mpr hi)]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hiA : i ∈ A
    · rw [annihilate_occupied_basis i A hiA]
      have hne : A.erase i ≠ B := by
        intro he
        exact (Finset.notMem_erase i A) (he.symm ▸ hi)
      simp [Module.Basis.repr_self, hne]
    · simp [annihilate_unoccupied_basis i A hiA]
  · rw [ite_eq_left hi, Finset.sum_eq_single (insert i B)]
    · rw [annihilate_occupied_basis i (insert i B) (Finset.mem_insert_self _ _),
        Finset.erase_insert hi]
      simp [mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · rw [annihilate_occupied_basis i A hiA]
        have hne : A.erase i ≠ B := by
          intro he
          exact hA ((Finset.insert_erase hiA).symm.trans (congrArg (insert i) he))
        simp [Module.Basis.repr_self, hne]
      · simp [annihilate_unoccupied_basis i A hiA]
    · simp

theorem fockMass_create (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∉ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (create i x) B) =
        if i ∈ B then Complex.normSq ((fockBasis Q).repr x (B.erase i)) else 0 := by
    rw [create_coordinate]
    by_cases hi : i ∈ B
    · simp only [hi, ↓reduceIte]
      rcases creationCoefficient_signed i (B.erase i) (Finset.notMem_erase _ _) with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (B.val.erase i)))
  simp_rw [insertModeEquiv_erase] at h
  exact h.symm

theorem fockMass_annihilate (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∈ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (annihilate i x) B) =
        if i ∉ B then Complex.normSq ((fockBasis Q).repr x (insert i B)) else 0 := by
    rw [annihilate_coordinate]
    by_cases hi : i ∉ B
    · simp only [hi]
      rcases creationCoefficient_signed i B hi with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).symm.sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (insert i B.val)))
  simp_rw [insertModeEquiv_symm_insert] at h
  exact h.symm

theorem fockMass_create_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) ≤ fockMass x := by
  classical
  rw [fockMass_create]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∉ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∉ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockMass_annihilate_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) ≤ fockMass x := by
  classical
  rw [fockMass_annihilate]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∈ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∈ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockCoordinates_norm_sq (x : Space Q) :
    ‖fockCoordinates Q x‖ ^ 2 = fockMass x := by
  simp only [EuclideanSpace.norm_sq_eq, fockCoordinates_apply,
    Complex.normSq_eq_norm_sq, fockMass]

theorem fockOperator_norm_le_one (T : Module.End ℂ (Space Q))
    (hT : ∀ x, fockMass (T x) ≤ fockMass x) : ‖fockOperator T‖ ≤ 1 := by
  apply (fockOperator T).opNorm_le_bound zero_le_one
  intro v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  rw [fockOperator_coordinates, one_mul]
  have h := hT x
  rw [← fockCoordinates_norm_sq, ← fockCoordinates_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Actual CAR creators and annihilators are contractions in the
canonical occupation norm, uniformly in the number of spectator modes. -/
theorem fockOperator_create_norm (i : Fin (Q + 1)) :
    ‖fockOperator (create i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_create_le i)

theorem fockOperator_annihilate_norm (i : Fin (Q + 1)) :
    ‖fockOperator (annihilate i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_annihilate_le i)

theorem fockOperator_sum {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Space Q)) :
    fockOperator (∑ i ∈ s, T i) = ∑ i ∈ s, fockOperator (T i) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, sum_apply,
    LinearMap.sum_apply, map_sum]

theorem fockOperator_transfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (transfer i j)‖ ≤ 1 := by
  rw [transfer, fockOperator_mul]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (fockOperator_create_norm i) (fockOperator_annihilate_norm j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockCoefficientNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient perturbations of the actual one- and two-body CAR
operators. The bounds depend polynomially on the number of modes and
not on the exponentially large dimension of the exterior algebra. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

private lemma fockOperator_mul_norm_one (S T : Module.End ℂ (Space Q))
    (hS : ‖fockOperator S‖ ≤ 1) (hT : ‖fockOperator T‖ ≤ 1) :
    ‖fockOperator (S * T)‖ ≤ 1 := by
  rw [fockOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hS hT (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

lemma fockOperator_quartic_norm (i j k l : Fin (Q + 1)) :
    ‖fockOperator (create i * create j * annihilate l * annihilate k)‖ ≤ 1 := by
  apply fockOperator_mul_norm_one _ _
  · apply fockOperator_mul_norm_one _ _
    · exact fockOperator_mul_norm_one _ _
        (fockOperator_create_norm i) (fockOperator_create_norm j)
    · exact fockOperator_annihilate_norm l
  · exact fockOperator_annihilate_norm k

lemma oneBodyOperator_norm (K : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ‖fockOperator (oneBodyOperator K)‖ ≤ ∑ i, ∑ j, ‖K i j‖ := by
  simp only [oneBodyOperator, fockOperator_sum, fockOperator_smul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (fockOperator_transfer_norm i j) (norm_nonneg _)).trans_eq
    (mul_one _)

lemma twoBodyOperator_norm
    (W : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ‖fockOperator (twoBodyOperator W)‖ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l, ‖W i j k l‖ := by
  simp only [twoBodyOperator, fockOperator_smul, fockOperator_sum]
  rw [norm_smul]
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by
    norm_num [norm_inv, Complex.norm_def, Complex.normSq]
  rw [hhalf]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (fockOperator_quartic_norm i j k l) (norm_nonneg _)).trans_eq
    (mul_one _)

lemma oneBodyOperator_sub (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    oneBodyOperator K - oneBodyOperator L = oneBodyOperator (fun i j => K i j - L i j) := by
  ext x
  simp [oneBodyOperator, Finset.sum_sub_distrib, sub_smul]

lemma twoBodyOperator_sub
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    twoBodyOperator W - twoBodyOperator V =
      twoBodyOperator (fun i j k l => W i j k l - V i j k l) := by
  ext x
  simp [twoBodyOperator, Finset.sum_sub_distrib, sub_smul, smul_sub]

lemma oneBodyOperator_error (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ) {ε : ℝ}
    (h : ∀ i j, ‖K i j - L i j‖ ≤ ε) :
    ‖fockOperator (oneBodyOperator K - oneBodyOperator L)‖ ≤ (Q + 1 : ℝ) ^ 2 * ε := by
  rw [oneBodyOperator_sub]
  apply (oneBodyOperator_norm _).trans
  calc
    _ ≤ ∑ _i : Fin (Q + 1), ∑ _j : Fin (Q + 1), ε :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

lemma twoBodyOperator_error
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) {ε : ℝ}
    (h : ∀ i j k l, ‖W i j k l - V i j k l‖ ≤ ε) :
    ‖fockOperator (twoBodyOperator W - twoBodyOperator V)‖ ≤ (1 / 2 : ℝ) * (Q + 1 : ℝ) ^ 4 * ε := by
  rw [twoBodyOperator_sub]
  apply (twoBodyOperator_norm _).trans
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (Q + 1), ∑ _j : Fin (Q + 1),
        ∑ _k : Fin (Q + 1), ∑ _l : Fin (Q + 1), ε :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h i j k l) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

lemma electronicOperator_error
    (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ)
    {ε η : ℝ} (hK : ∀ i j, ‖K i j - L i j‖ ≤ ε)
    (hW : ∀ i j k l, ‖W i j k l - V i j k l‖ ≤ η) :
    ‖fockOperator ((oneBodyOperator K + twoBodyOperator W) -
      (oneBodyOperator L + twoBodyOperator V))‖ ≤
        (Q + 1 : ℝ) ^ 2 * ε + (1 / 2 : ℝ) * (Q + 1 : ℝ) ^ 4 * η := by
  rw [show (oneBodyOperator K + twoBodyOperator W) -
      (oneBodyOperator L + twoBodyOperator V) =
      (oneBodyOperator K - oneBodyOperator L) + (twoBodyOperator W - twoBodyOperator V) by abel]
  rw [fockOperator_add]
  exact (norm_add_le _ _).trans (add_le_add (oneBodyOperator_error K L hK)
    (twoBodyOperator_error W V hW))

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
-- module Solutions.OAIQ092_CC.Laughlin_Operators_PositiveFockLift
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Exterior_SpinUnitary
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

end Laughlin.Fock

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
-- module Solutions.OAIQ092_CC.Laughlin_Tensor_PairContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

namespace Fock

theorem two_annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (i j : Fin (Q+1)) :
    annihilate j (annihilate i (tensorExterior (n+2) Q ψ)) =
      ((n+2 : ℂ)*(n+1)) • tensorExterior n Q (fun a => ψ (Fin.cons i (Fin.cons j a))) := by
  rw [annihilate_tensorExterior (n+1) Q ψ hψ,map_smul,
    annihilate_tensorExterior n Q _ (antisymmetric_cons hψ i),smul_smul]
  congr 1
  push_cast
  ring

end Fock

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockTensorCompression
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact one- and two-body matrix elements of the actual CAR operators on
normalized antisymmetric coefficient tensors. These are the finite algebraic
identities used to compare Slater integrals with occupation-space matrices. -/

noncomputable section
namespace ContinuumCoulomb.FockTensorCompression
open Laughlin Laughlin.Fock
open scoped BigOperators

private lemma annihilate_create_inner (Q : ℕ) (i : Fin (Q + 1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

private lemma factorial_normalizer (n : ℕ) :
    star ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * (n.factorial : ℂ) = 1 := by
  have hp : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
  have he : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← he]
  field_simp

lemma annihilation_inner (n Q : ℕ) (ψ φ : State (n + 1) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j : Fin (Q + 1)) :
    occupationInner Q
      (annihilate i (normalizedTensorExterior (n + 1) Q ψ))
      (annihilate j (normalizedTensorExterior (n + 1) Q φ)) =
      (n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  simp only [normalizedTensorExterior, map_smul, annihilate_tensorExterior n Q ψ hψ,
    annihilate_tensorExterior n Q φ hφ, occupationInner_smul_left, occupationInner_smul_right,
    tensorExterior_inner n Q _ _ (antisymmetric_cons hφ j)]
  have hn := factorial_normalizer (n + 1)
  have hf : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal,
    map_natCast, map_add, map_one] at *
  calc
    _ = (star ((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ : ℂ) *
      ((n + 1).factorial : ℂ)) *
      ((n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a)) := by
        rw [hf]
        simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
        ring
    _ = _ := by
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [hn, one_mul]

lemma oneBody_inner (n Q : ℕ) (ψ φ : State (n + 1) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j : Fin (Q + 1)) :
    occupationInner Q (normalizedTensorExterior (n + 1) Q ψ)
      (create i (annihilate j (normalizedTensorExterior (n + 1) Q φ))) =
      (n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  rw [annihilate_create_inner]
  exact annihilation_inner n Q ψ φ hψ hφ i j

lemma pair_annihilation_inner (n Q : ℕ) (ψ φ : State (n + 2) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j k l : Fin (Q + 1)) :
    occupationInner Q
      (annihilate j (annihilate i (normalizedTensorExterior (n + 2) Q ψ)))
      (annihilate l (annihilate k (normalizedTensorExterior (n + 2) Q φ))) =
      ((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a)) := by
  simp only [normalizedTensorExterior, map_smul,
    two_annihilate_tensorExterior n Q ψ hψ, two_annihilate_tensorExterior n Q φ hφ,
    occupationInner_smul_left, occupationInner_smul_right,
    tensorExterior_inner n Q _ _ (antisymmetric_cons (antisymmetric_cons hφ k) l)]
  have hn := factorial_normalizer (n + 2)
  have hf : ((n + 2).factorial : ℂ) =
      (n + 2 : ℂ) * ((n + 1 : ℂ) * (n.factorial : ℂ)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal,
    map_mul, map_natCast, map_add, map_one, map_ofNat] at *
  calc
    _ = (star ((Real.sqrt ((n + 2).factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt ((n + 2).factorial : ℝ))⁻¹ : ℂ) *
      ((n + 2).factorial : ℂ)) *
      (((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a))) := by
        rw [hf]
        simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
        ring
    _ = _ := by
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [hn, one_mul]

lemma twoBody_inner (n Q : ℕ) (ψ φ : State (n + 2) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j k l : Fin (Q + 1)) :
    occupationInner Q (normalizedTensorExterior (n + 2) Q ψ)
      (create i (create j (annihilate l (annihilate k
        (normalizedTensorExterior (n + 2) Q φ))))) =
      ((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a)) := by
  rw [annihilate_create_inner, annihilate_create_inner]
  exact pair_annihilation_inner n Q ψ φ hψ hφ i j k l

end ContinuumCoulomb.FockTensorCompression

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockOneBodyIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-body potential integral of an actual finite orbital tensor is
the corresponding CAR matrix element. Singular potentials need only the
integrability of the one-orbital matrix entries. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockOneBodyIntegral
open Laughlin Laughlin.Fock FockSlaterTensor

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
variable {n Q : ℕ}

omit [MeasurableSpace A] in
theorem tensorValue_bilinear (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (x : Fin n → A) :
    star (tensorValue v ψ x)*tensorValue v φ x =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        (star (∏ i, v (a i) (x i))*(∏ i, v (b i) (x i))) := by
  simp only [tensorValue,star_sum,star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [MeasurableSpace A] in
theorem tensorValue_weighted_expansion (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (w : A → ℂ) (i : Fin n) (x : Fin n → A) :
    w (x i)*(star (tensorValue v ψ x)*tensorValue v φ x) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        (w (x i)*(star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j)))) := by
  rw [tensorValue_bilinear]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weighted_tensor_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → ℂ)
    (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (a b : _root_.OAI.Laughlin.Configuration n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => w (x i)*
      (star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j))))
        (Measure.pi fun _ => μ) := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  exact Coulomb.weighted_tensor_integrable (fun j x => star (v (a j) x)*v (b j) x) w i
    (fun j => (hv (a j)).star.integrable_mul (hv (b j))) (hw _ _)

theorem tensorValue_weighted_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → ℂ)
    (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => w (x i)*
      (star (tensorValue v ψ x)*tensorValue v φ x)) (Measure.pi fun _ => μ) := by
  simp_rw [tensorValue_weighted_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (weighted_tensor_pair_integrable v hv w hw a b i).const_mul _))

theorem tensorValue_weighted_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → ℂ) (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State n Q) (i : Fin n) :
    (∫ x, w (x i)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        ((∫ x, w x*(star (v (a i) x)*v (b i) x) ∂μ)*
          ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0) := by
  simp_rw [tensorValue_weighted_expansion]
  have hi (a b : _root_.OAI.Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*(w (x i)*(star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j)))))
        (Measure.pi fun _ => μ) := (weighted_tensor_pair_integrable v hv w hw a b i).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul]
  congr 1
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [Coulomb.weighted_tensor_integral (fun j x => star (v (a j) x)*v (b j) x) w i]
  simp_rw [ho]

private theorem delta_insert_product (i : Fin (n+1)) (a b : Fin (Q+1))
    (c d : _root_.OAI.Laughlin.Configuration n Q) :
    (∏ j ∈ Finset.univ.erase i, if (i.insertNth a c : Fin (n+1) → Fin (Q+1)) j=
      (i.insertNth b d : Fin (n+1) → Fin (Q+1)) j then (1:ℂ) else 0) =
      if c=d then 1 else 0 := by
  by_cases h : c=d
  · subst d
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
    simp only [Fin.insertNth_apply_succAbove,ite_true, if_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k,Finset.mem_univ _⟩)
    simpa only [Fin.insertNth_apply_succAbove] using (ite_eq_right hk : (if c k=d k then (1:ℂ) else 0)=0)

theorem oneBody_contraction (K : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i : Fin (n+1)) :
    (∑ a, ∑ b, (star (ψ a)*φ b)*(K (a i) (b i)*
      ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0)) =
      ∑ a, ∑ b, K a b*∑ c : _root_.OAI.Laughlin.Configuration n Q, star (ψ (Fin.cons a c))*φ (Fin.cons b c) := by
  have hc (a b : Fin (Q+1)) (c d : _root_.OAI.Laughlin.Configuration n Q) :
      star (ψ (i.insertNth a c))*φ (i.insertNth b d) =
        star (ψ (Fin.cons a c))*φ (Fin.cons b d) := by
    rw [antisymmetric_insertNth hψ,antisymmetric_insertNth hφ,star_mul,star_pow]
    simp only [star_neg,star_one]
    have he : (-1:ℂ)^i.val*(-1:ℂ)^i.val=1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1:ℂ)^i.val*(-1:ℂ)^i.val)*
        (star (ψ (Fin.cons a c))*φ (Fin.cons b d)) := by ring
      _ = _ := by rw [he,one_mul]
  rw [sum_config_insert i]
  simp_rw [sum_config_insert i,Fin.insertNth_apply_same,delta_insert_product,hc]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem tensorValue_oneBody_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → ℂ) (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (∫ x, (∑ i, w (x i))*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+1) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
        (HubbardGlobal.oneBodyOperator (fun a b => ∫ x, w x*(star (v a x)*v b x) ∂μ)
          (normalizedTensorExterior (n+1) Q φ)) := by
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => tensorValue_weighted_integrable v hv w hw ψ φ i)]
  have hi (i : Fin (n+1)) := (tensorValue_weighted_integral v hv ho w hw ψ φ i).trans
    (oneBody_contraction (fun a b => ∫ x, w x*(star (v a x)*v b x) ∂μ) ψ φ hψ hφ i)
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    HubbardGlobal.oneBodyOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hcar := FockTensorCompression.oneBody_inner n Q ψ φ hψ hφ a b
  change occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
    ((HubbardGlobal.transfer a b) (normalizedTensorExterior (n+1) Q φ)) = _ at hcar
  rw [hcar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring

end ContinuumCoulomb.FockOneBodyIntegral

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockResidualIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact CAR compression of differential orbital residuals. The residual
family is only assumed to lie in L2, so the result applies to the actual
manufactured orbitals and their finite-box error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockResidualIntegral
open Laughlin Laughlin.Fock FockSlaterTensor FockOneBodyIntegral

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {n Q : ℕ}

theorem tensor_pair_slot_integrable (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (a b : Laughlin.Configuration n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => (star (∏ j, v (a j) (x j)))*
      (∏ j, if j=i then r (b j) (x j) else v (b j) (x j))) (Measure.pi fun _ => μ) := by
  have hm (j : Fin n) : MemLp (fun y => if j=i then r (b j) y else v (b j) y) 2 μ := by
    by_cases hj : j=i
    · simpa only [hj,ite_true, if_true] using hr (b i)
    · simpa only [hj,ite_false, if_false] using hv (b j)
  exact (Coulomb.scalarTensor_memLp v hv a).star.integrable_mul
    (Coulomb.scalarTensor_memLp (fun j y => if j=i then r (b j) y else v (b j) y) hm id)

theorem tensor_pair_slot_integral (v r : Fin (Q+1) → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (a b : Laughlin.Configuration n Q) (i : Fin n) :
    (∫ x : Fin n → A, (star (∏ j, v (a j) (x j)))*
      (∏ j, if j=i then r (b j) (x j) else v (b j) (x j)) ∂(Measure.pi fun _ => μ)) =
      (∫ x, star (v (a i) x)*r (b i) x ∂μ)*
        ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0 := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (f := fun j x => star (v (a j) x)*(if j=i then r (b j) x else v (b j) x)) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => ∫ x, star (v (a j) x)*(if j=i then r (b j) x else v (b j) x) ∂μ)
    (Finset.mem_univ i)]
  simp only [ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [(Finset.mem_erase.mp hj).1,ite_false, if_false,ho]

omit [MeasurableSpace A] in
theorem tensorValue_slot_expansion (v r : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (i : Fin n) (x : Fin n → A) :
    star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x =
      ∑ a, ∑ b, (star (ψ a)*φ b)*((star (∏ j, v (a j) (x j)))*
        (∏ j, if j=i then r (b j) (x j) else v (b j) (x j))) := by
  simp only [tensorValue,tensorSlotReplacement,star_sum,star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorValue_slot_integral (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (ψ φ : State n Q) (i : Fin n) :
    (∫ x, star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*((∫ x, star (v (a i) x)*r (b i) x ∂μ)*
        ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0) := by
  simp_rw [tensorValue_slot_expansion]
  have hi (a b : Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*((star (∏ j, v (a j) (x j)))*
        (∏ j, if j=i then r (b j) (x j) else v (b j) (x j)))) (Measure.pi fun _ => μ) :=
    (tensor_pair_slot_integrable v r hv hr a b i).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul,tensor_pair_slot_integral v r ho]

theorem tensorValue_residual_integral (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (∫ x, star (tensorValue v ψ x)*tensorTotalReplacement v r φ x
      ∂(Measure.pi fun _ : Fin (n+1) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
        (HubbardGlobal.oneBodyOperator (fun a b => ∫ x, star (v a x)*r b x ∂μ)
          (normalizedTensorExterior (n+1) Q φ)) := by
  have hp : MemLp (tensorValue v ψ) 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
    memLp_finsetSum _ (fun a _ => (Coulomb.scalarTensor_memLp v hv a).const_mul (ψ a))
  simp only [tensorTotalReplacement,Finset.mul_sum]
  have hslot (i : Fin (n+1)) : Integrable (fun x =>
      star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x) (Measure.pi fun _ => μ) :=
    hp.star.integrable_mul (tensorSlotReplacement_memLp v r hv hr φ i)
  rw [integral_finsetSum _ (fun i _ => hslot i)]
  have hi (i : Fin (n+1)) := (tensorValue_slot_integral v r hv hr ho ψ φ i).trans
    (oneBody_contraction (fun a b => ∫ x, star (v a x)*r b x ∂μ) ψ φ hψ hφ i)
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    HubbardGlobal.oneBodyOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hcar := FockTensorCompression.oneBody_inner n Q ψ φ hψ hφ a b
  change occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
    ((HubbardGlobal.transfer a b) (normalizedTensorExterior (n+1) Q φ)) = _ at hcar
  rw [hcar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring

end ContinuumCoulomb.FockResidualIntegral

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearTensorCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singular nuclear form of the full spinful finite tensor state is
the actual finite CAR one-body form, including every spin component. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem nuclearErrorEnergy_cube {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)) :
    (nuclearErrorEnergy F u : ℂ) =
      ∫ z, (∑ i, (F (WithLp.toLp 2 (z i).2) : ℂ))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z)
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  have hn (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = star z*z := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using (Complex.conj_mul' z).symm
  have h := spinConfiguration_complex_integral
    (fun s x => ((∑ i, F (Coulomb.position x i)*‖u.value s x‖^2 : ℝ):ℂ))
    (fun s => (integrable_finsetSum Finset.univ (fun i _ => hI s i)).ofReal)
  have he (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
      ((∑ i, F (Coulomb.position (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2) i)*
          ‖u.value ((Coulomb.spinCubeEquiv n) z).1
            (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)‖^2 : ℝ):ℂ) =
        (∑ i, (F (WithLp.toLp 2 (z i).2) : ℂ))*
          (star (Coulomb.cubeState u z)*Coulomb.cubeState u z) := by
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,hn,Finset.sum_mul]
    rfl
  simp_rw [he] at h
  rw [h]
  simp only [integral_complex_ofReal,← Complex.ofReal_sum]
  congr 1
  unfold nuclearErrorEnergy
  apply Finset.sum_congr rfl
  intro s _
  exact (integral_finsetSum Finset.univ (fun i _ => hI s i)).symm

theorem finiteTensorState_cubeState {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (c : Laughlin.State n Q) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    Coulomb.cubeState (finiteTensorState v hv hL2 hpartial c) z =
      FockSlaterTensor.tensorValue (fun a => Coulomb.flatSpinOrbital (v a)) c z := rfl

theorem finiteTensorState_nuclear_compression {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) (F : Position → ℝ)
    (hentry : ∀ a b, Integrable (fun z : Fin 2 × (Fin 3 → ℝ) =>
      (F (WithLp.toLp 2 z.2) : ℂ)*
        (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
        Coulomb.spinSpaceMeasure)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*
      ‖(finiteTensorState v hv hL2 hpartial c).value s x‖^2)) :
    (nuclearErrorEnergy F (finiteTensorState v hv hL2 hpartial c) : ℂ) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z : Fin 2 × (Fin 3 → ℝ), (F (WithLp.toLp 2 z.2) : ℂ)*
            (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z)
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)) := by
  rw [nuclearErrorEnergy_cube F _ hI]
  simp_rw [finiteTensorState_cubeState]
  apply FockOneBodyIntegral.tensorValue_oneBody_integral _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) _ _ hentry c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorKineticCompression
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual differential residual identifies the finite tensor kinetic
and bounded-potential form with its CAR matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_residual_compression {n Q : ℕ}
    (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) :
    (∑ s, ∫ x, star ((finiteTensorState v hv hL2 hpartial c).value s x)*
      finiteTensorResidualValue v r c s x) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)) := by
  have he := spinConfiguration_complex_integral
    (fun s x => star ((finiteTensorState v hv hL2 hpartial c).value s x)*
      finiteTensorResidualValue v r c s x)
    (fun s => ((finiteTensorState v hv hL2 hpartial c).value_L2 s).star.integrable_mul
      (finiteTensorResidualValue_memLp v r hL2 hr c s))
  rw [← he]
  have hp : (fun z : Fin (n+1) → Fin 2 × (Fin 3 → ℝ) =>
      star ((finiteTensorState v hv hL2 hpartial c).value ((Coulomb.spinCubeEquiv (n+1)) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv (n+1)) z).2))*
      finiteTensorResidualValue v r c ((Coulomb.spinCubeEquiv (n+1)) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv (n+1)) z).2)) =
      fun z => star (FockSlaterTensor.tensorValue (fun a => Coulomb.flatSpinOrbital (v a)) c z)*
        tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
          (fun a => Coulomb.flatSpinOrbital (r a)) c z := by
    funext z
    rw [finiteTensorResidualValue_eq_flat,spinConfigurationPoint_coordinates]
    rfl
  rw [hp]
  apply FockResidualIntegral.tensorValue_residual_integral _ _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a))
    (fun a => Coulomb.flatSpinOrbital_memLp (r a) (hr a)) _ c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

theorem finiteTensorState_bounded_compression (hdensity : PublishedSobolevSmoothDensity)
    {n Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B : ℝ)
    (hB : ∀ x : Configuration (n+1), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) :
    let p := finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c
    boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+1:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c))).re := by
  let hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s) :=
    fun a s => (hv a s).of_le (by norm_num)
  let p := finiteTensorState v hv₁ hL2 hpartial c
  let W : Configuration (n+1) → ℝ := fun x => ∑ i, V (Coulomb.position x i)
  have hW : Continuous W := continuous_finsetSum _ (fun i _ => hV.comp (Coulomb.positionCLM i).continuous)
  let R := finiteTensorResidualValue v r c
  have hR := finiteTensorResidualValue_memLp v r hL2 hr c
  have hid := classical_residual_pairing hdensity p p W hW B ((n+1:ℝ)*E) hB R hR
    (finiteTensorState_value_C2 v hv hL2 hpartial c)
    (finiteTensorState_gradient_classical v hv₁ hL2 hpartial c)
    (fun s x => by simpa only [Nat.cast_add,Nat.cast_one] using
      finiteTensorState_operator_residual v r hv hL2 hpartial V E heq c s x)
  have hself : (inner ℂ p.toHilbert p.toHilbert).re = Coulomb.mass p := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) p.toHilbert).symm.trans
      (Coulomb.H1Vector.toHilbert_norm_sq p)
  have hre := congrArg Complex.re hid
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hself,← graphBoundedCross_eq_re,graphBoundedCross_self] at hre
  have hswap : (∑ s, ∫ x, star (R s x)*p.value s x).re =
      (∑ s, ∫ x, star (p.value s x)*R s x).re := by
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hi : Integrable (fun x => star (R s x)*p.value s x) :=
      (hR s).star.integrable_mul (p.value_L2 s)
    have hj : Integrable (fun x => star (p.value s x)*R s x) :=
      (p.value_L2 s).star.integrable_mul (hR s)
    calc
      _ = ∫ x, (star (R s x)*p.value s x).re := (integral_re hi).symm
      _ = ∫ x, (star (p.value s x)*R s x).re := by
        congr 1
        funext x
        simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
        ring
      _ = _ := integral_re hj
  change boundedPotentialForm W p-(n+1:ℝ)*E*Coulomb.mass p = _
  rw [hre,hswap,finiteTensorState_residual_compression v r hv₁ hL2 hpartial hr ho c hc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockTwoBodyContraction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two occupied-coordinate contraction, with the signs obtained from
the actual antisymmetric coefficient tensor. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockTwoBodyContraction
open Laughlin

theorem pairInsert_left {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : pairInsert i j a b c i = a := by
  simp only [pairInsert,Fin.insertNth_apply_same]

theorem pairInsert_right {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : pairInsert i j a b c (i.succAbove j) = b := by
  simp only [pairInsert,Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same]

theorem pairInsert_rest {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) (k : Fin n) :
    pairInsert i j a b c (i.succAbove (j.succAbove k)) = c k := by
  simp only [pairInsert,Fin.insertNth_apply_succAbove]

theorem pairInsert_coefficient {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1)) (c : Laughlin.Configuration n Q) :
    ψ (pairInsert i j a b c) = (-1:ℂ)^(i.val+j.val)*ψ (Fin.cons a (Fin.cons b c)) := by
  rw [pairInsert,antisymmetric_insertNth hψ]
  rw [antisymmetric_insertNth (antisymmetric_cons hψ a),pow_add]
  ring

theorem pairInsert_delta {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (a b a' b' : Fin (Q+1)) (c d : Laughlin.Configuration n Q) :
    (∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j),
      if pairInsert i j a b c k=pairInsert i j a' b' d k then (1:ℂ) else 0) =
      if c=d then 1 else 0 := by
  by_cases h : c=d
  · subst d
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hki
    have hl : l ≠ j := fun he => hkj (congrArg i.succAbove he)
    obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hl
    simp only [pairInsert_rest,ite_true, if_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    have hki : i.succAbove (j.succAbove k) ≠ i := Fin.succAbove_ne _ _
    have hkj : i.succAbove (j.succAbove k) ≠ i.succAbove j := by
      rw [ne_eq,Fin.succAbove_right_inj]
      exact Fin.succAbove_ne _ _
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,
      Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩⟩)
    simp only [pairInsert_rest,ite_eq_right hk]

theorem twoBody_contraction {n Q : ℕ}
    (K : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ)
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (i : Fin (n+2)) (j : Fin (n+1)) :
    (∑ a, ∑ b, (star (ψ a)*φ b)*(K (a i) (a (i.succAbove j)) (b i) (b (i.succAbove j))*
      ∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j), if a k=b k then (1:ℂ) else 0)) =
      ∑ a, ∑ b, ∑ c, ∑ d, K a b c d*∑ e : Laughlin.Configuration n Q,
        star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e)) := by
  have hc (a b a' b' : Fin (Q+1)) (c d : Laughlin.Configuration n Q) :
      star (ψ (pairInsert i j a b c))*φ (pairInsert i j a' b' d) =
        star (ψ (Fin.cons a (Fin.cons b c)))*φ (Fin.cons a' (Fin.cons b' d)) := by
    rw [pairInsert_coefficient ψ hψ,pairInsert_coefficient φ hφ,star_mul,star_pow]
    simp only [star_neg,star_one]
    have hs : (-1:ℂ)^(i.val+j.val)*(-1:ℂ)^(i.val+j.val)=1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = ((-1:ℂ)^(i.val+j.val)*(-1:ℂ)^(i.val+j.val))*
        (star (ψ (Fin.cons a (Fin.cons b c)))*φ (Fin.cons a' (Fin.cons b' d))) := by ring
      _ = _ := by rw [hs,one_mul]
  rw [sum_config_insert i]
  simp_rw [sum_config_insert i,sum_config_insert j]
  change (∑ a, ∑ b, ∑ c, ∑ a', ∑ b', ∑ d,
    (star (ψ (pairInsert i j a b c))*φ (pairInsert i j a' b' d))*
      (K (pairInsert i j a b c i) (pairInsert i j a b c (i.succAbove j))
        (pairInsert i j a' b' d i) (pairInsert i j a' b' d (i.succAbove j))*
        ∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j),
          if pairInsert i j a b c k=pairInsert i j a' b' d k then (1:ℂ) else 0)) = _
  simp only [pairInsert_left,pairInsert_right,pairInsert_delta,hc,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end ContinuumCoulomb.FockTwoBodyContraction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockTwoBodyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singular two-particle integrals of the actual orbital tensor and their
CAR representation. Integrability is required only for the four-index entries. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockTwoBodyIntegral
open Laughlin Laughlin.Fock FockSlaterTensor FockOneBodyIntegral FockTwoBodyContraction

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {n Q : ℕ}

theorem tensor_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (a b : Laughlin.Configuration n Q) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j)*
      (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k)))) (Measure.pi fun _ => μ) := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  exact Coulomb.pair_weight_tensor_integrable i j hij
    (fun k x => star (v (a k) x)*v (b k) x) w
    (fun k => (hv (a k)).star.integrable_mul (hv (b k))) (hw _ _ _ _)

theorem tensor_pair_integral (v : Fin (Q+1) → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ) (a b : Laughlin.Configuration n Q) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Fin n → A, w (x i) (x j)*
      (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k))) ∂(Measure.pi fun _ => μ)) =
      (∫ z : A × A, w z.1 z.2*((star (v (a i) z.1)*v (b i) z.1)*
        (star (v (a j) z.2)*v (b j) z.2)) ∂(μ.prod μ))*
        ∏ k ∈ (Finset.univ.erase i).erase j, if a k=b k then (1:ℂ) else 0 := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [Coulomb.pair_weight_tensor_integral i j hij
    (fun k x => star (v (a k) x)*v (b k) x) w]
  simp_rw [ho]

omit [MeasurableSpace A] in
theorem tensorValue_pair_expansion (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (w : A → A → ℂ) (i j : Fin n) (x : Fin n → A) :
    w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*(w (x i) (x j)*
        (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k)))) := by
  rw [tensorValue_bilinear]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorValue_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State n Q) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j)*
      (star (tensorValue v ψ x)*tensorValue v φ x)) (Measure.pi fun _ => μ) := by
  simp_rw [tensorValue_pair_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (tensor_pair_integrable v hv w hw a b i j hij).const_mul _))

theorem tensorValue_pair_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State n Q) (i j : Fin n) (hij : i ≠ j) :
    (∫ x, w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        ((∫ z : A × A, w z.1 z.2*((star (v (a i) z.1)*v (b i) z.1)*
          (star (v (a j) z.2)*v (b j) z.2)) ∂(μ.prod μ))*
          ∏ k ∈ (Finset.univ.erase i).erase j, if a k=b k then (1:ℂ) else 0) := by
  simp_rw [tensorValue_pair_expansion]
  have hi (a b : Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*(w (x i) (x j)*
        (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k))))) (Measure.pi fun _ => μ) :=
    (tensor_pair_integrable v hv w hw a b i j hij).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul,tensor_pair_integral v ho w a b i j hij]

theorem tensorValue_pair_contraction (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    (∫ x, w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
          (star (v b z.2)*v d z.2)) ∂(μ.prod μ))*
          ∑ e : Laughlin.Configuration n Q,
            star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e)) := by
  obtain ⟨j',rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have hp := tensorValue_pair_integral (μ := μ) (n := n+2) (Q := Q)
    v hv ho w hw ψ φ i (i.succAbove j') hij
  have hc := twoBody_contraction (n := n) (Q := Q)
    (fun a b c d => ∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
      (star (v b z.2)*v d z.2)) ∂(μ.prod μ)) ψ φ hψ hφ i j'
  exact hp.trans hc

theorem tensorValue_twoBody_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (2:ℂ)⁻¹ * (∫ x, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j))*
      (star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+2) Q ψ)
        (HubbardGlobal.twoBodyOperator (fun a b c d =>
          ∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
            (star (v b z.2)*v d z.2)) ∂(μ.prod μ))
          (normalizedTensorExterior (n+2) Q φ)) := by
  let C : ℂ := ∑ a, ∑ b, ∑ c, ∑ d,
    (∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
      (star (v b z.2)*v d z.2)) ∂(μ.prod μ))*
        ∑ e : Laughlin.Configuration n Q,
          star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e))
  have hi : (∫ x, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j))*
      (star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) = ∑ i : Fin (n+2),
        ∑ _j ∈ Finset.univ.erase i, C := by
    simp only [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum _ (fun j hj => tensorValue_pair_integrable v hv w hw ψ φ i j
        (Finset.ne_of_mem_erase hj).symm))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j hj => tensorValue_pair_integrable v hv w hw ψ φ i j
      (Finset.ne_of_mem_erase hj).symm)]
    apply Finset.sum_congr rfl
    intro j hj
    exact tensorValue_pair_contraction v hv ho w hw ψ φ hψ hφ i j
      (Finset.ne_of_mem_erase hj).symm
  rw [hi]
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [HubbardGlobal.twoBodyOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    occupationInner_sum_right,occupationInner_smul_right]
  congr 1
  dsimp only [C]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have hcar := FockTensorCompression.twoBody_inner n Q ψ φ hψ hφ a b c d
  change occupationInner Q (normalizedTensorExterior (n+2) Q ψ)
    ((create a * create b * annihilate d * annihilate c)
      (normalizedTensorExterior (n+2) Q φ)) = _ at hcar
  rw [hcar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  push_cast
  ring

end ContinuumCoulomb.FockTwoBodyIntegral

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_PairTensorCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-spin Coulomb pair form is exactly the quartic CAR operator
on the finite orbital tensor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

private theorem symmetric_pair_sum {n : ℕ} (K : Fin n → Fin n → ℝ)
    (hK : ∀ i j, K i j=K j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, K i j) =
      2*(∑ i, ∑ j, if i < j then K i j else 0) := by
  have hrow (i : Fin n) :
      (∑ j, ((if i < j then K i j else 0)+(if j < i then K j i else 0))) =
        ∑ j ∈ Finset.univ.erase i, K i j := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i,
          ((if i < j then K i j else 0)+(if j < i then K j i else 0)) := by
        symm
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro j _ hj
        have he : j=i := by simpa only [Finset.mem_erase,Finset.mem_univ,and_true,not_not] using hj
        subst j
        simp only [lt_self_iff_false,ite_false, if_false,add_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj).symm with h|h
        · simp only [h,not_lt_of_gt h,ite_true, if_true,ite_false, if_false,add_zero]
        · simp only [h,not_lt_of_gt h,ite_true, if_true,ite_false, if_false,zero_add,hK]
  calc
    _ = ∑ i, ∑ j, ((if i < j then K i j else 0)+(if j < i then K j i else 0)) := by
      simp only [hrow]
    _ = (∑ i, ∑ j, if i < j then K i j else 0)+
        (∑ i, ∑ j, if j < i then K j i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j => if j < i then K j i else 0)]
      ring

theorem pairEnergy_cube {n : ℕ} (u : Coulomb.H1Vector n) :
    (Coulomb.pairEnergy u : ℂ) = (2:ℂ)⁻¹ *
      (∫ z, (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z)
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) := by
  have hn (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = star z*z := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using (Complex.conj_mul' z).symm
  have hpoint (x : Configuration n) :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        (Coulomb.coulombKernel (Coulomb.position x i-Coulomb.position x j):ℂ)) =
        2*(repulsionPotential x:ℂ) := by
    have h := symmetric_pair_sum
      (fun i j => Coulomb.coulombKernel (Coulomb.position x i-Coulomb.position x j))
      (fun i j => by unfold Coulomb.coulombKernel; rw [norm_sub_rev])
    exact_mod_cast (show _ = 2*repulsionPotential x from by
      simpa only [repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type] using h)
  have he := spinConfiguration_complex_integral
    (fun s x => ((repulsionPotential x*‖u.value s x‖^2 : ℝ):ℂ))
    (fun s => by
      convert (u.pair_integrable s).ofReal (𝕜 := ℂ) using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type]
      rfl)
  have hp (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z) =
      (2:ℂ)*((repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)*
        ‖u.value ((Coulomb.spinCubeEquiv n) z).1
          (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)‖^2 : ℝ):ℂ) := by
    rw [Complex.ofReal_mul,hn]
    change _ = (2:ℂ)*((repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2):ℂ)*
      (star (Coulomb.cubeState u z)*Coulomb.cubeState u z))
    have hz := hpoint (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)
    change (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j)) =
      2*(repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2):ℂ) at hz
    rw [hz]
    ring
  simp_rw [hp]
  rw [integral_const_mul,he]
  have hs : (∑ s, ∫ x, ((repulsionPotential x*‖u.value s x‖^2:ℝ):ℂ)) =
      (Coulomb.pairEnergy u : ℂ) := by
    simp only [integral_complex_ofReal,← Complex.ofReal_sum]
    simp only [Coulomb.pairEnergy,repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type]
  rw [hs]
  ring

theorem finiteTensorState_pair_compression {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (hentry : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
        (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
    (c : Laughlin.State (n+2) Q) (hc : Laughlin.Antisymmetric c) :
    (Coulomb.pairEnergy (finiteTensorState v hv hL2 hpartial c) : ℂ) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        (HubbardGlobal.twoBodyOperator (fun a b c d =>
          ∫ z, flatPairCoulomb z.1 z.2*
            ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
              (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2))
            ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)) := by
  rw [pairEnergy_cube]
  simp_rw [finiteTensorState_cubeState]
  apply FockTwoBodyIntegral.tensorValue_twoBody_integral _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) _ _ hentry c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorFormCompression
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compression of the interacting continuum form, including the
singular nuclear term, to the actual finite CAR Hamiltonian. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

namespace HubbardGlobal

theorem oneBodyOperator_add {Q : ℕ} (K L : Fin (Q+1) → Fin (Q+1) → ℂ) :
    oneBodyOperator (fun a b => K a b+L a b) = oneBodyOperator K+oneBodyOperator L := by
  simp only [oneBodyOperator,add_smul,Finset.sum_add_distrib]

end HubbardGlobal

theorem finiteTensorState_form_compression (hdensity : PublishedSobolevSmoothDensity)
    {n Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B t : ℝ)
    (hB : ∀ x : Configuration (n+2), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (F : Position → ℝ)
    (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
      Coulomb.spinSpaceMeasure)
    (hW : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
    (c : Laughlin.State (n+2) Q) (hc : Laughlin.Antisymmetric c)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*
      ‖(finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c).value s x‖^2)) :
    let p := finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c
    nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
      t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        ((HubbardGlobal.oneBodyOperator (fun a b => flatResidualMatrix v r a b+flatNuclearMatrix v F a b)+
          (t:ℂ) • HubbardGlobal.twoBodyOperator (flatCoulombTensor v))
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re := by
  let hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s) :=
    fun a s => (hv a s).of_le (by norm_num)
  let p := finiteTensorState v hv₁ hL2 hpartial c
  have hb := finiteTensorState_bounded_compression (n := n+1) hdensity v r hv hL2 hpartial
    hr ho V hV E B hB heq c hc
  have hn := congrArg Complex.re
    (finiteTensorState_nuclear_compression v hv₁ hL2 hpartial ho c hc F hN hI)
  have hp := congrArg Complex.re (finiteTensorState_pair_compression v hv₁ hL2 hpartial ho hW c hc)
  simp only [Complex.ofReal_re] at hn hp
  change nuclearPerturbedForm _ F p+t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p = _
  simp only [HubbardGlobal.oneBodyOperator_add,LinearMap.add_apply,LinearMap.smul_apply,
    Laughlin.Fock.occupationInner_add_right,Laughlin.Fock.occupationInner_smul_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ = (Laughlin.Fock.occupationInner Q _
      (HubbardGlobal.oneBodyOperator (flatResidualMatrix v r) _)).re+
    (Laughlin.Fock.occupationInner Q _ (HubbardGlobal.oneBodyOperator (flatNuclearMatrix v F) _)).re+
    t*(Laughlin.Fock.occupationInner Q _ (HubbardGlobal.twoBodyOperator (flatCoulombTensor v) _)).re
  change nuclearErrorEnergy F p =
    (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
      (HubbardGlobal.oneBodyOperator (flatNuclearMatrix v F)
        (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re at hn
  change Coulomb.pairEnergy p =
    (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
      (HubbardGlobal.twoBodyOperator (flatCoulombTensor v)
        (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re at hp
  rw [← hn,← hp]
  have hb' : boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+2:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        (HubbardGlobal.oneBodyOperator (flatResidualMatrix v r)
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re := by
    convert hb using 1 <;> first | rfl | (push_cast; ring)
  rw [← hb']
  unfold nuclearPerturbedForm
  ring

end ContinuumCoulomb

end

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorFormError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite continuum form inherits the polynomial CAR coefficient
error bound, with no dependence on the exponentially large Fock dimension. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
namespace HubbardGlobal

theorem oneBodyOperator_smul {Q : ℕ} (z : ℂ) (K : Fin (Q+1) → Fin (Q+1) → ℂ) :
    oneBodyOperator (fun a b => z*K a b) = z • oneBodyOperator K := by
  simp only [oneBodyOperator,smul_smul,Finset.smul_sum]

theorem twoBodyOperator_smul {Q : ℕ} (z : ℂ)
    (W : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ) :
    twoBodyOperator (fun a b c d => z*W a b c d) = z • twoBodyOperator W := by
  simp only [twoBodyOperator,smul_smul,Finset.smul_sum,mul_assoc,mul_comm]

end HubbardGlobal

section FormApproximation

variable (hdensity : PublishedSobolevSmoothDensity)

variable {n Q : ℕ}

variable (v r : Fin (Q+1) → Position → Fin 2 → ℂ)

variable (hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))

variable (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))

variable (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)

variable (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)

variable (hr : ∀ a s, MemLp (fun x => r a x s) 2)

variable (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)

variable (V : Position → ℝ)

variable (hV : Continuous V)

variable (E B t : ℝ)

variable (hB : ∀ x : Configuration (n+2), |∑ i, V (Coulomb.position x i)| ≤ B)

variable (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)

variable (F : Position → ℝ)

variable (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
      Coulomb.spinSpaceMeasure)

variable (hW : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))

variable (c : Laughlin.State (n+2) Q)

variable (hc : Laughlin.Antisymmetric c)

variable (hI : nuclearFormIntegrable F (finiteTensorState (n := n+2) v hv₁ hL2 hpartial c))

variable (scale ε η : ℝ)

variable (K : Fin (Q+1) → Fin (Q+1) → ℂ)

variable (W : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ)

variable (hK : ∀ a b, ‖(scale:ℂ)*(flatResidualMatrix v r a b+flatNuclearMatrix v F a b)-K a b‖ ≤ ε)

variable (hWerror : ∀ a b c d, ‖(scale*t:ℂ)*flatCoulombTensor v a b c d-W a b c d‖ ≤ η)

include hdensity hv hr ho hV hB heq hN hW hc hI hK hWerror

theorem finiteTensorState_form_approximation_oai :
    let p := finiteTensorState (n := n+2) v hv₁ hL2 hpartial c
    |scale*(nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
      t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p)-
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        ((HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re| ≤
      ((Q+1:ℝ)^2*ε+(1/2:ℝ)*(Q+1:ℝ)^4*η)*Coulomb.mass p := by
  let p := finiteTensorState v hv₁ hL2 hpartial c
  let M := fun a b => flatResidualMatrix v r a b+flatNuclearMatrix v F a b
  let T := flatCoulombTensor v
  let x := Laughlin.Fock.normalizedTensorExterior (n+2) Q c
  have he := finiteTensorState_form_compression (n := n) (Q := Q) hdensity v r hv hL2 hpartial hr ho V hV E B t
    hB heq F hN hW c hc hI
  have hscale : HubbardGlobal.oneBodyOperator (fun a b => (scale:ℂ)*M a b)+
      HubbardGlobal.twoBodyOperator (fun a b c d => (scale*t:ℂ)*T a b c d) =
      (scale:ℂ) • (HubbardGlobal.oneBodyOperator M+(t:ℂ) • HubbardGlobal.twoBodyOperator T) := by
    rw [HubbardGlobal.oneBodyOperator_smul,HubbardGlobal.twoBodyOperator_smul,smul_add,smul_smul]
  have hb := occupationInner_operator_error
    (HubbardGlobal.oneBodyOperator (fun a b => (scale:ℂ)*M a b)+
      HubbardGlobal.twoBodyOperator (fun a b c d => (scale*t:ℂ)*T a b c d))
    (HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
    _ (HubbardGlobal.electronicOperator_error _ _ _ _ hK hWerror) x
  rw [hscale,LinearMap.smul_apply,Laughlin.Fock.occupationInner_smul_right] at hb
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hb
  have hm := finiteTensorState_occupationMass v hv₁ hL2 hpartial ho c hc
  change Coulomb.mass p = Laughlin.Fock.occupationNormSq Q x at hm
  rw [← hm] at hb
  change _ = (Laughlin.Fock.occupationInner Q x
    ((HubbardGlobal.oneBodyOperator M+(t:ℂ) • HubbardGlobal.twoBodyOperator T) x)).re at he
  dsimp only
  rw [he]
  exact hb

end FormApproximation

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.finiteTensorState_form_approximation_oai := @OAI.ContinuumCoulomb.finiteTensorState_form_approximation_oai
