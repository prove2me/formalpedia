-- Prove2me | solution 1 for OAI.ContinuumCoulomb.source_cloud_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:04:40.807357+00:00
-- url     : https://prove2.me/submissions/0dad518e-71f1-4281-b225-f061bc509c03

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
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
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
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
import Theorems.Thm_OAI_ContinuumCoulomb_ManufacturedVelocityEvaluation_approximation_error
import Theorems.Thm_OAI_ContinuumCoulomb_manufactured_polynomial_comparison

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

lemma blockRadiusSq_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    blockRadiusSq i (nuclearHardyCoordinates i R) x = ‖position x i - R‖^2 := by
  simp [blockRadiusSq, nuclearHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma hardyCoulomb_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    hardyCoulomb i (nuclearHardyCoordinates i R) x = coulombKernel (position x i - R) := by
  rw [hardyCoulomb, blockRadiusSq_nuclear, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma H1Vector.nuclear_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i : Fin n) (R : Space) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_nuclear] using
    ψ.coulomb_integrable_bound s i (nuclearHardyCoordinates i R) hη

lemma pairEnergy_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ pairEnergy ψ := by
  apply Finset.sum_nonneg
  intro s _
  apply integral_nonneg
  intro x
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact inv_nonneg.mpr (norm_nonneg _)
  · exact le_rfl

lemma totalCharge_ge_card {M : ℕ} (S : Nuclei M) : (M : ℝ) ≤ totalCharge S := by
  calc
    (M : ℝ) = ∑ _j : Fin M, (1 : ℝ) := by simp
    _ ≤ totalCharge S := Finset.sum_le_sum (fun j _ => S.charge_ge_one j)

lemma totalCharge_pos {M : ℕ} (S : Nuclei M) : 0 < totalCharge S :=
  (Nat.cast_pos.mpr S.nonempty).trans_le (totalCharge_ge_card S)

lemma nuclearEnergy_eq_sum {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    nuclearEnergy S ψ = ∑ s, ∑ i, ∑ j,
      S.charge j * (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2) := by
  unfold nuclearEnergy
  apply Finset.sum_congr rfl
  intro s _
  have hI : ∀ i j, Integrable (fun x => S.charge j *
      (coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) := by
    intro i j
    exact ((ψ.nuclear_coulomb_integrable_bound s i (S.position j)
      (by norm_num : (0 : ℝ) < 1)).1).const_mul _
  simp only [attraction, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  simp only [integral_const_mul]

lemma nuclearEnergy_bound {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    {η : ℝ} (hη : 0 < η) :
    nuclearEnergy S ψ ≤ 8 * η * totalCharge S * kinetic ψ +
      ((n : ℝ) * totalCharge S / (4 * η)) * mass ψ := by
  let K : Spins n → Fin n → ℝ := fun s i => ∑ b : Fin 3, ∫ x,
    ‖ψ.gradient s (i,b) x‖^2
  let L : Spins n → ℝ := fun s => ∫ x, ‖ψ.value s x‖^2
  rw [nuclearEnergy_eq_sum]
  have hbound : (∑ s, ∑ i, ∑ j, S.charge j *
      (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) ≤
      ∑ s, ∑ i, ∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s) := by
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (ψ.nuclear_coulomb_integrable_bound s i (S.position j) hη).2
      (le_trans (by norm_num) (S.charge_ge_one j))
  refine hbound.trans_eq ?_
  have hJ : ∀ s i, (∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s)) =
      totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s) := by
    intro s i
    rw [← Finset.sum_mul]
    rfl
  simp_rw [hJ]
  have hI : ∀ s, (∑ i, totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s)) =
      (totalCharge S * (4 * η)) * (∑ i, K s i) +
      ((n : ℝ) * totalCharge S / (4 * η)) * L s := by
    intro s
    simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hI]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hK : (∑ s, ∑ i, K s i) = 2 * kinetic ψ := by
    unfold K kinetic
    simp only [Fintype.sum_prod_type]
    ring
  rw [hK]
  change _ = 8 * η * totalCharge S * kinetic ψ +
    ((n : ℝ) * totalCharge S / (4 * η)) * (∑ s, L s)
  ring

lemma form_lower_bound {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    -(2 * (n : ℝ) * (totalCharge S)^2) * mass ψ ≤ form S ψ := by
  let η : ℝ := 1 / (8 * totalCharge S)
  have hZ := totalCharge_pos S
  have hη : 0 < η := by dsimp [η]; positivity
  have hbound := nuclearEnergy_bound S ψ hη
  have hfactor₁ : 8 * η * totalCharge S = 1 := by
    dsimp [η]
    field_simp
  have hfactor₂ : (n : ℝ) * totalCharge S / (4 * η) =
      2 * (n : ℝ) * (totalCharge S)^2 := by
    dsimp [η]
    field_simp
    ring
  rw [hfactor₁, one_mul, hfactor₂] at hbound
  have hpair := pairEnergy_nonneg ψ
  unfold form
  linarith

end Coulomb
end
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

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical, norm-preserving embedding of the spin sector in Fock space. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

/-- The ordered spin wedge is exactly a canonical occupation-basis
vector, with no arbitrary normalization or phase. -/
theorem spinWedge_eq_fockBasis (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    spinWedge m s = fockBasis (2 * m + 1) (spinOccupationSet m s) := by
  let S := Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)
  change wedgeModes (m + 1) (fun i => siteMode m i (s i)) =
    (Pi.basisFun ℂ (Fin ((2 * m + 1) + 1))).ExteriorAlgebra S.val
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, S, Equiv.symm_apply_apply]
  unfold wedgeModes
  congr 1
  funext i
  rw [Function.comp_apply, Pi.basisFun_apply]
  rfl

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

theorem fockOperator_bondTransfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (bondTransfer i j)‖ ≤ 2 := by
  rw [bondTransfer, fockOperator_add]
  calc
    _ ≤ ‖fockOperator (transfer i j)‖ + ‖fockOperator (transfer j i)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (fockOperator_transfer_norm i j) (fockOperator_transfer_norm j i)
    _ = 2 := by norm_num

theorem fockOperator_siteHopping_norm (m : ℕ) (i j : Fin (m + 1)) :
    ‖fockOperator (siteHopping m i j)‖ ≤ 4 := by
  change ‖fockOperator (_ + _)‖ ≤ _
  rw [fockOperator_add]
  calc
    _ ≤ ‖fockOperator (bondTransfer (siteMode m i 0) (siteMode m j 0))‖ +
        ‖fockOperator (bondTransfer (siteMode m i 1) (siteMode m j 1))‖ := norm_add_le _ _
    _ ≤ 2 + 2 := add_le_add
      (fockOperator_bondTransfer_norm (siteMode m i 0) (siteMode m j 0))
      (fockOperator_bondTransfer_norm (siteMode m i 1) (siteMode m j 1))
    _ = 4 := by norm_num

/-- The actual global hopping has an edge-sum bound, independent of
the exponentially large Fock-space dimension. -/
theorem fockOperator_graphHopping_norm {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    ‖fockOperator (graphHopping m left right t)‖ ≤ 4 * ∑ e, ‖t e‖ := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul]
  calc
    _ ≤ ∑ e, ‖t e • fockOperator (siteHopping m (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖t e‖ * 4 := Finset.sum_le_sum fun e _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (fockOperator_siteHopping_norm m (left e) (right e)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockEnergyError
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HalfFilledSector
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

theorem spinOccupationSet_card (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    (spinOccupationSet m s).card = m + 1 :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).property

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

theorem isHalfFilled_of_totalNumber (m : ℕ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) : IsHalfFilled m x :=
  totalNumber_eigen_coordinate_zero (m + 1) x hx

theorem totalNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    totalNumber (2 * m + 1) (spinWedge m s) =
      ((m + 1 : ℕ) : ℂ) • spinWedge m s := by
  rw [spinWedge_eq_fockBasis, totalNumber_basis, spinOccupationSet_card]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SuperexchangeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

theorem fockOperator_diagonal_apply {Q : ℕ} (f : Finset (Fin (Q + 1)) → ℂ)
    (x : FockCoordinateSpace Q) (A : Finset (Fin (Q + 1))) :
    fockOperator (fockDiagonal f) x A = f A * x A := by
  obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective x
  rw [fockOperator_coordinates, fockCoordinates_apply, fockDiagonal_coordinate,
    fockCoordinates_apply]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardVariationalWitness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near-minimizers of the actual half-filled Hubbard Rayleigh quotient
are represented by antisymmetric tensors, with no restriction to spin product
states or a proper subspace of the occupation sector. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem exists_halfFilled_unit_mass (m : ℕ) :
    ∃ x : Space (2*m+1), IsHalfFilled m x ∧ fockMass x=1 := by
  let s : SourceSpinBasis (m+1) := fun _ => 0
  refine ⟨spinWedge m s,isHalfFilled_of_totalNumber m _ (totalNumber_spinWedge m s),?_⟩
  rw [spinWedge_eq_fockBasis]
  simp [fockMass,Module.Basis.repr_self,Finsupp.single_apply]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardBottomBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds on the actual half-filled Hubbard bottom. These
control its contribution to the full-continuum complement smallness test. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem chargePenalty_abs_bound {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (o : Fin m → Fin 3) :
    |chargePenalty U V o| ≤ (m:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  have hd (i : Fin m) : |occupationDeviation o i| ≤ 1 := by
    unfold occupationDeviation
    generalize o i = t
    fin_cases t <;> norm_num
  have hd2 (i : Fin m) : occupationDeviation o i^2 ≤ 1 := by
    nlinarith [abs_le.mp (hd i)]
  have hs : (∑ i, occupationDeviation o i^2) ≤ (m:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd2 i)
  have hnonneg : 0 ≤ ∑ i, occupationDeviation o i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ht : |∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j| ≤ ∑ i, ∑ j, |V i j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_mul]
    calc
      _ ≤ |V i j| * 1 * 1 := by gcongr <;> apply hd
      _ = _ := by ring
  calc
    _ ≤ |U/2*(∑ i, occupationDeviation o i^2)|+
        |(1/2:ℝ)*(∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j)| := abs_add_le _ _
    _ ≤ |U|/2*(m:ℝ)+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hnonneg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ = _ := by ring

theorem fockOperator_diagonal_norm {Q : ℕ} (f : Finset (Fin (Q+1)) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ A, ‖f A‖ ≤ C) :
    ‖fockOperator (fockDiagonal f)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [fockOperator_diagonal_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf A) 2) (sq_nonneg _)

theorem chargePenaltyFock_norm (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ) :
    ‖fockOperator (chargePenaltyFock m U V)‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  apply fockOperator_diagonal_norm _ (by positivity)
  intro A
  simpa only [Complex.norm_real,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] using
    chargePenalty_abs_bound U V (occupationAt m A)

theorem hubbardFermionBottom_abs_bound {Edge : Type*} [Fintype Edge]
    (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    |hubbardFermionBottom m U V left right t| ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have hop : ‖fockOperator T‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
    calc
      _ ≤ ‖fockOperator (chargePenaltyFock m U V)‖+
          ‖fockOperator (graphHopping m left right (fun e => (t e:ℂ)))‖ := by
        rw [show fockOperator T = fockOperator (chargePenaltyFock m U V)+
            fockOperator (graphHopping m left right (fun e => (t e:ℂ))) from fockOperator_add _ _]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add (chargePenaltyFock_norm m U V) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using
          fockOperator_graphHopping_norm m left right (fun e => (t e:ℂ)))
  obtain ⟨x,hx,hm⟩ := exists_halfFilled_unit_mass m
  have hset : Set.Nonempty {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} :=
    ⟨_,x,hx,by rw [hm]; norm_num,rfl⟩
  have hlo : -‖fockOperator T‖ ≤ hubbardFermionBottom m U V left right t := by
    apply le_csInf hset
    rintro e ⟨y,_hy,hy,rfl⟩
    apply (le_div_iff₀ hy).mpr
    have h := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith only [h]
  have hhi := (hubbardFermionBottom_lower m U V left right t x hx).trans
    (le_abs_self _ |>.trans (hubbardFermionForm_abs_bound m U V left right t x))
  rw [hm,mul_one,mul_one] at hhi
  exact (abs_le.mpr ⟨hlo,hhi⟩).trans hop

end ContinuumCoulomb.HubbardGlobal

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
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

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

theorem localizedCoulombCoeff_le {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v ≤ localizedPotentialBound freq := by
  have hi := (localizedDensity_integrable hfreq u).mul_const (localizedPotentialBound freq)
  have h := integral_mono (localizedCoulombCoeff_integrable hfreq u v) hi
    (fun x => mul_le_mul_of_nonneg_left
      (localizedDensity_coulomb_integrable_bound hfreq v x).2
      (localizedDensity_nonnegative freq u x))
  simpa only [integral_mul_const, localizedDensity_mass hfreq u, one_mul,
    localizedCoulombCoeff] using h

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform contact calibration for the actual Coulomb profile, with a
single polynomial scale also enforcing the many-site Gram bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombProfile_nonnegative (freq d : ℝ) : 0 ≤ localizedCoulombProfile freq d := by
  unfold localizedCoulombProfile
  rw [localizedCoulombProfileAt_eq]
  exact localizedCoulombCoeff_nonnegative freq _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialConstantBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed positive analytic constants fit uniform polynomial ranges for
every size parameter at least two. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_polynomial_constant_bounds {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ N : ℝ, 2 ≤ N → (N ^ q)⁻¹ ≤ c ∧ C ≤ N ^ q := by
  obtain ⟨q, hq⟩ := exists_nat_ge (max 1 (max (1 / c) C))
  have hq₁ : (1 : ℝ) ≤ q := (le_max_left _ _).trans hq
  have hqc : 1 / c ≤ (q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hqC : C ≤ (q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨q, by exact_mod_cast (by linarith : (0 : ℝ) < q), fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hp := hpow.trans (pow_le_pow_left₀ (by norm_num) hN q)
  refine ⟨?_, hqC.trans hp⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos hNp q)).mpr
  have h := (div_le_iff₀ hc).mp (hqc.trans hp)
  nlinarith only [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCounterterms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual well-depth counterterms: direct Coulomb sums
divided by the fixed positive onsite well integral. Their diagonal action
cancels the required linear occupancy term exactly. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedOffsiteSum_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedOffsiteSum freq u i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative freq _ _

theorem localizedCounterterm_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i :=
  div_nonneg (localizedOffsiteSum_nonnegative freq u i) (planarHopping_positive 0).le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordinary product coordinates for the slab Coulomb integral.
These allow the finite-box potential to be treated by one-coordinate
integrals without changing the Euclidean volume normalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_eq_setIntegral (rho H S : ℝ) (y : Position) :
    slabPotential rho H S y = -rho * ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x) := by
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity rho H S x) =
      (slabDomain H S).indicator (fun x => rho*Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx]
      ring
    · simp only [slabDensity, Set.indicator_of_notMem hx, mul_zero]
  unfold slabPotential
  rw [he, integral_indicator (slabDomain_isClosed H S).measurableSet, integral_const_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product sections of the actual rectangular slab measure. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ContinuumCoulomb

theorem slabPotential_nonpositive {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (y : Position) :
    slabPotential rho H S y ≤ 0 := by
  rw [slabPotential_eq_setIntegral]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
    (integral_nonneg (fun x => inv_nonneg.mpr (norm_nonneg (y-x))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarFieldBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar counterterm field has uniform derivative bounds,
independent of the number of sites. Separated unit supports leave at most
one nonzero summand at every point. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellDerivativeConstant_bound {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k manufacturedPlanarWell r‖ ≤ planarWellDerivativeConstant :=
  (Classical.choose_spec planarWell_derivatives_bounded).2 k hk r

private theorem well_derivative_near {k : ℕ} {r : PlanarPosition}
    (hr : iteratedFDeriv ℝ k manufacturedPlanarWell r ≠ 0) : ‖r‖ ≤ 1 := by
  have hs := (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := manufacturedPlanarWell) k) hr
  have hb := (manufacturedPlanarWell_support.trans planarForcing_support) hs
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb

private theorem countertermWellSum_derivative (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    iteratedFDeriv ℝ k (countertermWellSum freq scale u) r =
      ∑ i, (1+localizedCounterterm freq u i/scale) •
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) := by
  have hw : ContDiff ℝ k manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.of_le (by exact_mod_cast (show k ≤ 7 by omega))
  unfold countertermWellSum
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i x => (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (x-u i))
    (fun i _ => (contDiff_const.mul (hw.comp (contDiff_id.sub contDiff_const))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ k (fun x => (1+localizedCounterterm freq u i/scale) •
    manufacturedPlanarWell (x-u i)) r = _
  rw [iteratedFDeriv_const_smul_apply' (f := fun x => manufacturedPlanarWell (x-u i))
    (a := 1+localizedCounterterm freq u i/scale)
    (hw.comp (contDiff_id.sub contDiff_const)).contDiffAt,
    iteratedFDeriv_comp_sub]

/-- Uniformity in the number of separated sites is essential for the
polynomial-time transport/cubature constants. -/
theorem countertermWellSum_derivative_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k (countertermWellSum freq scale u) r‖ ≤
      2*planarWellDerivativeConstant := by
  rw [countertermWellSum_derivative freq scale u hk r]
  have hcoef (i : Fin m) : |1+localizedCounterterm freq u i/scale| ≤ 2 := by
    have hlo := div_nonneg (localizedCounterterm_nonnegative freq u i) hscale.le
    have hhi := (div_le_one hscale).mpr (hcounter i)
    rw [abs_of_nonneg (by linarith)]
    linarith
  by_cases h : ∃ i, iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hzero (j : Fin m) (hji : j ≠ i) :
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u j) = 0 := by
      by_contra hj
      have hri := well_derivative_near hi
      have hrj := well_derivative_near hj
      have ht : ‖u i-u j‖ ≤ ‖r-u i‖+‖r-u j‖ := by
        calc
          _ = ‖(u i-r)+(r-u j)‖ := by congr 1; abel
          _ ≤ ‖u i-r‖+‖r-u j‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev (u i) r]
      have hd := hsep i j hji.symm
      linarith
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hzero j hji, smul_zero])
      (fun hn => (hn (Finset.mem_univ i)).elim), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hcoef i) (planarWellDerivativeConstant_bound hk _) (norm_nonneg _)
      (by norm_num)
  · have hzero (i : Fin m) : iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    simp only [hzero, smul_zero, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (by norm_num) planarWellDerivativeConstant_positive.le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFieldBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivatives through order six of the actual three-dimensional
manufactured field. Constants do not grow with the number of wells or slab width. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem linear_comp_six_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 6 f) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hL : ‖L‖ ≤ D)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) {k : ℕ} (hk : k ≤ 6) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B*D^6 := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖^k := h
    _ ≤ B*D^k := mul_le_mul (hb k hk (L x))
      (pow_le_pow_left₀ (norm_nonneg L) hL k) (pow_nonneg (norm_nonneg L) k) hB
    _ ≤ B*D^6 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hk) hB

private theorem wellPlanar_bound_nonnegative : 0 ≤ wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  unfold wellPlanarDerivativeBound
  positivity

private theorem wellCutoff_bound_nonnegative : 0 ≤ wellCutoffDerivativeBound := by
  have h := (Classical.choose_spec cutoff_derivative_bound_exists).1
  unfold wellCutoffDerivativeBound wellCutoffDerivativeConstant
  positivity

private theorem manufacturedField_planar_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) x‖ ≤
        wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  exact linear_comp_six_bound wellPlanarProjection (countertermWellSum freq scale u)
    ((countertermWellSum_C7 freq scale u).of_le (by norm_num))
    (by positivity) (le_max_left _ _) (le_max_right _ _)
    (fun j hj r => countertermWellSum_derivative_bound freq hscale u hsep hcounter hj r) hk x

private theorem manufacturedField_cutoff_bound {S : ℝ} (hS : 1 ≤ S)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position => slabWellCutoff S (positionSplitCoordinates y).2) x‖ ≤
      wellCutoffDerivativeBound := by
  let L : Position →L[ℝ] ℝ := (2/S) • wellVerticalProjection
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hscale : |2/S| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hS0).mpr (by linarith)
  have hL : ‖L‖ ≤ max 1 (2*‖wellVerticalProjection‖) := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans (le_max_right _ _)
  exact linear_comp_six_bound L (verticalCutoffBump : ℝ → ℝ)
    (verticalCutoffBump.contDiff : ContDiff ℝ 6 (verticalCutoffBump : ℝ → ℝ))
    (Classical.choose_spec cutoff_derivative_bound_exists).1.le (le_max_left _ _) hL
    (Classical.choose_spec cutoff_derivative_bound_exists).2 hk x

/-- A fixed bound for all six derivatives, uniform over every separated
site family, every admissible counterterm and every slab width at least one. -/
theorem manufacturedWellField_derivative_bound (freq : ℝ) {scale S : ℝ}
    (hscale : 0 < scale) (hS : 1 ≤ S) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤
      manufacturedFieldDerivativeConstant := by
  have hcut : ContDiff ℝ 6 (fun y : Position =>
      slabWellCutoff S (positionSplitCoordinates y).2) :=
    ((slabWellCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)).comp
      positionSplitCoordinates.contDiff.snd
  have hplan : ContDiff ℝ 6 (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) :=
    ((countertermWellSum_C7 freq scale u).of_le (show (6 : WithTop ℕ∞) ≤ 7 by norm_num)).comp
      positionSplitCoordinates.contDiff.fst
  have h := norm_iteratedFDeriv_mul_le hcut hplan x
    (show (k : WithTop ℕ∞) ≤ 6 by exact_mod_cast hk)
  change ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (manufacturedField_cutoff_bound hS (hi'.trans hk) x)
          (Nat.cast_nonneg _))
        (manufacturedField_planar_bound freq hscale u hsep hcounter (Nat.sub_le k i |>.trans hk) x)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) wellCutoff_bound_nonnegative)
    _ = (2:ℝ)^k*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 64*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply mul_le_mul_of_nonneg_right _ wellPlanar_bound_nonnegative
      apply mul_le_mul_of_nonneg_right _ wellCutoff_bound_nonnegative
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)
    _ = _ := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlux
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit density homotopy and continuity equation used to transport
uniform slab density in the unit-charge construction. The identities describe
the explicit field and its density homotopy. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem homotopyDensity_bounds {rho : ℝ} (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    rho / 2 ≤ homotopyDensity rho V t x ∧
      homotopyDensity rho V t x ≤ 3 * rho / 2 := by
  have hrho : 0 ≤ rho := by linarith [abs_nonneg (manufacturedCharge V x), hbound x]
  have hb := abs_le.mp (hbound x)
  have hlow := mul_le_mul_of_nonneg_left hb.1 ht0
  have hupp := mul_le_mul_of_nonneg_left hb.2 ht0
  have hscale := mul_le_mul_of_nonneg_right ht1 (by linarith : 0 ≤ rho / 2)
  dsimp [homotopyDensity]
  constructor <;> nlinarith

theorem homotopyDensity_pos {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    0 < homotopyDensity rho V t x :=
  (by positivity : (0 : ℝ) < rho / 2).trans_le
    (homotopyDensity_bounds V hbound ht0 ht1 x).1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite C⁶ regularity of the manufactured well gives the C⁴ transport
field required by the unit-charge cubature. No C∞ assumption is added. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem manufacturedCharge_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (manufacturedCharge V) := by
  have hp (v : Position) : ContDiff ℝ 5 (dirPartial V v) :=
    (hV.fderiv_right (show (5 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const
  have hpp (v : Position) : ContDiff ℝ 4 (dirPartial (dirPartial V v) v) :=
    ((hp v).fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 5 by norm_num)).clm_apply contDiff_const
  have heq : coordinateLaplacian V = fun x =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) x :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  change ContDiff ℝ 4 (fun x => coordinateLaplacian V x / (4 * Real.pi))
  rw [heq]
  exact (ContDiff.sum (fun a _ => hpp (axis a))).div_const _

theorem homotopyDensity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) :=
  contDiff_const.add (contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd))

theorem moserDomain_isOpen (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    IsOpen (moserDomain rho V) :=
  isOpen_ne.preimage (homotopyDensity_joint_C4 rho V hV).continuous

theorem moserVelocity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiffOn ℝ 4 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2)
      (moserDomain rho V) := by
  apply (contDiffOn_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hden : ContDiffOn ℝ 4
      (fun p : ℝ × Position => 4 * Real.pi * homotopyDensity rho V p.1 p.2)
      (moserDomain rho V) :=
    (contDiff_const.mul (homotopyDensity_joint_C4 rho V hV)).contDiffOn
  exact (hp.comp contDiff_snd).neg.contDiffOn.div hden (fun p hp =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hp)

theorem moserDomain_contains_time_slab {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ moserDomain rho V := by
  intro p hp
  exact (homotopyDensity_pos hrho V hbound hp.1.1 hp.1.2 p.2).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Dilation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial dilation on the actual weak H¹ domain

The physical-energy amplification in both manuscripts changes coordinates
on the full fermionic form domain. Here weak derivatives are transformed
by changing variables in the compact-test identity, rather than assuming
pointwise differentiability of an arbitrary state.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem coulombKernel_smul (x : Position) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.coulombKernel (scale • x) = scale⁻¹ * Coulomb.coulombKernel x := by
  simp only [Coulomb.coulombKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hscale, mul_inv_rev]
  ring

theorem attraction_dilatedNuclei {M : ℕ} (S : Coulomb.Nuclei M)
    {scale : ℝ} (hscale : 0 < scale) (x : Position) :
    Coulomb.attraction (dilatedNuclei S scale hscale.ne') x =
      scale * Coulomb.attraction S (scale • x) := by
  have hpos (a : Fin M) : x - scale⁻¹ • S.position a =
      scale⁻¹ • (scale • x - S.position a) := by
    rw [smul_sub, inv_smul_smul₀ hscale.ne']
  simp only [Coulomb.attraction, dilatedNuclei, hpos,
    coulombKernel_smul _ (inv_pos.mpr hscale), inv_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeGeometry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Euclidean mesh cells: volume, radius, node containment, and
disjoint interiors. These retain the volume normalization of the Gauss rule. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem mem_positionCube {x b : Position} {h : ℝ} :
    x ∈ positionCube b h ↔ ∀ i, |x i-b i| ≤ h/2 := by
  change ((fun i => b i-h/2) ≤ WithLp.ofLp x ∧
    WithLp.ofLp x ≤ (fun i => b i+h/2)) ↔ _
  constructor
  · rintro ⟨hl,hu⟩ i
    exact abs_le.mpr ⟨by linarith [hl i],by linarith [hu i]⟩
  · intro hx
    constructor <;> intro i <;> have hi := abs_le.mp (hx i) <;> linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal _root_.OAI.ContinuumCoulomb.centeredGridIndices_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite family of lattice cubes tiles the enclosing rectangular
slab, including its boundary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem exists_centered_grid_integer (N : ℕ) {h x : ℝ} (hh : 0 < h)
    (hx : |x| ≤ ((N:ℝ)+1/2)*h) :
    ∃ k : ℤ, -(N:ℤ) ≤ k ∧ k ≤ (N:ℤ) ∧ |x-h*(k:ℝ)| ≤ h/2 := by
  let j : ℤ := ⌊x/h+1/2⌋
  have hx' := abs_le.mp hx
  have he : (x/h)*h = x := div_mul_cancel₀ _ hh.ne'
  have hjl : (j:ℝ) ≤ x/h+1/2 := Int.floor_le _
  have hju : x/h+1/2 < (j:ℝ)+1 := Int.lt_floor_add_one _
  have hjlow : -(N:ℤ) ≤ j := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith
  by_cases hj : j ≤ (N:ℤ)
  · refine ⟨j,hjlow,hj,abs_le.mpr ⟨?_,?_⟩⟩
    · nlinarith [mul_le_mul_of_nonneg_right hjl hh.le]
    · nlinarith [mul_lt_mul_of_pos_right hju hh]
  · refine ⟨(N:ℤ),by omega,le_rfl,abs_le.mpr ⟨?_,?_⟩⟩
    · have hjn : (N:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show (N:ℤ)+1 ≤ j by omega)
      norm_num only [Int.cast_natCast]
      nlinarith [mul_le_mul_of_nonneg_right hjn hh.le,mul_le_mul_of_nonneg_right hjl hh.le]
    · exact_mod_cast (show x-h*(N:ℝ) ≤ h/2 by nlinarith [hx'.2])

theorem centeredGrid_covers (r : Fin 3 → ℕ) {h : ℝ} (hh : 0 < h) :
    (⋃ k : {k // k ∈ centeredGridIndices r}, positionCube (gaussCellCenter h k.val) h) =
      {x : Position | ∀ i, |x i| ≤ ((r i:ℝ)+1/2)*h} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    have hki := (mem_centeredGridIndices r k.val).mp k.property
    intro i
    have hc := abs_le.mp (mem_positionCube.mp hk i)
    have hb1 : -(r i:ℝ) ≤ (k.val i:ℝ) := by exact_mod_cast (hki i).1
    have hb2 : (k.val i:ℝ) ≤ (r i:ℝ) := by exact_mod_cast (hki i).2
    apply abs_le.mpr
    change -(h/2) ≤ x i-h*(k.val i:ℝ) ∧ x i-h*(k.val i:ℝ) ≤ h/2 at hc
    rcases hc with ⟨hcl,hcu⟩
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb1 hh.le,
      mul_le_mul_of_nonneg_left hb2 hh.le]
  · intro hx
    choose k hk1 hk2 hk3 using fun i => exists_centered_grid_integer (r i) hh (hx i)
    refine Set.mem_iUnion.mpr ⟨⟨k,(mem_centeredGridIndices r k).mpr (fun i => ⟨hk1 i,hk2 i⟩)⟩,?_⟩
    rw [mem_positionCube]
    exact hk3

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability under rounding a nuclear position

Translated Hardy estimates uniformly control rational rounding on arbitrary
form-domain states. The constant eight permits a pointwise kernel inequality
also at the poles, using Lean's convention `0⁻¹ = 0`, and suffices for the
polynomial precision budget.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Pointwise control valid even where an inverse distance is totalized to zero. -/
theorem coulomb_kernel_shift_bound (x a b : Coulomb.Space) :
    |Coulomb.coulombKernel (x - a) - Coulomb.coulombKernel (x - b)| ≤
      ‖a - b‖ * (Coulomb.coulombKernel (x - a) ^ 2 +
        Coulomb.coulombKernel (x - b) ^ 2) := by
  unfold Coulomb.coulombKernel
  by_cases ha : x = a
  · subst x
    by_cases hab : a = b
    · simp [hab]
    · have hn : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
      simp only [sub_self, norm_zero, inv_zero, zero_sub, abs_neg,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), zero_pow (by decide : 2 ≠ 0),
        zero_add]
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  by_cases hb : x = b
  · subst x
    have hn : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha)
    simp only [sub_self, norm_zero, inv_zero, sub_zero,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), zero_pow (by decide : 2 ≠ 0),
      add_zero]
    rw [norm_sub_rev a b, pow_two, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have hr : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hs : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hd : |‖x - a‖ - ‖x - b‖| ≤ ‖a - b‖ := by
    have h := abs_norm_sub_norm_le (x - a) (x - b)
    have heq : (x - a) - (x - b) = b - a := by abel
    simpa only [heq, norm_sub_rev b a] using h
  have heq : ‖x - a‖⁻¹ - ‖x - b‖⁻¹ =
      (‖x - b‖ - ‖x - a‖) / (‖x - a‖ * ‖x - b‖) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hr hs), abs_sub_comm]
  calc
    |‖x - a‖ - ‖x - b‖| / (‖x - a‖ * ‖x - b‖) ≤
        ‖a - b‖ / (‖x - a‖ * ‖x - b‖) :=
      div_le_div_of_nonneg_right hd (mul_nonneg hr.le hs.le)
    _ = ‖a - b‖ * (‖x - a‖⁻¹ * ‖x - b‖⁻¹) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ‖a - b‖ * (‖x - a‖⁻¹ ^ 2 + ‖x - b‖⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [sq_nonneg (‖x - a‖⁻¹ - ‖x - b‖⁻¹), sq_nonneg ‖x - a‖⁻¹,
        sq_nonneg ‖x - b‖⁻¹]

/-- Translated Hardy as a bound for the square of the physical Coulomb kernel. -/
theorem nuclear_hardy_square {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a : Coulomb.Space) :
    Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ∧
    (∫ x, Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ≤
      4 * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  have h := state.hardy spin i (Coulomb.nuclearHardyCoordinates i a)
  simpa only [← Coulomb.hardyCoulomb_sq,
    Coulomb.hardyCoulomb_nuclear] using h

/-- An actual form-domain estimate on every spin component, uniform in both
nuclear positions and without a separation condition. -/
theorem nuclear_position_rounding_bound {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a b : Coulomb.Space) :
    |∫ x, (Coulomb.coulombKernel (Coulomb.position x i - a) -
      Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| ≤
      8 * ‖a - b‖ * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  obtain ⟨hia, hba⟩ := nuclear_hardy_square state spin i a
  obtain ⟨hib, hbb⟩ := nuclear_hardy_square state spin i b
  have hI : Integrable (fun x =>
      ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2)) := (hia.add hib).const_mul _
  have hdiff : Integrable (fun x =>
      (Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) *
          ‖state.value spin x‖ ^ 2) := by
    simp only [sub_mul]
    exact (state.nuclear_coulomb_integrable_bound spin i a (by norm_num : (0 : ℝ) < 1)).1.sub
      (state.nuclear_coulomb_integrable_bound spin i b (by norm_num : (0 : ℝ) < 1)).1
  have hp : ∀ x,
      |(Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| ≤
      ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := by
    intro x
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖state.value spin x‖)]
    have h := mul_le_mul_of_nonneg_right
      (coulomb_kernel_shift_bound (Coulomb.position x i) a b)
      (sq_nonneg ‖state.value spin x‖)
    simpa only [add_mul, mul_assoc] using h
  calc
    _ ≤ ∫ x, |(Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := integral_mono hdiff.abs hI hp
    _ = ‖a - b‖ * ((∫ x, Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2) +
      ∫ x, Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := by
      rw [integral_const_mul, integral_add hia hib]
    _ ≤ 8 * ‖a - b‖ * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hba hbb) (norm_nonneg (a - b))
      nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserChargeBounds
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivative control of the actual Poisson charge, from exactly
the six derivatives of the manufactured scalar potential. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem dirPartial_iterated_norm_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (v : Position) {k : ℕ} (hk : k ≤ 5) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial V v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) V x‖ := by
  have hf : ContDiff ℝ 5 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := v) hf.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 5 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

private theorem axis_second_partial_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial (dirPartial V (axis a)) (axis a)) x‖ ≤
      ‖iteratedFDeriv ℝ (k+2) V x‖ := by
  have hp : ContDiff ℝ 5 (dirPartial V (axis a)) :=
    (hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const
  have hpp : ContDiff ℝ 4 (fderiv ℝ (dirPartial V (axis a))) :=
    hp.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := axis a) hpp.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h' := dirPartial_iterated_norm_bound V hV (axis a) (show k+1 ≤ 5 by omega) x
  have hn : ‖axis a‖ = 1 := by simp [axis]
  simp only [hn, one_mul] at h h'
  exact h.trans (by simpa only [Nat.add_assoc] using h')

/-- All derivatives of the manufactured charge through order four have a
bound depending only on the scalar field's order-six bound. -/
theorem manufacturedCharge_derivative_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedCharge V) x‖ ≤ 3*B/(4*Real.pi) := by
  have hpp (a : Fin 3) : ContDiff ℝ 4 (dirPartial (dirPartial V (axis a)) (axis a)) :=
    (((hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const).fderiv_right
      (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 5)).clm_apply contDiff_const
  have he : coordinateLaplacian V = fun y =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) y :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  have hl : ‖iteratedFDeriv ℝ k (coordinateLaplacian V) x‖ ≤ 3*B := by
    rw [he, iteratedFDeriv_fun_sum_apply (fun a _ =>
      ((hpp a).of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt)]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Fin 3, B := Finset.sum_le_sum (fun a _ =>
        (axis_second_partial_bound V hV a hk x).trans (hbound (k+2) (by omega) x))
      _ = _ := by simp
  have hlreg : ContDiff ℝ 4 (coordinateLaplacian V) := by
    rw [he]
    exact ContDiff.sum (fun a _ => hpp a)
  have hc : (manufacturedCharge V) = fun y => (4*Real.pi)⁻¹ • coordinateLaplacian V y := by
    funext y
    unfold manufacturedCharge
    simp only [smul_eq_mul]
    ring
  rw [hc, iteratedFDeriv_const_smul_apply'
    (hlreg.of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformReciprocal
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform four-derivative reciprocal estimate away from zero, used
only for the positive density in the Moser field. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

private theorem reciprocal_derivatives_bounded {rho : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ 4, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k (fun z : ℝ => z⁻¹) y‖ ≤ C := by
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hsub : Set.Icc (rho/2) (3*rho/2) ⊆ T := by
    intro z hz
    exact ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hz.1)
  have hb (k : Fin 5) : ∃ A : ℝ, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹) y‖ ≤ A := by
    have hc : ContinuousOn (iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹)) T := by
      apply (hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast (show k.val ≤ 4 by omega))
        hT.uniqueDiffOn).congr
      intro z hz
      exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        k.val hT hz).symm
    obtain ⟨A,hA⟩ := isCompact_Icc.bddAbove_image ((hc.mono hsub).norm)
    exact ⟨A, fun y hy => hA ⟨y,hy,rfl⟩⟩
  choose B hB using hb
  let C : ℝ := 1+∑ k : Fin 5, max (B k) 0
  have hn : 0 ≤ ∑ k : Fin 5, max (B k) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro k hk y hy
  let i : Fin 5 := ⟨k, by omega⟩
  have hs : max (B i) 0 ≤ ∑ j : Fin 5, max (B j) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  exact (hB i y hy).trans ((le_max_left _ _).trans (by dsimp [C]; linarith))

/-- The constant depends on the density floor and on the four-derivative
bound, not on the support or the number of wells. -/
theorem uniform_reciprocal_four_bound {rho B : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ × Position → ℝ, ContDiff ℝ 4 f →
      ∀ x, f x ∈ Set.Icc (rho/2) (3*rho/2) →
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      ∀ k ≤ 4, ‖iteratedFDeriv ℝ k (fun y => (f y)⁻¹) x‖ ≤ C := by
  obtain ⟨A,hA,hAb⟩ := reciprocal_derivatives_bounded hrho
  let D : ℝ := max 1 B
  refine ⟨24*A*D^4, by dsimp [D]; positivity, ?_⟩
  intro f hf x hx hb k hk
  let U : Set (ℝ × Position) := {y | f y ≠ 0}
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hU : IsOpen U := isOpen_ne.preimage hf.continuous
  have hxU : x ∈ U := ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hx.1)
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hcomp := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
    hT.uniqueDiffOn hU.uniqueDiffOn (fun y hy => hy) hxU
    (C := A) (D := D) (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        j hT (show f x ∈ T from hxU)]
      exact hAb j (hj.trans hk) (f x) hx)
    (fun j hj hjk => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hxU]
      exact (hb j (hjk.trans hk)).trans ((le_max_right 1 B).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (le_max_left 1 B) hj)))
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := (fun z : ℝ => z⁻¹) ∘ f) k hU hxU] at hcomp
  apply hcomp.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show k.factorial ≤ 24 from
        (Nat.factorial_le hk).trans (by decide))) hA.le
  · exact pow_le_pow_right₀ (le_max_left 1 B) hk
  · exact pow_nonneg (le_trans zero_le_one (le_max_left 1 B)) k
  · positivity

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserUniformDensity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform joint density bounds for the actual Moser homotopy. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem contraction_four_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : F → ℝ) (hf : ContDiff ℝ 4 f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j ≤ 4, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : E) : ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  exact (mul_le_mul (hb k hk _) (pow_le_one₀ (norm_nonneg L) hL)
    (pow_nonneg (norm_nonneg L) _) hB).trans_eq (mul_one B)

private theorem fst_four_bound {k : ℕ} (x : ℝ × Position) (hx : |x.1| ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × Position => y.1) x‖ ≤ 1 := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    change ‖iteratedFDeriv ℝ k (fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position)) x‖ ≤ 1
    have hder : fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position) =
        fun _ => ContinuousLinearMap.fst ℝ ℝ Position :=
      funext (fun _ => (ContinuousLinearMap.fst ℝ ℝ Position).fderiv)
    rw [hder]
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := ℝ) (F := Position))
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

/-- A uniform bound for the four joint derivatives of rho+t*charge. -/
theorem homotopyDensity_uniform_derivatives {rho B : ℝ} (hB : 0 ≤ B)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) (t,x)‖ ≤
      |rho|+16*(3*B/(4*Real.pi)) := by
  let C : ℝ := 3*B/(4*Real.pi)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcharge (j : ℕ) (hj : j ≤ 4) (y : ℝ × Position) :
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => manufacturedCharge V p.2) y‖ ≤ C :=
    contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (manufacturedCharge V) (manufacturedCharge_C4 V hV)
      hC (fun j hj z => manufacturedCharge_derivative_bound V hV hB hb hj z) hj y
  have hf : ContDiff ℝ 4 (fun p : ℝ × Position => p.1 * manufacturedCharge V p.2) :=
    contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd)
  have hprod : ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
      p.1*manufacturedCharge V p.2) (t,x)‖ ≤ 16*C := by
    apply (norm_iteratedFDeriv_mul_le contDiff_fst
      ((manufacturedCharge_C4 V hV).comp contDiff_snd) (t,x)
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have ht' : |(t,x).1| ≤ 1 := by
          change |t| ≤ 1
          rw [abs_of_nonneg ht.1]
          exact ht.2
        exact (mul_le_mul
          (mul_le_mul_of_nonneg_left (fst_four_bound (k := i) (t,x) ht')
            (Nat.cast_nonneg _))
          (hcharge (k-i) ((Nat.sub_le k i).trans hk) (t,x))
          (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ = (2:ℝ)^k*C := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
      _ ≤ 16*C := mul_le_mul_of_nonneg_right
        ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)) hC
  change ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
    rho + p.1*manufacturedCharge V p.2) (t,x)‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply contDiff_const.contDiffAt
    (hf.of_le (by exact_mod_cast hk)).contDiffAt]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hprod
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, abs_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserUniformVelocity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Moser velocity and flow have a common derivative bound over all
potentials with a common order-six bound. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem product_four_bound (U : Set (ℝ × Position)) (hU : IsOpen U)
    (f g : ℝ × Position → ℝ) (hf : ContDiffOn ℝ 4 f U) (hg : ContDiffOn ℝ 4 g U)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) {x : ℝ × Position} (hx : x ∈ U)
    (hb : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hc : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 16*B*C := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := U) _ hU hx] at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*B*C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hk)) (Nat.cast_nonneg _))
        (hc (k-i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^k*B*C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 16*B*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul_of_nonneg_right _ hB
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)

private theorem partial_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 4 (dirPartial V (axis a)) :=
  (hV.fderiv_right (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const

private theorem partial_joint_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : ℝ × Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => dirPartial V (axis a) p.2) x‖ ≤ B := by
  apply contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
    (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (dirPartial V (axis a)) (partial_C4 V hV a) hB
    (fun j hj y => ?_) hk x
  have h := dirPartial_iterated_norm_bound V hV (axis a) (show j ≤ 5 by omega) y
  have hn : ‖axis a‖ = 1 := by simp [axis]
  rw [hn, one_mul] at h
  exact h.trans (hb (j+1) (by omega) y)

/-- One bound controls all joint velocity derivatives through order four
for the entire bounded family of potentials. -/
theorem moserVelocity_family_derivative_bound {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ k ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t,x)‖ ≤ C := by
  let D : ℝ := |rho|+16*(3*B/(4*Real.pi))
  obtain ⟨A,hA,hAb⟩ := uniform_reciprocal_four_bound (B := D) hrho
  refine ⟨48*(B+1)*A/(4*Real.pi), by positivity, ?_⟩
  intro V hV hb hcharge k hk t ht x
  let U := moserDomain rho V
  have hU : IsOpen U := moserDomain_isOpen rho V hV
  have hxU : (t,x) ∈ U := moserDomain_contains_time_slab hrho V hcharge ⟨ht,Set.mem_univ _⟩
  let d : ℝ × Position → ℝ := fun p => homotopyDensity rho V p.1 p.2
  let invd : ℝ × Position → ℝ := fun p => (d p)⁻¹
  have hd : ContDiff ℝ 4 d := homotopyDensity_joint_C4 rho V hV
  have hi : ContDiffOn ℝ 4 invd U := hd.contDiffOn.inv (fun p hp => hp)
  have hiB (j : ℕ) (hj : j ≤ 4) : ‖iteratedFDeriv ℝ j invd (t,x)‖ ≤ A :=
    hAb d hd (t,x) (homotopyDensity_bounds V hcharge ht.1 ht.2 x)
      (fun i hi => homotopyDensity_uniform_derivatives hB V hV hb hi ht x) j hj
  let f : Fin 3 → ℝ × Position → ℝ := fun a p =>
    -(4*Real.pi)⁻¹ * dirPartial V (axis a) p.2
  have hf (a : Fin 3) : ContDiff ℝ 4 (f a) :=
    contDiff_const.mul ((partial_C4 V hV a).comp contDiff_snd)
  have hfB (a : Fin 3) (j : ℕ) (hj : j ≤ 4) :
      ‖iteratedFDeriv ℝ j (f a) (t,x)‖ ≤ B/(4*Real.pi) := by
    change ‖iteratedFDeriv ℝ j (fun p : ℝ × Position =>
      (-(4*Real.pi)⁻¹) • dirPartial V (axis a) p.2) (t,x)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      (f := fun p : ℝ × Position => dirPartial V (axis a) p.2)
      (a := -(4*Real.pi)⁻¹)
      (((partial_C4 V hV a).comp contDiff_snd).of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (partial_joint_bound V hV hB hb a hj (t,x))
      (by positivity)).trans_eq (by ring)
  let F : Fin 3 → ℝ × Position → ℝ := fun a p => f a p * invd p
  have hF (a : Fin 3) : ContDiffOn ℝ 4 (F a) U := (hf a).contDiffOn.mul hi
  have hFB (a : Fin 3) : ‖iteratedFDeriv ℝ k (F a) (t,x)‖ ≤ 16*(B/(4*Real.pi))*A :=
    product_four_bound U hU (f a) invd (hf a).contDiffOn hi
      (by positivity) hA.le hxU (hfB a) hiB hk
  let L : Fin 3 → ℝ →L[ℝ] Position := fun a =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (axis a)
  have hL (a : Fin 3) : ‖L a‖ = 1 := by
    simp [L, ContinuousLinearMap.norm_smulRight_apply, axis]
  have hsum : (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) =
      fun p => ∑ a : Fin 3, L a (F a p) := by
    funext p
    ext a
    simp [moserVelocity, L, F, f, invd, d, axis, Pi.single_apply, eq_comm, div_eq_mul_inv, mul_inv_rev, mul_assoc]; ring
  rw [hsum, iteratedFDeriv_fun_sum_apply
    (f := fun a p => L a (F a p)) (fun a _ =>
    (((L a).contDiff.comp_contDiffOn (hF a)).contDiffAt (hU.mem_nhds hxU)).of_le
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a : Fin 3, 16*(B/(4*Real.pi))*A := by
      apply Finset.sum_le_sum
      intro a _
      have h := (L a).norm_iteratedFDeriv_comp_left
        ((hF a).contDiffAt (hU.mem_nhds hxU))
        (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
      rw [hL, one_mul] at h
      exact h.trans (hFB a)
    _ ≤ 48*(B+1)*A/(4*Real.pi) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      have hp : 0 < 4*Real.pi := by positivity
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ScalarScaleBudgets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed size-independent thresholds for the scalar conditions in the
manufactured continuum comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_logarithmic_scale_threshold (D : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      D ≤ 25*(k:ℝ)*Real.log N := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k₀,hk₀⟩ := exists_nat_ge (max 1 (D/(25*Real.log 2)))
  refine ⟨k₀,by exact_mod_cast (le_max_left _ _).trans hk₀,fun k hk N hN => ?_⟩
  have hquot : D/(25*Real.log 2) ≤ (k:ℝ) :=
    ((le_max_right _ _).trans hk₀).trans (by exact_mod_cast hk)
  have hD := (div_le_iff₀ (by positivity : 0 < 25*Real.log 2)).mp hquot
  have hlogs : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  calc
    D ≤ 25*(k:ℝ)*Real.log 2 := by nlinarith only [hD]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (by positivity)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the two entrywise approximation budgets in the finite form. -/

noncomputable section
namespace ContinuumCoulomb

theorem double_inverse_power_le {N : ℝ} (hN : 2 ≤ N) (j : ℕ) :
    (N^(j+1))⁻¹+(N^(j+1))⁻¹ ≤ (N^j)⁻¹ := by
  have hN0 : 0 < N := by linarith
  rw [pow_succ]
  have hh : 2/(N^j*N) ≤ 1/N^j :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith [pow_pos hN0 j])
  simpa only [div_eq_mul_inv,one_mul,two_mul] using hh

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerApproximation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative inexact Euler estimates. All error assumptions concern
the vector field and the actual local differential equation; no endpoint
approximation is assumed. -/

noncomputable section
namespace ContinuumCoulomb.EulerApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem step_error (v evaluate : ℕ → E → E) (z : ℕ → E)
    (x : E) (n : ℕ) {h L δ D : ℝ} (hh : 0 ≤ h)
    (hLip : ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ‖evaluate n x-v n x‖ ≤ δ)
    (hdefect : ‖z n+h • v n (z n)-z (n+1)‖ ≤ D) :
    ‖x+h • evaluate n x-z (n+1)‖ ≤ (1+h*L)*‖x-z n‖+h*δ+D := by
  have hid : x+h • evaluate n x-z (n+1) =
      (x-z n) + h • (evaluate n x-v n (z n)) + (z n+h • v n (z n)-z (n+1)) := by
    module
  have hv : ‖evaluate n x-v n (z n)‖ ≤ δ+L*‖x-z n‖ := by
    have heq : evaluate n x-v n (z n) = (evaluate n x-v n x)+(v n x-v n (z n)) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add heval hLip)
  rw [hid]
  calc
    _ ≤ ‖x-z n‖+‖h • (evaluate n x-v n (z n))‖+‖z n+h • v n (z n)-z (n+1)‖ :=
      by
        have h₁ := norm_add_le ((x-z n)+h • (evaluate n x-v n (z n)))
          (z n+h • v n (z n)-z (n+1))
        have h₂ := norm_add_le (x-z n) (h • (evaluate n x-v n (z n)))
        linarith
    _ ≤ ‖x-z n‖+h*(δ+L*‖x-z n‖)+D := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
      gcongr
    _ = _ := by ring

theorem finite_recurrence_bound (u : ℕ → ℝ) (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u 0)
    (hstep : ∀ k < N, u (k+1) ≤ (1+a)*u k+b) :
    ∀ n ≤ N, u n ≤ (u 0+(n:ℝ)*b)*Real.exp ((n:ℝ)*a) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnk : n < N := by omega
    have hprev := ih (Nat.le_of_lt hnk)
    have hbase : 0 ≤ u 0+(n:ℝ)*b := add_nonneg hu (mul_nonneg (Nat.cast_nonneg _) hb)
    have hfac : (1+a)*Real.exp ((n:ℝ)*a) ≤ Real.exp (((n:ℝ)+1)*a) := by
      calc
        _ ≤ Real.exp a*Real.exp ((n:ℝ)*a) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hexp : 1 ≤ Real.exp (((n:ℝ)+1)*a) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) ha)
    calc
      u (n+1) ≤ (1+a)*u n+b := hstep n hnk
      _ ≤ (1+a)*((u 0+(n:ℝ)*b)*Real.exp ((n:ℝ)*a))+b := by gcongr
      _ = (u 0+(n:ℝ)*b)*((1+a)*Real.exp ((n:ℝ)*a))+b := by ring
      _ ≤ (u 0+(n:ℝ)*b)*Real.exp (((n:ℝ)+1)*a)+b*Real.exp (((n:ℝ)+1)*a) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfac hbase)
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hb)
      _ = (u 0+((n+1:ℕ):ℝ)*b)*Real.exp (((n+1:ℕ):ℝ)*a) := by
        push_cast
        ring

/-- The actual solution has a quadratic one-step error whenever its
velocity is bounded and the field is jointly Lipschitz in time and space. -/
theorem local_defect (v : ℝ → E → E) (z : ℝ → E)
    {t h L M : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hz : ∀ s ∈ Set.Icc t (t+h),
      HasDerivWithinAt z (v s (z s)) (Set.Icc t (t+h)) s)
    (hbound : ∀ s ∈ Set.Icc t (t+h), ‖v s (z s)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc t (t+h),
      ‖v s (z s)-v t (z t)‖ ≤ L*(|s-t|+‖z s-z t‖)) :
    ‖z t+h • v t (z t)-z (t+h)‖ ≤ L*(1+M)*h^2 := by
  have hab : t ≤ t+h := by linarith
  have hspeed (s : ℝ) (hs : s ∈ Set.Icc t (t+h)) : ‖z s-z t‖ ≤ M*(s-t) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hz
      (fun r hr => hbound r ⟨hr.1,hr.2.le⟩) s hs
  let F : ℝ → E := fun s => z s-(s-t) • v t (z t)
  have hF (s : ℝ) (hs : s ∈ Set.Icc t (t+h)) :
      HasDerivWithinAt F (v s (z s)-v t (z t)) (Set.Icc t (t+h)) s := by
    have hlin : HasDerivAt (fun r : ℝ => (r-t) • v t (z t)) (v t (z t)) s := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id s).sub_const t).smul_const (v t (z t))
    exact (hz s hs).sub hlin.hasDerivWithinAt
  have hderiv (s : ℝ) (hs : s ∈ Set.Ico t (t+h)) :
      ‖v s (z s)-v t (z t)‖ ≤ L*(1+M)*h := by
    have hs' : s ∈ Set.Icc t (t+h) := ⟨hs.1,hs.2.le⟩
    have hnorm := hspeed s hs'
    have habs : |s-t| = s-t := abs_of_nonneg (sub_nonneg.mpr hs.1)
    calc
      _ ≤ L*(|s-t|+‖z s-z t‖) := hLip s hs'
      _ ≤ L*((s-t)+M*(s-t)) := by rw [habs]; gcongr
      _ = L*(1+M)*(s-t) := by ring
      _ ≤ L*(1+M)*h := mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)
  have hest := norm_image_sub_le_of_norm_deriv_le_segment' hF hderiv (t+h) ⟨hab,le_rfl⟩
  have hid : F (t+h)-F t = -(z t+h • v t (z t)-z (t+h)) := by
    dsimp [F]
    simp only [add_sub_cancel_left,sub_self,zero_smul,sub_zero]
    abel
  rw [hid,norm_neg] at hest
  convert hest using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb.EulerApproximation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalBoxRound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded integer numerator registers for rounded Euler iteration.
Clipping to a fixed box prevents malformed evaluator outputs from causing
unbounded register growth. On valid trajectories clipping never increases
the distance to the exact coordinate. -/

namespace ContinuumCoulomb.RationalBoxRound
open ExactQuantumFactoring.BitStackProgram

theorem clip_real_error {B x q : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |max (-B) (min B q)-x| ≤ |q-x| := by
  by_cases hlo : q ≤ -B
  · rw [min_eq_right (by linarith),max_eq_left hlo]
    have hxl := (abs_le.mp hx).1
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · by_cases hhi : B ≤ q
    · rw [min_eq_left hhi,max_eq_right (by linarith)]
      have hxu := (abs_le.mp hx).2
      rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo)]

theorem value_error {D B : ℕ} (hD : 0 < D) (q : ℚ) (x : ℝ)
    (hx : |x| ≤ (B:ℝ)/(D:ℝ)) :
    |(value D B q:ℝ)-x| ≤ |(q:ℝ)-x|+1/(D:ℝ) := by
  have hDp : (0:ℝ) < D := by exact_mod_cast hD
  have hfloor : |(⌊(D:ℚ)*q⌋:ℝ)-(D:ℝ)*(q:ℝ)| ≤ 1 := by
    have hl := Int.floor_le ((D:ℚ)*q)
    have hu := Int.lt_floor_add_one ((D:ℚ)*q)
    have hlR : (⌊(D:ℚ)*q⌋:ℝ) ≤ (D:ℝ)*(q:ℝ) := by exact_mod_cast hl
    have huR : (D:ℝ)*(q:ℝ) < (⌊(D:ℚ)*q⌋:ℝ)+1 := by exact_mod_cast hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have htarget : |(D:ℝ)*x| ≤ B := by
    rw [abs_mul,abs_of_pos hDp]
    exact (mul_le_mul_of_nonneg_left hx hDp.le).trans_eq (by field_simp)
  have hc := clip_real_error (show (0:ℝ) ≤ B by positivity) htarget
    (q := (⌊(D:ℚ)*q⌋:ℝ))
  have hcast : (numerator D B q:ℝ) =
      max (-(B:ℝ)) (min (B:ℝ) (⌊(D:ℚ)*q⌋:ℝ)) := by
    simp only [numerator,clip,Int.cast_max,Int.cast_min,Int.cast_neg,Int.cast_natCast]
  rw [← hcast] at hc
  have ht := abs_sub_le (⌊(D:ℚ)*q⌋:ℝ) ((D:ℝ)*(q:ℝ)) ((D:ℝ)*x)
  have hscale : |(D:ℝ)*(q:ℝ)-(D:ℝ)*x| = (D:ℝ)*|(q:ℝ)-x| := by
    rw [← mul_sub,abs_mul,abs_of_pos hDp]
  rw [hscale] at ht
  have heq : (value D B q:ℝ)-x = ((numerator D B q:ℝ)-(D:ℝ)*x)/(D:ℝ) := by
    simp only [value,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
    field_simp
  rw [heq,abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  have hs : (|(q:ℝ)-x|+1/(D:ℝ))*(D:ℝ) = (D:ℝ)*|(q:ℝ)-x|+1 := by field_simp
  rw [hs]
  linarith

end ContinuumCoulomb.RationalBoxRound

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |(value (b, q) : ℝ) - Real.sqrt (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  have h := DyadicRootProgram.value_error b q.num.toNat q.den q.pos
  rw [hre] at h
  change |(DyadicRootProgram.value b q.num.toNat q.den : ℝ) - Real.sqrt (q : ℝ)| ≤ _
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2.le.trans_eq (by simp only [one_div, inv_pow])

end ContinuumCoulomb.RationalSquareRoot

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_RoundedEuler
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Grid rounding after every Euler step controls the size of rational
intermediates. The rounding error is accumulated in the actual trajectory
estimate, separately from the field sampling and time discretization. -/

noncomputable section
namespace ContinuumCoulomb.EulerApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_flow_local_defect (v : ℝ → E → E) (z : ℝ → E)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖v s (z s)-v t (z t)‖ ≤ L*(|s-t|+‖z s-z t‖))
    {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t+h ≤ 1) :
    ‖z t+h • v t (z t)-z (t+h)‖ ≤ L*(1+M)*h^2 := by
  have hsub : Set.Icc t (t+h) ⊆ Set.Icc (0:ℝ) 1 := by
    intro s hs
    exact ⟨ht.trans hs.1, hs.2.trans hth⟩
  exact local_defect v z hh hL hM
    (fun s hs => (hz s (hsub hs)).mono hsub)
    (fun s hs => hbound s (hsub hs))
    (fun s hs => hLip s (hsub hs) t ⟨ht, by linarith⟩)

/-- Projection onto a fixed box may move an inaccurate Euler proposal a
long way, but it only improves its distance to a trajectory inside that
box. This form of the recurrence handles such projections directly. -/
theorem projected_sequence_error (v evaluate : ℕ → E → E) (z y : ℕ → E)
    (N : ℕ) {h L δ D R : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hLip : ∀ n < N, ∀ x, ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ∀ n < N, ‖evaluate n (y n)-v n (y n)‖ ≤ δ)
    (hdefect : ∀ n < N, ‖z n+h • v n (z n)-z (n+1)‖ ≤ D)
    (hproject : ∀ n < N, ‖y (n+1)-z (n+1)‖ ≤
      ‖y n+h • evaluate n (y n)-z (n+1)‖+R) :
    ‖y N-z N‖ ≤
      (‖y 0-z 0‖+(N:ℝ)*(h*δ+D+R))*Real.exp ((N:ℝ)*(h*L)) := by
  let u : ℕ → ℝ := fun n => ‖y n-z n‖
  have hb : 0 ≤ h*δ+D+R := by positivity
  have hs (n : ℕ) (hn : n < N) : u (n+1) ≤ (1+h*L)*u n+(h*δ+D+R) := by
    have he := step_error v evaluate z (y n) n hh (hLip n hn _)
      (heval n hn) (hdefect n hn)
    dsimp [u]
    linarith [hproject n hn]
  exact finite_recurrence_bound u N (mul_nonneg hh hL) hb (norm_nonneg _) hs N le_rfl

theorem sampled_unit_error (v : ℝ → E → E) (z : ℝ → E)
    (evaluate : ℕ → E → E) (y : ℕ → E) {N : ℕ} (hN : 0 < N)
    {L M δ R : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x w,
      ‖v s x-v t w‖ ≤ L*(|s-t|+‖x-w‖))
    (heval : ∀ n < N, ‖evaluate n (y n)-v ((n:ℝ)/N) (y n)‖ ≤ δ)
    (hproject : ∀ n < N,
      ‖y (n+1)-z (((n:ℝ)+1)/N)‖ ≤
        ‖y n+(N:ℝ)⁻¹ • evaluate n (y n)-z (((n:ℝ)+1)/N)‖+R) :
    ‖y N-z 1‖ ≤
      (‖y 0-z 0‖+δ+L*(1+M)/(N:ℝ)+(N:ℝ)*R)*Real.exp L := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hNN : (N:ℝ) ≠ 0 := hNp.ne'
  let zseq : ℕ → E := fun n => z ((n:ℝ)/N)
  let vseq : ℕ → E → E := fun n => v ((n:ℝ)/N)
  have htime (n : ℕ) (hn : n ≤ N) : (n:ℝ)/N ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hNp).mpr (by exact_mod_cast hn)
  have hnext (n : ℕ) : (n:ℝ)/N+(N:ℝ)⁻¹ = ((n:ℝ)+1)/N := by ring
  have hl (n : ℕ) (hn : n < N) (x : E) :
      ‖vseq n x-vseq n (zseq n)‖ ≤ L*‖x-zseq n‖ := by
    simpa only [vseq,zseq,sub_self,abs_zero,zero_add] using
      hLip ((n:ℝ)/N) (htime n hn.le) ((n:ℝ)/N) (htime n hn.le) x (zseq n)
  have hd (n : ℕ) (hn : n < N) :
      ‖zseq n+(N:ℝ)⁻¹ • vseq n (zseq n)-zseq (n+1)‖ ≤
        L*(1+M)*((N:ℝ)⁻¹)^2 := by
    have hnxt : (n:ℝ)/N+(N:ℝ)⁻¹ ≤ 1 := by
      rw [hnext]
      apply (div_le_one hNp).mpr
      exact_mod_cast (show n+1 ≤ N by omega)
    have he := uniform_flow_local_defect v z hL hM hz hbound
      (fun s hs t ht => hLip s hs t ht (z s) (z t))
      (t := (n:ℝ)/N) (h := (N:ℝ)⁻¹) (htime n hn.le).1 (by positivity) hnxt
    simpa only [zseq,vseq,hnext,Nat.cast_add,Nat.cast_one] using he
  have hp (n : ℕ) (hn : n < N) :
      ‖y (n+1)-zseq (n+1)‖ ≤ ‖y n+(N:ℝ)⁻¹ • evaluate n (y n)-zseq (n+1)‖+R := by
    simpa only [zseq,Nat.cast_add,Nat.cast_one] using hproject n hn
  have he := projected_sequence_error vseq evaluate zseq y N (by positivity) hL hδ
    (by positivity) hR hl heval hd hp
  have hexp : (N:ℝ)*((N:ℝ)⁻¹*L) = L := by field_simp
  have hsum : (N:ℝ)*((N:ℝ)⁻¹*δ+L*(1+M)*((N:ℝ)⁻¹)^2+R) =
      δ+L*(1+M)/(N:ℝ)+(N:ℝ)*R := by field_simp
  have hsum' : (N:ℝ)*((N:ℝ)⁻¹*δ+(L*(1+M)*((N:ℝ)⁻¹)^2+R)) =
      δ+(L*(1+M)/(N:ℝ)+(N:ℝ)*R) := by simpa only [add_assoc] using hsum
  simpa only [zseq,div_self hNN,Nat.cast_zero,zero_div,hexp,add_assoc,hsum'] using he

end ContinuumCoulomb.EulerApproximation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerGeometry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Componentwise box projection preserves Euclidean distance to every
point in the box. Rounding the projected numerator adds at most `3 / D`;
there is no multiplicative loss in the Euler error recurrence. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

private theorem norm_le_of_abs_le (x y : Position)
    (h : ∀ a, |x a| ≤ |y a|) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro a _
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (h a)

theorem norm_of_coordinate_error {x y : Position} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ a, |x a| ≤ |y a|+d) : ‖x‖ ≤ ‖y‖+3*d := by
  let a : Position := WithLp.toLp 2 (fun i => |y i|)
  let b : Position := WithLp.toLp 2 (fun _ : Fin 3 => d)
  have ha : ‖a‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [a,sq_abs]
  have hb : ‖b‖ ≤ 3*d := by
    have hs : ‖b‖^2 = 3*d^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [b,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_ofNat]
    nlinarith [norm_nonneg b]
  have hc : ‖x‖ ≤ ‖a+b‖ := by
    apply norm_le_of_abs_le
    intro i
    simpa only [a,b,PiLp.add_apply,PiLp.toLp_apply,abs_of_nonneg (add_nonneg (abs_nonneg _) hd)] using h i
  exact hc.trans ((norm_add_le a b).trans (by rw [ha]; linarith))

theorem round_position_error {D B : ℕ} (hD : 0 < D) (q : Triple) (x : Position)
    (hx : ∀ a, |x a| ≤ (B:ℝ)/(D:ℝ)) :
    ‖position (point D (round D B q))-x‖ ≤ ‖position q-x‖+3/(D:ℝ) := by
  have hd : (0:ℝ) ≤ 1/(D:ℝ) := by positivity
  have hc (a : Fin 3) :
      |(position (point D (round D B q))-x) a| ≤ |(position q-x) a|+1/(D:ℝ) := by
    fin_cases a <;>
      simpa [point,round,position,RationalBoxRound.value] using RationalBoxRound.value_error hD _ _ (hx _)
  have he := norm_of_coordinate_error hd hc
  simpa only [mul_one_div] using he

theorem proposal_position (h : ℚ) (q v : Triple) :
    position (proposal h q v) = position q+(h:ℝ) • position v := by
  ext a
  fin_cases a <;> simp [proposal,position]

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerTrajectory
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual clipped-register iteration obeys the proved Euler error
estimate. All numerical values here are the rational register values;
the hypotheses concern the usual velocity error, speed and Lipschitz bounds. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

variable {E : Type}

theorem trajectory_zero (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) : trajectory evaluate e N D B r 0 = point D r := rfl

theorem trajectory_succ (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) (n : ℕ) :
    trajectory evaluate e N D B r (n+1) =
      point D (round D B (proposal (N:ℚ)⁻¹ (trajectory evaluate e N D B r n)
        (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n)))) := by
  unfold trajectory
  rw [Function.iterate_succ_apply']
  simp only [advance,iterate_parameters,iterate_counter,initial,Nat.zero_add]

/-- Final error for the exact rational register recurrence. The box
condition is only imposed on the true solution, not on numerical proposals. -/
theorem trajectory_error (evaluate : E → ℚ → Triple → Triple) (e : E)
    {N D : ℕ} (hN : 0 < N) (hD : 0 < D) (B : ℕ) (r : Registers)
    (v : ℝ → Position → Position) (z : ℝ → Position)
    {L M δ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x w,
      ‖v s x-v t w‖ ≤ L*(|s-t|+‖x-w‖))
    (hbox : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ (B:ℝ)/(D:ℝ))
    (heval : ∀ n < N,
      ‖position (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n))-
        v ((n:ℝ)/N) (position (trajectory evaluate e N D B r n))‖ ≤ δ) :
    ‖position (trajectory evaluate e N D B r N)-z 1‖ ≤
      (‖position (point D r)-z 0‖+δ+L*(1+M)/(N:ℝ)+3*(N:ℝ)/(D:ℝ))*Real.exp L := by
  let y : ℕ → Position := fun n => position (trajectory evaluate e N D B r n)
  let sample : ℕ → Position → Position := fun n _ =>
    position (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n))
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hp (n : ℕ) (hn : n < N) :
      ‖y (n+1)-z (((n:ℝ)+1)/N)‖ ≤
        ‖y n+(N:ℝ)⁻¹ • sample n (y n)-z (((n:ℝ)+1)/N)‖+3/(D:ℝ) := by
    have ht : ((n:ℝ)+1)/(N:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one hNp).mpr
        exact_mod_cast (show n+1 ≤ N by omega)
    have he := round_position_error hD
      (proposal (N:ℚ)⁻¹ (trajectory evaluate e N D B r n)
        (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n)))
      (z (((n:ℝ)+1)/N)) (hbox _ ht)
    simpa only [y,sample,trajectory_succ,proposal_position,Rat.cast_inv,Rat.cast_natCast] using he
  have he := EulerApproximation.sampled_unit_error v z sample y hN hL hM hδ
    (show 0 ≤ 3/(D:ℝ) by positivity) hz hbound hLip heval hp
  have hmul : (N:ℝ)*(3/(D:ℝ)) = 3*(N:ℝ)/(D:ℝ) := by ring
  simpa only [y,trajectory_zero,hmul] using he

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial step count, sample precision, and register denominator for
unit-time integration with fixed speed/Lipschitz guards. The same step
count is used as the velocity sample precision. -/

namespace ContinuumCoulomb.EulerRegisters

theorem steps_positive {C P : ℕ} (hC : 0 < C) : 0 < steps C P := by
  unfold steps
  positivity

theorem schedule_budget {C P : ℕ} (hC : 0 < C) {L M : ℝ}
    (hExp : Real.exp L ≤ (C:ℝ)) (hLM : L*(1+M) ≤ C) :
    (3/(denominator C P:ℝ)+((steps C P:ℝ)+1)⁻¹+
      L*(1+M)/(steps C P:ℝ)+3*(steps C P:ℝ)/(denominator C P:ℝ))*Real.exp L ≤
      ((P:ℝ)+1)⁻¹ := by
  let N : ℝ := steps C P
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  have hC1 : (1:ℝ) ≤ C := by exact_mod_cast hC
  have hNp : 0 < N := by dsimp [N]; exact_mod_cast steps_positive (P := P) hC
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast steps_positive (P := P) hC
  have hN : N = 16*(C:ℝ)^2*((P:ℝ)+1) := by
    simp only [N,steps,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  have hD : (denominator C P:ℝ) = N^2 := by simp only [denominator,Nat.cast_pow,N]
  have hq : 0 < (P:ℝ)+1 := by positivity
  have hi : 3/(denominator C P:ℝ) ≤ 3/N := by
    rw [hD]
    apply (div_le_div_iff₀ (sq_pos_of_pos hNp) hNp).mpr
    nlinarith
  have hs : ((steps C P:ℝ)+1)⁻¹ ≤ 1/N := by
    change (N+1)⁻¹ ≤ 1/N
    rw [one_div]
    exact inv_anti₀ hNp (le_add_of_nonneg_right zero_le_one)
  have hl : L*(1+M)/(steps C P:ℝ) ≤ (C:ℝ)/N :=
    div_le_div_of_nonneg_right hLM hNp.le
  have hr : 3*(steps C P:ℝ)/(denominator C P:ℝ) = 3/N := by
    rw [hD]
    change 3*N/N^2 = 3/N
    field_simp [hNp.ne']
  have ht : 3/(denominator C P:ℝ)+((steps C P:ℝ)+1)⁻¹+
      L*(1+M)/(steps C P:ℝ)+3*(steps C P:ℝ)/(denominator C P:ℝ) ≤ 8*(C:ℝ)/N := by
    rw [hr]
    have hc : 3/N+1/N+(C:ℝ)/N+3/N ≤ 8*(C:ℝ)/N := by
      calc
        _ = ((C:ℝ)+7)/N := by ring
        _ ≤ 8*(C:ℝ)/N := div_le_div_of_nonneg_right (by nlinarith) hNp.le
    exact (add_le_add (add_le_add (add_le_add hi hs) hl) le_rfl).trans hc
  calc
    _ ≤ (8*(C:ℝ)/N)*Real.exp L := mul_le_mul_of_nonneg_right ht (Real.exp_pos L).le
    _ ≤ (8*(C:ℝ)/N)*(C:ℝ) := mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = (1/2:ℝ)*((P:ℝ)+1)⁻¹ := by
      rw [hN]
      field_simp [hCp.ne',hq.ne']
      norm_num
    _ ≤ ((P:ℝ)+1)⁻¹ := mul_le_of_le_one_left (inv_nonneg.mpr hq.le) (by norm_num)

end ContinuumCoulomb.EulerRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_EulerInitialBox
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary-encoded box radius computed directly from the three input
rational numerators encloses the true bounded-speed trajectory. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

private theorem rational_abs_le_num (q : ℚ) : |(q:ℝ)| ≤ (q.num.natAbs:ℝ) := by
  have hd : (1:ℝ) ≤ q.den := by exact_mod_cast (Nat.succ_le_of_lt q.pos)
  have hp : (0:ℝ) < q.den := by exact_mod_cast q.pos
  rw [Rat.cast_def,abs_div,abs_of_pos hp,Nat.cast_natAbs,Int.cast_abs]
  exact (div_le_self (abs_nonneg _) hd)

theorem inputRadius_bound (q : Triple) (a : Fin 3) : |position q a| ≤ (inputRadius q:ℝ) := by
  have h0 := rational_abs_le_num q.1
  have h1 := rational_abs_le_num q.2.1
  have h2 := rational_abs_le_num q.2.2
  have hn0 : (0:ℝ) ≤ q.1.num.natAbs := Nat.cast_nonneg _
  have hn1 : (0:ℝ) ≤ q.2.1.num.natAbs := Nat.cast_nonneg _
  have hn2 : (0:ℝ) ≤ q.2.2.num.natAbs := Nat.cast_nonneg _
  simp only [Nat.cast_natAbs,Int.cast_abs] at h0 h1 h2 hn0 hn1 hn2
  fin_cases a <;> simp only [inputRadius,Nat.cast_add,position,PiLp.toLp_apply] <;> norm_num <;> linarith

theorem boxNumerator_ratio {D C : ℕ} (hD : 0 < D) (q : Triple) :
    (boxNumerator C D q:ℝ)/(D:ℝ) = (inputRadius q:ℝ)+(C:ℝ)+1 := by
  have hd : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [boxNumerator,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem initial_round_error {D C : ℕ} (hD : 0 < D) (q : Triple) :
    ‖position (point D (round D (boxNumerator C D q) q))-position q‖ ≤ 3/(D:ℝ) := by
  have h := round_position_error (B := boxNumerator C D q) hD q (position q) (fun a => by
    rw [boxNumerator_ratio (C := C) hD]
    exact (inputRadius_bound q a).trans (by linarith [Nat.cast_nonneg (α := ℝ) C]))
  simpa only [sub_self,norm_zero,zero_add] using h

end ContinuumCoulomb.EulerRegisters

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserDifferenceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial precision parameters for coordinate differences of
the manufactured field. Both the spatial step and scalar accuracy are
chosen from its already proved uniform six-derivative bound. -/

noncomputable section
namespace ContinuumCoulomb.MoserDifferenceBudget

theorem guard_bound : manufacturedFieldDerivativeConstant ≤ (guard:ℝ) := by
  have h := Nat.le_ceil manufacturedFieldDerivativeConstant
  unfold guard
  push_cast
  linarith

end ContinuumCoulomb.MoserDifferenceBudget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserNumericalBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single integer controls the speed and the joint time-space
Lipschitz constant for every manufactured field. It is fixed before the
input instance and can be hardcoded into the rational Euler program. -/

noncomputable section
namespace ContinuumCoulomb

 theorem exists_uniform_velocity_integer (rho : ℕ) (hrho : 0 < rho) :
    ∃ C : ℕ, 0 < C ∧ ∀ V : Position → ℝ, ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ)) →
      (∀ x, |manufacturedCharge V x| ≤ (rho:ℝ)/2) →
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x, ‖moserVelocity (rho:ℝ) V t x‖ ≤ C) ∧
      (∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x y,
        ‖moserVelocity (rho:ℝ) V s x-moserVelocity (rho:ℝ) V t y‖ ≤
          (C:ℝ)*(|s-t|+‖x-y‖)) := by
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  obtain ⟨A,hA,hAb⟩ := moserVelocity_family_derivative_bound hr
    (Nat.cast_nonneg MoserDifferenceBudget.guard)
  obtain ⟨C,hC⟩ := exists_nat_gt (max (1:ℝ) A)
  have hCp : 0 < C := by
    have he : (1:ℝ) < C := (le_max_left _ _).trans_lt hC
    exact_mod_cast (lt_trans zero_lt_one he)
  have hAC : A ≤ (C:ℝ) := ((le_max_right _ _).trans_lt hC).le
  refine ⟨C,hCp,?_⟩
  intro V hV hb hc
  let F : ℝ×Position → Position := fun p => moserVelocity (rho:ℝ) V p.1 p.2
  let S : Set (ℝ×Position) := Set.Icc (0:ℝ) 1 ×ˢ Set.univ
  have hdom : S ⊆ moserDomain (rho:ℝ) V := moserDomain_contains_time_slab hr V hc
  have hreg : ContDiffOn ℝ 4 F (moserDomain (rho:ℝ) V) :=
    moserVelocity_joint_C4 (rho:ℝ) V hV
  have hopen := moserDomain_isOpen (rho:ℝ) V hV
  have hd (p : ℝ×Position) (hp : p ∈ S) : ‖fderiv ℝ F p‖ ≤ (C:ℝ) := by
    have he := hAb V hV hb hc 1 (by norm_num) p.1 hp.1 p.2
    rw [norm_iteratedFDeriv_one] at he
    exact he.trans hAC
  have hDiff (p : ℝ×Position) (hp : p ∈ S) : DifferentiableAt ℝ F p :=
    (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num)
  constructor
  · intro t ht x
    have he := hAb V hV hb hc 0 (by norm_num) t ht x
    rw [norm_iteratedFDeriv_zero] at he
    exact he.trans hAC
  · intro s hs t ht x y
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hd
      ((convex_Icc (0:ℝ) 1).prod convex_univ)
      (show (t,y) ∈ S from ⟨ht,Set.mem_univ _⟩)
      (show (s,x) ∈ S from ⟨hs,Set.mem_univ _⟩)
    change ‖moserVelocity (rho:ℝ) V s x-moserVelocity (rho:ℝ) V t y‖ ≤ _ at he
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
    rw [Prod.norm_def]
    change max ‖s-t‖ ‖x-y‖ ≤ |s-t|+‖x-y‖
    rw [Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))

 theorem trajectory_coordinate_box (v : ℝ → Position → Position) (z : ℝ → Position)
    {M R : ℝ} (hM : 0 ≤ M)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hv : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hzero : ∀ a, |z 0 a| ≤ R) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ R+M := by
  intro t ht a
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hz hv
    (convex_Icc (0:ℝ) 1) (show (0:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) ht
  have htm : ‖t-(0:ℝ)‖ ≤ 1 := by rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1]; exact ht.2
  have hm : ‖z t-z 0‖ ≤ M := he.trans ((mul_le_mul_of_nonneg_left htm hM).trans_eq (mul_one _))
  have ha : |z t a-z 0 a| ≤ M := by
    have hc := PiLp.norm_apply_le (z t-z 0) a
    simpa only [Real.norm_eq_abs,PiLp.sub_apply] using hc.trans hm
  have htri := abs_add_le (z t a-z 0 a) (z 0 a)
  have hzid : z t a-z 0 a+z 0 a = z t a := by ring
  rw [hzid] at htri
  exact htri.trans (by simpa only [add_comm] using add_le_add ha (hzero a))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ResolventNumericalBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary quantitative bounds for the fixed polynomial schedule.
These estimates keep all mesh choices explicit. -/

noncomputable section
namespace ContinuumCoulomb.ResolventSchedule

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

end ContinuumCoulomb.ResolventSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalGaussNodes
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.decode_index _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.enumeration_first _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.enumeration_second _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.index_decode _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational initial nodes for the tensor Gauss rule on mesh `1/N`.
The only irrational constant is evaluated by the existing dyadic square-root
program; the error bound is uniform over the entire integer lattice. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.RationalGaussNodes
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)

theorem abscissa_error (P : ℕ) :
    |(abscissa P:ℝ)-gaussAbscissa| ≤ (2*((P:ℝ)+1))⁻¹ := by
  have he := RationalSquareRoot.value_error (2*(P+1)) (q := (1/3:ℚ)) (by norm_num)
  have hs : Real.sqrt ((1/3:ℚ):ℝ) = gaussAbscissa := by
    norm_num [gaussAbscissa,Real.sqrt_inv]
  rw [hs] at he
  apply he.trans
  have hn : 2*(P+1) ≤ 2^(2*(P+1)) := (ResolventSchedule.succ_le_two_pow _).trans' (by omega)
  have hr : 2*((P:ℝ)+1) ≤ (2:ℝ)^(2*(P+1)) := by exact_mod_cast hn
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem signed_error (P : ℕ) (b : Bool) :
    |(signed P b:ℝ)-gaussNode (if b then 1 else 0)| ≤ (2*((P:ℝ)+1))⁻¹ := by
  cases b
  · change |((-abscissa P:ℚ):ℝ)-(-gaussAbscissa)| ≤ _
    rw [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact abscissa_error P
  · change |(abscissa P:ℝ)-gaussAbscissa| ≤ _
    exact abscissa_error P

private theorem coordinate_error (P : ℕ) {N : ℕ} (hN : 0 < N) (k : ℤ) (b : Bool) :
    |((((k:ℚ)+signed P b/2)/N:ℚ):ℝ)-
      (N:ℝ)⁻¹*((k:ℝ)+gaussNode (if b then 1 else 0)/2)| ≤
      (1/(2*(N:ℝ)))*(2*((P:ℝ)+1))⁻¹ := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hid : ((((k:ℚ)+signed P b/2)/N:ℚ):ℝ)-
      (N:ℝ)⁻¹*((k:ℝ)+gaussNode (if b then 1 else 0)/2) =
      (1/(2*(N:ℝ)))*((signed P b:ℝ)-gaussNode (if b then 1 else 0)) := by
    push_cast
    ring
  rw [hid,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*(N:ℝ)))]
  exact mul_le_mul_of_nonneg_left (signed_error P b) (by positivity)

theorem approximation_error (P : ℕ) {N : ℕ} (hN : 0 < N) (k : Registers) (b : Signs) :
    ‖position (value P N k b)-gaussLatticePoint (N:ℝ)⁻¹ (index k b)‖ ≤ ((P:ℝ)+1)⁻¹ := by
  let d : ℝ := (1/(2*(N:ℝ)))*(2*((P:ℝ)+1))⁻¹
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hc (a : Fin 3) :
      |(position (value P N k b)-gaussLatticePoint (N:ℝ)⁻¹ (index k b)) a| ≤ |(0:Position) a|+d := by
    fin_cases a
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.1 b.1
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.2.1 b.2.1
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.2.2 b.2.2
  have he := EulerRegisters.norm_of_coordinate_error hd hc
  simp only [norm_zero,zero_add] at he
  apply he.trans
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hp : 0 < (P:ℝ)+1 := by positivity
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hid : 3*d = (3/(4*(N:ℝ)))/((P:ℝ)+1) := by
    dsimp [d]
    field_simp [hNp.ne',hp.ne']
    ring
  rw [hid,← one_div]
  apply div_le_div_of_nonneg_right _ hp.le
  apply (div_le_one (by positivity : (0:ℝ) < 4*(N:ℝ))).mpr
  nlinarith

/-- The initial-node error and the rational ODE solver error add after
transport by the actual common Lipschitz map. -/
theorem transported_error (G : Position → Position) {K : ℝ≥0} (hG : LipschitzWith K G)
    (P : ℕ) {N : ℕ} (hN : 0 < N) (k : Registers) (b : Signs)
    (out : Triple) {δ : ℝ}
    (he : ‖position out-G (position (value P N k b))‖ ≤ δ) :
    ‖position out-G (gaussLatticePoint (N:ℝ)⁻¹ (index k b))‖ ≤
      δ+(K:ℝ)*((P:ℝ)+1)⁻¹ := by
  have ht := hG.dist_le_mul (position (value P N k b))
    (gaussLatticePoint (N:ℝ)⁻¹ (index k b))
  rw [dist_eq_norm,dist_eq_norm] at ht
  have hh := ht.trans (mul_le_mul_of_nonneg_left (approximation_error P hN k b) K.coe_nonneg)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (G (position (value P N k b))) _).trans (add_le_add he hh)

end ContinuumCoulomb.RationalGaussNodes

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedEuler
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal clipped Euler iteration approximates the actual manufactured
Moser flow. Its step count and denominator are fixed polynomials in the
requested unary precision, uniformly over all valid input geometries. -/

noncomputable section
namespace ContinuumCoulomb.ManufacturedEuler
open CappedKernelProgram (Triple position)
open EulerRegisters

theorem approximation_error (rho U C P : ℕ) (hrho : 0 < rho) (hC : 0 < C)
    (hExp : Real.exp (U:ℝ) ≤ C) (hUC : (U:ℝ)*(1+(U:ℝ)) ≤ C)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (hcharge : ∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
      scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x,
      ‖moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t x‖ ≤ U)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x y,
      ‖moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) s x-
        moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t y‖ ≤
        (U:ℝ)*(|s-t|+‖x-y‖))
    (G : Position → ℝ → Position)
    (hG : IsUnitTimeFlow (moserVelocity (rho:ℝ)
      (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)))) G)
    (q : Triple) :
    ‖position (approximate rho U C P scale S (List.ofFn u) q)-G (position q) 1‖ ≤
      ((P:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  let N := steps C P
  let D := denominator C P
  let B := boxNumerator U D q
  let e : Environment := (N,((scale,S),List.ofFn u))
  let z := G (position q)
  have hN : 0 < N := steps_positive hC
  have hD : 0 < D := pow_pos hN _
  have hz0 : z 0 = position q := hG.1 _
  have hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (moserVelocity (rho:ℝ) V t (z t)) (Set.Icc (0:ℝ) 1) t := hG.2 _
  have hzbox : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ (B:ℝ)/(D:ℝ) := by
    have hh := trajectory_coordinate_box (moserVelocity (rho:ℝ) V) z
      (Nat.cast_nonneg U) hz (fun t ht => hbound t ht _) (fun a => by
        rw [hz0]
        exact inputRadius_bound q a)
    intro t ht a
    dsimp [B]
    rw [boxNumerator_ratio hD]
    exact (hh t ht a).trans (by linarith)
  have heval (n : ℕ) (hn : n < N) :
      ‖position (evaluate rho e ((n:ℚ)*(N:ℚ)⁻¹)
        (trajectory (evaluate rho) e N D B (round D B q) n))-
        moserVelocity (rho:ℝ) V ((n:ℝ)/N)
          (position (trajectory (evaluate rho) e N D B (round D B q) n))‖ ≤ ((N:ℝ)+1)⁻¹ := by
    have htime : (((n:ℚ)*(N:ℚ)⁻¹ : ℚ):ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      rw [Rat.cast_mul,Rat.cast_natCast,Rat.cast_inv,Rat.cast_natCast,← div_eq_mul_inv]
      constructor
      · positivity
      · exact (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hn.le)
    have hh := ManufacturedVelocityEvaluation.approximation_error rho N hrho hscale hS u hu
      hsep hc hcharge (t := (n:ℚ)*(N:ℚ)⁻¹) htime (trajectory (evaluate rho) e N D B (round D B q) n)
    simpa only [evaluate,e,V,Rat.cast_mul,Rat.cast_natCast,Rat.cast_inv,div_eq_mul_inv] using hh
  have he := trajectory_error (evaluate rho) e hN hD B (round D B q)
    (moserVelocity (rho:ℝ) V) z (Nat.cast_nonneg U) (Nat.cast_nonneg U)
    (show 0 ≤ ((N:ℝ)+1)⁻¹ by positivity) hz (fun t ht => hbound t ht _) hLip hzbox heval
  rw [hz0] at he
  have hinit := initial_round_error (C := U) hD q
  have hb : (‖position (point D (round D B q))-position q‖+((N:ℝ)+1)⁻¹+
      (U:ℝ)*(1+(U:ℝ))/(N:ℝ)+3*(N:ℝ)/(D:ℝ))*Real.exp (U:ℝ) ≤
      (3/(D:ℝ)+((N:ℝ)+1)⁻¹+(U:ℝ)*(1+(U:ℝ))/(N:ℝ)+
        3*(N:ℝ)/(D:ℝ))*Real.exp (U:ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (add_le_add (add_le_add (add_le_add hinit le_rfl) le_rfl) le_rfl)
      (Real.exp_pos _).le
  exact he.trans (hb.trans (schedule_budget hC hExp hUC))

/-- Fixed program constants work simultaneously for every valid manufactured
field. No oracle for a potential, derivative, or flow value is used. -/
theorem exists_uniform_constants (rho : ℕ) (hrho : 0 < rho) :
    ∃ U C : ℕ, 0 < U ∧ 0 < C ∧ ∀ (P : ℕ) (scale S : ℚ),
      (1:ℝ) ≤ scale → (1:ℝ) ≤ S → ∀ (m : ℕ) (u : Fin m → ℚ×ℚ),
      Function.Injective u →
      (∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
      (∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2) →
      ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i)))) G →
      ∀ q : Triple,
        ‖position (approximate rho U C P scale S (List.ofFn u) q)-G (position q) 1‖ ≤
          ((P:ℝ)+1)⁻¹ := by
  obtain ⟨U,hU,hUb⟩ := exists_uniform_velocity_integer rho hrho
  obtain ⟨C,hC⟩ := exists_nat_gt (max (Real.exp (U:ℝ)) ((U:ℝ)*(1+(U:ℝ))))
  have hCp : 0 < C := by
    have hp : (0:ℝ) < C := (Real.exp_pos _).trans ((le_max_left _ _).trans_lt hC)
    exact_mod_cast hp
  refine ⟨U,C,hU,hCp,?_⟩
  intro P scale S hs hS m u hu hsep hc hcharge G hG q
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)
  have hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ) := by
    intro k hk x
    exact (manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc hk x).trans MoserDifferenceBudget.guard_bound
  obtain ⟨hbound,hLip⟩ := hUb V hV hb hcharge
  exact approximation_error rho U C P hrho hCp ((le_max_left _ _).trans_lt hC).le
    ((le_max_right _ _).trans_lt hC).le hs hS u hu hsep hc hcharge hbound hLip G hG q

end ContinuumCoulomb.ManufacturedEuler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGauss
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational transport of Gauss nodes. A common polynomial precision
absorbs both the initial square-root error and the numerical flow error. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

theorem error_budget (K P : ℕ) :
    (1+(K:ℝ))*((precision K P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  have hP : 0 < (P:ℝ)+1 := by positivity
  have hK : 0 < (K:ℝ)+1 := by positivity
  have hT : (precision K P:ℝ) = 2*((K:ℝ)+1)*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  apply (mul_inv_le_iff₀ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)).mpr
  rw [hT]
  have he : ((P:ℝ)+1)⁻¹*(2*((K:ℝ)+1)*((P:ℝ)+1)+1) =
      2*((K:ℝ)+1)+((P:ℝ)+1)⁻¹ := by field_simp
  rw [he]
  linarith [inv_nonneg.mpr hP.le]

/-- This is an error-composition lemma. Its numerical-flow premise is
supplied below by the proved actual manufactured Euler construction. -/
theorem error_of_endpoint_error (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (k : Registers) (b : Signs)
    (G : Position → Position) {L : ℝ≥0} (hG : LipschitzWith L G) (hL : (L:ℝ) ≤ K)
    (hendpoint : ∀ q : Triple,
      ‖position (ManufacturedEuler.approximate rho U C (precision K P) scale S sites q)-G (position q)‖ ≤
        ((precision K P:ℝ)+1)⁻¹) :
    ‖position (value rho U C K P N scale S sites k b)-
      G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index k b))‖ ≤ ((P:ℝ)+1)⁻¹ := by
  have he := RationalGaussNodes.transported_error G hG (precision K P) hN k b
    (ManufacturedEuler.approximate rho U C (precision K P) scale S sites
      (RationalGaussNodes.value (precision K P) N k b))
    (hendpoint (RationalGaussNodes.value (precision K P) N k b))
  apply he.trans
  have hm := mul_le_mul_of_nonneg_right hL
    (inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg (precision K P)) zero_le_one))
  calc
    _ ≤ ((precision K P:ℝ)+1)⁻¹+(K:ℝ)*((precision K P:ℝ)+1)⁻¹ := add_le_add le_rfl hm
    _ = (1+(K:ℝ))*((precision K P:ℝ)+1)⁻¹ := by ring
    _ ≤ _ := error_budget K P

/-- The transformed-node approximation is uniform over all manufactured
fields and all their actual time-one maps. U and C are fixed beforehand. -/
theorem exists_uniform_constants (rho : ℕ) (hrho : 0 < rho) :
    ∃ U C : ℕ, 0 < U ∧ 0 < C ∧ ∀ (K P N : ℕ), 0 < N → ∀ (scale S : ℚ),
      (1:ℝ) ≤ scale → (1:ℝ) ≤ S → ∀ (m : ℕ) (u : Fin m → ℚ×ℚ),
      Function.Injective u →
      (∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
      (∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2) →
      ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i)))) G →
      ∀ L : ℝ≥0, LipschitzWith L (fun x => G x 1) → (L:ℝ) ≤ K →
      ∀ (k : Registers) (b : Signs),
        ‖position (value rho U C K P N scale S (List.ofFn u) k b)-
          G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index k b)) 1‖ ≤ ((P:ℝ)+1)⁻¹ := by
  obtain ⟨U,C,hU,hC,herror⟩ := ManufacturedEuler.exists_uniform_constants rho hrho
  refine ⟨U,C,hU,hC,?_⟩
  intro K P N hN scale S hs hS m u hu hsep hc hcharge G hG L hLip hL k b
  exact error_of_endpoint_error rho U C K P hN scale S (List.ofFn u) k b
    (fun x => G x 1) hLip hL
    (herror (precision K P) scale S hs hS m u hu hsep hc hcharge G hG)

end ContinuumCoulomb.TransformedGauss

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGaussSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinctness of the numerical transported nodes. The input labels use
the same integer cells and eight sign choices as the exact Gauss grid. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

theorem value_injective {I : Type*} (labels : I → Registers×Signs)
    (hlabels : Function.Injective labels) (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (G : Position → Position)
    {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ i,
      ‖position (value rho U C K P N scale S sites (labels i).1 (labels i).2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))‖ ≤
          ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3) :
    Function.Injective (fun i => value rho U C K P N scale S sites (labels i).1 (labels i).2) := by
  intro i j hij
  by_contra hne
  have hindices : RationalGaussNodes.index (labels i).1 (labels i).2 ≠
      RationalGaussNodes.index (labels j).1 (labels j).2 := by
    intro he
    exact hne (hlabels (index_injective he))
  have hbase := gaussLatticePoint_separation
    (show 0 < (N:ℝ)⁻¹ by positivity) _ _ hindices
  have htrans := hG.le_mul_dist
    (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))
    (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))
  simp only [dist_eq_norm] at htrans
  have hi := herror i
  have hj := herror j
  have he := congrArg position hij
  rw [he] at hi
  have ht : ‖G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))-
      G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))‖ ≤
        2*((P:ℝ)+1)⁻¹ := by
    calc
      _ ≤ ‖G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))-
          position (value rho U C K P N scale S sites (labels i).1 (labels i).2)‖+
          ‖position (value rho U C K P N scale S sites (labels i).1 (labels i).2)-
          G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by rw [norm_sub_rev _ (position _),he]; linarith
  have hmul := mul_le_mul_of_nonneg_left ht J.coe_nonneg
  nlinarith

end ContinuumCoulomb.TransformedGauss

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGaussList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same certified node program is applied to the whole finite list of
Gauss labels. It preserves the nucleus count and, at the proved precision,
pairwise distinctness. -/

open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)
open EulerRegisters (Registers registersCode)
open RationalGaussNodes (Signs signsCode)

theorem nodes_length (rho U C K : ℕ) (x : Environment×List Label) :
    (nodes rho U C K x).length = x.2.length := by simp only [nodes,List.length_map]

theorem nodes_nodup (rho U C K : ℕ) (P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (labels : List Label) (hnodup : labels.Nodup)
    (G : Position → Position) {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ l : Label,
      ‖position (value rho U C K P N scale S sites l.1 l.2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤ ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3) :
    (nodes rho U C K (((P,N),((scale,S),sites)),labels)).Nodup := by
  exact hnodup.map (value_injective id Function.injective_id rho U C K P hN scale S sites G
    hG herror hprecision)

end ContinuumCoulomb.TransformedGauss

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearCoordinateOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Serialization of computed rational triples into the actual nuclear
position codec. The canonical numerator and positive denominator are kept
exactly; no real-coordinate oracle is used. -/

namespace ContinuumCoulomb.NuclearCoordinateOutput
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

theorem rational_value (q : ℚ) : (rational q).value = q := Rat.num_div_den q
theorem position_value (q : Triple) : (position q).value = ![q.1,q.2.1,q.2.2] := by
  simp only [position,BinaryPosition.value,rational_value]
theorem position_valid (q : Triple) : (position q).Valid :=
  ⟨q.1.den_pos,q.2.1.den_pos,q.2.2.den_pos⟩
theorem position_value_injective : Function.Injective (fun q => (position q).value) := by
  intro q r h
  have he := h
  change (position q).value = (position r).value at he
  rw [position_value,position_value] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem real_position (q : Triple) : realPosition (position q).value = CappedKernelProgram.position q := by
  rw [position_value]
  ext i
  fin_cases i <;> rfl

theorem positions_length (qs : List Triple) : (positions qs).length = qs.length := by
  simp only [positions,List.length_map]
theorem positions_valid (qs : List Triple) {p : BinaryPosition} (hp : p ∈ positions qs) : p.Valid := by
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact position_valid q

end ContinuumCoulomb.NuclearCoordinateOutput

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_FormStability
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the full variational bottom under nuclear rounding

The Hardy estimate is combined with coercivity of the actual Coulomb form.
Consequently rational rounding is controlled on the unrestricted fermionic
ground-energy infimum, without assuming a minimizing eigenvector or an
independent kinetic-energy bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Keeping half of the kinetic form gives a uniform coercive lower bound. -/
theorem coulomb_form_coercive {m n : ℕ} (S : Coulomb.Nuclei m)
    (state : Coulomb.H1Vector n) :
    Coulomb.kinetic state / 2 -
        4 * (n : ℝ) * Coulomb.totalCharge S ^ 2 * Coulomb.mass state ≤
      Coulomb.form S state := by
  let eta : ℝ := 1 / (16 * Coulomb.totalCharge S)
  have hZ := Coulomb.totalCharge_pos S
  have heta : 0 < eta := by dsimp [eta]; positivity
  have h := Coulomb.nuclearEnergy_bound S state heta
  have hfactor : 8 * eta * Coulomb.totalCharge S = 1 / 2 := by
    dsimp [eta]
    field_simp
    norm_num
  have hconstant : (n : ℝ) * Coulomb.totalCharge S / (4 * eta) =
      4 * (n : ℝ) * Coulomb.totalCharge S ^ 2 := by
    dsimp [eta]
    field_simp
    ring
  rw [hfactor, hconstant] at h
  have hpair := Coulomb.pairEnergy_nonneg state
  unfold Coulomb.form
  linarith

/-- The rounding estimate includes arbitrary positive nuclear charges, with
their total mass rather than their maximum charge in the error budget. -/
theorem coulomb_form_position_error {m n : ℕ} (S T : Coulomb.Nuclei m)
    (state : Coulomb.H1Vector n) {delta : ℝ}
    (hcharge : S.charge = T.charge)
    (hmove : ∀ a, ‖S.position a - T.position a‖ ≤ delta) :
    |Coulomb.form S state - Coulomb.form T state| ≤
      16 * delta * Coulomb.totalCharge S * Coulomb.kinetic state := by
  let I := fun (R : Coulomb.Nuclei m) (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) =>
    ∫ x, Coulomb.coulombKernel (Coulomb.position x i - R.position a) *
      ‖state.value s x‖ ^ 2
  let G := fun (s : Coulomb.Spins n) (i : Fin n) =>
    ∑ k : Fin 3, ∫ x, ‖state.gradient s (i, k) x‖ ^ 2
  have hG : ∀ s i, 0 ≤ G s i := by
    intro s i
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hI (R : Coulomb.Nuclei m) (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - R.position a) *
        ‖state.value s x‖ ^ 2) :=
    (state.nuclear_coulomb_integrable_bound s i (R.position a)
      (by norm_num : (0 : ℝ) < 1)).1
  have hdiff (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      I S s i a - I T s i a = ∫ x,
        (Coulomb.coulombKernel (Coulomb.position x i - S.position a) -
          Coulomb.coulombKernel (Coulomb.position x i - T.position a)) *
            ‖state.value s x‖ ^ 2 := by
    simp only [sub_mul, integral_sub (hI S s i a) (hI T s i a), I]
  have hterm (s : Coulomb.Spins n) (i : Fin n) (a : Fin m) :
      |S.charge a * (I S s i a - I T s i a)| ≤
        S.charge a * (8 * delta * G s i) := by
    have hz : 0 ≤ S.charge a := (by norm_num : (0 : ℝ) ≤ 1).trans (S.charge_ge_one a)
    rw [abs_mul, abs_of_nonneg hz, hdiff]
    apply mul_le_mul_of_nonneg_left _ hz
    exact (nuclear_position_rounding_bound state s i (S.position a) (T.position a)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmove a) (by norm_num)) (hG s i))
  have hnuclear : Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state =
      ∑ s, ∑ i, ∑ a, S.charge a * (I S s i a - I T s i a) := by
    rw [Coulomb.nuclearEnergy_eq_sum, Coulomb.nuclearEnergy_eq_sum, ← hcharge]
    simp only [← Finset.sum_sub_distrib, ← mul_sub, I]
  have hsum : |Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state| ≤
      ∑ s, ∑ i, ∑ a, S.charge a * (8 * delta * G s i) := by
    rw [hnuclear]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro s _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun a _ => hterm s i a)
  have htotal : (∑ s, ∑ i, ∑ a, S.charge a * (8 * delta * G s i)) =
      16 * delta * Coulomb.totalCharge S * Coulomb.kinetic state := by
    simp only [← Finset.sum_mul]
    unfold G Coulomb.kinetic Coulomb.totalCharge
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    ring
  have heq : Coulomb.form S state - Coulomb.form T state =
      -(Coulomb.nuclearEnergy S state - Coulomb.nuclearEnergy T state) := by
    unfold Coulomb.form
    ring
  rw [heq, abs_neg]
  exact hsum.trans_eq htotal

theorem formGroundEnergy_le_trial {m n : ℕ} (S : Coulomb.Nuclei m)
    (state : FormState n) (hnorm : normSq state = 1) :
    formGroundEnergy S n ≤ (Coulomb.form S state.val : EReal) :=
  sInf_le ⟨state, hnorm, rfl⟩

theorem formGroundEnergy_lower_of_forall {m n : ℕ} (S : Coulomb.Nuclei m) (a : ℝ)
    (ha : ∀ state : FormState n, normSq state = 1 → a ≤ Coulomb.form S state.val) :
    (a : EReal) ≤ formGroundEnergy S n := by
  apply le_sInf
  rintro e ⟨state, hnorm, rfl⟩
  exact EReal.coe_le_coe (ha state hnorm)

theorem formGroundEnergy_finite {m n : ℕ} (S : Coulomb.Nuclei m)
    (trial : FormState n) (htrial : normSq trial = 1) :
    formGroundEnergy S n ≠ ⊤ ∧ formGroundEnergy S n ≠ ⊥ := by
  constructor
  · exact ne_of_lt ((formGroundEnergy_le_trial S trial htrial).trans_lt (EReal.coe_lt_top _))
  · apply ne_of_gt
    apply (EReal.bot_lt_coe (-(2 * (n : ℝ) * Coulomb.totalCharge S ^ 2))).trans_le
    apply formGroundEnergy_lower_of_forall
    intro state hnorm
    have h := Coulomb.form_lower_bound S state.val
    change _ * normSq state ≤ _ at h
    simpa only [hnorm, mul_one] using h

/-- A quantitative change of the full bottom under nuclear movement. The
single normalized trial proves both bottoms finite; it need not minimize.
The factor in parentheses is automatically nonnegative by coercivity. -/
theorem formGroundEnergy_position_stability {m n : ℕ} (S T : Coulomb.Nuclei m)
    (trial : FormState n) (htrial : normSq trial = 1) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hcharge : S.charge = T.charge)
    (hmove : ∀ a, ‖S.position a - T.position a‖ ≤ delta)
    (hsmall : 32 * delta * Coulomb.totalCharge S ≤ 1) :
    |(formGroundEnergy T n).toReal - (formGroundEnergy S n).toReal| ≤
      32 * delta * Coulomb.totalCharge S *
        ((formGroundEnergy S n).toReal + 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2) := by
  let theta : ℝ := 16 * delta * Coulomb.totalCharge S
  let C : ℝ := 4 * (n : ℝ) * Coulomb.totalCharge S ^ 2
  let E : ℝ := (formGroundEnergy S n).toReal
  let F : ℝ := (formGroundEnergy T n).toReal
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact mul_nonneg (mul_nonneg (by norm_num) hdelta) (Coulomb.totalCharge_pos S).le
  have hslower : 0 ≤ 1 - 2 * theta := by dsimp [theta]; nlinarith
  have hsupper : 0 < 1 + 2 * theta := by linarith
  have hEcoe : (E : EReal) = formGroundEnergy S n :=
    EReal.coe_toReal (formGroundEnergy_finite S trial htrial).1
      (formGroundEnergy_finite S trial htrial).2
  have hFcoe : (F : EReal) = formGroundEnergy T n :=
    EReal.coe_toReal (formGroundEnergy_finite T trial htrial).1
      (formGroundEnergy_finite T trial htrial).2
  have hEtrial (u : FormState n) (hu : normSq u = 1) : E ≤ Coulomb.form S u.val := by
    apply EReal.coe_le_coe_iff.mp
    rw [hEcoe]
    exact formGroundEnergy_le_trial S u hu
  have hFtrial (u : FormState n) (hu : normSq u = 1) : F ≤ Coulomb.form T u.val := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    exact formGroundEnergy_le_trial T u hu
  have hpoint (u : FormState n) (hu : normSq u = 1) :
      (1 - 2 * theta) * Coulomb.form S u.val - 2 * theta * C ≤ Coulomb.form T u.val ∧
      Coulomb.form T u.val ≤ (1 + 2 * theta) * Coulomb.form S u.val + 2 * theta * C := by
    have hcoercive := coulomb_form_coercive S u.val
    change Coulomb.kinetic u.val / 2 - C * normSq u ≤ Coulomb.form S u.val at hcoercive
    rw [hu, mul_one] at hcoercive
    have hk := mul_le_mul_of_nonneg_left hcoercive (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htheta)
    have he := coulomb_form_position_error S T u.val hcharge hmove
    change |Coulomb.form S u.val - Coulomb.form T u.val| ≤ theta * Coulomb.kinetic u.val at he
    obtain ⟨hl, hr⟩ := abs_le.mp he
    constructor <;> nlinarith
  have hlower : (1 - 2 * theta) * E - 2 * theta * C ≤ F := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    apply formGroundEnergy_lower_of_forall
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hEtrial u hu) hslower
    have hp := (hpoint u hu).1
    linarith
  have hupper : F ≤ (1 + 2 * theta) * E + 2 * theta * C := by
    have haux : (F - 2 * theta * C) / (1 + 2 * theta) ≤ E := by
      apply EReal.coe_le_coe_iff.mp
      rw [hEcoe]
      apply formGroundEnergy_lower_of_forall
      intro u hu
      apply (div_le_iff₀ hsupper).2
      have h := hFtrial u hu
      have hp := (hpoint u hu).2
      nlinarith
    have h := (div_le_iff₀ hsupper).mp haux
    nlinarith
  change |F - E| ≤ _
  have hbound : |F - E| ≤ 2 * theta * (E + C) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [theta, E, C]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GroundRoundingInterval
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding a cloud using an already proved two-sided ground-energy
interval. No minimizing eigenvector or independent kinetic bound is needed. -/

noncomputable section
namespace ContinuumCoulomb

theorem formGroundEnergy_exists_trial_of_upper {m n : ℕ} (S : Coulomb.Nuclei m)
    {C : ℝ} (hC : formGroundEnergy S n ≤ (C:EReal)) :
    ∃ trial : FormState n, normSq trial = 1 := by
  have htop : formGroundEnergy S n < ⊤ := hC.trans_lt (EReal.coe_lt_top C)
  obtain ⟨e,⟨trial,ht,_⟩,_⟩ := sInf_lt_iff.mp htop
  exact ⟨trial,ht⟩

theorem formGroundEnergy_position_stability_of_upper {m n : ℕ} (S T : Coulomb.Nuclei m)
    {C δ : ℝ} (hC : formGroundEnergy S n ≤ (C:EReal))
    (hδ : 0 ≤ δ) (hcharge : S.charge=T.charge)
    (hmove : ∀ a, ‖S.position a-T.position a‖ ≤ δ)
    (hsmall : 32*δ*Coulomb.totalCharge S ≤ 1) :
    |(formGroundEnergy T n).toReal-(formGroundEnergy S n).toReal| ≤
      32*δ*Coulomb.totalCharge S*(C+4*(n:ℝ)*Coulomb.totalCharge S^2) := by
  obtain ⟨trial,ht⟩ := formGroundEnergy_exists_trial_of_upper S hC
  have hf := formGroundEnergy_finite S trial ht
  have hCr : (formGroundEnergy S n).toReal ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hf.1 hf.2] using hC
  exact (formGroundEnergy_position_stability S T trial ht hδ hcharge hmove hsmall).trans
    (mul_le_mul_of_nonneg_left (add_le_add hCr le_rfl)
      (by exact mul_nonneg (mul_nonneg (by norm_num) hδ) (Coulomb.totalCharge_pos S).le))

theorem formGroundEnergy_rounding_interval {m n : ℕ} (S T : Coulomb.Nuclei m)
    {center error δ roundError : ℝ}
    (hlower : ((center-error:ℝ):EReal) ≤ formGroundEnergy S n)
    (hupper : formGroundEnergy S n ≤ ((center+error:ℝ):EReal))
    (hδ : 0 ≤ δ) (hcharge : S.charge=T.charge)
    (hmove : ∀ a, ‖S.position a-T.position a‖ ≤ δ)
    (hsmall : 32*δ*Coulomb.totalCharge S ≤ 1)
    (hbudget : 32*δ*Coulomb.totalCharge S*
      (center+error+4*(n:ℝ)*Coulomb.totalCharge S^2) ≤ roundError) :
    ((center-error-roundError:ℝ):EReal) ≤ formGroundEnergy T n ∧
      formGroundEnergy T n ≤ ((center+error+roundError:ℝ):EReal) := by
  obtain ⟨trial,ht⟩ := formGroundEnergy_exists_trial_of_upper S hupper
  have hfS := formGroundEnergy_finite S trial ht
  have hfT := formGroundEnergy_finite T trial ht
  have hslo : center-error ≤ (formGroundEnergy S n).toReal := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hfS.1 hfS.2] using hlower
  have hshi : (formGroundEnergy S n).toReal ≤ center+error := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hfS.1 hfS.2] using hupper
  have hdiff := (formGroundEnergy_position_stability_of_upper S T hupper hδ hcharge hmove hsmall).trans hbudget
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hdiff
  constructor
  · rw [← EReal.coe_toReal hfT.1 hfT.2]
    exact EReal.coe_le_coe_iff.mpr (by linarith only [hslo,hdlo])
  · rw [← EReal.coe_toReal hfT.1 hfT.2]
    exact EReal.coe_le_coe_iff.mpr (by linarith only [hshi,hdhi])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_RoundingPolynomialBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial coordinate precision controls the full Coulomb ground
energy, including the total charge of the large finite nuclear grid. -/

noncomputable section
namespace ContinuumCoulomb

theorem inverse_power_product_le {N : ℝ} (hN : 1 ≤ N)
    {a b p : ℕ} (hab : b+p ≤ a) : (N^a)⁻¹*N^b ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [inv_mul_eq_div,inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul,← pow_add]
  exact pow_le_pow_right₀ hN (by omega)

theorem rounding_polynomial_budget {N Q M δ E : ℝ} (hN : 2 ≤ N)
    {r q c p a : ℕ} (ha : c+3*q+r+p+8 ≤ a)
    (hQ : 0 ≤ Q) (hQN : Q ≤ N^q) (_hM : 0 ≤ M) (hMN : M ≤ N^r)
    (hE : E ≤ N^c) (hδ : 0 ≤ δ) (hδN : δ ≤ (N^a)⁻¹) :
    32*δ*Q ≤ 1 ∧ 32*δ*Q*(E+4*M*Q^2) ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let b := c+r+3*q
  have hMQ : M*Q^2 ≤ N^(r+2*q) := by
    calc
      _ ≤ N^r*(N^q)^2 := mul_le_mul hMN (pow_le_pow_left₀ hQ hQN 2) (sq_nonneg Q) (by positivity)
      _ = _ := by rw [show 2*q=q*2 by omega,pow_add,pow_mul]
  have hterms : E+4*M*Q^2 ≤ 5*N^(c+r+2*q) := by
    have hEc := hE.trans (pow_le_pow_right₀ hN1 (by omega : c ≤ c+r+2*q))
    have hMc := hMQ.trans (pow_le_pow_right₀ hN1 (by omega : r+2*q ≤ c+r+2*q))
    linarith only [hEc,hMc]
  have hnum : 32*Q*(E+4*M*Q^2) ≤ 160*N^b := by
    calc
      _ ≤ 32*Q*(5*N^(c+r+2*q)) := mul_le_mul_of_nonneg_left hterms (by positivity)
      _ ≤ 32*N^q*(5*N^(c+r+2*q)) := by gcongr
      _ = _ := by dsimp [b]; rw [pow_add,pow_add,pow_add]; ring
  have h160 : (160:ℝ) ≤ N^8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 8
    norm_num at hh
    linarith
  have hnum' : 160*N^b ≤ N^(b+8) := by
    rw [pow_add N b 8]
    nlinarith [pow_nonneg hN0.le b]
  constructor
  · have h32 : 32*Q ≤ N^(b+8) := by
      have hQb : Q ≤ N^b := hQN.trans (pow_le_pow_right₀ hN1 (by dsimp [b]; omega))
      have h32' : (32:ℝ) ≤ N^8 := (by norm_num : (32:ℝ) ≤ 160).trans h160
      rw [pow_add N b 8]
      nlinarith [mul_le_mul h32' hQb hQ (pow_nonneg hN0.le 8)]
    calc
      _ = δ*(32*Q) := by ring
      _ ≤ (N^a)⁻¹*N^(b+8) := mul_le_mul hδN h32 (by positivity) (by positivity)
      _ ≤ 1 := by simpa only [pow_zero,inv_one] using inverse_power_product_le hN1 (a := a) (b := b+8) (p := 0) (by dsimp [b]; omega)
  · calc
      _ = δ*(32*Q*(E+4*M*Q^2)) := by ring
      _ ≤ δ*(160*N^b) := mul_le_mul_of_nonneg_left hnum hδ
      _ ≤ (N^a)⁻¹*N^(b+8) := mul_le_mul hδN hnum' (by positivity) (by positivity)
      _ ≤ _ := inverse_power_product_le hN1 (by dsimp [b]; omega)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabBoxSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational slab dimensions with separate unary magnitude bounds. This
covers exactly the half-cell boundary of the odd centered grid. -/

noncomputable section
namespace ContinuumCoulomb.SlabBoxSchedule

theorem centeredWidth_real (q N : ℕ) :
    (centeredWidth q N:ℝ) = ((q:ℝ)+1/2)*(N:ℝ)⁻¹ := by
  simp [centeredWidth,div_eq_mul_inv]

theorem centeredWidth_product (W N : ℕ) (hN : 0 < N) :
    centeredWidth (W*N) N = (W:ℚ)+1/(2*(N:ℚ)) := by
  have hn : (N:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [centeredWidth,Nat.cast_mul]
  field_simp [hn]

theorem centeredWidth_product_bounds (W N : ℕ) (hW : 0 < W) (hN : 0 < N) :
    (W:ℚ) ≤ centeredWidth (W*N) N ∧ centeredWidth (W*N) N ≤ 2*(W:ℚ) := by
  rw [centeredWidth_product W N hN]
  have hn : (1:ℚ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hw : (1:ℚ) ≤ W := by exact_mod_cast (Nat.succ_le_iff.mpr hW)
  have he : 0 ≤ 1/(2*(N:ℚ)) := by positivity
  have he' : 1/(2*(N:ℚ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor <;> linarith

end ContinuumCoulomb.SlabBoxSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGaussEquiv
attribute [-instance] _root_.OAI.ContinuumCoulomb.centeredGridIndices_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The emitted centered label list is exactly the finite cell-by-eight-node
grid used by the Coulomb quadrature theorems. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CenteredGaussLabels

theorem sum_enumeration {A : Type*} [AddCommMonoid A] (r : Radii) (f : GaussLatticeIndex → A) :
    (∑ a : Fin (labels r).length,
      f (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2)) =
    ∑ k : {k // k ∈ centeredGridIndices (radiiVector r)}, ∑ v : Fin 3 → Fin 2, f (k.val,v) := by
  have he := (enumerationEquiv r).sum_comp (fun kv : Grid r => f (kv.1.val,kv.2))
  simpa only [Fintype.sum_prod_type,enumeration_first,enumeration_second] using he

end ContinuumCoulomb.CenteredGaussLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ShiftedHubbardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Hubbard energy, including its off-site shift and
form error, has polynomial size. No occupation-space dimension enters. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedOffsiteCoulomb_nonnegative {m : ℕ} (freq : ℝ)
    (u : Fin m → PlanarPosition) (i j : Fin m) : 0 ≤ localizedOffsiteCoulomb freq u i j := by
  unfold localizedOffsiteCoulomb
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GridGroundUpper
attribute [-simp] _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.decode_index _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.enumeration_first _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.enumeration_second _root_.OAI.ContinuumCoulomb.CenteredGaussLabels.index_decode _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial size bounds used to choose the precision of the literal
nuclear-coordinate program. The negative slab offset is retained. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem shifted_hubbard_upper {Edge : Type*} [Fintype Edge]
    {freq : ℝ} (hf : 0 < freq) (m : ℕ) (u : Fin (m+1) → PlanarPosition)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j) ≤
      (m+1:ℝ)/2*localizedPotentialBound freq+4*(∑ e, |t e|) := by
  have hU0 := localizedCoulombProfile_nonnegative freq 0
  have hU : localizedCoulombProfile freq 0 ≤ localizedPotentialBound freq := by
    simpa only [localizedCoulombCoeff_distance,sub_self,norm_zero] using
      localizedCoulombCoeff_le hf (0 : PlanarPosition) 0
  have h := (le_abs_self _).trans (hubbardFermionBottom_abs_bound m
    (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t)
  simp_rw [abs_of_nonneg hU0,abs_of_nonneg (localizedOffsiteCoulomb_nonnegative freq u _ _)] at h
  have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ (m+1:ℝ)/2 by positivity)
  linarith only [h,hmul]

theorem exists_grid_ground_upper_exponent {freq rho a : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r v p k : ℕ, ∀ N H S : ℝ, 2 ≤ N →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v →
    let scale := a*(N^k)^30
    scale^2*(m+1:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))+
      scale*(N^p)⁻¹ ≤ N^(q+60*k+r+v) := by
  let E0 := (-1/2:ℝ)+freq/2
  let C := a^2*E0+a*localizedPotentialBound freq/2+5*a
  have hE0 : 0 ≤ E0 := by dsimp [E0]; linarith
  have hP := localizedPotentialBound_nonnegative freq
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) C
  refine ⟨q,by omega,?_⟩
  intro r v p k N H S hN Edge _ m u left right t hm ht
  dsimp only
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let Z := N^(60*k+r+v)
  have hfirst : (a*(N^k)^30)^2*(m+1:ℝ)*E0 ≤ (a^2*E0)*Z := by
    calc
      _ = (a^2*E0)*((N^k)^60*(m+1:ℝ)) := by ring
      _ ≤ (a^2*E0)*((N^k)^60*N^r) := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hMr : (N^k)^30*(m+1:ℝ) ≤ Z := by
    calc
      _ ≤ (N^k)^30*N^r := by gcongr
      _ ≤ _ := by
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hTr : (N^k)^30*(∑ e, |t e|) ≤ Z := by
    calc
      _ ≤ (N^k)^30*N^v := by gcongr
      _ ≤ _ := by
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hLast : (N^k)^30*(N^p)⁻¹ ≤ Z := by
    calc
      _ ≤ (N^k)^30*1 := mul_le_mul_of_nonneg_left
        (inv_le_one_of_one_le₀ (one_le_pow₀ hN1)) (by positivity)
      _ ≤ _ := by dsimp [Z]; rw [mul_one,← pow_mul]; exact pow_le_pow_right₀ hN1 (by omega)
  have hneg := slabPotential_nonpositive hrho H S 0
  have hslab := mul_le_mul_of_nonneg_left (show slabPotential rho H S 0+E0 ≤ E0 by linarith)
    (show 0 ≤ (a*(N^k)^30)^2*(m+1:ℝ) by positivity)
  have hhub := mul_le_mul_of_nonneg_left (shifted_hubbard_upper hfp m u left right t)
    (show 0 ≤ a*(N^k)^30 by positivity)
  have hmid := mul_le_mul_of_nonneg_left hMr (show 0 ≤ a*localizedPotentialBound freq/2 by positivity)
  have ht' := mul_le_mul_of_nonneg_left hTr (show 0 ≤ 4*a by positivity)
  have hend := mul_le_mul_of_nonneg_left hLast ha.le
  calc
    _ ≤ C*Z := by dsimp only [C,E0] at *; nlinarith only [hslab,hhub,hfirst,hmid,ht',hend]
    _ ≤ N^q*Z := mul_le_mul_of_nonneg_right (hconst N hN).2 (by dsimp [Z]; positivity)
    _ = _ := by dsimp [Z]; rw [← pow_add]; congr 1; omega

theorem centered_grid_count_power {N : ℝ} (hN : 2 ≤ N) (k : ℕ)
    {r : CenteredGaussLabels.Radii}
    (h0 : (r.1:ℝ) ≤ N^(60*k)) (h1 : (r.2.1:ℝ) ≤ N^(60*k))
    (h2 : (r.2.2:ℝ) ≤ N^(15*k)) :
    ((CenteredGaussLabels.labels r).length:ℝ) ≤ N^(135*k+8) := by
  have hN1 : 1 ≤ N := by linarith
  have hp60 : 1 ≤ N^(60*k) := one_le_pow₀ hN1
  have hp15 : 1 ≤ N^(15*k) := one_le_pow₀ hN1
  have ha : 2*(r.1:ℝ)+1 ≤ 3*N^(60*k) := by linarith
  have hb : 2*(r.2.1:ℝ)+1 ≤ 3*N^(60*k) := by linarith
  have hc : 2*(r.2.2:ℝ)+1 ≤ 3*N^(15*k) := by linarith
  have h216 : (216:ℝ) ≤ N^8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 8
    norm_num at h
    linarith
  rw [CenteredGaussLabels.labels_length]
  push_cast
  calc
    _ ≤ 8*((3*N^(60*k))*(3*N^(60*k))*(3*N^(15*k))) := by gcongr
    _ = 216*N^(135*k) := by rw [show 135*k=(60*k+60*k)+15*k by omega,pow_add,pow_add]; ring
    _ ≤ _ := by rw [pow_add N (135*k) 8]; nlinarith [pow_nonneg (by linarith : 0 ≤ N) (135*k)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GridNodePrecision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial precision for the emitted nodes: separation and the
full-ground rounding budget account for all nuclei in the centered box. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

theorem exists_grid_node_separation_offset (J : ℝ≥0) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ k a : ℕ, q+10*k ≤ a →
    ∀ (N : ℝ) (P : ℕ), 2 ≤ N → N^a ≤ (P:ℝ) →
      2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (1/(N^k)^10)/3 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds
    (by norm_num : (0:ℝ)<1) (6*(J:ℝ))
  refine ⟨q,by omega,fun k a ha N P hN hP => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hmul : 6*(J:ℝ)*(N^k)^10 < (P:ℝ)+1 := by
    calc
      _ ≤ N^q*(N^k)^10 := mul_le_mul_of_nonneg_right (hbound N hN).2 (by positivity)
      _ = N^(q+10*k) := by rw [pow_add,← pow_mul]; congr 2; omega
      _ ≤ N^a := pow_le_pow_right₀ hN1 ha
      _ < _ := by linarith only [hP]
  rw [← div_eq_mul_inv,div_div]
  apply (div_lt_div_iff₀ (by positivity) (by positivity : 0 < (N^k)^10*3)).mpr
  nlinarith only [hmul]

theorem grid_node_rounding_budget {N scale Q M E : ℝ} (hN : 2 ≤ N) (hs : 1 ≤ scale)
    {q r v p k a P : ℕ} (ha : q+465*k+2*r+v+p+32 ≤ a) (hP : N^a ≤ (P:ℝ))
    (hQ : 0 ≤ Q) (hQN : Q ≤ N^(135*k+8)) (hM : 0 ≤ M) (hMN : M ≤ N^r)
    (hE : E ≤ N^(q+60*k+r+v)) :
    32*(scale⁻¹*((P:ℝ)+1)⁻¹)*Q ≤ 1 ∧
      32*(scale⁻¹*((P:ℝ)+1)⁻¹)*Q*(E+4*M*Q^2) ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hs0 : 0 < scale := lt_of_lt_of_le zero_lt_one hs
  apply rounding_polynomial_budget hN (a := a) (c := q+60*k+r+v)
    (q := 135*k+8) (r := r) (p := p) (by omega) hQ hQN hM hMN hE (by positivity)
  calc
    _ ≤ 1*((P:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hs) (by positivity)
    _ ≤ (N^a)⁻¹ := by
      rw [one_mul]
      exact inv_anti₀ (pow_pos hN0 a) (by linarith only [hP])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GridNuclei
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transported Gauss cloud is an actual collection of distinct unit
nuclei. Its physical form has exactly the slab-origin energy offset. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem gridNuclei_attraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h) (y : Position) :
    Coulomb.attraction (gridNuclei index hi G hG hh) y =
      ∑ a : ι × (Fin 3 → Fin 2),
        Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a))) := by
  simp only [Coulomb.attraction,gridNuclei,one_mul]
  exact (Fintype.equivFin (ι × (Fin 3 → Fin 2))).symm.sum_comp
    (fun a : ι × (Fin 3 → Fin 2) =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFrequency
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency evaluated by the literal programs satisfies exactly the
oscillator/slab relation and lies in the uniform spectral-gap regime. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_frequency_ge_one {rho : ℕ} (hrho : 0 < rho) :
    1 ≤ GaussianFrequency.frequency rho := by
  have hr : (1:ℝ) ≤ rho := by exact_mod_cast Nat.succ_le_iff.mpr hrho
  have hp : (1:ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  unfold GaussianFrequency.frequency
  apply Real.le_sqrt_of_sq_le
  simpa only [one_mul,one_pow] using mul_le_mul hp hr (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 4*Real.pi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedScaleThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical scale lies in the domain required by the numerical field
program after a fixed, input-independent exponent threshold. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_manufactured_scale_threshold {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ k : ℕ, q ≤ k → ∀ N : ℝ, 2 ≤ N → 1 ≤ a*(N^k)^30 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds ha 1
  refine ⟨q,by omega,fun k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hinv : 1/(N^k)^30 ≤ a := by
    calc
      _ ≤ (N^q)⁻¹ := by
        rw [one_div]
        apply inv_anti₀ (by positivity)
        rw [← pow_mul]
        exact pow_le_pow_right₀ hN1 (by omega)
      _ ≤ _ := (hbound N hN).1
  exact (div_le_iff₀ (by positivity : 0 < (N^k)^30)).mp hinv

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EnumeratedGridNuclei
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered label list and the analytic finite grid describe the same
nuclear cloud, including after physical dilation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem formGroundEnergy_eq_of_attraction {m l : ℕ} (S : Coulomb.Nuclei m)
    (T : Coulomb.Nuclei l) (h : ∀ x, Coulomb.attraction S x=Coulomb.attraction T x) (n : ℕ) :
    formGroundEnergy S n=formGroundEnergy T n := by
  have he (w : Coulomb.H1Vector n) : Coulomb.form S w=Coulomb.form T w := by
    unfold Coulomb.form Coulomb.nuclearEnergy
    simp_rw [h]
  simp only [formGroundEnergy,he]

namespace CenteredGaussLabels

theorem nuclei_attraction (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) (x : Position) :
    Coulomb.attraction (nuclei r G hG hh) x =
      Coulomb.attraction
        (gridNuclei (fun k : {k // k ∈ centeredGridIndices (radiiVector r)} => k.val)
          Subtype.val_injective G hG hh) x := by
  rw [gridNuclei_attraction]
  simp only [Coulomb.attraction,nuclei,one_mul]
  simpa only [Fintype.sum_prod_type,gridGaussIndex] using
    sum_enumeration r (fun a => Coulomb.coulombKernel (x-G (gaussLatticePoint h a)))

theorem dilated_nuclei_ground (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h scale : ℝ} (hh : 0 < h) (hs : 0 < scale) (n : ℕ) :
    formGroundEnergy (dilatedNuclei (nuclei r G hG hh) scale hs.ne') n =
      formGroundEnergy (dilatedNuclei
        (gridNuclei (fun k : {k // k ∈ centeredGridIndices (radiiVector r)} => k.val)
          Subtype.val_injective G hG hh) scale hs.ne') n := by
  apply formGroundEnergy_eq_of_attraction
  intro x
  rw [attraction_dilatedNuclei _ hs,attraction_dilatedNuclei _ hs,nuclei_attraction]

theorem nuclei_totalCharge (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.totalCharge (nuclei r G hG hh)=(labels r).length := by
  simp [Coulomb.totalCharge,nuclei]

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NumericalGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the full ground-energy interval to the actual rational
Euler/Gauss nodes, with the physical inverse-scale coordinates. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open CappedKernelProgram (Triple position)

namespace CenteredGaussLabels

theorem numerical_ground_interval (r : Radii) (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (fieldScale S : ℚ) (sites : List (ℚ×ℚ)) (G : Position → Position)
    (hG : Function.Injective G) {J : ℝ≥0} (hAnti : AntilipschitzWith J G)
    (herror : ∀ l : TransformedGauss.Label,
      ‖position (TransformedGauss.value rho U C K P N fieldScale S sites l.1 l.2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤ ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3)
    {scale : ℝ} (hs : 0 < scale) (n : ℕ) {center error roundError : ℝ}
    (hlo : ((center-error:ℝ):EReal) ≤
      formGroundEnergy (dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne') n)
    (hhi : formGroundEnergy (dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne') n ≤
      ((center+error:ℝ):EReal))
    (hsmall : 32*(scale⁻¹*((P:ℝ)+1)⁻¹)*(labels r).length ≤ 1)
    (hbudget : 32*(scale⁻¹*((P:ℝ)+1)⁻¹)*(labels r).length*
      (center+error+4*(n:ℝ)*((labels r).length:ℝ)^2) ≤ roundError) :
    let q := fun a : Fin (labels r).length => TransformedGauss.value rho U C K P N fieldScale S sites
      ((labels r).get a).1 ((labels r).get a).2
    ∃ hq : Function.Injective q,
      ((center-error-roundError:ℝ):EReal) ≤
        formGroundEnergy (physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs) n ∧
      formGroundEnergy (physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs) n ≤
        ((center+error+roundError:ℝ):EReal) := by
  dsimp only
  let q := fun a : Fin (labels r).length => TransformedGauss.value rho U C K P N fieldScale S sites
    ((labels r).get a).1 ((labels r).get a).2
  have hlabels : Function.Injective (fun a : Fin (labels r).length => (labels r).get a) := by
    intro a b hab
    apply (List.Nodup.getEquiv (labels r) (labels_nodup r)).injective
    exact Subtype.ext hab
  have hq : Function.Injective q := TransformedGauss.value_injective _ hlabels rho U C K P hN
    fieldScale S sites G hAnti (fun a => herror ((labels r).get a)) hprecision
  refine ⟨hq,?_⟩
  let exactNuc := dilatedNuclei (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) scale hs.ne'
  let approxNuc := physicalRationalNuclei (by rw [labels_length]; positivity) q hq hs
  have hcharge : exactNuc.charge=approxNuc.charge := rfl
  have htotal : Coulomb.totalCharge exactNuc=(labels r).length := by
    change Coulomb.totalCharge (nuclei r G hG (by positivity : 0 < (N:ℝ)⁻¹)) = _
    exact nuclei_totalCharge r G hG (by positivity : 0 < (N:ℝ)⁻¹)
  have hmove (a : Fin (labels r).length) :
      ‖exactNuc.position a-approxNuc.position a‖ ≤ scale⁻¹*((P:ℝ)+1)⁻¹ := by
    change ‖scale⁻¹ • G (gaussLatticePoint (N:ℝ)⁻¹
      (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2))-
        scale⁻¹ • position (q a)‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (herror ((labels r).get a)) (inv_nonneg.mpr hs.le)
  apply formGroundEnergy_rounding_interval exactNuc approxNuc hlo hhi (by positivity)
    hcharge hmove
  · simpa only [htotal] using hsmall
  · simpa only [htotal] using hbudget

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PhysicalNuclearProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical nuclear coordinates for h=1/N. The exact rational factor is
1/λ=rho/(8N^3), matching the manuscript's y=λx convention. -/

namespace ContinuumCoulomb.PhysicalNuclearProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)

theorem factor_positive {rho N : ℕ} (hrho : 0 < rho) (hN : 0 < N) : 0 < factor rho N := by
  unfold factor
  positivity

theorem factor_real (rho N : ℕ) : (factor rho N:ℝ) = (rho:ℝ)/(8*(N:ℝ)^3) := by
  simp only [factor,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]

theorem scale_position (a : ℚ) (p : Triple) : position (scale a p) = (a:ℝ) • position p := by
  ext i
  fin_cases i <;> simp [position,scale]

theorem scale_injective {a : ℚ} (ha : a ≠ 0) : Function.Injective (scale a) := by
  intro p q h
  have hx : a*p.1 = a*q.1 := congrArg Prod.fst h
  have hy : a*p.2.1 = a*q.2.1 := congrArg (fun p : Triple => p.2.1) h
  have hz : a*p.2.2 = a*q.2.2 := congrArg (fun p : Triple => p.2.2) h
  exact Prod.ext (mul_left_cancel₀ ha hx)
    (Prod.ext (mul_left_cancel₀ ha hy) (mul_left_cancel₀ ha hz))

theorem nuclei_length (rho U C K : ℕ) (x : Input) :
    (nuclei rho U C K x).length = 8*((2*x.2.1+1)*(2*x.2.2.1+1)*(2*x.2.2.2+1)) := by
  rw [nuclei,NuclearCoordinateOutput.positions_length,triples,List.length_map,
    TransformedGauss.nodes_length,CenteredGaussLabels.labels_length]

theorem nuclei_valid (rho U C K : ℕ) (x : Input) {p : BinaryPosition}
    (hp : p ∈ nuclei rho U C K x) : p.Valid := NuclearCoordinateOutput.positions_valid _ hp

theorem nuclei_nonempty (rho U C K : ℕ) (x : Input) : 0 < (nuclei rho U C K x).length := by
  rw [nuclei_length]
  positivity

theorem nuclei_values_nodup (rho U C K : ℕ) (x : Input) (hrho : 0 < rho)
    (hN : 0 < x.1.1.2)
    (hnodes : (TransformedGauss.nodes rho U C K (x.1,CenteredGaussLabels.labels x.2)).Nodup) :
    ((nuclei rho U C K x).map BinaryPosition.value).Nodup := by
  have hs := hnodes.map (scale_injective (factor_positive hrho hN).ne')
  have hm := hs.map NuclearCoordinateOutput.position_value_injective
  simpa only [nuclei,NuclearCoordinateOutput.positions,List.map_map,Function.comp_def,triples] using hm

end ContinuumCoulomb.PhysicalNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_UnitCoulombProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal output codec for a complete unit-charge Coulomb instance.
The electron count is unary, and both rational thresholds are emitted in
canonical numerator/positive-denominator form. -/

namespace ContinuumCoulomb.UnitCoulombProgram
open ExactQuantumFactoring.BitStackProgram

private theorem positions_injective {ns : List BinaryPosition}
    (h : (ns.map BinaryPosition.value).Nodup) :
    Function.Injective (fun a : Fin ns.length => (ns.get a).value) := by
  intro i j hij
  apply Fin.ext
  exact (List.Nodup.getElem_inj_iff h (i := i.val) (j := j.val) (hi := by simp) (hj := by simp)).1
    (by simp only [List.getElem_map]; exact hij)

theorem valid (rho U C K : ℕ) (x : Input) (helectrons : 0 < x.2.1)
    (hpositions : ((PhysicalNuclearProgram.nuclei rho U C K x.1).map BinaryPosition.value).Nodup)
    (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1) : (value rho U C K x).Valid where
  nuclei_pos := PhysicalNuclearProgram.nuclei_nonempty rho U C K x.1
  electrons_pos := helectrons
  positions a := PhysicalNuclearProgram.nuclei_valid rho U C K x.1 (List.get_mem _ a)
  distinct := positions_injective hpositions
  lower_denominator := x.2.2.1.den_pos
  upper_denominator := x.2.2.2.den_pos
  gap := by simpa only [value,NuclearCoordinateOutput.rational_value] using hgap

theorem valid_of_nodes (rho U C K : ℕ) (x : Input) (hrho : 0 < rho)
    (hN : 0 < x.1.1.1.2) (helectrons : 0 < x.2.1)
    (hnodes : (TransformedGauss.nodes rho U C K
      (x.1.1,CenteredGaussLabels.labels x.1.2)).Nodup)
    (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1) : (value rho U C K x).Valid :=
  valid rho U C K x helectrons
    (PhysicalNuclearProgram.nuclei_values_nodup rho U C K x.1 hrho hN hnodes) hgap

end ContinuumCoulomb.UnitCoulombProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ProgramGroundIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The serialized unit-Coulomb instance has exactly the ground energy of
the rational array generated by the numerical node program. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb
open CappedKernelProgram (Triple position)

theorem unitData_attraction_list (d : UnitCoulomb) (hd : d.Valid) (y : Position) :
    Coulomb.attraction (d.toData hd).toNuclearData.toNuclei y =
      (d.nuclei.map (fun p => Coulomb.coulombKernel (y-realPosition p.value))).sum := by
  simp only [Coulomb.attraction,NuclearData.toNuclei,UnitNuclearData.toNuclearData,
    UnitCoulomb.toData,Nat.cast_one,one_mul,List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem d.nuclei (fun p => Coulomb.coulombKernel (y-realPosition p.value))

theorem program_ground_identity (rho U C K : ℕ) (x : UnitCoulombProgram.Input)
    (hx : (UnitCoulombProgram.value rho U C K x).Valid)
    {scale : ℝ} (hs : 0 < scale)
    (hfactor : (PhysicalNuclearProgram.factor rho x.1.1.1.2:ℝ)=scale⁻¹)
    (hq : Function.Injective (fun a : Fin (CenteredGaussLabels.labels x.1.2).length =>
      TransformedGauss.value rho U C K x.1.1.1.1 x.1.1.1.2 x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2
        ((CenteredGaussLabels.labels x.1.2).get a).1 ((CenteredGaussLabels.labels x.1.2).get a).2)) :
    unitGroundEnergy ((UnitCoulombProgram.value rho U C K x).toData hx) =
      formGroundEnergy (physicalRationalNuclei
        (by rw [CenteredGaussLabels.labels_length]; positivity) _ hq hs) x.2.1 := by
  change formGroundEnergy ((UnitCoulombProgram.value rho U C K x).toData hx).toNuclearData.toNuclei _ = _
  apply formGroundEnergy_eq_of_attraction
  intro y
  rw [unitData_attraction_list]
  change ((PhysicalNuclearProgram.nuclei rho U C K x.1).map
    (fun p => Coulomb.coulombKernel (y-realPosition p.value))).sum = _
  simp only [PhysicalNuclearProgram.nuclei,NuclearCoordinateOutput.positions,
    PhysicalNuclearProgram.triples,TransformedGauss.nodes,List.map_map,Function.comp_def,
    NuclearCoordinateOutput.real_position,PhysicalNuclearProgram.scale_position,hfactor]
  change ((CenteredGaussLabels.labels x.1.2).map (fun l =>
    Coulomb.coulombKernel (y-scale⁻¹ • position (TransformedGauss.value rho U C K
      x.1.1.1.1 x.1.1.1.2 x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)))).sum = _
  simp only [Coulomb.attraction,physicalRationalNuclei,one_mul,List.get_eq_getElem]
  exact (Fin.sum_univ_fun_getElem (CenteredGaussLabels.labels x.1.2) (fun l =>
    Coulomb.coulombKernel (y-scale⁻¹ • position (TransformedGauss.value rho U C K
      x.1.1.1.1 x.1.1.1.2 x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)))).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_UnitProgramGroundInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal binary-encoded unit-charge output inherits the full
ground-energy interval and validity from the computed node estimates. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb.UnitCoulombProgram
open CappedKernelProgram (position)

theorem ground_interval (rho U C K : ℕ) (hrho : 0 < rho) (x : Input)
    (hN : 0 < x.1.1.1.2) (hn : 0 < x.2.1) (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1)
    (G : Position → Position) (hG : Function.Injective G) {J : ℝ≥0}
    (hAnti : AntilipschitzWith J G)
    (herror : ∀ l : TransformedGauss.Label,
      ‖position (TransformedGauss.value rho U C K x.1.1.1.1 x.1.1.1.2
        x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)-
        G (gaussLatticePoint (x.1.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤
          ((x.1.1.1.1:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((x.1.1.1.1:ℝ)+1)⁻¹ < (x.1.1.1.2:ℝ)⁻¹/3)
    {scale center error roundError : ℝ} (hs : 0 < scale)
    (hfactor : (PhysicalNuclearProgram.factor rho x.1.1.1.2:ℝ)=scale⁻¹)
    (hlo : ((center-error:ℝ):EReal) ≤ formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei x.1.2 G hG (by positivity : 0 < (x.1.1.1.2:ℝ)⁻¹))
        scale hs.ne') x.2.1)
    (hhi : formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei x.1.2 G hG (by positivity : 0 < (x.1.1.1.2:ℝ)⁻¹))
        scale hs.ne') x.2.1 ≤ ((center+error:ℝ):EReal))
    (hsmall : 32*(scale⁻¹*((x.1.1.1.1:ℝ)+1)⁻¹)*(CenteredGaussLabels.labels x.1.2).length ≤ 1)
    (hbudget : 32*(scale⁻¹*((x.1.1.1.1:ℝ)+1)⁻¹)*(CenteredGaussLabels.labels x.1.2).length*
      (center+error+4*(x.2.1:ℝ)*((CenteredGaussLabels.labels x.1.2).length:ℝ)^2) ≤ roundError) :
    ∃ hx : (value rho U C K x).Valid,
      ((center-error-roundError:ℝ):EReal) ≤ unitGroundEnergy ((value rho U C K x).toData hx) ∧
      unitGroundEnergy ((value rho U C K x).toData hx) ≤ ((center+error+roundError:ℝ):EReal) := by
  have hnodes := TransformedGauss.nodes_nodup rho U C K x.1.1.1.1 hN
    x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 (CenteredGaussLabels.labels x.1.2)
    (CenteredGaussLabels.labels_nodup x.1.2) G hAnti herror hprecision
  let hx := valid_of_nodes rho U C K x hrho hN hn hnodes hgap
  obtain ⟨hq,hl,hu⟩ := CenteredGaussLabels.numerical_ground_interval x.1.2 rho U C K x.1.1.1.1 hN
    x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 G hG hAnti herror hprecision hs x.2.1 hlo hhi hsmall hbudget
  refine ⟨hx,?_,?_⟩
  · rw [program_ground_identity rho U C K x hx hs hfactor hq]
    exact hl
  · rw [program_ground_identity rho U C K x hx hs hfactor hq]
    exact hu

end ContinuumCoulomb.UnitCoulombProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal composition from the encoded source to the calibrated
contact coordinates. The signed retained bonds determine the geometric
strips; the final positive bond list supplies their nineteen target weights. -/

namespace ContinuumCoulomb.SourceContactProgram
open ExactQuantumFactoring.BitStackProgram

theorem size_ge_two (d : BinaryHeisenberg) : 2 ≤ size d := by
  simp only [size,SourceMetadataProgram.size]
  omega

end ContinuumCoulomb.SourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePhysicalThreshold
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal raw-source assembly of the complete physical threshold pair.
The same fixed powers determine the calibration amplification, the centered
nuclear mesh, and the rational slab dimensions. -/

namespace ContinuumCoulomb.SourcePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

theorem horizontal_product (k : ℕ) (d : BinaryHeisenberg) :
    horizontalRadius k d = SourceContactProgram.size d^(50*k)*mesh k d := by
  dsimp [horizontalRadius,mesh]
  rw [← pow_add]
  congr 1
  omega

theorem vertical_product (k : ℕ) (d : BinaryHeisenberg) :
    verticalRadius k d = SourceContactProgram.size d^(5*k)*mesh k d := by
  dsimp [verticalRadius,mesh]
  rw [← pow_add]
  congr 1
  omega

theorem mesh_positive (k : ℕ) (d : BinaryHeisenberg) : 0 < mesh k d := by
  apply pow_pos
  exact lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)

theorem slabHorizontal_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d^(50*k):ℕ):ℚ) ≤ slabHorizontal k d ∧
      slabHorizontal k d ≤ 2*((SourceContactProgram.size d^(50*k):ℕ):ℚ) := by
  rw [slabHorizontal,horizontal_product]
  exact SlabBoxSchedule.centeredWidth_product_bounds _ _
    (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)) _)
    (mesh_positive k d)

theorem slabVertical_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d^(5*k):ℕ):ℚ) ≤ slabVertical k d ∧
      slabVertical k d ≤ 2*((SourceContactProgram.size d^(5*k):ℕ):ℚ) := by
  rw [slabVertical,vertical_product]
  exact SlabBoxSchedule.centeredWidth_product_bounds _ _
    (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)) _)
    (mesh_positive k d)

end ContinuumCoulomb.SourcePhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGridGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale and box identities for the existing source nuclear program.
The calibrated source-site geometry is handled separately. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram

theorem amplification_real (rho k : ℕ) (d : BinaryHeisenberg) :
    (amplification rho k d:ℝ) = (8/(rho:ℝ))*((SourceContactProgram.size d:ℝ)^k)^30 := by
  simp only [amplification,CenteredPhysicalThreshold.amplification,SourcePhysicalThreshold.mesh,
    Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Nat.cast_pow]
  rw [← pow_mul,← pow_mul]
  ring

theorem inverse_mesh_real (k : ℕ) (d : BinaryHeisenberg) :
    (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹ = 1/((SourceContactProgram.size d:ℝ)^k)^10 := by
  simp only [SourcePhysicalThreshold.mesh,Nat.cast_pow,one_div,← pow_mul]
  congr 2
  omega

theorem horizontal_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d:ℝ)^k)^50 ≤ (SourcePhysicalThreshold.slabHorizontal k d:ℝ) ∧
      (SourcePhysicalThreshold.slabHorizontal k d:ℝ) ≤ 2*((SourceContactProgram.size d:ℝ)^k)^50 := by
  have h := SourcePhysicalThreshold.slabHorizontal_bounds k d
  exact_mod_cast (show ((SourceContactProgram.size d:ℚ)^k)^50 ≤ SourcePhysicalThreshold.slabHorizontal k d ∧
    SourcePhysicalThreshold.slabHorizontal k d ≤ 2*((SourceContactProgram.size d:ℚ)^k)^50 by
      simpa only [← pow_mul,Nat.cast_pow,show k*50=50*k by omega] using h)

theorem vertical_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d:ℝ)^k)^5 ≤ (SourcePhysicalThreshold.slabVertical k d:ℝ) ∧
      (SourcePhysicalThreshold.slabVertical k d:ℝ) ≤ 2*((SourceContactProgram.size d:ℝ)^k)^5 := by
  have h := SourcePhysicalThreshold.slabVertical_bounds k d
  exact_mod_cast (show ((SourceContactProgram.size d:ℚ)^k)^5 ≤ SourcePhysicalThreshold.slabVertical k d ∧
    SourcePhysicalThreshold.slabVertical k d ≤ 2*((SourceContactProgram.size d:ℚ)^k)^5 by
      simpa only [← pow_mul,Nat.cast_pow,show k*5=5*k by omega] using h)

theorem grid_cover (k : ℕ) (d : BinaryHeisenberg) :
    (⋃ j : {j // j ∈ centeredGridIndices (CenteredGaussLabels.radiiVector (radii k d))},
      positionCube (gaussCellCenter (1/((SourceContactProgram.size d:ℝ)^k)^10) j.val)
        (1/((SourceContactProgram.size d:ℝ)^k)^10)) =
      slabDomain (SourcePhysicalThreshold.slabHorizontal k d) (SourcePhysicalThreshold.slabVertical k d) := by
  rw [← inverse_mesh_real]
  rw [centeredGrid_covers (CenteredGaussLabels.radiiVector (radii k d)) (by
    exact inv_pos.mpr (by exact_mod_cast SourcePhysicalThreshold.mesh_positive k d))]
  ext y
  change (∀ i, |y i| ≤ ((CenteredGaussLabels.radiiVector (radii k d) i:ℝ)+1/2)*
    (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹) ↔ _
  simp only [SourcePhysicalThreshold.slabHorizontal,SourcePhysicalThreshold.slabVertical,
    SlabBoxSchedule.centeredWidth_real,slabDomain,Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 0,
      by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 1,
      by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 2⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h0
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h1
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h2

theorem factor_amplification {rho : ℕ} (hrho : 0 < rho) (k : ℕ) (d : BinaryHeisenberg) :
    (PhysicalNuclearProgram.factor rho (SourcePhysicalThreshold.mesh k d):ℝ)=
      (amplification rho k d:ℝ)⁻¹ := by
  have hm : (SourcePhysicalThreshold.mesh k d:ℝ) ≠ 0 := by
    exact_mod_cast (SourcePhysicalThreshold.mesh_positive k d).ne'
  have hr : (rho:ℝ) ≠ 0 := by exact_mod_cast hrho.ne'
  rw [PhysicalNuclearProgram.factor_real]
  simp only [amplification,CenteredPhysicalThreshold.amplification,Rat.cast_div,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
  field_simp

theorem grid_count (k : ℕ) (d : BinaryHeisenberg) :
    ((CenteredGaussLabels.labels (radii k d)).length:ℝ) ≤
      (SourceContactProgram.size d:ℝ)^(135*k+8) := by
  apply centered_grid_count_power (by exact_mod_cast SourceContactProgram.size_ge_two d) k
  all_goals simp only [radii,SourcePhysicalThreshold.horizontalRadius,SourcePhysicalThreshold.verticalRadius,Nat.cast_pow]; rfl

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCloudComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source nuclear program has the manufactured Hubbard ground
interval. The remaining premises concern only its finite calibrated sites
and hopping matrix, not any continuum energy comparison. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem source_cloud_comparison_oai
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (_hrho : 0 < rho) (U F K q : ℕ), 1 ≤ q ∧
    ∀ (r s v p k ap calC srcS pc h A B qt : ℕ) (eps c : ℚ) (d : BinaryHeisenberg),
      q+9*r+72*s+v+p ≤ k → q+465*k+2*r+v+p+34 ≤ ap →
    ∀ (m n : ℕ) (u : Fin (m+1) → ℚ×ℚ), n+2=m+1 →
      (SourcePositiveProgram.output srcS d).vertices=n+2 →
      SourceNuclearProgram.sites rho calC eps c srcS pc h k A B d=List.ofFn u →
      (m+1:ℝ) ≤ (SourceContactProgram.size d:ℝ)^r →
      (∀ i, ‖PlanarForcingProgram.position (u i)‖ ≤ (SourceContactProgram.size d:ℝ)^s) →
    ∀ D : ℝ, 25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ (SourceContactProgram.size d:ℝ)^v →
      (∀ i j, ‖((SourceNuclearProgram.amplification rho k d:ℝ):ℂ)*
          (planarHoppingMatrix (fun a => PlanarForcingProgram.position (u a)) i j:ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤
          ((SourceContactProgram.size d:ℝ)^(2*r+p+7))⁻¹) →
      (1:ℚ) ≤ (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).2-
        (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).1 →
    let freq := GaussianFrequency.frequency rho
    let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
    let center := scale^2*(n+2:ℝ)*
      (slabPotential rho (SourcePhysicalThreshold.slabHorizontal k d)
        (SourcePhysicalThreshold.slabVertical k d) 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a))) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a)) i j))
    let output := SourceUnitCoulomb.value rho calC U F K eps c srcS pc h k A B qt ap d
    ∃ ho : output.Valid,
      ((center-scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤ unitGroundEnergy (output.toData ho) ∧
      unitGroundEnergy (output.toData ho) ≤ ((center+scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) := by
  obtain ⟨rho,hrho,L,J,hL,hJ,q₀,hq₀,hpoly⟩ := manufactured_polynomial_comparison hflow hp hv hdensity
  let freq := GaussianFrequency.frequency rho
  have hf : 1 ≤ freq := manufactured_frequency_ge_one hrho
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨U,F,_hU,_hF,hnum⟩ := TransformedGauss.exists_uniform_constants rho hrho
  obtain ⟨K,hK⟩ := exists_nat_ge (L:ℝ)
  obtain ⟨qS,_hqS,hscale⟩ := exists_manufactured_scale_threshold ha
  obtain ⟨qU,_hqU,hupper⟩ := exists_grid_ground_upper_exponent hf hr.le ha
  obtain ⟨qJ,_hqJ,hprecision⟩ := exists_grid_node_separation_offset J
  obtain ⟨qD,_hqD,hthree⟩ := exists_logarithmic_scale_threshold 3
  refine ⟨rho,hrho,U,F,K,q₀+qS+qU+qJ+qD+4,by omega,?_⟩
  intro r s v p k ap calC srcS pc h A B qt eps c d hk hap m n u hNe helectrons hsites hm hu D hD hsep
    Edge _ left right t ht hgraph hgap
  dsimp only
  let N := SourceContactProgram.size d
  let uu := fun i => PlanarForcingProgram.position (u i)
  let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
  let H := (SourcePhysicalThreshold.slabHorizontal k d:ℝ)
  let S := (SourcePhysicalThreshold.slabVertical k d:ℝ)
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
    scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq uu) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq uu i j))
  have hN : (2:ℝ) ≤ N := by exact_mod_cast SourceContactProgram.size_ge_two d
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hscaleEq : scale=(8/(rho:ℝ))*((N:ℝ)^k)^30 := SourceNuclearProgram.amplification_real rho k d
  have hs1 : 1 ≤ scale := by rw [hscaleEq]; exact hscale k (by omega) N hN
  have hs : 0 < scale := lt_of_lt_of_le zero_lt_one hs1
  have hmesh := SourcePhysicalThreshold.mesh_positive k d
  have hH := SourceNuclearProgram.horizontal_bounds k d
  have hS := SourceNuclearProgram.vertical_bounds k d
  let rad := SourceNuclearProgram.radii k d
  let index := fun j : {j // j ∈ centeredGridIndices (CenteredGaussLabels.radiiVector rad)} => j.val
  have hgraph' : ∀ i j, ‖((((8/(rho:ℝ))*((N:ℝ)^k)^30)*planarHoppingMatrix uu i j:ℝ):ℂ)-
      graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ ((N:ℝ)^(2*r+(p+1)+6))⁻¹ := by
    simpa only [← hscaleEq,Complex.ofReal_mul,uu,scale,N,show 2*r+(p+1)+6=2*r+p+7 by omega] using hgraph
  obtain ⟨G,hbij,hGflow,hLip,hAnti,hfix,hcharge,hreg,hjets,hcounter,hlo,hhi⟩ :=
    hpoly r s v (p+1) k (by omega) N H S D hN hH.1 hH.2 hS.1 hS.2 hD
      m n uu hNe hm hu hsep left right t ht hgraph' index Subtype.val_injective
      (SourceNuclearProgram.grid_cover k d)
  have hthreeD : 3 ≤ D := (hthree k (by omega) N hN).trans hD
  have huinj : Function.Injective u := by
    intro i j hij
    by_contra hne
    have hh := hthreeD.trans (hsep i j hne)
    rw [hij,sub_self,norm_zero] at hh
    norm_num at hh
  have hSp : 1 ≤ S := (one_le_pow₀ (one_le_pow₀ hN1 : (1:ℝ) ≤ (N:ℝ)^k)).trans hS.1
  have hnum' := hnum K (N^ap) (SourcePhysicalThreshold.mesh k d) hmesh
    (SourceNuclearProgram.amplification rho k d) (SourcePhysicalThreshold.slabVertical k d)
    hs1 hSp (m+1) u huinj (fun i j hij => hthreeD.trans (hsep i j hij))
    (by simpa only [uu,← hscaleEq] using hcounter) (by simpa only [uu,← hscaleEq] using hcharge)
    G (by simpa only [uu,← hscaleEq] using hGflow) L hLip hK
  have hNpow : (N:ℝ)^ap ≤ (N^ap:ℕ) := by simp only [Nat.cast_pow]; exact le_rfl
  have hprec := hprecision k ap (by omega) N (N^ap) hN hNpow
  rw [← SourceNuclearProgram.inverse_mesh_real k d] at hprec
  have hNeR : (n+2:ℝ)=(m+1:ℝ) := by exact_mod_cast hNe
  have hupper' : center+scale*((N:ℝ)^(p+1))⁻¹ ≤ (N:ℝ)^(qU+60*k+r+v) := by
    have hh := hupper r v (p+1) k N H S hN m uu left right t hm ht
    simpa only [center,hNeR,hscaleEq] using hh
  have hcount := SourceNuclearProgram.grid_count k d
  have hbudget := grid_node_rounding_budget hN hs1 (q := qU) (r := r) (v := v) (p := p+1)
    (k := k) (a := ap) (P := N^ap) (by omega) hNpow (Q := (CenteredGaussLabels.labels rad).length)
    (by positivity) hcount (M := (n+2:ℝ)) (by positivity) (by simpa only [hNeR] using hm) hupper'
  have hhlo : ((center-scale*((N:ℝ)^(p+1))⁻¹:ℝ):EReal) ≤ formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei rad (fun x => G x 1) hbij.injective
        (by positivity : 0 < (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹)) scale hs.ne') (n+2) := by
    rw [CenteredGaussLabels.dilated_nuclei_ground (hs := hs)]
    simpa only [SourceNuclearProgram.inverse_mesh_real,center,hscaleEq,H,S,N,uu,index,rad] using hlo
  have hhhi : formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei rad (fun x => G x 1) hbij.injective
        (by positivity : 0 < (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹)) scale hs.ne') (n+2) ≤
      ((center+scale*((N:ℝ)^(p+1))⁻¹:ℝ):EReal) := by
    rw [CenteredGaussLabels.dilated_nuclei_ground (hs := hs)]
    simpa only [SourceNuclearProgram.inverse_mesh_real,center,hscaleEq,H,S,N,uu,index,rad] using hhi
  let x := AffinePhysicalOutput.argument rho (SourceUnitCoulomb.input rho calC eps c srcS pc h k A B qt ap d)
  have hn : 0 < x.2.1 := by change 0 < (SourcePositiveProgram.output srcS d).vertices; omega
  have hNx : 0 < x.1.1.1.2 := hmesh
  have hnumx : ∀ l : TransformedGauss.Label,
      ‖CappedKernelProgram.position (TransformedGauss.value rho U F K x.1.1.1.1 x.1.1.1.2
        x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)-
        G (gaussLatticePoint (x.1.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2)) 1‖ ≤
          ((x.1.1.1.1:ℝ)+1)⁻¹ := by
    intro l
    simpa only [x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,SourceNuclearProgram.input,hsites,N] using hnum' l.1 l.2
  have hxs : x.2.1=n+2 := helectrons
  obtain ⟨ho,hl,hh⟩ := UnitCoulombProgram.ground_interval (center := center) (error := scale*((N:ℝ)^(p+1))⁻¹) (roundError := ((N:ℝ)^(p+1))⁻¹) rho U F K hrho x hNx hn hgap
    (fun x => G x 1) hbij.injective hAnti hnumx hprec hs (SourceNuclearProgram.factor_amplification hrho k d)
    (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii] using hhlo)
    (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii] using hhhi)
    hbudget.1 (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii,Nat.cast_add,Nat.cast_ofNat] using hbudget.2)
  have hsum : scale*((N:ℝ)^(p+1))⁻¹+((N:ℝ)^(p+1))⁻¹ ≤ scale*((N:ℝ)^p)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ ((N:ℝ)^(p+1))⁻¹)
    have hdouble := mul_le_mul_of_nonneg_left (double_inverse_power_le hN p) hs.le
    nlinarith only [hmul,hdouble]
  refine ⟨ho,?_,?_⟩
  · have he : center-scale*((N:ℝ)^p)⁻¹ ≤ center-scale*((N:ℝ)^(p+1))⁻¹-((N:ℝ)^(p+1))⁻¹ := by linarith only [hsum]
    exact (EReal.coe_le_coe_iff.mpr he).trans hl
  · have he : center+scale*((N:ℝ)^(p+1))⁻¹+((N:ℝ)^(p+1))⁻¹ ≤ center+scale*((N:ℝ)^p)⁻¹ := by linarith only [hsum]
    exact hh.trans (EReal.coe_le_coe_iff.mpr he)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.source_cloud_comparison_oai := @OAI.ContinuumCoulomb.source_cloud_comparison_oai
