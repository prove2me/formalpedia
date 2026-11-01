-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufactured_grid_ground_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:01:02.229202+00:00
-- url     : https://prove2.me/submissions/a9577964-09df-40c6-963a-828a64266e6a

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
import Theorems.Thm_OAI_ContinuumCoulomb_localizedTensor_hubbard_lower
import Theorems.Thm_OAI_ContinuumCoulomb_localized_hubbard_near_trial
import Theorems.Thm_OAI_ContinuumCoulomb_manufacturedSlab_uniform_tensorComplement_gap
import Theorems.Thm_OAI_ContinuumCoulomb_manufacturedTensor_nuclear_interacting_lower

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Space
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

lemma norm_real_mul_sq (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z‖ ^ 2 = a ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

open ContinuousLinearMap
open scoped Convolution

end Coulomb
end
end

end OAI
end

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

lemma H1Vector.nuclear_integrable {M n : ℕ} (ψ : H1Vector n) (S : Nuclei M)
    (s : Spins n) :
    Integrable (fun x => (∑ i, attraction S (position x i)) * ‖ψ.value s x‖^2) := by
  simp only [attraction, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (ψ.nuclear_coulomb_integrable_bound s i (S.position j) (by norm_num : (0 : ℝ) < 1)).1
  simpa only [mul_assoc] using h.const_mul (S.charge j)

lemma mass_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma kinetic_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ kinetic ψ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

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

lemma Antisymmetric.rsmul {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (t : ℝ) : Antisymmetric (ψ.rsmul t) := by
  intro p s
  filter_upwards [hψ p s] with x hx
  change (t : ℂ) * ψ.value (s ∘ p) (permute p x) = _
  rw [hx]
  change _ = ((p.sign : ℤ) : ℂ) * ((t : ℂ) * ψ.value s x)
  ring

lemma mass_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    mass (ψ.rsmul t) = t^2 * mass ψ := by
  unfold mass H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, Finset.mul_sum]

lemma kinetic_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    kinetic (ψ.rsmul t) = t^2 * kinetic ψ := by
  unfold kinetic H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, ← Finset.mul_sum]
  ring

lemma nuclearEnergy_rsmul {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) (t : ℝ) :
    nuclearEnergy S (ψ.rsmul t) = t^2 * nuclearEnergy S ψ := by
  unfold nuclearEnergy H1Vector.rsmul
  simp only [norm_real_mul_sq]
  simp_rw [mul_left_comm _ (t^2), integral_const_mul]
  rw [← Finset.mul_sum]

lemma pairEnergy_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    pairEnergy (ψ.rsmul t) = t^2 * pairEnergy ψ := by
  unfold pairEnergy H1Vector.rsmul
  simp only [norm_real_mul_sq]
  simp_rw [mul_left_comm _ (t^2), integral_const_mul]
  rw [← Finset.mul_sum]

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
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

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

end NeutralAtom
end
end
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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_FermionicCoefficients
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
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
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
lemma coulombKernel_integrableOn_ball (R : ℝ) : IntegrableOn coulombKernel (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact Filter.Eventually.of_forall (fun x => by simp [coulombKernel, Real.rpow_neg_one])
  · exact coulombKernel_measurable.aestronglyMeasurable

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball

lemma coulomb_integrand_bound {f : Space → ℝ} {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) * f y ≤ M * truncatedCoulomb R (x-y) + R⁻¹ * f y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    have H := mul_le_mul_of_nonneg_left (hfM y) (coulombKernel_nonneg (x-y))
    linarith [mul_nonneg (inv_nonneg.mpr hR.le) (hf0 y)]
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, mul_zero, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hR hn) (hf0 y)

lemma coulomb_convolution_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    Integrable (fun y => coulombKernel (x-y) * f y) := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  apply ((hnear.const_mul M).add (hf.const_mul R⁻¹)).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y) * f y‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hf0 _))]
    exact coulomb_integrand_bound hf0 hfM hR x y)

lemma coulomb_signed_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have h := coulomb_convolution_integrable hf.norm hm.norm (fun y => norm_nonneg _) hM
    (by norm_num : (0:ℝ) < 1) x
  apply h.mono' (((coulombKernel_measurable.comp (by fun_prop)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y)*f y‖ ≤ coulombKernel (x-y)*‖f y‖
    rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)] )

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CorePerm
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

lemma H1Vector.value_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) : ψ.value s =ᵐ[volume] 0 := by
  have hnon (t : Spins n) : 0 ≤ ∫ x, ‖ψ.value t x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hz : (∫ x, ‖ψ.value s x‖^2) = 0 := by
    apply le_antisymm _ (hnon s)
    exact hψ ▸ Finset.single_le_sum (fun t _ => hnon t) (Finset.mem_univ s)
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖ψ.value s x‖)
    ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide))).mp hz
  filter_upwards [ha] with x hx
  simpa using hx

lemma H1Vector.gradient_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) (a : Fin n × Fin 3) :
    ψ.gradient s a =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((ψ.partial_L2 s a).locallyIntegrable (by norm_num))
  intro φ hφ hφC
  have H := ψ.weak_partial s a φ hφ hφC
  have hv : (∫ x, ψ.value s x *
      (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
    simp [hx]
  rw [hv, eq_neg_iff_add_eq_zero, zero_add] at H
  simpa only [Complex.real_smul, mul_comm] using H

lemma kinetic_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) : kinetic ψ = 0 := by
  have hzero (s : Spins n) (a : Fin n × Fin 3) : ∫ x, ‖ψ.gradient s a x‖^2 = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.gradient_eq_zero_of_mass_zero hψ s a] with x hx
    simp [hx]
  simp [kinetic, hzero]

lemma mass_normalized {n : ℕ} (ψ : H1Vector n) (hψ : 0 < mass ψ) :
    mass ψ.normalized = 1 := by
  rw [H1Vector.normalized, mass_rsmul, inv_pow, Real.sq_sqrt hψ.le, inv_mul_cancel₀ hψ.ne']

lemma Antisymmetric.normalized {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ) :
    Antisymmetric ψ.normalized := hψ.rsmul _

lemma kinetic_normalized_weight {n : ℕ} (ψ : H1Vector n) :
    mass ψ * kinetic ψ.normalized = kinetic ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, kinetic_eq_zero_of_mass_zero ψ hz]
  · rw [H1Vector.normalized, kinetic_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

lemma potentialForm_rsmul {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) (t : ℝ) :
    potentialForm V (ψ.rsmul t) = t^2 * potentialForm V ψ := by
  simp only [potentialForm, H1Vector.rsmul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp_rw [mul_left_comm (V _) (t^2), integral_const_mul, ← Finset.mul_sum]

lemma potentialForm_eq_zero_of_mass_zero {n : ℕ} (V : Configuration n → ℝ)
    (ψ : H1Vector n) (hψ : mass ψ = 0) : potentialForm V ψ = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply integral_eq_zero_of_ae
  filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
  simp [hx]

lemma potentialForm_normalized_weight {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) :
    mass ψ * potentialForm V ψ.normalized = potentialForm V ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, potentialForm_eq_zero_of_mass_zero V ψ hz]
  · rw [H1Vector.normalized, potentialForm_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

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

lemma form_normalized_weight {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    mass ψ * form S ψ.normalized = form S ψ := by
  change mass ψ * (kinetic ψ.normalized - potentialForm (nuclearPotential S) ψ.normalized +
    potentialForm pairPotential ψ.normalized) = _
  rw [mul_add, mul_sub, kinetic_normalized_weight, potentialForm_normalized_weight,
    potentialForm_normalized_weight]
  rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem manufacturedPlanarWell_nonpositive (r : PlanarPosition) : manufacturedPlanarWell r ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (planarForcing_nonnegative r))
    (mul_nonneg (by norm_num) (planarResolventMode_positive r).le)

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

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

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

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

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

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

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

theorem countertermWellSum_nonpositive (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos
    (add_nonneg zero_le_one (div_nonneg (localizedCounterterm_nonnegative freq u i) hscale))
    (manufacturedPlanarWell_nonpositive _)

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

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

private theorem well_zero_away_from_near_site {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (r : PlanarPosition)
    (i : Fin m) (hi : ‖r-u i‖ < 1) (j : Fin m) (hji : j ≠ i) :
    manufacturedPlanarWell (r-u j) = 0 := by
  apply manufacturedPlanarWell_zero_of_norm_ge_one
  have ht : ‖u i-u j‖ ≤ ‖r-u i‖ + ‖r-u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) r] using dist_triangle (u i) r (u j)
  linarith [hsep i j hji.symm]

/-- Disjoint planar supports prevent the counterterm perturbation from
growing with the number of sites. -/
theorem countertermWellSum_lower (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (r : PlanarPosition) :
    planarWellSum u r - δ*PlanarSobolev.wellBound ≤ countertermWellSum freq scale u r := by
  classical
  by_cases hnear : ∃ i, ‖r-u i‖ < 1
  · obtain ⟨i, hi⟩ := hnear
    have hz := well_zero_away_from_near_site u hsep r i hi
    have hsum : planarWellSum u r = manufacturedPlanarWell (r-u i) := by
      unfold planarWellSum
      exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
    have hsum' : countertermWellSum freq scale u r =
        (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
      unfold countertermWellSum
      exact Finset.sum_eq_single i (fun j _ hji => by rw [hz j hji, mul_zero]) (by simp)
    rw [hsum, hsum']
    have hw : -PlanarSobolev.wellBound ≤ manufacturedPlanarWell (r-u i) := by
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using
        PlanarSobolev.wellBound_spec (r-u i))).1
    have h1 := mul_le_mul_of_nonneg_left hw (hcoeff i).1
    have h2 := mul_le_mul_of_nonneg_right (hcoeff i).2 PlanarSobolev.wellBound_nonnegative
    nlinarith only [h1, h2]
  · have hz (i : Fin m) : manufacturedPlanarWell (r-u i) = 0 :=
      manufacturedPlanarWell_zero_of_norm_ge_one (le_of_not_gt (fun hi => hnear ⟨i, hi⟩))
    simp only [planarWellSum, countertermWellSum, hz, mul_zero, Finset.sum_const_zero]
    linarith [mul_nonneg hδ PlanarSobolev.wellBound_nonnegative]

/-- Global lower comparison to the separable uncapped multiwell field. -/
theorem manufacturedWellField_lower (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    (S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 - δ*PlanarSobolev.wellBound ≤
      manufacturedWellField freq scale S u x := by
  apply (countertermWellSum_lower freq scale u hsep hδ hcoeff _).trans
  exact le_mul_of_le_one_left (countertermWellSum_nonpositive freq hscale u _)
    (slabWellCutoff_bounds S _).2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedSourcePairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for the absolute nuclear error measure. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem weighted_real_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F f g : X → ℝ)
    (hF : AEMeasurable F μ) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfi : Integrable (fun x => |F x| *f x^2) μ)
    (hgi : Integrable (fun x => |F x| *g x^2) μ) :
    Integrable (fun x => F x*f x*g x) μ ∧
      |∫ x, F x*f x*g x ∂μ|^2 ≤
        (∫ x, |F x| *f x^2 ∂μ)*(∫ x, |F x| *g x^2 ∂μ) := by
  let a : X → ℝ := fun x => Real.sqrt |F x| *|f x|
  let b : X → ℝ := fun x => Real.sqrt |F x| *|g x|
  have ha : AEMeasurable a μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hf.abs
  have hb : AEMeasurable b μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hg.abs
  have hasq (x : X) : a x^2 = |F x| *f x^2 := by
    dsimp [a]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hbsq (x : X) : b x^2 = |F x| *g x^2 := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hpa : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (by simpa only [hasq] using hfi)
  have hpb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (by simpa only [hbsq] using hgi)
  let A := hpa.toLp a
  let B := hpb.toLp b
  have hi : inner ℝ A B = ∫ x, a x*b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp,hpb.coeFn_toLp] with x hax hbx
    change inner ℝ (A x) (B x) = a x*b x
    rw [hax,hbx,Real.inner_apply]
  have hnA : ‖A‖^2 = ∫ x, |F x| *f x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp] with x hax
    rw [real_inner_self_eq_norm_sq,hax,Real.norm_eq_abs,sq_abs,hasq]
  have hnB : ‖B‖^2 = ∫ x, |F x| *g x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpb.coeFn_toLp] with x hbx
    rw [real_inner_self_eq_norm_sq,hbx,Real.norm_eq_abs,sq_abs,hbsq]
  have hab (x : X) : a x*b x = ‖F x*f x*g x‖ := by
    dsimp [a,b]
    rw [abs_mul,abs_mul]
    calc
      _ = (Real.sqrt |F x|)^2*(|f x| *|g x|) := by ring
      _ = _ := by rw [Real.sq_sqrt (abs_nonneg (F x))]; ring
  have hip := hpa.integrable_mul hpb
  have hIfg : Integrable (fun x => F x*f x*g x) μ := by
    apply hip.mono' ((hF.mul hf).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => (hab x).ge)
  refine ⟨hIfg,?_⟩
  have hle : |∫ x, F x*f x*g x ∂μ| ≤ ∫ x, a x*b x ∂μ := by
    have h := norm_integral_le_integral_norm (μ := μ) (fun x => F x*f x*g x)
    simpa only [Real.norm_eq_abs,← hab] using h
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℝ A B)) (norm_inner_le_norm (𝕜 := ℝ) A B) 2
  rw [mul_pow,hnA,hnB,hi,Real.norm_eq_abs,sq_abs] at hcs
  exact (pow_le_pow_left₀ (abs_nonneg _) hle 2).trans hcs

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedNuclearCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute nuclear form errors control mixed terms on the full complex,
spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem weighted_inner_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ) (f g : X → ℂ) (hF : AEMeasurable F μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun x => |F x| * ‖f x‖^2) μ)
    (hgi : Integrable (fun x => |F x| * ‖g x‖^2) μ) :
    Integrable (fun x => F x*inner ℝ (f x) (g x)) μ ∧
      |∫ x, F x*inner ℝ (f x) (g x) ∂μ|^2 ≤
        (∫ x, |F x| * ‖f x‖^2 ∂μ)*(∫ x, |F x| * ‖g x‖^2 ∂μ) := by
  obtain ⟨hi,hsq⟩ := weighted_real_pairing μ (fun x => |F x|) (fun x => ‖f x‖) (fun x => ‖g x‖)
    hF.abs hf.norm.aemeasurable hg.norm.aemeasurable
    (by simpa only [abs_abs] using hfi) (by simpa only [abs_abs] using hgi)
  have hb (x : X) : ‖F x*inner ℝ (f x) (g x)‖ ≤ |F x| * ‖f x‖*‖g x‖ := by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (f x) (g x)) (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  have hI : Integrable (fun x => F x*inner ℝ (f x) (g x)) μ :=
    hi.mono' (hF.aestronglyMeasurable.mul (hf.inner hg)) (Filter.Eventually.of_forall hb)
  refine ⟨hI,?_⟩
  have he : |∫ x, F x*inner ℝ (f x) (g x) ∂μ| ≤ ∫ x, |F x| * ‖f x‖*‖g x‖ ∂μ := by
    apply (show |∫ x, F x*inner ℝ (f x) (g x) ∂μ| ≤ ∫ x, ‖F x*inner ℝ (f x) (g x)‖ ∂μ from
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => F x*inner ℝ (f x) (g x))).trans
    exact integral_mono hI.norm hi hb
  apply (pow_le_pow_left₀ (abs_nonneg _) he 2).trans
  simpa only [sq_abs,abs_abs] using hsq

theorem nuclearAbsoluteError_bound {n : ℕ} (F : Position → ℝ) (B : ℝ)
    (u : Coulomb.H1Vector n)
    (hb : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :
    nuclearAbsoluteError F u ≤ B*((n:ℝ)*Coulomb.mass u+2*Coulomb.kinetic u) := by
  apply (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun i _ => hb s i))).trans_eq
  simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  simp only [Coulomb.mass,Coulomb.kinetic,Fintype.sum_prod_type,← Finset.mul_sum]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedNuclearForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization and graph bounds for the actual nuclear error potential,
including its Coulomb singularities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem nuclearErrorEnergy_abs_le {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) :
    |nuclearErrorEnergy F u| ≤ nuclearAbsoluteError F u := by
  have hi (s : SpinConfiguration n) (i : Fin n) :
      |∫ x, F (Coulomb.position x i)*‖u.value s x‖^2| ≤
        ∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2 := by
    have h := norm_integral_le_integral_norm (μ := volume)
      (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)
    simpa only [norm_mul,Real.norm_eq_abs,abs_pow,abs_norm] using h
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun s _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => hi s i)))

theorem nuclearErrorEnergy_graph_bound {n : ℕ} (hn : 1 ≤ n)
    (F : Position → ℝ) {B : ℝ} (hB : 0 ≤ B) (u : Coulomb.H1Vector n)
    (hb : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :
    |nuclearErrorEnergy F u| ≤ B*n*(Coulomb.mass u+2*Coulomb.kinetic u) := by
  apply (nuclearErrorEnergy_abs_le F u).trans ((nuclearAbsoluteError_bound F B u hb).trans ?_)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk := mul_le_mul_of_nonneg_right hnR (Coulomb.kinetic_nonneg u)
  nlinarith only [mul_le_mul_of_nonneg_left hk hB]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedSpinOrbitals
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin lifting of the actual weighted spatial matrix elements. Only
integrability of the spatial product is required, including at nuclear poles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem weighted_realSpinOrbital_integrable (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ s : Fin 2) :
    Integrable (fun x => (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s)) := by
  by_cases hs : s=σ
  · by_cases ht : s=τ
    · subst s
      subst τ
      have hi : Integrable (fun x => ((F x*f x*g x : ℝ) : ℂ)) := hI.ofReal
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [realSpinOrbital,ite_true, if_true,Complex.star_def,Complex.conj_ofReal,
        Complex.ofReal_mul]
      ring
    · have ht' : σ ≠ τ := by simpa only [hs] using ht
      simp only [realSpinOrbital,hs,ht',ite_true, if_true,ite_false, if_false,mul_zero]
      exact integrable_zero _ _ _
  · simp only [realSpinOrbital,hs,ite_false, if_false,star_zero,zero_mul,mul_zero]
    exact integrable_zero _ _ _

theorem weighted_realSpinOrbital_inner (F f g : Position → ℝ) (σ τ : Fin 2) :
    (∑ s : Fin 2, ∫ x, (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s)) =
      if σ=τ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
  by_cases h : σ=τ
  · subst τ
    have hp (s : Fin 2) :
        (∫ x, (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g σ x s)) =
          if s=σ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
      by_cases hs : s=σ
      · subst s
        simp only [realSpinOrbital,ite_true, if_true,Complex.star_def,Complex.conj_ofReal,
          ← Complex.ofReal_mul,integral_complex_ofReal,mul_assoc]
      · simp [realSpinOrbital,hs]
    simp only [hp,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  · have hz (s : Fin 2) (x : Position) :
        (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s) = 0 := by
      by_cases hs : s=σ
      · subst s
        simp [realSpinOrbital,h]
      · simp [realSpinOrbital,hs]
    simp only [hz,integral_zero,Finset.sum_const_zero,h,ite_false, if_false]

theorem flatWeighted_realSpinOrbital_integrable (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ : Fin 2) :
    Integrable (fun z : Fin 2 × (Fin 3 → ℝ) => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*
        Coulomb.flatSpinOrbital (realSpinOrbital g τ) z)) Coulomb.spinSpaceMeasure := by
  apply Coulomb.integrable_finite_count_prod
  intro s
  exact (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_of_integrable
    (weighted_realSpinOrbital_integrable F f g hI σ τ s)

theorem flatWeighted_realSpinOrbital_inner (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ : Fin 2) :
    (∫ z : Fin 2 × (Fin 3 → ℝ), (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*
        Coulomb.flatSpinOrbital (realSpinOrbital g τ) z) ∂Coulomb.spinSpaceMeasure) =
      if σ=τ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
  unfold Coulomb.spinSpaceMeasure
  rw [Coulomb.integral_finite_count_prod _ (fun s =>
    (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_of_integrable
      (weighted_realSpinOrbital_integrable F f g hI σ τ s))]
  rw [← weighted_realSpinOrbital_inner F f g σ τ]
  apply Finset.sum_congr rfl
  intro s _
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  exact hm.integral_comp'
    (fun x => (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-interval comparison for the actual one-coordinate Coulomb
integrals. It is the coordinatewise monotonicity step in the slab estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem centeredLineIntegral_translate (f : ℝ → ℝ) (H x : ℝ) :
    centeredLineIntegral f H x = ∫ t in (-H)..H, f (x-t) := by
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [centeredLineIntegral, sub_neg_eq_add]

theorem centeredLineIntegral_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (H x : ℝ) :
    HasDerivAt (centeredLineIntegral f H) (f (x+H)-f (x-H)) x := by
  let F : ℝ → ℝ := fun a => ∫ t in (0:ℝ)..a, f t
  have hF (a : ℝ) : HasDerivAt F (f a) a :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : centeredLineIntegral f H = (fun a => F (a+H)-F (a-H)) := by
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (a+H)) (hf.intervalIntegrable 0 (a-H))).symm
  rw [he]
  simpa only [Function.comp_def, id_eq, mul_one] using
    ((hF (x+H)).comp x ((hasDerivAt_id x).add_const H)).fun_sub
      ((hF (x-H)).comp x ((hasDerivAt_id x).sub_const H))

theorem centeredLineIntegral_even (f : ℝ → ℝ) (heven : ∀ t, f (-t) = f t)
    (H x : ℝ) : centeredLineIntegral f H (-x) = centeredLineIntegral f H x := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := x-H) (b := x+H)
  simp only [heven] at h
  have ha : -(x+H) = -x-H := by ring
  have hb : -(x-H) = -x+H := by ring
  rw [ha, hb] at h
  exact h.symm

theorem centeredLineIntegral_antitone (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral f H) (Set.Ici (0:ℝ)) := by
  have hd : Differentiable ℝ (centeredLineIntegral f H) :=
    fun x => (centeredLineIntegral_hasDerivAt f hf H x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn
    hd.differentiableOn
  intro x hx
  have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici (0:ℝ))
  rw [(centeredLineIntegral_hasDerivAt f hf H x).deriv]
  apply sub_nonpos.mpr
  apply hdec
  rw [abs_of_nonneg (add_nonneg hx0 hH)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredLineIntegral_le_center (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral f H x ≤ centeredLineIntegral f H 0 := by
  have heven (t : ℝ) : f (-t) = f t := by
    apply le_antisymm
    · exact hdec t (-t) (by simp)
    · exact hdec (-t) t (by simp)
  have ha := centeredLineIntegral_antitone f hf hdec hH
  by_cases hx : 0 ≤ x
  · exact ha (Set.mem_Ici.mpr le_rfl) hx hx
  · have hn : 0 ≤ -x := by linarith
    rw [← centeredLineIntegral_even f heven H x]
    exact ha (Set.mem_Ici.mpr le_rfl) hn hn

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

theorem coulombLineKernel_radial_antitone {A : ℝ} (hA : 0 < A)
    {a b : ℝ} (hab : |a| ≤ |b|) : coulombLineKernel A b ≤ coulombLineKernel A a := by
  have hs : a^2 ≤ b^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)).mpr hab
  exact inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a] : 0 < A+a^2))
    (Real.sqrt_le_sqrt (by linarith : A+a^2 ≤ A+b^2))

theorem coulombLineIntegral_antitone {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral (coulombLineKernel A) H) (Set.Ici (0:ℝ)) :=
  centeredLineIntegral_antitone _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH

theorem coulombLineIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral (coulombLineKernel A) H x ≤
      centeredLineIntegral (coulombLineKernel A) H 0 :=
  centeredLineIntegral_le_center _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabKernelEstimates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube horizontal tail bound and the exact absolute-value
integral that produce the quadratic potential of the infinite slab. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem reciprocal_sqrt_difference_bound {R A B : ℝ} (hR : 0 < R)
    (hA : R^2 ≤ A) (hB : R^2 ≤ B) :
    |(Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹| ≤ |A-B|/(2*R^3) := by
  have hA0 : 0 ≤ A := (sq_nonneg R).trans hA
  have hB0 : 0 ≤ B := (sq_nonneg R).trans hB
  have hsA : R ≤ Real.sqrt A := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hA
  have hsB : R ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hB
  have hpA : 0 < Real.sqrt A := hR.trans_le hsA
  have hpB : 0 < Real.sqrt B := hR.trans_le hsB
  have hd : 0 < Real.sqrt A * Real.sqrt B * (Real.sqrt A + Real.sqrt B) := by positivity
  have he : (Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹ =
      (B-A)/(Real.sqrt A * Real.sqrt B * (Real.sqrt A+Real.sqrt B)) := by
    field_simp
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hprod : R^2 ≤ Real.sqrt A * Real.sqrt B := by
    simpa only [pow_two] using mul_le_mul hsA hsB hR.le hpA.le
  have hsum : 2*R ≤ Real.sqrt A+Real.sqrt B := by linarith
  have hden : 2*R^3 ≤ Real.sqrt A*Real.sqrt B*(Real.sqrt A+Real.sqrt B) := by
    have h := mul_le_mul hprod hsum (by positivity : 0 ≤ 2*R)
      (mul_nonneg hpA.le hpB.le)
    nlinarith only [h]
  rw [he, abs_div, abs_of_pos hd, abs_sub_comm B A]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

private theorem integral_abs_sub_of_inside {S z : ℝ} (_hS : 0 ≤ S)
    (hz : |z| ≤ S) :
    (∫ w in (-S)..S, |z-w|) = S^2+z^2 := by
  have hzlo : -S ≤ z := (abs_le.mp hz).1
  have hzhi : z ≤ S := (abs_le.mp hz).2
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-S) z) (hc.intervalIntegrable z S)]
  have hl : (∫ w in (-S)..z, |z-w|) = ∫ w in (-S)..z, z-w := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc (-S) z := by simpa only [Set.uIcc_of_le hzlo] using hw
    exact abs_of_nonneg (sub_nonneg.mpr hmem.2)
  have hr : (∫ w in z..S, |z-w|) = ∫ w in z..S, w-z := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc z S := by simpa only [Set.uIcc_of_le hzhi] using hw
    change |z-w| = w-z
    rw [abs_of_nonpos (sub_nonpos.mpr hmem.1)]
    ring
  rw [hl, hr]
  calc
    _ = ((∫ w : ℝ in (-S)..z, z) - (∫ w : ℝ in (-S)..z, w)) +
        ((∫ w : ℝ in z..S, w) - (∫ w : ℝ in z..S, z)) := by
      exact congrArg₂ (· + ·)
        (intervalIntegral.integral_sub (f := fun _ : ℝ => z) (g := fun w : ℝ => w)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _))
        (intervalIntegral.integral_sub (f := fun w : ℝ => w) (g := fun _ : ℝ => z)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _))
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring

theorem slab_absolute_difference_integral {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S) :
    (∫ w in (-S)..S, (|z-w|-|w|)) = z^2 := by
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (continuous_abs.intervalIntegrable _ _),
    integral_abs_sub_of_inside hS hz]
  have h := integral_abs_sub_of_inside hS (show |(0:ℝ)| ≤ S by simpa using hS)
  simp only [zero_sub, abs_neg, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h]
  ring

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

theorem dilateState_antisymmetric {n : ℕ} (state : Coulomb.H1Vector n)
    (hstate : Coulomb.Antisymmetric state) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.Antisymmetric (dilateState state scale hscale) := by
  intro p spin
  have h := (Measure.quasiMeasurePreserving_smul volume hscale).ae (hstate p spin)
  filter_upwards [h] with x hx
  have hperm : Coulomb.permute p (scale • x) = scale • Coulomb.permute p x := by
    ext a
    rfl
  simpa only [dilateState, hperm] using hx

theorem integral_dilation {n : ℕ} (f : Configuration n → ℝ) (scale : ℝ) :
    (∫ x, f (scale • x)) =
      |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ * ∫ x, f x := by
  simpa only [abs_inv, smul_eq_mul] using
    Measure.integral_comp_smul volume f scale

theorem mass_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.mass (dilateState state scale hscale) =
      |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ * Coulomb.mass state := by
  change (∑ spin, ∫ x, ‖state.value spin (scale • x)‖ ^ 2) = _
  rw [Coulomb.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  exact integral_dilation (fun x => ‖state.value spin x‖ ^ 2) scale

theorem kinetic_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.kinetic (dilateState state scale hscale) =
      scale ^ 2 * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.kinetic state := by
  change (1 / 2 : ℝ) * (∑ spin, ∑ a, ∫ x,
    ‖(scale : ℂ) * state.gradient spin a (scale • x)‖ ^ 2) = _
  have hI (spin : SpinConfiguration n) (a : Fin n × Fin 3) :
      (∫ x, ‖state.gradient spin a (scale • x)‖ ^ 2) =
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, ‖state.gradient spin a x‖ ^ 2 :=
    integral_dilation (fun x => ‖state.gradient spin a x‖ ^ 2) scale
  simp_rw [Coulomb.norm_real_mul_sq, integral_const_mul, hI]
  simp only [← Finset.mul_sum, Coulomb.kinetic]
  ring

theorem mass_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.mass (normalizedDilation state scale hscale) = Coulomb.mass state := by
  rw [normalizedDilation, Coulomb.mass_rsmul, mass_dilateState,
    Real.sq_sqrt (abs_nonneg _), ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr (pow_ne_zero _ hscale)), one_mul]

theorem kinetic_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.kinetic (normalizedDilation state scale hscale) =
      scale ^ 2 * Coulomb.kinetic state := by
  rw [normalizedDilation, Coulomb.kinetic_rsmul, kinetic_dilateState,
    Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale))
  calc
    _ = scale ^ 2 * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) * Coulomb.kinetic state := by ring
    _ = _ := by rw [h, mul_one]

theorem normalizedDilation_antisymmetric {n : ℕ} (state : Coulomb.H1Vector n)
    (hstate : Coulomb.Antisymmetric state) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.Antisymmetric (normalizedDilation state scale hscale) :=
  (dilateState_antisymmetric state hstate scale hscale).rsmul _

theorem h1Vector_ext {n : ℕ} {u v : Coulomb.H1Vector n}
    (hvalue : u.value = v.value) (hgradient : u.gradient = v.gradient) : u = v := by
  cases u
  cases v
  cases hvalue
  cases hgradient
  rfl

/-- Inverse dilation acts on every weak-H¹ state, so lower energy estimates
can be transferred back from the entire physical form domain. -/
theorem normalizedDilation_inverse {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    normalizedDilation (normalizedDilation state scale hscale) scale⁻¹
      (inv_ne_zero hscale) = state := by
  have hroot : Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (abs_pos.mpr (pow_ne_zero _ hscale))
  have hamp : Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| *
      Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| = 1 := by
    rw [inv_pow, abs_inv, Real.sqrt_inv, inv_mul_cancel₀ hroot]
  have hampC : (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) = 1 := by
    exact_mod_cast hamp
  have hscaleC : (scale : ℂ) * ((scale⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast (mul_inv_cancel₀ hscale)
  apply h1Vector_ext
  · funext spin x
    change (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      ((Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) *
        state.value spin (scale • scale⁻¹ • x)) = _
    rw [smul_inv_smul₀ hscale, ← mul_assoc, hampC, one_mul]
  · funext spin a x
    change (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      (((scale⁻¹ : ℝ) : ℂ) *
        ((Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) *
          ((scale : ℂ) * state.gradient spin a (scale • scale⁻¹ • x)))) = _
    rw [smul_inv_smul₀ hscale]
    calc
      _ = ((Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
          (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ)) *
            ((scale : ℂ) * ((scale⁻¹ : ℝ) : ℂ)) * state.gradient spin a x := by ring
      _ = _ := by rw [hampC, hscaleC, one_mul, one_mul]

theorem position_smul {n : ℕ} (x : Configuration n) (i : Fin n) (scale : ℝ) :
    Coulomb.position (scale • x) i = scale • Coulomb.position x i := by
  ext a
  rfl

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

theorem nuclearEnergy_dilateState {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.nuclearEnergy (dilatedNuclei S scale hscale.ne')
        (dilateState state scale hscale.ne') =
      scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.nuclearEnergy S state := by
  have hspin (spin : SpinConfiguration n) :
      (∫ x, (∑ i, Coulomb.attraction (dilatedNuclei S scale hscale.ne')
          (Coulomb.position x i)) * ‖state.value spin (scale • x)‖ ^ 2) =
        scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, (∑ i, Coulomb.attraction S (Coulomb.position x i)) *
            ‖state.value spin x‖ ^ 2 := by
    simp_rw [attraction_dilatedNuclei S hscale, ← position_smul,
      ← Finset.mul_sum, mul_assoc, integral_const_mul]
    have hi := integral_dilation (fun x =>
      (∑ i, Coulomb.attraction S (Coulomb.position x i)) *
        ‖state.value spin x‖ ^ 2) scale
    simpa only [mul_assoc] using congrArg (fun z : ℝ => scale * z) hi
  change (∑ spin, ∫ x, (∑ i, Coulomb.attraction
    (dilatedNuclei S scale hscale.ne') (Coulomb.position x i)) *
      ‖state.value spin (scale • x)‖ ^ 2) = _
  rw [Coulomb.nuclearEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  exact hspin spin

theorem nuclearEnergy_normalizedDilation {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.nuclearEnergy (dilatedNuclei S scale hscale.ne')
        (normalizedDilation state scale hscale.ne') =
      scale * Coulomb.nuclearEnergy S state := by
  rw [normalizedDilation, Coulomb.nuclearEnergy_rsmul,
    nuclearEnergy_dilateState S state hscale, Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale.ne'))
  calc
    _ = scale * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) *
          Coulomb.nuclearEnergy S state := by ring
    _ = _ := by rw [h, mul_one]

theorem pairPotential_dilation {n : ℕ} (x : Configuration n)
    {scale : ℝ} (hscale : 0 < scale) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then
      Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) =
      scale * (∑ i : Fin n, ∑ j : Fin n, if i < j then
        Coulomb.coulombKernel (Coulomb.position (scale • x) i -
          Coulomb.position (scale • x) j) else 0) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [position_smul, position_smul, ← smul_sub, coulombKernel_smul _ hscale]
    rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
  · exact (mul_zero _).symm

theorem pairEnergy_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.pairEnergy (dilateState state scale hscale.ne') =
      scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.pairEnergy state := by
  have hspin (spin : SpinConfiguration n) :
      (∫ x, (∑ i : Fin n, ∑ j : Fin n, if i < j then
          Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
            ‖state.value spin (scale • x)‖ ^ 2) =
        scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, (∑ i : Fin n, ∑ j : Fin n, if i < j then
            Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
              ‖state.value spin x‖ ^ 2 := by
    conv_lhs => enter [2, x, 1]; rw [pairPotential_dilation x hscale]
    simp_rw [mul_assoc, integral_const_mul]
    have hi := integral_dilation (fun x =>
      (∑ i : Fin n, ∑ j : Fin n, if i < j then
        Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
          ‖state.value spin x‖ ^ 2) scale
    simpa only [mul_assoc] using congrArg (fun z : ℝ => scale * z) hi
  change (∑ spin, ∫ x, _ * ‖state.value spin (scale • x)‖ ^ 2) = _
  simp_rw [hspin]
  exact (Finset.mul_sum _ _ _).symm

theorem pairEnergy_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.pairEnergy (normalizedDilation state scale hscale.ne') =
      scale * Coulomb.pairEnergy state := by
  rw [normalizedDilation, Coulomb.pairEnergy_rsmul,
    pairEnergy_dilateState state hscale, Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale.ne'))
  calc
    _ = scale * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) * Coulomb.pairEnergy state := by ring
    _ = _ := by rw [h, mul_one]

/-- Full electronic form under physical coordinate scaling; no projected
sector or differentiability beyond weak H¹ is used. -/
theorem form_normalizedDilation {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.form (dilatedNuclei S scale hscale.ne')
        (normalizedDilation state scale hscale.ne') =
      scale ^ 2 * Coulomb.kinetic state - scale * Coulomb.nuclearEnergy S state +
        scale * Coulomb.pairEnergy state := by
  rw [Coulomb.form, kinetic_normalizedDilation,
    nuclearEnergy_normalizedDilation S state hscale,
    pairEnergy_normalizedDilation state hscale]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearGridPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual equal-mass grid potential and its error against the
manufactured continuous potential, at every evaluation point. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem gridNuclearPotential_measurable {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) : Measurable (gridNuclearPotential index G rho h) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Coulomb.coulombKernel_measurable.comp (measurable_id.sub measurable_const)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularization
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularization of the actual finite-slab potential. The singular
Coulomb limit is justified on the full volume integral; no continuity of
the slab indicator is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabCoulomb_integrableOn {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-x)) (slabDomain H S) := by
  have hm : Measurable (slabDensity 1 H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hb (x : Position) : ‖slabDensity 1 H S x‖ ≤ 1 := by
    by_cases hx : x ∈ slabDomain H S <;>
      simp [slabDensity, hx]
  have hi := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS 1) hm hb y
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity 1 H S x) =
      (slabDomain H S).indicator (fun x => Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S <;> simp [slabDensity, hx]
  rw [he, integrable_indicator_iff (slabDomain_isClosed H S).measurableSet] at hi
  exact hi

theorem regularizedSlab_integrableOn {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => NeutralAtom.regularizedKernel epsilon (y-x)) (slabDomain H S) :=
  ((NeutralAtom.contDiff_regularizedKernel hepsilon).continuous.comp
    (continuous_const.sub continuous_id)).continuousOn.integrableOn_compact
      (slabDomain_isCompact hH hS)

theorem regularizedSlabPotential_tendsto {epsilon : ℕ → ℝ}
    (hepsilon : ∀ n, 0 < epsilon n) (hlim : Tendsto epsilon atTop (𝓝 0))
    (rho : ℝ) {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S y)
      atTop (𝓝 (slabPotential rho H S y)) := by
  have hae : ∀ᵐ x ∂(volume.restrict (slabDomain H S)), y-x ≠ 0 := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne y)] with x hx
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hi := slabCoulomb_integrableOn hH hS y
  have hc : Tendsto
      (fun n => ∫ x in slabDomain H S, NeutralAtom.regularizedKernel (epsilon n) (y-x))
      atTop (𝓝 (∫ x in slabDomain H S, Coulomb.coulombKernel (y-x))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => Coulomb.coulombKernel (y-x))
    · intro n
      exact ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').continuous.comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact hi
    · intro n
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (NeutralAtom.regularizedKernel_nonneg _ _)]
      exact NeutralAtom.regularizedKernel_le hx
    · filter_upwards [hae] with x hx
      exact NeutralAtom.regularizedKernel_tendsto hlim hx
  rw [slabPotential_eq_setIntegral]
  exact hc.const_mul (-rho)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem slabProductDomain_preimage (H S : ℝ) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' slabProductDomain H S = slabDomain H S := by
  ext x
  change (∀ i : Fin 3, i ∈ Set.univ → -slabSide H S i ≤ x i ∧ x i ≤ slabSide H S i) ↔
    |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S
  simp only [Set.mem_univ, true_implies, abs_le]
  constructor
  · intro h
    exact ⟨by simpa [slabSide] using h 0,
      by simpa [slabSide] using h 1, by simpa [slabSide] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [slabSide] using h0
    · simpa [slabSide] using h1
    · simpa [slabSide] using h2

theorem slabProductMeasure_eq (H S : ℝ) :
    slabProductMeasure H S = (volume : Measure (Fin 3 → ℝ)).restrict (slabProductDomain H S) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))).symm

theorem slabProduct_measurePreserving (H S : ℝ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (slabProductMeasure H S) (volume.restrict (slabDomain H S)) := by
  have hm := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).restrict_preimage
    (s := slabProductDomain H S)
    (MeasurableSet.univ_pi (fun i => measurableSet_Icc))
  rw [slabProductDomain_preimage, ← slabProductMeasure_eq] at hm
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm hm

theorem slabProduct_integral (H S : ℝ) (f : Position → ℝ) :
    (∫ x, f (WithLp.toLp 2 x) ∂slabProductMeasure H S) =
      ∫ y in slabDomain H S, f y := by
  exact (slabProduct_measurePreserving H S).integral_comp' f

theorem slabProduct_integrable (H S : ℝ) (f : Position → ℝ) :
    Integrable (fun x => f (WithLp.toLp 2 x)) (slabProductMeasure H S) ↔
      IntegrableOn f (slabDomain H S) :=
  (slabProduct_measurePreserving H S).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding

theorem regularizedKernel_eq_sqrt (epsilon : ℝ) (x : Position) :
    NeutralAtom.regularizedKernel epsilon x = (Real.sqrt (‖x‖^2+epsilon^2))⁻¹ := by
  rw [NeutralAtom.regularizedKernel, Real.sqrt_eq_rpow]
  convert Real.rpow_neg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg epsilon)) (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem regularizedKernel_section (epsilon : ℝ) (y : Position) (i : Fin 3)
    (t : ℝ) (v : Fin 2 → ℝ) :
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v)) =
      coulombLineKernel
        (epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2) (y i-t) := by
  rw [regularizedKernel_eq_sqrt]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp only [PiLp.sub_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  ring

theorem zeroPositionCoordinate_same (i : Fin 3) (y : Position) :
    zeroPositionCoordinate i y i = 0 := by simp [zeroPositionCoordinate]

theorem zeroPositionCoordinate_other (i : Fin 3) (y : Position) (j : Fin 2) :
    zeroPositionCoordinate i y (i.succAbove j) = y (i.succAbove j) := by
  simp [zeroPositionCoordinate, Fin.succAbove_ne]

private theorem regularizedProduct_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Integrable (fun x : Fin 3 → ℝ => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 x)) (slabProductMeasure H S) :=
  (slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y)

private theorem regularizedSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have h := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
    (regularizedProduct_integrable hepsilon hH hS y)
  exact h

theorem regularizedSlab_sectionIntegral {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) =
      ∫ v : Fin 2 → ℝ, ∫ t : ℝ,
        NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
        ∂slabAxisMeasure H S i
        ∂Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)) := by
  rw [← slabProduct_integral H S (fun x => NeutralAtom.regularizedKernel epsilon (y-x))]
  change (∫ x : Fin 3 → ℝ, NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 x)
    ∂Measure.pi (slabAxisMeasure H S)) = _
  rw [← ((measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  exact integral_prod_symm _ (regularizedSection_integrable hepsilon hH hS y i)

private theorem coulombLine_setIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H)
    (x : ℝ) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t) := by
  have h := coulombLineIntegral_le_center hA hH x
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Centering one coordinate increases the attractive Coulomb integral.
The statement holds for the actual finite slab, before taking the singular limit. -/
theorem regularizedSlab_coordinate_max {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) ≤
      ∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon
        (zeroPositionCoordinate i y-x) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS (zeroPositionCoordinate i y) i]
  apply integral_mono
    (regularizedSection_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSection_integrable hepsilon hH hS (zeroPositionCoordinate i y) i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_le_center hA hside (y i)

/-- The actual singular finite-slab potential is minimized in each centered
coordinate. The regularized comparison passes through a dominated limit. -/
theorem slabPotential_coordinate_min {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    slabPotential rho H S (zeroPositionCoordinate i y) ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS (zeroPositionCoordinate i y))
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left (regularizedSlab_coordinate_max (hep n).ne' hH hS y i)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabMonotonicity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise monotonicity of the actual singular slab potential.
This strengthens centering to comparison at any two absolute coordinates. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem coulombLineIntegral_abs_antitone {A H x y : ℝ} (hA : 0 < A)
    (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    centeredLineIntegral (coulombLineKernel A) H y ≤
      centeredLineIntegral (coulombLineKernel A) H x := by
  have he (t : ℝ) : coulombLineKernel A (-t) = coulombLineKernel A t := by
    simp [coulombLineKernel]
  have ha (t : ℝ) : centeredLineIntegral (coulombLineKernel A) H |t| =
      centeredLineIntegral (coulombLineKernel A) H t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      exact centeredLineIntegral_even _ he H t
  rw [← ha x, ← ha y]
  exact coulombLineIntegral_antitone hA hH (abs_nonneg x) (abs_nonneg y) hxy

private theorem coulombLine_setIntegral_abs_antitone {A H x y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (y-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t) := by
  have h := coulombLineIntegral_abs_antitone hA hH hxy
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem regularizedSections_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  exact (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))

theorem regularizedSlab_coordinate_antitone {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) :
    (∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-b)) ≤
      ∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (x-b) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS x i]
  apply integral_mono
    (regularizedSections_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSections_integrable hepsilon hH hS x i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, hother]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_abs_antitone hA hside hxy

/-- Increasing a single absolute coordinate increases the singular slab potential. -/
theorem slabPotential_coordinate_monotone {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) : slabPotential rho H S x ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS x)
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left
      (regularizedSlab_coordinate_antitone (hep n).ne' hH hS x y i hother hxy)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal-plane Coulomb differences. The individually divergent
plane integrals are never separated; their integrable difference has a
finite antiderivative and a zero limit at infinity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabRootDifference_quotient {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    slabRootDifference A B r = (A-B)/(Real.sqrt (r^2+A)+Real.sqrt (r^2+B)) := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have hden : 0 < Real.sqrt (r^2+A)+Real.sqrt (r^2+B) := by positivity
  apply (eq_div_iff hden.ne').mpr
  unfold slabRootDifference
  nlinarith [Real.sq_sqrt hpA.le, Real.sq_sqrt hpB.le]

theorem slabRootDifference_tendsto {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (slabRootDifference A B) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have ha := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ A hp)
  have hb := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ B hp)
  have hd := ha.atTop_add_atTop hb
  simpa only [Function.comp_apply, ← slabRootDifference_quotient hA hB] using hd.const_div_atTop (A-B)

theorem slabRootDifference_hasDerivAt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    HasDerivAt (slabRootDifference A B) (slabRadialDifference A B r) r := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have ha := (((hasDerivAt_id r).pow 2).add_const A).sqrt hpA.ne'
  have hb := (((hasDerivAt_id r).pow 2).add_const B).sqrt hpB.ne'
  refine (ha.fun_sub hb).congr_deriv ?_
  · dsimp only [slabRadialDifference, coulombLineKernel]
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [add_comm A (r^2), add_comm B (r^2)]
    field_simp

theorem slabRadialDifference_nonnegative {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ slabRadialDifference A B r := by
  apply mul_nonneg hr
  apply sub_nonneg.mpr
  unfold coulombLineKernel
  exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity : 0 < A+r^2))
    (Real.sqrt_le_sqrt (by linarith : A+r^2 ≤ B+r^2))

theorem slabRadialDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (slabRadialDifference A B) (Set.Ioi (0:ℝ)) := by
  rcases le_total A B with hAB | hBA
  · exact integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hA hB r)
      (fun r hr => slabRadialDifference_nonnegative hA hAB hr.le)
      (slabRootDifference_tendsto hA hB)
  · have h := (integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hB hA r)
      (fun r hr => slabRadialDifference_nonnegative hB hBA hr.le)
      (slabRootDifference_tendsto hB hA)).neg
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    change slabRadialDifference A B r = -slabRadialDifference B A r
    unfold slabRadialDifference
    ring

theorem slabRadialDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ r in Set.Ioi (0:ℝ), slabRadialDifference A B r) = Real.sqrt B-Real.sqrt A := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => slabRootDifference_hasDerivAt hA hB r)
    (slabRadialDifference_integrable hA hB) (slabRootDifference_tendsto hA hB)
  simpa [slabRootDifference] using h

theorem slabPlanarDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Integrable (fun p : PlanarPosition =>
      coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := fun r => coulombLineKernel A r-coulombLineKernel B r)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialDifference_integrable hA hB

/-- Exact difference of two horizontal Coulomb plane integrals. -/
theorem slabPlanarDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p : PlanarPosition, coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) =
      2*Real.pi*(Real.sqrt B-Real.sqrt A) := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume
    (fun r => coulombLineKernel A r-coulombLineKernel B r)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hi : (∫ r in Set.Ioi (0:ℝ),
      r*(coulombLineKernel A r-coulombLineKernel B r)) = Real.sqrt B-Real.sqrt A :=
    slabRadialDifference_integral hA hB
  rw [hm, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube tail in two horizontal dimensions. Its exact mass is
`2π/H`, giving the finite-slab truncation error without divergent integrals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slabRadialTail_weight {H : ℝ} (hH : 0 < H) (r : ℝ) :
    r * slabRadialTail H r = (Set.Ioi H).indicator (fun t : ℝ => t ^ (-2 : ℝ)) r := by
  by_cases hr : H < r
  · simp only [slabRadialTail, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]
    have hp : 0 < r := hH.trans hr
    rw [show (-2 : ℝ) = -3+1 by norm_num, Real.rpow_add hp, Real.rpow_one]
    ring
  · simp [slabRadialTail, hr]

private theorem slabRadialTail_weight_integrable {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun r : ℝ => r * slabRadialTail H r) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [slabRadialTail_weight hH] using h.integrableOn

private theorem slabRadialTail_weight_integral {H : ℝ} (hH : 0 < H) :
    (∫ r in Set.Ioi (0:ℝ), r * slabRadialTail H r) = H⁻¹ := by
  simp_rw [slabRadialTail_weight hH]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [Set.Ioi_inter_Ioi, max_eq_left hH.le]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  rw [Real.rpow_neg_one]

theorem slabPlanarTail_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (slabPlanarTail H) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := slabRadialTail H)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialTail_weight_integrable hH

theorem slabPlanarTail_nonnegative (H : ℝ) (p : PlanarPosition) :
    0 ≤ slabPlanarTail H p := by
  unfold slabPlanarTail slabRadialTail
  by_cases h : H < ‖p‖
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    exact Real.rpow_nonneg (norm_nonneg p) _
  · simp [h]

/-- The exact horizontal inverse-cube tail mass. -/
theorem slabPlanarTail_integral {H : ℝ} (hH : 0 < H) :
    (∫ p, slabPlanarTail H p) = 2*Real.pi/H := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume (slabRadialTail H)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hm, slabRadialTail_weight_integral hH] at h
  change (∫ p, slabRadialTail H ‖p‖) = _
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

theorem slabPlanarBox_measurable (H : ℝ) : MeasurableSet (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  exact (h0.inter h1).measurableSet

theorem slabPlanarBox_compl_norm {H : ℝ} {p : PlanarPosition}
    (hp : p ∉ slabPlanarBox H) : H < ‖p‖ := by
  by_contra h
  have hn : ‖p‖ ≤ H := le_of_not_gt h
  apply hp
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact ⟨h0.trans hn, h1.trans hn⟩

theorem slab_regularized_line_difference_uniform {R S epsilon z w : ℝ}
    (hR : 0 < R) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |coulombLineKernel (epsilon^2+(z-w)^2) R -
      coulombLineKernel (epsilon^2+w^2) R| ≤ 3*S^2/(2*R^3) := by
  have h := reciprocal_sqrt_difference_bound hR
    (show R^2 ≤ (epsilon^2+(z-w)^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg (z-w)])
    (show R^2 ≤ (epsilon^2+w^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg w])
  have hS : 0 ≤ S := (abs_nonneg z).trans hz
  have hz2 : z^2 ≤ S^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hS).mpr hz
  have hzw : |z*w| ≤ S^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hz hw (abs_nonneg w) hS
  have ha : |(epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2)| ≤ 3*S^2 := by
    rw [show (epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2) = z^2-2*(z*w) by ring]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg z), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact h.trans (div_le_div_of_nonneg_right ha (by positivity))

/-- The finite square loses at most the integrable radial tail. -/
theorem slabPlanarDifference_tail_bound {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |∫ p in (slabPlanarBox H)ᶜ,
      (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
       coulombLineKernel (epsilon^2+w^2) ‖p‖)| ≤ 3*Real.pi*S^2/H := by
  let f := fun p : PlanarPosition =>
    coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hi : Integrable f := slabPlanarDifference_integrable hA hB
  have ht : Integrable (fun p => (3*S^2/2)*slabPlanarTail H p) :=
    (slabPlanarTail_integrable hH).const_mul _
  have hpt (p : PlanarPosition) (hp : p ∈ (slabPlanarBox H)ᶜ) :
      ‖f p‖ ≤ (3*S^2/2)*slabPlanarTail H p := by
    have hn := slabPlanarBox_compl_norm hp
    have hn0 : 0 < ‖p‖ := hH.trans hn
    have hbound := slab_regularized_line_difference_uniform (epsilon := epsilon) hn0 hz hw
    rw [Real.norm_eq_abs]
    change |coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖| ≤ _
    unfold slabPlanarTail slabRadialTail
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hn), Real.rpow_neg (norm_nonneg p), Real.rpow_ofNat]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm : (∫ p in (slabPlanarBox H)ᶜ, ‖f p‖) ≤
      ∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_mono_on hi.norm.integrableOn ht.integrableOn
      (slabPlanarBox_measurable H).compl hpt
  have hall : (∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p) ≤
      ∫ p, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_le_integral ht (Filter.Eventually.of_forall
      (fun p => mul_nonneg (by positivity) (slabPlanarTail_nonnegative H p)))
  calc
    _ = ‖∫ p in (slabPlanarBox H)ᶜ, f p‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p in (slabPlanarBox H)ᶜ, ‖f p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (3*S^2/2)*slabPlanarTail H p := hm.trans hall
    _ = _ := by rw [integral_const_mul, slabPlanarTail_integral hH]; ring

/-- The finite horizontal square differs from the infinite-plane formula by
at most the inverse-cube tail. -/
theorem slabPlanarDifference_estimate {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |(∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2))| ≤
        3*Real.pi*S^2/H := by
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hs := integral_add_compl (slabPlanarBox_measurable H)
    (slabPlanarDifference_integrable hA hB)
  rw [slabPlanarDifference_integral hA hB] at hs
  have he : (∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2)) =
      -(∫ p in (slabPlanarBox H)ᶜ,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) := by linarith
  rw [he, abs_neg]
  exact slabPlanarDifference_tail_bound hH hepsilon hz hw

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabProfile
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the vertical regularization. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slab_sqrt_regularization (epsilon a : ℝ) :
    0 ≤ Real.sqrt (epsilon^2+a^2)-|a| ∧
      Real.sqrt (epsilon^2+a^2)-|a| ≤ |epsilon| := by
  have hp : 0 ≤ epsilon^2+a^2 := by positivity
  have hl : |a| ≤ Real.sqrt (epsilon^2+a^2) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg epsilon])
  constructor
  · linarith
  · have hs := Real.sq_sqrt hp
    have he := sq_abs epsilon
    have ha := sq_abs a
    nlinarith [Real.sqrt_nonneg (epsilon^2+a^2), abs_nonneg epsilon,
      abs_nonneg a, mul_nonneg (abs_nonneg epsilon) (abs_nonneg a)]

theorem slabRegularizedProfile_error {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    (epsilon : ℝ) : |slabRegularizedProfile epsilon S z-z^2| ≤ 4*S*|epsilon| := by
  have hc : Continuous (fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-
      Real.sqrt (epsilon^2+w^2)) := by fun_prop
  have hd : Continuous (fun w : ℝ => |z-w|-|w|) := by fun_prop
  rw [slabRegularizedProfile, ← slab_absolute_difference_integral hS hz,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  have hbound (w : ℝ) :
      ‖(Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2))-(|z-w|-|w|)‖ ≤
        2*|epsilon| := by
    obtain ⟨ha0,ha1⟩ := slab_sqrt_regularization epsilon (z-w)
    obtain ⟨hb0,hb1⟩ := slab_sqrt_regularization epsilon w
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -S) (b := S) (fun w _ => hbound w)
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem slabRegularizedProfile_tendsto {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    {epsilon : ℕ → ℝ} (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => slabRegularizedProfile (epsilon n) S z) atTop (𝓝 (z^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro delta hdelta
  have hlim : Tendsto (fun n => 4*S*|epsilon n|) atTop (𝓝 0) := by
    simpa using hepsilon.abs.const_mul (4*S)
  filter_upwards [((tendsto_order.1 hlim).2 delta hdelta)] with n hn
  rw [Real.dist_eq]
  exact (slabRegularizedProfile_error hS hz (epsilon n)).trans_lt hn

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabVerticalCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical-first coordinates for the actual three-dimensional slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabVerticalEquiv_symm_apply (p : ℝ × PlanarPosition) :
    slabVerticalEquiv.symm p = WithLp.toLp 2 ![p.2 0, p.2 1, p.1] := by
  ext i
  fin_cases i <;> rfl

theorem slabVerticalEquiv_apply (x : Position) :
    slabVerticalEquiv x = (x 2, WithLp.toLp 2 ![x 0, x 1]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem slabVerticalEquiv_measurePreserving : MeasurePreserving slabVerticalEquiv :=
  ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem slabVerticalEquiv_preimage (H S : ℝ) :
    slabVerticalEquiv ⁻¹' (Set.Icc (-S) S ×ˢ slabPlanarBox H) = slabDomain H S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, slabVerticalEquiv_apply,
    slabPlanarBox, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, slabDomain, abs_le]
  tauto

theorem slabVertical_setIntegral (H S : ℝ) (f : Position → ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ p in Set.Icc (-S) S ×ˢ slabPlanarBox H, f (slabVerticalEquiv.symm p) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    h.integral_comp' (f ∘ slabVerticalEquiv.symm)

theorem regularizedSlab_vertical_kernel (epsilon z : ℝ) (p : ℝ × PlanarPosition) :
    NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-slabVerticalEquiv.symm p) =
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖ := by
  rw [regularizedKernel_eq_sqrt, slabVerticalEquiv_symm_apply]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [slabAxisPoint, PiLp.sub_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    zero_sub, neg_sq]
  rw [Fin.succ_zero_eq_one]
  ring

theorem regularizedSlab_vertical_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntegrableOn (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      (Set.Icc (-S) S ×ˢ slabPlanarBox H) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  have hs := (MeasurePreserving.symm slabVerticalEquiv h).integrable_comp_emb
    (g := fun x : Position => NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-x))
    slabVerticalEquiv.symm.measurableEmbedding
  exact (hs.mpr (regularizedSlab_integrableOn hepsilon hH hS (slabAxisPoint z))).congr
    (Filter.Eventually.of_forall (regularizedSlab_vertical_kernel epsilon z))

theorem regularizedSlab_vertical (epsilon rho : ℝ) {H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in Set.Icc (-S) S, ∫ p in slabPlanarBox H,
        coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖ := by
  unfold regularizedSlabPotential
  rw [slabVertical_setIntegral]
  simp_rw [regularizedSlab_vertical_kernel]
  rw [Measure.volume_eq_prod, setIntegral_prod _
    (regularizedSlab_vertical_integrable hepsilon hH hS z)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabConfinement
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative confinement by the actual finite rectangular Coulomb slab. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

private theorem slabPlanarBox_compact {H : ℝ} (hH : 0 ≤ H) :
    IsCompact (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : PlanarPosition) (2*(H+1))).of_isClosed_subset (h0.inter h1)
  intro p hp
  have hcoord (i : Fin 2) : |p i| ≤ H := by
    fin_cases i
    · exact hp.1
    · exact hp.2
  have hsq : ‖p‖^2 ≤ 2*H^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (sq_le_sq₀ (abs_nonneg (p i)) hH).mpr (hcoord i))
    simpa only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg p]

private theorem slabPlanarSection_kernel_integrable {epsilon H : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (z w : ℝ) :
    IntegrableOn (fun p : PlanarPosition => coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖)
      (slabPlanarBox H) :=
  ((coulombLineKernel_continuous (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _))).comp continuous_norm).continuousOn.integrableOn_compact
      (slabPlanarBox_compact hH)

private theorem slabPlanarSection_intervalIntegrable {epsilon H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntervalIntegrable (slabPlanarSection epsilon H z) volume (-S) S := by
  have hp : Integrable (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      ((volume.restrict (Set.Icc (-S) S)).prod (volume.restrict (slabPlanarBox H))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact regularizedSlab_vertical_integrable hepsilon hH hS z
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hp.integral_prod_left

private theorem slabPlanarSection_sub {epsilon H : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (z w : ℝ) :
    slabPlanarSection epsilon H z w-slabPlanarSection epsilon H 0 w =
      ∫ p in slabPlanarBox H,
        (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
          coulombLineKernel (epsilon^2+w^2) ‖p‖) := by
  unfold slabPlanarSection
  rw [← integral_sub (slabPlanarSection_kernel_integrable hepsilon hH z w)
    (slabPlanarSection_kernel_integrable hepsilon hH 0 w)]
  simp only [zero_sub, neg_sq]

private theorem regularizedSlab_vertical_interval (epsilon rho : ℝ) {H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in (-S)..S, slabPlanarSection epsilon H z w := by
  rw [regularizedSlab_vertical epsilon rho hepsilon hH hS z,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem slabPlaneError_bound {epsilon H S z w : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 < H) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |slabPlaneError epsilon H z w| ≤ 3*Real.pi*S^2/H := by
  unfold slabPlaneError
  rw [slabPlanarSection_sub hepsilon hH.le]
  have he := slabPlanarDifference_estimate hH hepsilon hz hw
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

private theorem regularizedSlab_error_identity {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z =
        -rho*∫ w in (-S)..S, slabPlaneError epsilon H z w := by
  let P := fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hIz := slabPlanarSection_intervalIntegrable hepsilon hH hS z
  have hI0 := slabPlanarSection_intervalIntegrable hepsilon hH hS 0
  rw [regularizedSlab_vertical_interval epsilon rho hepsilon hH hS z,
    regularizedSlab_vertical_interval epsilon rho hepsilon hH hS 0]
  unfold slabPlaneError slabRegularizedProfile
  rw [intervalIntegral.integral_add (hIz.sub hI0)
    ((hP.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_sub hIz hI0, intervalIntegral.integral_const_mul]
  ring

/-- The regularized finite slab differs from its one-dimensional profile
by at most the horizontal inverse-cube tail. -/
theorem regularizedSlab_confinement_error {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H)
    (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z| ≤ 6*Real.pi*rho*S^3/H := by
  have hbound (w : ℝ) (hw : w ∈ Set.uIoc (-S) S) :
      ‖slabPlaneError epsilon H z w‖ ≤ 3*Real.pi*S^2/H := by
    have hh : w ∈ Set.Ioc (-S) S := by
      simpa only [Set.uIoc_of_le (by linarith : -S ≤ S)] using hw
    rw [Real.norm_eq_abs]
    exact slabPlaneError_bound hepsilon hH hz (abs_le.mpr ⟨hh.1.le, hh.2⟩)
  have hEI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at hEI
  rw [regularizedSlab_error_identity hepsilon hH.le hS,
    abs_mul, abs_neg, abs_of_nonneg hrho]
  calc
    _ ≤ rho*((3*Real.pi*S^2/H)*(S+S)) := mul_le_mul_of_nonneg_left hEI hrho
    _ = _ := by ring

/-- The actual singular finite-slab potential has the quadratic profile,
with a uniform error controlled by its finite horizontal extent. -/
theorem slabPotential_axis_error {rho H S z : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-
      2*Real.pi*rho*z^2| ≤ 6*Real.pi*rho*S^3/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hzlim := regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint z)
  have hzero : slabAxisPoint 0 = 0 := by ext i; fin_cases i <;> rfl
  have h0lim : Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0))
      atTop (𝓝 (slabPotential rho H S 0)) := by
    simpa only [hzero] using
      regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint 0)
  have hplim := (slabRegularizedProfile_tendsto hS hz heps).const_mul (2*Real.pi*rho)
  have hlim : Tendsto (fun n => |regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint z)-
      regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile (epsilon n) S z|) atTop
      (𝓝 |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-2*Real.pi*rho*z^2|) :=
    ((hzlim.sub h0lim).sub hplim).abs
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n =>
    regularizedSlab_confinement_error (hep n).ne' hrho hH hS hz)

/-- Global capped-quadratic confinement in the physical vertical coordinate. -/
theorem slabPotential_confinement {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) :
    2*Real.pi*rho*min ((y 2)^2) (S^2)-6*Real.pi*rho*S^3/H ≤
      slabPotential rho H S y-slabPotential rho H S 0 := by
  let t : ℝ := min |y 2| S
  have ht0 : 0 ≤ t := le_min (abs_nonneg _) hS
  have htS : |t| ≤ S := by rw [abs_of_nonneg ht0]; exact min_le_right _ _
  have hty : |t| ≤ |y 2| := by rw [abs_of_nonneg ht0]; exact min_le_left _ _
  have ht2 : t^2 = min ((y 2)^2) (S^2) := by
    by_cases h : |y 2| ≤ S
    · have hs : (y 2)^2 ≤ S^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hS).mpr h
      simp only [t, min_eq_left h, sq_abs, min_eq_left hs]
    · have hs : S^2 ≤ (y 2)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hS (abs_nonneg _)).mpr (le_of_not_ge h)
      simp only [t, min_eq_right (le_of_not_ge h), min_eq_right hs]
  have haxis : slabPotential rho H S (slabAxisPoint t) ≤
      slabPotential rho H S (slabAxisPoint (y 2)) := by
    apply slabPotential_coordinate_monotone hrho hH.le hS _ _ 2
    · intro j
      fin_cases j <;> rfl
    · exact hty
  have h0 := slabPotential_coordinate_min hrho hH.le hS y 0
  have h1 := slabPotential_coordinate_min hrho hH.le hS (zeroPositionCoordinate 0 y) 1
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hmono := haxis.trans (h1.trans h0)
  have herr := (abs_le.mp (slabPotential_axis_error hrho hH hS htS)).1
  rw [ht2] at herr
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedSlabLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global comparison of the actual manufactured Coulomb field with the
separable capped oscillator and planar wells. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlabPotential_lower {rho H S freq scale δ : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hscale : 0 ≤ scale)
    (hfreq : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 +
      verticalCapPotential freq S (positionSplitCoordinates x).2 -
      (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have hs := slabPotential_confinement hrho hH hS x
  have hw := manufacturedWellField_lower freq hscale S u hsep hδ hcoeff x
  have he : verticalCapPotential freq S (positionSplitCoordinates x).2 =
      2*Real.pi*rho*min ((x 2)^2) (S^2) := by
    rw [verticalCapPotential,hfreq,positionSplitCoordinates_snd]
    ring
  rw [he]
  unfold manufacturedSlabPotential
  linarith

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearPerturbedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complement elimination with the actual singular nuclear error form.
The general form error enters quadratically through its mixed term. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem nuclearPerturbed_coercive_complement {n : ℕ} (hn : 1 ≤ n)
    (V : Configuration n → ℝ) (F : Position → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (q : Coulomb.H1Vector n) (E a g₀ g : ℝ)
    (herror : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖q.value s x‖^2) ≤
      B*((∫ x, ‖q.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖q.gradient s (i,k) x‖^2))
    (hgap : g₀*(Coulomb.mass q+2*Coulomb.kinetic q) ≤
      boundedPotentialForm V q-E*Coulomb.mass q)
    (hsmall : B*n+|a|+g ≤ g₀) :
    (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤
      nuclearPerturbedForm V F q := by
  have he := (abs_le.mp (nuclearErrorEnergy_graph_bound hn F hB q herror)).1
  have hm := Coulomb.mass_nonneg q
  have hk := Coulomb.kinetic_nonneg q
  have hgraph : Coulomb.mass q ≤ Coulomb.mass q+2*Coulomb.kinetic q := by linarith
  have ham := mul_le_mul_of_nonneg_right (le_abs_self a) hm
  have hag := mul_le_mul_of_nonneg_left hgraph (abs_nonneg a)
  have hs := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ Coulomb.mass q+2*Coulomb.kinetic q by positivity)
  unfold nuclearPerturbedForm
  nlinarith only [he,hgap,ham,hag,hs]

end ContinuumCoulomb

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedNuclearError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite basis correction of the actual nuclear error form. Only
polynomially many orbital matrix entries are summed. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedLinearOrbital_weighted_integrable (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x)) (a b : Fin m → ℝ) :
    Integrable (fun x => F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*
      (F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) :=
    (hI i j).const_mul _
  have he (x : Position) : F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x =
      ∑ i, ∑ j, (a i*b j)*(F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x) := by
    simp only [localizedLinearOrbital,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ShiftedPhysicalForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact energy offset between the manufactured form and the physical
Coulomb Hamiltonian. All identities hold on the full weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem nuclearPerturbedForm_physical_identity {M n : ℕ}
    (nuc : Coulomb.Nuclei M) (W F : Position → ℝ) (scale offset : ℝ)
    (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
    (w : Coulomb.H1Vector n) (hI : nuclearFormIntegrable F w) :
    nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w =
      Coulomb.kinetic w-scale⁻¹*Coulomb.nuclearEnergy nuc w-
        (n:ℝ)*offset*Coulomb.mass w := by
  have hpoint (s : SpinConfiguration n) (x : Configuration n) :
      (∑ i, W (Coulomb.position x i))*‖w.value s x‖^2 =
        -scale⁻¹*((∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)-
        (n:ℝ)*offset*‖w.value s x‖^2-
        ∑ i, F (Coulomb.position x i)*‖w.value s x‖^2 := by
    have he (i : Fin n) : W (Coulomb.position x i) =
        -scale⁻¹*Coulomb.attraction nuc (Coulomb.position x i)-offset-F (Coulomb.position x i) := by
      linarith only [hsplit (Coulomb.position x i)]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hi (s : SpinConfiguration n) :
      (∫ x, (∑ i, W (Coulomb.position x i))*‖w.value s x‖^2)+
        ∑ i, ∫ x, F (Coulomb.position x i)*‖w.value s x‖^2 =
      -scale⁻¹*(∫ x, (∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)-
        (n:ℝ)*offset*(∫ x, ‖w.value s x‖^2) := by
    simp_rw [hpoint]
    have ha : Integrable (fun x => -scale⁻¹*
        ((∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)) :=
      (w.nuclear_integrable nuc s).const_mul _
    have hb : Integrable (fun x => (n:ℝ)*offset*‖w.value s x‖^2) :=
      (w.value_L2 s).norm.integrable_sq.const_mul _
    have hc : Integrable (fun x => ∑ i, F (Coulomb.position x i)*‖w.value s x‖^2) :=
      integrable_finsetSum _ (fun i _ => hI s i)
    have hsub := integral_sub (ha.sub hb) hc
    have hsub' := integral_sub ha hb
    simp only [Pi.sub_apply] at hsub hsub'
    rw [hsub,hsub',
      integral_const_mul,integral_const_mul,
      integral_finsetSum _ (fun i _ => hI s i)]
    ring
  unfold nuclearPerturbedForm boundedPotentialForm nuclearErrorEnergy Coulomb.nuclearEnergy Coulomb.mass
  rw [add_assoc,← Finset.sum_add_distrib]
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

theorem dilated_physicalForm_shift {M n : ℕ}
    (nuc : Coulomb.Nuclei M) (W F : Position → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (offset : ℝ) (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
    (w : Coulomb.H1Vector n) (hI : nuclearFormIntegrable F w) :
    Coulomb.form (dilatedNuclei nuc scale (ne_of_gt hscale))
        (normalizedDilation w scale (ne_of_gt hscale)) =
      scale^2*(nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w)+(scale^2*(n:ℝ)*offset)*Coulomb.mass w := by
  rw [form_normalizedDilation nuc w hscale,
    nuclearPerturbedForm_physical_identity nuc W F scale offset hsplit w hI]
  field_simp [ne_of_gt hscale]
  ring

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

theorem gridNuclearPotential_attraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h)
    (rho : ℝ) (y : Position) :
    gridNuclearPotential index G rho h y =
      -(rho*h^3/8)*Coulomb.attraction (gridNuclei index hi G hG hh) y := by
  rw [gridNuclei_attraction]
  rfl

theorem manufactured_grid_split {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h)
    (rho H S freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hscale : rho*h^3/8=scale⁻¹) (y : Position) :
    manufacturedSlabPotential rho H S freq scale u y+
      (gridNuclearPotential index G rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)) =
      -scale⁻¹*Coulomb.attraction (gridNuclei index hi G hG hh) y-slabPotential rho H S 0 := by
  rw [gridNuclearPotential_attraction index hi G hG hh, hscale]
  unfold manufacturedSlabPotential
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOneBodyMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spinful one-body matrix is precisely the corrected spatial
matrix, repeated in the two conserved spin components. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinResidual_matrix {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (a b : Fin ((2*m+1)+1)) :
    flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        (correctedManufacturedOneBodyMatrix rho H S freq scale u (p a).1 (p b).1:ℂ) else 0 := by
  let p := (HubbardGlobal.siteModes m).symm
  have hi : Integrable (fun x => correctedLocalizedMode freq u (p a).1 x*
      correctedManufacturedResidual rho H S freq scale u (p b).1 x) :=
    (correctedLocalizedMode_memLp hf u _).integrable_mul
      (correctedManufacturedResidual_memLp hrho hH hS hf scale u hδ hcoeff _)
  have h := flatWeighted_realSpinOrbital_inner (fun _ => 1)
    (correctedLocalizedMode freq u (p a).1)
    (correctedManufacturedResidual rho H S freq scale u (p b).1)
    (by simpa only [one_mul] using hi) (p a).2 (p b).2
  simpa only [flatResidualMatrix,localizedSpinMode,localizedSpinResidual,
    correctedManufacturedOneBodyMatrix,Complex.ofReal_one,one_mul] using h

theorem localizedSpin_nuclear_integrable {freq : ℝ} {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
        Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure := by
  exact flatWeighted_realSpinOrbital_integrable F _ _ (hI _ _) _ _

theorem localizedSpin_nuclear_matrix {freq : ℝ} {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    flatNuclearMatrix (localizedSpinMode freq u) F a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        ((∫ x, F x*correctedLocalizedMode freq u (p a).1 x*
          correctedLocalizedMode freq u (p b).1 x : ℝ):ℂ) else 0 := by
  exact flatWeighted_realSpinOrbital_inner F _ _ (hI _ _) _ _

theorem localizedSpin_oneBody_matrix {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b+
      flatNuclearMatrix (localizedSpinMode freq u) F a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        (correctedNuclearOneBodyMatrix rho H S freq scale u F (p a).1 (p b).1:ℂ) else 0 := by
  rw [localizedSpinResidual_matrix hrho hH hS hf scale u hδ hcoeff,
    localizedSpin_nuclear_matrix u F hI]
  dsimp only
  split_ifs <;> simp only [correctedNuclearOneBodyMatrix,Complex.ofReal_add,add_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbardEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the actual spatial one-body error to the full spinful Hubbard
coefficient error. The off-site counterterm is kept exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

section Entries
variable {Edge : Type*} [Fintype Edge]
variable {m : ℕ} {rho H S freq scale δ ε η : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
variable (u : Fin (m+1) → PlanarPosition) (hδ : 0 ≤ δ)
variable (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
  localizedCounterterm freq u i/scale ≤ δ)
variable (F : Position → ℝ)
variable (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
  correctedLocalizedMode freq u j x))
variable (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
variable (hε : 0 ≤ ε) (hη : 0 ≤ η)
variable (hmatrix : ∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
  localizedOneBodyTarget scale freq u i j| ≤ ε)
variable (hgraph : ∀ i j, ‖(scale*planarHoppingMatrix u i j:ℂ)-
  graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ η)
include hrho hH hS hf hδ hcoeff hI hε hη hmatrix hgraph

theorem localizedSpin_hubbard_oneBody_error (a b : Fin ((2*m+1)+1)) :
    ‖(scale:ℂ)*(flatResidualMatrix (localizedSpinMode freq u)
        (localizedSpinResidual rho H S freq scale u) a b+
        flatNuclearMatrix (localizedSpinMode freq u) F a b)-
      hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ ε+η := by
  rw [localizedSpin_oneBody_matrix hrho hH hS hf scale u hδ hcoeff F hI]
  let p := (siteModes m).symm
  change ‖(scale:ℂ)*(if (p a).2=(p b).2 then _ else 0)-
    (if (p a).2=(p b).2 then _ else 0)‖ ≤ _
  by_cases hs : (p a).2=(p b).2
  · simp only [hs,ite_true, if_true]
    have he := hmatrix (p a).1 (p b).1
    have hg := hgraph (p a).1 (p b).1
    have hc : localizedOffsiteSum freq u (p a).1 =
        ∑ j, localizedOffsiteCoulomb freq u (p a).1 j := by
      rfl
    have ht : ((localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℝ):ℂ)-
        (graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1-
          if (p a).1=(p b).1 then ((∑ j, localizedOffsiteCoulomb freq u (p a).1 j:ℝ):ℂ) else 0) =
        (scale*planarHoppingMatrix u (p a).1 (p b).1:ℂ)-
          graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1 := by
      unfold localizedOneBodyTarget
      rw [hc]
      split_ifs <;> push_cast <;> ring
    calc
      _ ≤ ‖(scale:ℂ)*(correctedNuclearOneBodyMatrix rho H S freq scale u F (p a).1 (p b).1:ℂ)-
          (localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℂ)‖+
          ‖(localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℂ)-
          (graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1-
          if (p a).1=(p b).1 then ((∑ j, localizedOffsiteCoulomb freq u (p a).1 j:ℝ):ℂ) else 0)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε+η := by
        rw [ht]
        apply add_le_add _ hg
        simpa only [← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs] using he
  · simp only [hs,ite_false, if_false,mul_zero,sub_self,norm_zero]
    exact add_nonneg hε hη
end Entries

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedCoercivity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive tensor-complement gap retains kinetic coercivity. The
potential lower bound is uniform in the growing slab dimensions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem gap_kinetic_coercivity {F K M C g : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hg : 0 < g)
    (hgap : g*M ≤ F) (hkin : K-C*M ≤ F) :
    (g/(2*(C+g+1)))*(M+2*K) ≤ F := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2*(C+g+1))).2
  have h₁ := mul_le_mul_of_nonneg_left hkin (by positivity : 0 ≤ 2*g)
  have h₂ := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*(C+1))
  nlinarith only [h₁,h₂,mul_nonneg hg.le hM]

theorem planarWellSum_uniform_lower {m : ℕ} (u : Fin m → PlanarPosition)
    (x : PlanarPosition) : -(m:ℝ)*PlanarSobolev.wellBound ≤ planarWellSum u x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (x-u i))).1)
  simpa only [planarWellSum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_neg,neg_mul] using h

theorem manufacturedSlab_uniform_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (x : Position) :
    -(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have h := manufacturedSlabPotential_lower hrho hH hS.le hscale hrelation u hsep hη hcoeff x
  have hp := planarWellSum_uniform_lower u (positionSplitCoordinates x).1
  have hv : 0 ≤ verticalCapPotential freq S (positionSplitCoordinates x).2 := by
    unfold verticalCapPotential
    positivity
  have hratio : 6*Real.pi*rho*S^3/H ≤ 6*Real.pi*rho := by
    apply (div_le_iff₀ hH).2
    exact mul_le_mul_of_nonneg_left hSH (by positivity)
  linarith

theorem boundedPotentialForm_kinetic_lower {n : ℕ}
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (C : ℝ) (hC : ∀ x, -C ≤ V x) (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u-C*Coulomb.mass u ≤ boundedPotentialForm V u := by
  have hp (s : SpinConfiguration n) := integral_mono
    ((u.value_L2 s).norm.integrable_sq.const_mul (-C))
    (bounded_state_potential_integrable u V hV B hB s)
    (fun x => mul_le_mul_of_nonneg_right (hC x) (sq_nonneg ‖u.value s x‖))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s)
  simp only [integral_const_mul,← Finset.mul_sum] at h
  change (-C)*Coulomb.mass u ≤ Coulomb.potentialForm V u at h
  change Coulomb.kinetic u-C*Coulomb.mass u ≤ Coulomb.kinetic u+Coulomb.potentialForm V u
  linarith

theorem manufacturedSlab_manyElectron_kinetic_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) {n : ℕ} (v : Coulomb.H1Vector n) :
    Coulomb.kinetic v-(n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho)*Coulomb.mass v ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) v := by
  let V (x : Configuration n) := ∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  have hV : Continuous V := continuous_finsetSum _ (fun i _ =>
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
      (Coulomb.positionCLM i).continuous)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hb (x : Configuration n) : |V x| ≤ (n:ℝ)*B := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB (Coulomb.position x i)))
  apply boundedPotentialForm_kinetic_lower V hV _ hb
  intro x
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    manufacturedSlab_uniform_lower hrho hH hS hSH hscale hrelation u hsep hη hcoeff (Coulomb.position x i))
  simpa only [V,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg] using h

theorem manufacturedSlab_coercive_of_gap {rho H S freq scale η E g : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) {n : ℕ} (v : Coulomb.H1Vector n)
    (hE : 0 ≤ E) (hg : 0 < g)
    (hgap : ((n:ℝ)*E+g)*Coulomb.mass v ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) v) :
    (g/(2*((n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+E)+g+1)))*
      (Coulomb.mass v+2*Coulomb.kinetic v) ≤
    boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
      (Coulomb.position x i)) v-(n:ℝ)*E*Coulomb.mass v := by
  have hk := manufacturedSlab_manyElectron_kinetic_lower hrho hH hS hSH hscale
    hrelation u hsep hη hcoeff v
  have hC : 0 ≤ (n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+E) := by
    have hw := PlanarSobolev.wellBound_nonnegative
    positivity
  apply gap_kinetic_coercivity (Coulomb.mass_nonneg v) hC hg
  · nlinarith only [hgap]
  · nlinarith only [hk]

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

theorem nuclearFormIntegrable_of_absolute {n : ℕ} (F : Position → ℝ)
    (hF : Measurable F) (p : Coulomb.H1Vector n)
    (hI : ∀ s i, Integrable (fun x => |F (Coulomb.position x i)| * ‖p.value s x‖^2)) :
    nuclearFormIntegrable F p := by
  intro s i
  have h := (weighted_inner_pairing volume (fun x => F (Coulomb.position x i))
    (p.value s) (p.value s)
    (hF.comp (Coulomb.positionCLM i).continuous.measurable).aemeasurable
    (p.value_L2 s).aestronglyMeasurable (p.value_L2 s).aestronglyMeasurable
    (hI s i) (hI s i)).1
  simpa only [real_inner_self_eq_norm_sq] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_FormStability
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RayleighGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-mass trial vectors give upper bounds for the exact full-domain
Coulomb infimum after normalization. -/

noncomputable section
namespace ContinuumCoulomb

theorem formGroundEnergy_le_rayleigh {M n : ℕ} (S : Coulomb.Nuclei M)
    (w : Coulomb.H1Vector n) (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w) :
    formGroundEnergy S n ≤ ((Coulomb.form S w/Coulomb.mass w : ℝ):EReal) := by
  have h := formGroundEnergy_le_trial S ⟨w.normalized,hw.normalized⟩
    (Coulomb.mass_normalized w hm)
  have he : Coulomb.form S w.normalized = Coulomb.form S w/Coulomb.mass w := by
    apply (eq_div_iff (ne_of_gt hm)).mpr
    simpa only [mul_comm] using Coulomb.form_normalized_weight S w
  simpa only [he] using h

theorem formGroundEnergy_finite_of_positive_mass {M n : ℕ} (S : Coulomb.Nuclei M)
    (w : Coulomb.H1Vector n) (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w) :
    formGroundEnergy S n ≠ ⊤ ∧ formGroundEnergy S n ≠ ⊥ :=
  formGroundEnergy_finite S ⟨w.normalized,hw.normalized⟩ (Coulomb.mass_normalized w hm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_PhysicalGroundComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer manufactured-form estimates to the actual full-domain physical
ground energy. Inverse dilation covers every weak-H1 state; upper bounds use
positive-mass trial states and do not assume an attained continuum minimum. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

section PhysicalComparison
variable {M n : ℕ} (nuc : Coulomb.Nuclei M) (W F : Position → ℝ)
  {scale : ℝ} (hscale : 0 < scale) (offset : ℝ)
  (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
  (hI : ∀ w : Coulomb.H1Vector n, nuclearFormIntegrable F w)

include hsplit hI

theorem formGroundEnergy_dilated_lower (a : ℝ)
    (hbound : ∀ w : Coulomb.H1Vector n, Coulomb.Antisymmetric w →
      a*Coulomb.mass w ≤
        nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
          scale⁻¹*Coulomb.pairEnergy w) :
    ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) ≤
      formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n := by
  apply formGroundEnergy_lower_of_forall
  intro state hnorm
  change Coulomb.mass state.val=1 at hnorm
  let w := normalizedDilation state.val scale⁻¹ (inv_ne_zero hscale.ne')
  have hw : Coulomb.Antisymmetric w :=
    normalizedDilation_antisymmetric state.val state.property _ _
  have hm : Coulomb.mass w=1 :=
    (mass_normalizedDilation state.val _ _).trans hnorm
  have hinv : normalizedDilation w scale hscale.ne'=state.val := by
    simpa only [w,inv_inv] using
      normalizedDilation_inverse state.val scale⁻¹ (inv_ne_zero hscale.ne')
  have hb := mul_le_mul_of_nonneg_left (hbound w hw) (sq_nonneg scale)
  rw [hm,mul_one] at hb
  have he := dilated_physicalForm_shift nuc W F hscale offset hsplit w (hI w)
  rw [hinv,hm,mul_one] at he
  nlinarith only [hb,he]

theorem formGroundEnergy_dilated_trial (a : ℝ) (w : Coulomb.H1Vector n)
    (hw : Coulomb.Antisymmetric w) (hm : 0 < Coulomb.mass w)
    (hbound : nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
      scale⁻¹*Coulomb.pairEnergy w ≤ a*Coulomb.mass w) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n ≤
      ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) := by
  let v := normalizedDilation w scale hscale.ne'
  have hv := normalizedDilation_antisymmetric w hw scale hscale.ne'
  have hmass : Coulomb.mass v=Coulomb.mass w := mass_normalizedDilation w _ _
  have hmv : 0 < Coulomb.mass v := by rw [hmass]; exact hm
  apply (formGroundEnergy_le_rayleigh _ v hv hmv).trans
  apply EReal.coe_le_coe
  apply (div_le_iff₀ hmv).mpr
  have he := dilated_physicalForm_shift nuc W F hscale offset hsplit w (hI w)
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg scale)
  change Coulomb.form _ v = _ at he
  rw [hmass]
  nlinarith only [hb,he]

theorem formGroundEnergy_dilated_upper (a : ℝ)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ w : Coulomb.H1Vector n,
      Coulomb.Antisymmetric w ∧ 0 < Coulomb.mass w ∧
      nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w ≤ (a+ε)*Coulomb.mass w) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') n ≤
      ((scale^2*(a+(n:ℝ)*offset):ℝ):EReal) := by
  obtain ⟨w,hw,hm,_⟩ := hnear 1 zero_lt_one
  have hfin := formGroundEnergy_finite_of_positive_mass
    (dilatedNuclei nuc scale hscale.ne') (normalizedDilation w scale hscale.ne')
    (normalizedDilation_antisymmetric w hw _ _) (by
      rw [mass_normalizedDilation]; exact hm)
  have hcoe := EReal.coe_toReal hfin.1 hfin.2
  rw [← hcoe]
  apply EReal.coe_le_coe
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v,hv,hmv,hb⟩ := hnear (ε/scale^2) (div_pos hε (sq_pos_of_pos hscale))
  have hu := formGroundEnergy_dilated_trial nuc W F hscale offset hsplit hI
    (a+ε/scale^2) v hv hmv hb
  have he : scale^2*(a+ε/scale^2+(n:ℝ)*offset) = scale^2*(a+(n:ℝ)*offset)+ε := by
    field_simp [ne_of_gt hscale]
    ring
  rw [he,← hcoe] at hu
  exact EReal.coe_le_coe_iff.mp hu

end PhysicalComparison
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGroundUpper
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Hubbard variational bottom supplies admissible trials for
the full continuum problem, including the exact physical energy offset. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal Laughlin.Fock

section LocalizedUpper
variable (hdensity : PublishedSobolevSmoothDensity)
variable {Edge : Type*} [Fintype Edge]
variable {n m : ℕ} {rho H S freq scale δ D εK : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hf : 0 < freq)
variable (hrelation : freq^2=4*Real.pi*rho) (hscale : 0 < scale)
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
  hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ εK)
variable (hI : ∀ w : Coulomb.H1Vector (n+2), nuclearFormIntegrable F w)
variable (hNelec : n+2=m+1)

include hdensity hrho hH hS hf hrelation hscale hsep hs hδ hcoeff hN hK hI hNelec

theorem localized_hubbard_physical_upper {M : ℕ} (nuc : Coulomb.Nuclei M)
    (offset : ℝ)
    (hsplit : ∀ y, manufacturedSlabPotential rho H S freq scale u y+F y =
      -scale⁻¹*Coulomb.attraction nuc y-offset) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') (n+2) ≤
      ((scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+offset)+
        scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
          localizedHubbardFormError m freq D εK):ℝ):EReal) := by
  have hu := formGroundEnergy_dilated_upper nuc (manufacturedSlabPotential rho H S freq scale u)
    F hscale offset hsplit hI
    ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+
      (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
        localizedHubbardFormError m freq D εK)/scale)
    (localized_hubbard_near_trial hdensity hrho hH hS hf hrelation hscale u hsep hs
      hδ hcoeff F hN left right t hK hI hNelec)
  convert hu using 2
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_add,Nat.cast_ofNat]
  field_simp [ne_of_gt hscale]
  ring

end LocalizedUpper
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedTensorCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform kinetic coercivity on the actual spinful tensor complement. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_tensorComplement_coercivity
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
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
      ((γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1)))*
        (Coulomb.mass q+2*Coulomb.kinetic q) ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) q-(n+1:ℕ)*((-1/2:ℝ)+freq/2)*Coulomb.mass q := by
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_uniform_tensorComplement_gap hp hv hdensity hfreq hrho hrelation
  refine ⟨γ,R,S₀,δ,max C 1,hγ,hγsmall,hR,hS₀,hδ,le_max_right _ _,
    fun m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall v ha => ?_⟩
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSbase : S^3 ≤ max C 1*S^3 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right C 1)
      (pow_nonneg hSpos.le 3)
  have hSH : S^3 ≤ H := hSbase.trans hCH
  have hCH' : C*S^3 ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hSpos.le 3)).trans hCH
  have hsep₂ (i j : Fin (m+1)) (hij : i≠j) : 2 ≤ ‖u i-u j‖ :=
    (by linarith : 2 ≤ D).trans (hsep i j hij)
  have hg := hgap m n D S H scale r ε η hD hm hS hH hCH' hscale hr hrH hrS
    hε hη hηδ u hsep hcoeff herr hsmall v ha
  exact manufacturedSlab_coercive_of_gap hrho hHpos hSpos hSH hscale hrelation
    u hsep₂ hη hcoeff _ (by linarith) (by positivity) hg

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedNuclearComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured orbital space retains full-domain complement
control after a singular nuclear perturbation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_nuclear_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
    ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ F : Position → ℝ, Measurable F → ∀ B : ℝ, 0 ≤ B →
      (∀ (z : Coulomb.H1Vector (n+1)) s i,
        Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
          B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2)) →
      ∀ w : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric w →
      let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
      let p := finiteTensorProjection (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) w
      let V : Configuration (n+1) → ℝ := fun x => ∑ i,
        manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
      let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
      let e : ℝ := 2*(n+1:ℝ)*ε
      let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+e
      let g₀ : ℝ := (γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      ∀ a g t : ℝ, 0 < g → 0 ≤ t → B*(n+1)+|a|+g ≤ g₀ →
      (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
      (E+a-3*(e^2+t^2*(8*(n+1:ℝ)^3*K)+B^2*((n+1:ℝ)+2*K)*(n+1))/g)*Coulomb.mass w ≤
        nuclearPerturbedForm V F w+t*Coulomb.pairEnergy w := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,_hC,hgap⟩ :=
    manufacturedSlab_uniform_tensorComplement_coercivity hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,max C 1,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,
    le_max_right _ _,?_⟩
  intro m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall
    F hF B hB herror w hw
  dsimp only
  intro a g t hg ht hsmallB hfinite
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hCCH : C*S^3 ≤ H := (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)).trans hCH
  have hSH : S^3 ≤ H := by
    have h := mul_le_mul_of_nonneg_right (le_max_right C 1) (show 0 ≤ S^3 by positivity)
    simpa only [one_mul] using h.trans hCH
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hD₂ : 2 ≤ D := by linarith only [hR,le_max_left R R₂,hD]
  let p := finiteTensorProjection (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let q := finiteTensorRemainder (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let V : Configuration (n+1) → ℝ := fun x => ∑ i,
    manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
  let e : ℝ := 2*(n+1:ℝ)*ε
  have he : 0 ≤ e := by dsimp [e]; positivity
  have herr' : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ e^2 := by
    have h := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2*(n+1:ℝ)^2 by positivity)
    dsimp [e]
    nlinarith only [h,sq_nonneg ((n+1:ℝ)*ε)]
  have hcoercive := hgap m n D S H scale r ε η ((le_max_left _ _).trans hD) hm hS hH hCCH
    hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall w hw
  have hsmallB' : B*(n+1:ℕ)+|a|+g ≤
      (γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hsmallB
  have hcomp := nuclearPerturbed_coercive_complement (show 1 ≤ n+1 by omega)
    V F hB q E a _ g (fun s i => (herror q s i).2) (by simpa only [E,V,q,Nat.cast_add,Nat.cast_one] using hcoercive) hsmallB'
  have h := manufacturedTensor_nuclear_interacting_lower hdensity hrho hHp hSp hSH hfreq hrelation
    hr hrH hrS scale hscale u hD₂ hsep hs hη hcoeff he herr' F hF B hB herror w a g t hg ht hfinite hcomp
  simpa only [e,Nat.cast_add,Nat.cast_one] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedHubbardComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Hubbard lower bound passes through the full continuum
complement estimate. The only spectral and domain inputs here are the
explicit published planar, oscillator, and smooth-density propositions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufacturedSlab_uniform_hubbard_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
    ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 < scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ F : Position → ℝ, Measurable F → ∀ B : ℝ, 0 ≤ B →
      (∀ (z : Coulomb.H1Vector (n+2)) s i,
        Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
          B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2)) →
      ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ) (εK : ℝ),
      (∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
        (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
          Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure) →
      (∀ a b, ‖(scale:ℂ)*(flatResidualMatrix (localizedSpinMode freq u)
          (localizedSpinResidual rho H S freq scale u) a b+
          flatNuclearMatrix (localizedSpinMode freq u) F a b)-
        hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ εK) →
      n+2=m+1 → ∀ w : Coulomb.H1Vector (n+2), Coulomb.Antisymmetric w →
      let A := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
        localizedHubbardFormError m freq D εK
      let V : Configuration (n+2) → ℝ := fun x => ∑ i,
        manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
      let E : ℝ := (n+2:ℝ)*((-1/2:ℝ)+freq/2)
      let e : ℝ := 2*(n+2:ℝ)*ε
      let K : ℝ := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+e
      let g₀ : ℝ := (γ/8)/(2*((n+2:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      ∀ g : ℝ, 0 < g → B*(n+2)+|A/scale|+g ≤ g₀ →
      (E+A/scale-3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+
        B^2*((n+2:ℝ)+2*K)*(n+2))/g)*Coulomb.mass w ≤
        nuclearPerturbedForm V F w+scale⁻¹*Coulomb.pairEnergy w := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hbase⟩ :=
    manufacturedSlab_uniform_nuclear_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,?_⟩
  intro m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ
    u hsep hcoeff herr hsmall F hF B hB herror Edge inst left right t εK hN hK hNe w hw
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
    left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
      localizedHubbardFormError m freq D εK
  dsimp only
  intro g hg hsmallB
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  let p := finiteTensorProjection (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) w
  have hc : Laughlin.Antisymmetric (Coulomb.orbitalCoefficient w (localizedSpinMode freq u)) := by
    intro i j hij a
    simpa only [Equiv.Perm.sign_swap hij,Units.val_neg,Units.val_one,
      Int.cast_neg,Int.cast_one,neg_one_mul] using
      Coulomb.orbitalCoefficient_antisymmetric hw (localizedSpinMode freq u) (Equiv.swap i j) a
  have hfinite := localizedTensor_hubbard_lower hdensity hrho hHp hSp hf hrelation hscale u hsep hs
    hη hcoeff F hN left right t hK (Coulomb.orbitalCoefficient w (localizedSpinMode freq u))
    hc
    (nuclearFormIntegrable_of_absolute F hF p (fun s i => (herror p s i).1)) hNe
  have hfinite' : ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale)*Coulomb.mass p ≤
      nuclearPerturbedForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) F p+scale⁻¹*Coulomb.pairEnergy p := by
    apply (mul_le_mul_iff_right₀ hscale).mp
    have hcancel : A/scale*scale=A := div_mul_cancel₀ A (ne_of_gt hscale)
    have he : scale*(((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale)*Coulomb.mass p) =
        (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+A)*Coulomb.mass p := by
      calc
        _ = (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+(A/scale*scale))*Coulomb.mass p := by ring
        _ = _ := by rw [hcancel]
    rw [he]
    dsimp only [A, p, finiteTensorProjection]
    convert hfinite using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hncast : ((n:ℝ)+1)+1=(n:ℝ)+2 := by ring
  have hout := hbase m (n+1) D S H scale r ε η ((le_max_left _ _).trans hD)
    hm hS hH hCH hscale.le hr hrH hrS hε hη hηδ u hsep hcoeff herr
    (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall) F hF B hB herror w hw
    (A/scale) g scale⁻¹ hg (inv_nonneg.mpr hscale.le)
    (by simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hsmallB)
    (by simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hfinite')
  simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hout

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGridGroundComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transported unit-charge cloud has two-sided physical ground
bounds obtained from the full-domain lower estimate and localized trials. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_grid_ground_bounds_oai
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2=4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
    ∀ (m n : ℕ) (D S H scale r ε η εM εG : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      ∀ hscale : 0 < scale, 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      0 ≤ εM → 0 ≤ εG →
    ∀ (u : Fin (m+1) → PlanarPosition), (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
      (G : Position → Position) (hG : Function.Injective G) (h : ℝ) (hh : 0 < h), rho*h^3/8=scale⁻¹ →
    ∀ B : ℝ, 0 ≤ B →
      (∀ (w : Coulomb.H1Vector (n+2)) s i,
        Integrable (fun x => |manufacturedGridError index G rho H S freq scale h u (Coulomb.position x i)| * ‖w.value s x‖^2) ∧
        (∫ x, |manufacturedGridError index G rho H S freq scale h u (Coulomb.position x i)| * ‖w.value s x‖^2) ≤
          B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) →
      (∀ i j, Integrable (fun x => manufacturedGridError index G rho H S freq scale h u x*
        continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) →
      (∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u
        (manufacturedGridError index G rho H S freq scale h u) i j-localizedOneBodyTarget scale freq u i j| ≤ εM) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∀ i j, ‖(scale*planarHoppingMatrix u i j:ℂ)-graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ εG) →
      n+2=m+1 →
      let Hb := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t
      let Vsum := (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)
      let Eform := localizedHubbardFormError m freq D (εM+εG)
      let A := Hb-Vsum-Eform
      let e := 2*(n+2:ℝ)*ε
      let K := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+e
      let g₀ := (γ/8)/(2*((n+2:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+scale*(Hb-Vsum)
      ∀ g : ℝ, 0 < g → B*(n+2)+|A/scale|+g ≤ g₀ →
      let I := 3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+B^2*((n+2:ℝ)+2*K)*(n+2))/g
      ((center-scale*Eform-scale^2*I:ℝ):EReal) ≤
        formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ∧
      formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ≤
        ((center+scale*Eform:ℝ):EReal) := by
  obtain ⟨γ,R,S₀,δ,C,hγ,hγ1,hR,hS₀,hδ,hC,hlower⟩ :=
    manufacturedSlab_uniform_hubbard_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγ1,hR.trans (le_max_left _ _),hS₀,hδ,hC,?_⟩
  intro m n D S H scale r ε η εM εG hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ hεM hεG
    u hsep hcoeff herr hsmall ι _ _ index hindex G hG h hh hmatch B hB hfull hraw hmatrix Edge _ left right t hgraph hNe
  dsimp only
  intro g hg hsmallB
  let F := manufacturedGridError index G rho H S freq scale h u
  let Hb := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t
  let Vsum := (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)
  let Eform := localizedHubbardFormError m freq D (εM+εG)
  let A := Hb-Vsum-Eform
  let e := 2*(n+2:ℝ)*ε
  let K := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+e
  let I := 3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+B^2*((n+2:ℝ)+2*K)*(n+2))/g
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+scale*(Hb-Vsum)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hcorr (i j : Fin (m+1)) : Integrable (fun x => F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) :=
    localizedLinearOrbital_weighted_integrable freq u F hraw _ _
  have hN := localizedSpin_nuclear_integrable u F hcorr
  have hK := localizedSpin_hubbard_oneBody_error hrho hHp.le hSp.le hf u hη hcoeff F hcorr
    left right t hεM hεG hmatrix hgraph
  have hF : Measurable F := (gridNuclearPotential_measurable index G rho h).sub
    (((slabPotential_continuous hrho hHp.le hSp.le).add (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  have hI (w : Coulomb.H1Vector (n+2)) : nuclearFormIntegrable F w :=
    nuclearFormIntegrable_of_absolute F hF w (fun s i => (hfull w s i).1)
  have hsplit := manufactured_grid_split index hindex G hG hh rho H S freq scale u hmatch
  have hl (w : Coulomb.H1Vector (n+2)) (hw : Coulomb.Antisymmetric w) :
      ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I)*Coulomb.mass w ≤
      nuclearPerturbedForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w :=
    hlower m n D S H scale r ε η ((le_max_left _ _).trans hD) hm hS hH hCH hscale hr hrH hrS hε hη hηδ
      u hsep hcoeff herr hsmall F hF B hB hfull left right t (εM+εG) hN hK hNe w hw g hg hsmallB
  have hlphys := formGroundEnergy_dilated_lower (gridNuclei index hindex G hG hh)
    (manufacturedSlabPotential rho H S freq scale u) F hscale (slabPotential rho H S 0) hsplit hI
    ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I) hl
  have huphys := localized_hubbard_physical_upper hdensity hrho hHp hSp hf hrelation hscale u hsep hs hη hcoeff
    F hN left right t hK hI hNe (gridNuclei index hindex G hG hh) (slabPotential rho H S 0) hsplit
  simp only [Nat.cast_add,Nat.cast_ofNat] at hlphys huphys
  constructor
  · have hid : scale^2*(((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I)+(n+2:ℝ)*slabPotential rho H S 0) =
        center-scale*Eform-scale^2*I := by dsimp [center,A]; field_simp [ne_of_gt hscale]; ring
    rw [hid] at hlphys
    exact hlphys
  · have hid : scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+slabPotential rho H S 0)+
        scale*(Hb-Vsum+Eform) = center+scale*Eform := by dsimp [center]; ring
    change formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ≤
      ((scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+slabPotential rho H S 0)+
        scale*(Hb-Vsum+Eform):ℝ):EReal) at huphys
    rw [hid] at huphys
    exact huphys

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufactured_grid_ground_bounds_oai := @OAI.ContinuumCoulomb.manufactured_grid_ground_bounds_oai
