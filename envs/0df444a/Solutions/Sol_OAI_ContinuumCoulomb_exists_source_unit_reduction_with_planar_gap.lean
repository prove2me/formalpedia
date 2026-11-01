-- Prove2me | solution 1 for OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:51:21.722471+00:00
-- url     : https://prove2.me/submissions/f85d566b-412e-4976-a4d6-0a4b4d0398ef

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
import Theorems.Thm_OAI_ContinuumCoulomb_ContactCalibratedGeometry_separation
import Theorems.Thm_OAI_ContinuumCoulomb_PrefactorSourceContactProgram_exists_source_calibration
import Theorems.Thm_OAI_ContinuumCoulomb_SourceNuclearProgram_exists_indexed_matrix_offsets
import Theorems.Thm_OAI_ContinuumCoulomb_SourceUnitCoulomb_promise_of_hubbard_interval
import Theorems.Thm_OAI_ContinuumCoulomb_exists_source_target_parameters
import Theorems.Thm_OAI_ContinuumCoulomb_source_cloud_comparison

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

lemma kinetic_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ kinetic ψ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

lemma mass_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    mass (ψ.rsmul t) = t^2 * mass ψ := by
  unfold mass H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, Finset.mul_sum]

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit prefix-free binary encodings for finite source and circuit data.
Natural numbers use their binary digits, with one marker bit per digit.
Pairs concatenate; lists have a binary length header. In particular, list
serialization does not repeatedly pair large natural-number codes. -/

namespace ContinuumCoulomb
namespace BinaryEncoding

theorem list_length {α : Type*} (a : Codec α) (xs : List α) :
    ((list a).encode xs).length = 2 * xs.length.size + 1 +
      (xs.map (fun x => (a.encode x).length)).sum := by
  simp only [list, List.length_append, natural_length, List.length_flatMap]

end BinaryEncoding
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_IsolatedForms
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolated-well energy forms on the actual weak H¹ domain

The perturbation bounds here concern the full one-electron form, including
both Coulomb poles and the capped background. They give the shifted relative
form comparison used before constructing isolated eigenfunctions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem singlePoleEnergy_bound (a : Position) (state : Coulomb.H1Vector 1)
    {eta : ℝ} (heta : 0 < eta) :
    singlePoleEnergy a state ≤ 8 * eta * Coulomb.kinetic state +
      (1 / (4 * eta)) * Coulomb.mass state := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun spin _ =>
    (state.nuclear_coulomb_integrable_bound spin 0 a heta).2
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Coulomb.kinetic, Coulomb.mass,
    Fintype.sum_prod_type, Fin.sum_univ_one]
  ring

theorem hydrogenForm_coercive (a : Position) (state : Coulomb.H1Vector 1) :
    Coulomb.kinetic state / 2 - 4 * Coulomb.mass state ≤ hydrogenForm a state := by
  have h := singlePoleEnergy_bound a state (by norm_num : (0 : ℝ) < 1 / 16)
  norm_num at h
  unfold hydrogenForm
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronTrial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete normalized weak-H¹ trial, independent of all nuclear data. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronBumpState_mass_pos : 0 < Coulomb.mass oneElectronBumpState := by
  have hzero : (fun t : ℝ => t ^ 2) 0 = 0 := zero_pow (by decide)
  have hc : HasCompactSupport (fun x : Configuration 1 => oneElectronBump x ^ 2) :=
    oneElectronBump.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) hzero
  have hI : Integrable (fun x : Configuration 1 => oneElectronBump x ^ 2) :=
    (oneElectronBump.continuous.pow 2).integrable_of_hasCompactSupport hc
  have hb0 : oneElectronBump (0 : Configuration 1) = 1 :=
    oneElectronBump.one_of_mem_closedBall (by simp [oneElectronBump])
  have hpos : 0 < ∫ x : Configuration 1, oneElectronBump x ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero (oneElectronBump.continuous.pow 2)
      hI (fun _ => sq_nonneg _) (by rw [hb0]; norm_num)
  have hmass : Coulomb.mass oneElectronBumpState =
      (Fintype.card (Coulomb.Spins 1) : ℝ) * ∫ x : Configuration 1, oneElectronBump x ^ 2 := by
    simp only [Coulomb.mass, oneElectronBumpState, Coulomb.H1Vector.ofSmoothCompact,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hmass]
  exact mul_pos (by norm_num [Coulomb.Spins]) hpos

theorem oneElectronTrial_mass : Coulomb.mass oneElectronTrial = 1 := by
  rw [oneElectronTrial, Coulomb.mass_rsmul, inv_pow,
    Real.sq_sqrt oneElectronBumpState_mass_pos.le,
    inv_mul_cancel₀ oneElectronBumpState_mass_pos.ne']

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_IsolatedSpectrum
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the unrestricted isolated-well variational bottom

All infima range over normalized spinful weak-H¹ states. The estimates use
form comparison and a concrete normalized bump trial; no eigenfunction, attainment, or
spectral oracle is supplied as an assumption.
-/

noncomputable section
namespace ContinuumCoulomb

theorem oneElectronEnergy_le_trial (form : Coulomb.H1Vector 1 → ℝ)
    (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
    oneElectronEnergy form ≤ (form state : EReal) :=
  sInf_le ⟨state, hnorm, rfl⟩

theorem oneElectronEnergy_lower_of_forall (form : Coulomb.H1Vector 1 → ℝ) (a : ℝ)
    (ha : ∀ state : Coulomb.H1Vector 1, Coulomb.mass state = 1 → a ≤ form state) :
    (a : EReal) ≤ oneElectronEnergy form := by
  apply le_sInf
  rintro e ⟨state, hnorm, rfl⟩
  exact EReal.coe_le_coe (ha state hnorm)

theorem oneElectronEnergy_finite (form : Coulomb.H1Vector 1 → ℝ)
    (trial : Coulomb.H1Vector 1) (htrial : Coulomb.mass trial = 1) (a : ℝ)
    (ha : ∀ state : Coulomb.H1Vector 1, Coulomb.mass state = 1 → a ≤ form state) :
    oneElectronEnergy form ≠ ⊤ ∧ oneElectronEnergy form ≠ ⊥ := by
  exact ⟨ne_of_lt ((oneElectronEnergy_le_trial form trial htrial).trans_lt
    (EReal.coe_lt_top _)),
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (oneElectronEnergy_lower_of_forall form a ha))⟩

theorem hydrogenEnergy_finite (a : Position) : hydrogenEnergy a ≠ ⊤ ∧ hydrogenEnergy a ≠ ⊥ := by
  apply oneElectronEnergy_finite (hydrogenForm a) oneElectronTrial oneElectronTrial_mass (-4)
  intro state hnorm
  have h := hydrogenForm_coercive a state
  rw [hnorm] at h
  linarith [Coulomb.kinetic_nonneg state]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AtomicOutputs
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed one-electron outputs for the decidable one-spin source branch.
The only spectral input is the precisely stated published hydrogen bottom. -/

noncomputable section
namespace ContinuumCoulomb
open MeasureTheory

theorem oneElectron_antisymmetric (w : Coulomb.H1Vector 1) : Coulomb.Antisymmetric w := by
  intro p s
  have hp : p=1 := Subsingleton.elim _ _
  subst p
  filter_upwards [] with x
  have hx : Coulomb.permute (1 : Equiv.Perm (Fin 1)) x=x := by ext i; rfl
  simp [hx]

theorem atomic_form (w : FormState 1) : unitCoulombForm atomicData w = hydrogenForm 0 w.val := by
  have ha (y : Position) : Coulomb.attraction atomicData.toNuclearData.toNuclei y =
      Coulomb.coulombKernel y := by
    unfold Coulomb.attraction
    erw [Fin.sum_univ_one]
    have hr : realPosition (0 : Fin 3 → ℚ)=0 := by ext i; simp [realPosition]
    simp only [atomicData,UnitNuclearData.toNuclearData,NuclearData.toNuclei,
      Nat.cast_one,hr,sub_zero,one_mul]
  have hp : Coulomb.pairEnergy w.val=0 := by simp [Coulomb.pairEnergy]
  change Coulomb.kinetic w.val-Coulomb.nuclearEnergy atomicData.toNuclearData.toNuclei w.val+
    Coulomb.pairEnergy w.val = hydrogenForm 0 w.val
  simp only [hp,add_zero,Coulomb.nuclearEnergy,ha,Fin.sum_univ_one,
    hydrogenForm,singlePoleEnergy,sub_zero]

theorem atomic_ground : unitGroundEnergy atomicData = hydrogenEnergy 0 := by
  unfold unitGroundEnergy hydrogenEnergy oneElectronEnergy
  congr 1
  ext e
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.val,hw,congrArg (fun t : ℝ => (t:EReal)) (atomic_form w)⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨w,oneElectron_antisymmetric w⟩,hw,
      congrArg (fun t : ℝ => (t:EReal)) (atomic_form ⟨w,oneElectron_antisymmetric w⟩).symm⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteAtomicOutputs
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed YES and NO instances need only finiteness of the atomic energy.
No hydrogen spectral formula is needed for this branch of the reduction. -/

noncomputable section
namespace ContinuumCoulomb

theorem atomicThresholdOutput_valid (z : ℤ) : (atomicThresholdOutput z).Valid := by
  refine ⟨by change 0<1; decide,by change 0<1; decide,?_,?_,?_,?_,?_⟩
  · intro i
    change Fin 1 at i
    fin_cases i
    change (0:ℕ)<1 ∧ (0:ℕ)<1 ∧ (0:ℕ)<1
    decide
  · intro i j _
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change i.val<1 at hi
    change j.val<1 at hj
    omega
  · exact Rat.den_pos _
  · exact Rat.den_pos _
  · simp only [atomicThresholdOutput,BinaryRational.value_ofRat]
    norm_num

theorem atomicThresholdOutput_data (z : ℤ) (h : (atomicThresholdOutput z).Valid) :
    (atomicThresholdOutput z).toData h = atomicData := by
  unfold UnitCoulomb.toData atomicThresholdOutput atomicData
  congr 1
  funext i
  fin_cases i
  ext j
  fin_cases j <;> norm_num [BinaryPosition.value]

theorem exists_atomic_yes_no : ∃ y z : UnitCoulomb,
    y ∈ unitCoulombPromise.yes ∧ z ∈ unitCoulombPromise.no := by
  let E := (hydrogenEnergy 0).toReal
  have hE : (E : EReal)=hydrogenEnergy 0 :=
    EReal.coe_toReal (hydrogenEnergy_finite 0).1 (hydrogenEnergy_finite 0).2
  refine ⟨atomicThresholdOutput ⌈E⌉,atomicThresholdOutput (⌊E⌋-1),?_,?_⟩
  · refine ⟨atomicThresholdOutput_valid _,?_⟩
    rw [atomicThresholdOutput_data,atomic_ground,← hE]
    simpa only [atomicThresholdOutput,BinaryRational.value_ofRat,Rat.cast_intCast] using
      EReal.coe_le_coe (Int.le_ceil E)
  · refine ⟨atomicThresholdOutput_valid _,?_⟩
    rw [atomicThresholdOutput_data,atomic_ground,← hE]
    have hfloor : (⌊E⌋:ℝ)-1+1 ≤ E := by linarith [Int.floor_le E]
    simpa only [atomicThresholdOutput,BinaryRational.value_ofRat,Rat.cast_intCast,
      Rat.cast_add,Rat.cast_sub,Rat.cast_one,Int.cast_sub,Int.cast_one] using EReal.coe_le_coe hfloor

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorListCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete TM2 bond lists are exactly the enumerations of the finite
spin matrices whose three-stage bottom-energy estimates were proved. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

theorem Bonds.toList_get {n r : ℕ} (F : Bonds n r) (i : ℕ) (hi : i < r) :
    (F.toList.drop i).headD MediatorListProgram.zeroBond =
      ((F.left ⟨i, hi⟩).val, (F.right ⟨i, hi⟩).val, F.weight ⟨i, hi⟩) := by
  simp only [List.headD_eq_head?_getD, List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some, Bonds.toList, List.getElem_ofFn]

theorem lift_toList {n q : ℕ} (r : ℕ) (F : Bonds n q) : (lift r F).toList = F.toList := by
  unfold Bonds.toList
  congr 1

theorem join_toList {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) :
    (join F K).toList = F.toList ++ K.toList := by
  unfold Bonds.toList
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext e
    change ((join F K).left (Fin.castAdd r e) |>.val,
      (join F K).right (Fin.castAdd r e) |>.val, (join F K).weight (Fin.castAdd r e)) = _
    simp only [join, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · congr 1
    funext e
    simp only [join, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

theorem central_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (central n r (MediatorParameters.delta r W G : ℚ)).toList =
      MediatorListProgram.central ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp [MediatorListProgram.central]
  · intro i hi hj
    simp only [Bonds.toList, List.getElem_ofFn, MediatorListProgram.central,
      List.getElem_map, List.getElem_range, central, fresh_val, Fin.val_zero, Fin.val_one, add_zero]

theorem spokes_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))).toList =
      MediatorListProgram.spokes ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp only [Bonds.toList_length, MediatorListProgram.spokes, List.length_map,
      List.length_range]
    omega
  · intro i hi hj
    have hir : i < r * 2 := by simpa only [Bonds.toList_length] using hi
    have hdiv : i / 2 < r := by omega
    let S := spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))
    change (List.ofFn (fun e => ((S.left e).val, (S.right e).val, S.weight e)))[i]'(by
      simpa only [List.length_ofFn] using hir) = _
    rw [List.getElem_ofFn]
    simp only [MediatorListProgram.spokes, List.getElem_map, List.getElem_range]
    rw [Bonds.toList_get F (i / 2) hdiv]
    dsimp only [S]
    simp only [spokes, MediatorListProgram.spoke, old_val, fresh_val]
    change ( (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then
        F.left ((⟨i, hir⟩ : Fin (r * 2)).divNat) else F.right ((⟨i, hir⟩ : Fin (r * 2)).divNat)).val,
      n + 2 * (i / 2) +
        (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then (0 : Fin 2) else member (F.weight ⟨i / 2, hdiv⟩)).val,
      MediatorParameters.spoke r W G (F.weight ⟨i / 2, hdiv⟩)) = _
    have hmod : (⟨i, hir⟩ : Fin (r * 2)).modNat = (0 : Fin 2) ↔ i % 2 = 0 := by
      exact Fin.ext_iff
    by_cases hm : i % 2 = 0
    · simp only [hm, hmod.mpr hm, ite_true, if_true, Fin.val_zero]
      rfl
    · simp only [hm, ite_false, if_false, (not_congr hmod).mpr hm, member]
      split <;> rfl

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorFullListCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact list semantics for all three computed mediator stages and their
rational scalar offset. The emitted list is the full finite spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorListProgram MediatorUnaryProgram
open scoped BigOperators

theorem secondInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondEnv (literalInput F W G).1, MediatorListProgram.spokes (literalInput F W G)) =
      literalInput (firstSpokes F W G) (secondBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, secondEnv, secondBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (spokes_toList_input F W G).symm

theorem secondPaths_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondPaths F W G).toList =
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) := by
  rw [secondInput_literal]
  unfold secondPaths
  rw [join_toList]
  exact congrArg₂ List.append
    (central_toList_input (firstSpokes F W G) (secondBound r W G) G)
    (spokes_toList_input (firstSpokes F W G) (secondBound r W G) G)

theorem thirdInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (thirdEnv (literalInput F W G).1,
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G))) =
      literalInput (secondPaths F W G) (thirdBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, thirdEnv, thirdBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (secondPaths_toList F W G).symm

theorem finalGraph_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).toList = MediatorThreeStageProgram.finalBonds (literalInput F W G) := by
  unfold finalGraph retainedCentral
  rw [join_toList, lift_toList, lift_toList, join_toList]
  have hc1 := central_toList_input F W G
  have hc3 := central_toList_input (secondPaths F W G) (thirdBound r W G) G
  have hs3 := spokes_toList_input (secondPaths F W G) (thirdBound r W G) G
  change (firstCentral F W G).toList ++
    ((thirdCentral F W G).toList ++ (thirdSpokes F W G).toList) = _
  rw [show (firstCentral F W G).toList = MediatorListProgram.central (literalInput F W G) from hc1]
  rw [show (thirdCentral F W G).toList =
    MediatorListProgram.central (literalInput (secondPaths F W G) (thirdBound r W G) G) from hc3]
  rw [show (thirdSpokes F W G).toList =
    MediatorListProgram.spokes (literalInput (secondPaths F W G) (thirdBound r W G) G) from hs3]
  rw [← thirdInput_literal]
  simp only [MediatorThreeStageProgram.finalBonds, List.append_assoc]

theorem stageOffset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.stageOffset (literalInput F W G) =
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |F.weight e| := by
  simp only [MediatorOffsetProgram.stageOffset, literalInput, Bonds.toList,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem offset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.offset (literalInput F W G) = offset F W G := by
  unfold MediatorOffsetProgram.offset
  rw [thirdInput_literal, secondInput_literal]
  rw [stageOffset_toList, stageOffset_toList, stageOffset_toList]
  simp only [MediatorIteration.offset, deltaOne, deltaTwo, deltaThree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]

theorem bonds_toList (n : ℕ) (xs : List MediatorListProgram.Bond)
    (h : SourceBondLists.bounded n xs) : (SourceBondLists.bonds n xs h).toList = xs := by
  change List.ofFn (fun e => ((xs.get e).1, (xs.get e).2.1, (xs.get e).2.2)) = xs
  simpa only [Prod.eta] using List.ofFn_get xs

end ContinuumCoulomb.MediatorIteration

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

theorem localizedDensity_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < localizedDensity freq u x :=
  sq_pos_of_pos (continuumLocalizedMode_positive hfreq u x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ApproximateBisection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate rational bisection for a Lipschitz residual.  A numerically
ambiguous sign terminates with a certified residual bound; otherwise the
true endpoint signs are preserved.  No monotonicity or derivative lower
bound is required. -/

namespace ContinuumCoulomb.ApproximateBisection

theorem midpoint_mem (s : Interval) (h : s.lo ≤ s.hi) :
    s.lo ≤ midpoint s ∧ midpoint s ≤ s.hi := by
  dsimp [midpoint]
  constructor <;> linarith

theorem initial_invariant {a b δ : ℚ} {f : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    Invariant a b f δ (initial a b) := by
  refine ⟨le_rfl, le_rfl, hab, ?_, ?_⟩
  · simp [initial]
  · intro _
    exact ⟨ha, hb⟩

theorem step_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (_hδ : 0 ≤ δ)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    {s : Interval} (hs : Invariant a b f δ s) :
    Invariant a b f δ (step δ evaluate s) := by
  have hm := midpoint_mem s hs.ordered
  have he := abs_le.mp (heval (midpoint s) ⟨hs.lower.trans hm.1, hm.2.trans hs.upper⟩)
  unfold step
  split_ifs with hd hp hn
  · exact hs
  · have hp' : (δ : ℝ) < evaluate (midpoint s) := by exact_mod_cast hp
    refine ⟨hs.lower.trans hm.1, hs.upper, hm.2, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨by linarith [he.2], (hs.signs (by simpa using hd)).2⟩
  · have hn' : (evaluate (midpoint s) : ℝ) < -(δ : ℝ) := by exact_mod_cast hn
    refine ⟨hs.lower, hm.2.trans hs.upper, hm.1, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨(hs.signs (by simpa using hd)).1, by linarith [he.1]⟩
  · have hp' : (evaluate (midpoint s) : ℝ) ≤ δ := by exact_mod_cast le_of_not_gt hp
    have hn' : -(δ : ℝ) ≤ evaluate (midpoint s) := by exact_mod_cast le_of_not_gt hn
    refine ⟨hs.lower.trans hm.1, hm.2.trans hs.upper, le_rfl, ?_, ?_⟩
    · intro _
      refine ⟨rfl, abs_le.mpr ?_⟩
      constructor <;> linarith [he.1, he.2]
    · simp

theorem step_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    {s : Interval} (hs : Invariant a b f δ s) :
    width (step δ evaluate s) ≤ width s / 2 := by
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  unfold step
  split_ifs with hd hp hn
  · have heq := (hs.certified hd).1
    simp only [width, heq, sub_self, zero_div, le_refl]
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, sub_self]
    linarith

theorem run_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    Invariant a b f δ (run δ evaluate a b n) := by
  induction n with
  | zero => exact initial_invariant hab ha hb
  | succ n ih =>
    change Invariant a b f δ ((step δ evaluate)^[n + 1] (initial a b))
    rw [Function.iterate_succ_apply']
    exact step_invariant hδ heval ih

theorem run_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    width (run δ evaluate a b n) ≤ ((b : ℝ) - a) / 2 ^ n := by
  induction n with
  | zero => simp [run, initial, width]
  | succ n ih =>
    have hw := step_width (evaluate := evaluate) (run_invariant hδ hab ha hb heval n)
    have hrun : run δ evaluate a b (n + 1) = step δ evaluate (run δ evaluate a b n) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    calc
      width (step δ evaluate (run δ evaluate a b n)) ≤
          width (run δ evaluate a b n) / 2 := hw
      _ ≤ (((b : ℝ) - a) / 2 ^ n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = ((b : ℝ) - a) / 2 ^ (n + 1) := by rw [pow_succ, div_div]

theorem invariant_residual {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|)
    {s : Interval} (hs : Invariant a b f δ s) :
    |f (midpoint s)| ≤ 2 * (δ : ℝ) + L * width s := by
  have hl : (a : ℝ) ≤ s.lo := by exact_mod_cast hs.lower
  have hu : (s.hi : ℝ) ≤ b := by exact_mod_cast hs.upper
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  have hm := midpoint_mem s hs.ordered
  have hmlo : (s.lo : ℝ) ≤ midpoint s := by exact_mod_cast hm.1
  have hmhi : (midpoint s : ℝ) ≤ s.hi := by exact_mod_cast hm.2
  have hw : 0 ≤ width s := sub_nonneg.mpr ho
  by_cases hd : s.settled = true
  · obtain ⟨heq, herr⟩ := hs.certified hd
    have he : midpoint s = s.lo := by simp [midpoint, heq]
    rw [he]
    exact herr.trans (le_add_of_nonneg_right (mul_nonneg hL hw))
  · have hsign := hs.signs (by simpa using hd)
    have hmemb : (midpoint s : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨hl.trans hmlo, hmhi.trans hu⟩
    have hleft := hLip (midpoint s) hmemb s.lo ⟨hl, ho.trans hu⟩
    have hright := hLip (midpoint s) hmemb s.hi ⟨hl.trans ho, hu⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hmlo)] at hleft
    rw [abs_of_nonpos (sub_nonpos.mpr hmhi)] at hright
    have hlw : L * ((midpoint s : ℝ) - s.lo) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hrw : L * -((midpoint s : ℝ) - s.hi) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hδ' : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ
    apply abs_le.mpr
    constructor
    · have h := (neg_le_abs (f (midpoint s) - f s.lo)).trans hleft
      linarith [hsign.1]
    · have h := (le_abs_self (f (midpoint s) - f s.hi)).trans hright
      linarith [hsign.2]

/-- After `n` steps the returned rational has residual at most numerical
ambiguity plus the Lipschitz constant times the halved interval width. -/
theorem run_residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (midpoint (run δ evaluate a b n))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  exact (invariant_residual hδ hL hLip (run_invariant hδ hab ha hb heval n)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (run_width hδ hab ha hb heval n) hL) _)

end ContinuumCoulomb.ApproximateBisection

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionRegisters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-denominator registers for approximate bisection.  Each update
doubles the denominator and uses only addition and doubling of numerators;
therefore every register gains at most one bit per iteration. -/

namespace ContinuumCoulomb.BisectionRegisters
open ExactQuantumFactoring.BitStackProgram

theorem initial_den_pos (a b : ℚ) : 0 < (initial a b).2.2.1 :=
  Nat.mul_pos a.pos b.pos

theorem middle_eq (r : Registers) (hr : 0 < r.2.2.1) :
    middle r = ApproximateBisection.midpoint (interval r) := by
  have hd : (r.2.2.1 : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [middle, ApproximateBisection.midpoint, interval, left, right,
    Rat.mkRat_eq_div, Int.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem initial_interval (a b : ℚ) :
    interval (initial a b) = ApproximateBisection.initial a b := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have hl : left (initial a b) = a := by
    change mkRat (a.num * b.den) (a.den * b.den) = a
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den a]
    field_simp
  have hh : right (initial a b) = b := by
    change mkRat (b.num * a.den) (a.den * b.den) = b
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den b]
    field_simp
  change (⟨left (initial a b), right (initial a b), false⟩ :
    ApproximateBisection.Interval) = ⟨a, b, false⟩
  rw [hl, hh]

theorem step_den_pos (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : 0 < (step δ evaluate r).2.2.1 := by
  unfold step
  split_ifs <;> first | exact hr | exact Nat.mul_pos (by decide) hr

private theorem double_quotient (z : ℤ) (d : ℕ) (hd : 0 < d) :
    mkRat (2 * z) (2 * d) = mkRat z d := by
  have h : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Rat.mkRat_eq_div, Int.cast_mul, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem step_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : interval (step δ evaluate r) =
      ApproximateBisection.step δ evaluate (interval r) := by
  have hm : middle r = (left r + right r) / 2 := middle_eq r hr
  unfold step ApproximateBisection.step
  simp only [interval, ApproximateBisection.midpoint, ← hm]
  split_ifs <;> simp [left, right, middle, double_quotient, hr]

theorem iterate_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) (n : ℕ) :
    0 < ((step δ evaluate)^[n] r).2.2.1 ∧
      interval ((step δ evaluate)^[n] r) =
        (ApproximateBisection.step δ evaluate)^[n] (interval r) := by
  induction n with
  | zero => exact ⟨hr, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨step_den_pos δ evaluate _ ih.1, (step_interval δ evaluate _ ih.1).trans
      (congrArg (ApproximateBisection.step δ evaluate) ih.2)⟩

/-- The actual unreduced register execution satisfies the analytic residual
bound; all evaluation calls remain inside the initial rational interval. -/
theorem residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (middle ((step δ evaluate)^[n] (initial a b)))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  obtain ⟨hp, hi⟩ := iterate_interval δ evaluate (initial a b) (initial_den_pos a b) n
  rw [middle_eq _ hp, hi, initial_interval]
  exact ApproximateBisection.run_residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time bisection with a supplied polynomial-time
rational evaluator.  The evaluator environment and tolerance remain in
the input registers; they are not fixed nonuniform advice. -/

namespace ContinuumCoulomb.BisectionProgram
open ExactQuantumFactoring.BitStackProgram
open BisectionRegisters

theorem residual {E : Type} (evaluate : E → ℚ → ℚ) (e : E)
    {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate e q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (approximate evaluate (n, (e, (δ, (a, b)))))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) :=
  BisectionRegisters.residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical threshold reference for the exact half-cell boundary of the
centered grid. The finite threshold is scaled by lambda and the true rational
slab reference by lambda squared times the electron count. -/

noncomputable section
namespace ContinuumCoulomb.CenteredPhysicalThreshold

theorem gap (rho : ℕ) (x : Input) :
    (value rho x).2-(value rho x).1 = amplification rho x.1.1*(x.2.2.2.2-x.2.2.2.1) := by
  unfold value
  ring

end ContinuumCoulomb.CenteredPhysicalThreshold

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedTailConstant_nonnegative (freq : ℝ) : 0 ≤ localizedTailConstant freq :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDuality
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact local dual tests: a common positive diagonal mass,
disjoint supports and exponentially small off-site pairings. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem localizedDualPair_diagonal (freq : ℝ) (u : PlanarPosition) (χ : Position → ℝ) :
    localizedDualPair freq u u χ = ∫ x, localizedDensity freq 0 x * χ x := by
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter u)) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right]

theorem localizedDualPair_diagonal_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hn : ∀ x, 0 ≤ χ x) (h0 : 0 < χ 0) : 0 < localizedDualPair freq u u χ := by
  rw [localizedDualPair_diagonal]
  exact integral_pos_of_integrable_nonneg_nonzero
    ((localizedDensity_continuous freq 0).mul hχ)
    (((localizedDensity_continuous freq 0).mul hχ).integrable_of_hasCompactSupport hc.mul_left)
    (fun x => mul_nonneg (localizedDensity_nonnegative freq 0 x) (hn x))
    (mul_pos (localizedDensity_positive hfreq 0 0) h0).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDualMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact bumps supply local duality for the actual mode densities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localDualBump_smooth : ContDiff ℝ ∞ (localDualBump : Position → ℝ) :=
  localDualBump.contDiff

theorem localDualMass_positive {freq : ℝ} (hfreq : 0 < freq) : 0 < localDualMass freq := by
  have h0 : localDualBump (0 : Position) = 1 :=
    localDualBump.one_of_mem_closedBall (by simp [localDualBump])
  have h := localizedDualPair_diagonal_positive hfreq 0 localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump.nonneg' (by rw [h0]; norm_num)
  simpa only [localizedDualPair_diagonal, localDualMass] using h

theorem localLeakageBound_nonnegative (freq D : ℝ) : 0 ≤ localLeakageBound freq D :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramSpacing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed logarithmic spacing controls the total leakage for every
polynomial number of sites. The exponent is chosen once for the reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localLeakageBound_log (freq : ℝ) (k : ℕ) {N : ℝ} (hN : 0 < N) :
    localLeakageBound freq ((k : ℝ) * Real.log N) = localLeakageConstant freq / N ^ k := by
  unfold localLeakageBound localLeakageConstant
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hN]
  ring

theorem exists_localizedGram_spacing {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (k : ℝ) * Real.log N ∧
      N ^ A * localLeakageBound freq ((k : ℝ) * Real.log N) ≤ localDualMass freq / 2 := by
  let C := localLeakageConstant freq
  let a := localDualMass freq
  have ha : 0 < a := localDualMass_positive hfreq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hq⟩ := exists_nat_ge (max (5 / Real.log 2) (2 * C / a))
  have hqD : 5 / Real.log 2 ≤ (q : ℝ) := (le_max_left _ _).trans hq
  have hqC : 2 * C / a ≤ (q : ℝ) := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := (div_pos (by norm_num) hlog).trans_le hqD
  have hqNat : 0 < q := by exact_mod_cast hqpos
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨A + q, by omega, fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hD := (div_le_iff₀ hlog).mp hqD
  have hqN : (2 : ℝ) ^ q ≤ N ^ q := pow_le_pow_left₀ (by norm_num) hN q
  have hC : 2 * C ≤ a * N ^ q := by
    have h := (div_le_iff₀ ha).mp (hqC.trans (hpow.trans hqN))
    nlinarith only [h]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg q)
    have hadd := mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith : 1 ≤ N))
    push_cast
    nlinarith only [hD, h, hadd]
  · rw [localLeakageBound_log freq (A + q) hNp, pow_add]
    have hcancel : N ^ A * (C / (N ^ A * N ^ q)) = C / N ^ q := by
      field_simp [pow_ne_zero A hNp.ne', pow_ne_zero q hNp.ne']
    change N ^ A * (C / (N ^ A * N ^ q)) ≤ a / 2
    rw [hcancel]
    apply (div_le_iff₀ (pow_pos hNp q)).mpr
    nlinarith only [hC]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial mesh and precision budgets for the six-coordinate
Coulomb quadrature. All varying parameters below are unary naturals. -/

noncomputable section
namespace ContinuumCoulomb.CoulombQuadratureSchedule

theorem dyadic_le_inverse (b : ℕ) : (2 : ℝ)⁻¹ ^ b ≤ ((b : ℝ) + 1)⁻¹ := by
  have hb : (b : ℝ) + 1 ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.succ_le_of_lt b.lt_two_pow_self
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hb

end ContinuumCoulomb.CoulombQuadratureSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AffinePhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete scalar shift in the unit-charge construction. Input endpoints
already contain the exact mediator offset. The remaining finite shift is the
sum of edge weights and the off-site Coulomb energy; only the latter and the
one-particle reference require numerical approximation. -/

noncomputable section
namespace ContinuumCoulomb.AffinePhysicalThreshold

theorem gap (rho : ℕ) (x : Input) :
    (value rho x).2-(value rho x).1 =
      CenteredPhysicalThreshold.amplification rho x.1.1.1*x.2.1^2*
        (x.1.2.2.2.2-x.1.2.2.2.1) := by
  rw [value,CenteredPhysicalThreshold.gap]
  simp only [argument,finiteValue]
  ring

end ContinuumCoulomb.AffinePhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedEvaluationBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial accuracy schedule for the calibrated hopping
residual. The square-root input uses quadratic precision in the requested
inverse error, rather than assuming a spectral gap for numerical samples. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

theorem root_budget (P : ℕ) :
    (2 : ℝ)⁻¹ ^ rootPrecision P ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  apply (CoulombQuadratureSchedule.dyadic_le_inverse _).trans
  apply inv_anti₀ (by positivity)
  simp only [rootPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedBisectionLocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every returned rational remains in its original search interval. This
geometric invariant does not need an accuracy or residual-sign hypothesis. -/

namespace ContinuumCoulomb

private theorem bisection_step_nested (δ : ℚ) (evaluate : ℚ → ℚ)
    {a b : ℚ} (s : ApproximateBisection.Interval)
    (hs : a ≤ s.lo ∧ s.lo ≤ s.hi ∧ s.hi ≤ b) :
    a ≤ (ApproximateBisection.step δ evaluate s).lo ∧
      (ApproximateBisection.step δ evaluate s).lo ≤ (ApproximateBisection.step δ evaluate s).hi ∧
      (ApproximateBisection.step δ evaluate s).hi ≤ b := by
  have hm := ApproximateBisection.midpoint_mem s hs.2.1
  unfold ApproximateBisection.step
  split_ifs
  · exact hs
  · exact ⟨hs.1.trans hm.1, hm.2, hs.2.2⟩
  · exact ⟨hs.1, hm.1, hm.2.trans hs.2.2⟩
  · exact ⟨hs.1.trans hm.1, le_rfl, hm.2.trans hs.2.2⟩

theorem bisection_run_nested (δ : ℚ) (evaluate : ℚ → ℚ) (a b : ℚ)
    (hab : a ≤ b) (n : ℕ) :
    a ≤ (ApproximateBisection.run δ evaluate a b n).lo ∧
      (ApproximateBisection.run δ evaluate a b n).lo ≤
        (ApproximateBisection.run δ evaluate a b n).hi ∧
      (ApproximateBisection.run δ evaluate a b n).hi ≤ b := by
  induction n with
  | zero => exact ⟨le_rfl, hab, le_rfl⟩
  | succ n ih =>
    simpa only [ApproximateBisection.run, Function.iterate_succ_apply'] using
      bisection_step_nested δ evaluate (ApproximateBisection.run δ evaluate a b n) ih

theorem bisection_value_mem {E : Type} (evaluate : E → ℚ → ℚ) (e : E)
    (δ a b : ℚ) (hab : a ≤ b) (n : ℕ) :
    BisectionProgram.approximate evaluate (n, (e, (δ, (a, b)))) ∈ Set.Icc a b := by
  obtain ⟨hp, hi⟩ := BisectionRegisters.iterate_interval δ (evaluate e)
    (BisectionRegisters.initial a b) (BisectionRegisters.initial_den_pos a b) n
  unfold BisectionProgram.approximate
  rw [BisectionRegisters.middle_eq _ hp, hi, BisectionRegisters.initial_interval]
  have hs := bisection_run_nested δ (evaluate e) a b hab n
  have hm := ApproximateBisection.midpoint_mem (ApproximateBisection.run δ (evaluate e) a b n) hs.2.1
  exact ⟨hs.1.trans hm.1, hm.2.trans hs.2.2⟩

namespace CalibratedEvaluation

theorem bisect_mem (rho : ℕ) (e : Environment) (a b : ℚ) (hab : a ≤ b) (n : ℕ) :
    bisect rho (n, (e, (a, b))) ∈ Set.Icc a b :=
  bisection_value_mem (value rho) e (tolerance e) a b hab n

theorem scheduledValue_mem (rho : ℕ) (e : Environment) (a b : ℚ) (hab : a ≤ b) :
    scheduledValue rho e a b ∈ Set.Icc a b :=
  bisect_mem rho (refinedEnvironment e) a b hab (iterations rho e)

end CalibratedEvaluation
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fixed nine-link contact templates used after spin subdivision.
Coordinates use the Euclidean plane. The link lengths and separation
bounds are stable under small movements of the sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem contactPoint_dist_sq (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ^ 2 =
      (x - x') ^ 2 + (y - y') ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, contactPoint_zero, contactPoint_one, Real.dist_eq, sq_abs]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactAdjustment
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit one-variable continuation for independent contact lengths.
Four sloping links share a transverse height; the other five remain axial.
Thus each nine-link path is adjusted by one scalar intermediate-value solve,
with fixed endpoints and no solve whose dimension grows with the lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

/-- A quantitative square-root estimate, with fixed rational margins. -/
theorem adjustedContactForward_bound {length c h : ℝ}
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance)
    (hc : 7 / 10 ≤ c) (hc' : c ≤ 9 / 10) (hh : h ^ 2 = 1 - c ^ 2) :
    c - 1 / 10000 ≤ adjustedContactForward length h ∧
      adjustedContactForward length h ≤ c + 1 / 10000 := by
  have hlnonneg : 0 ≤ length := by unfold contactLengthTolerance at hl; linarith
  have hlo : (1 - contactLengthTolerance) ^ 2 ≤ length ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ length + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hhi : length ^ 2 ≤ (1 + contactLengthTolerance) ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl')
      (show 0 ≤ (1 + contactLengthTolerance) + length by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
  have hrad : 0 ≤ length ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hlo
    nlinarith
  have hs : adjustedContactForward length h ^ 2 = length ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsnonneg : 0 ≤ adjustedContactForward length h := Real.sqrt_nonneg _
  unfold contactLengthTolerance at hlo hhi
  constructor <;> nlinarith

theorem contactHeightLow_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ^ 2 = 1 - (c + 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeightHigh_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightHigh c ^ 2 = 1 - (c - 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeight_order {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ≤ contactHeightHigh c := by
  have hlow := contactHeightLow_sq hc hc'
  have hhigh := contactHeightHigh_sq hc hc'
  have hl : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  nlinarith

theorem adjustedContactSpan_continuous (lengths : ℕ → ℝ) :
    Continuous (adjustedContactSpan lengths) := by
  unfold adjustedContactSpan adjustedContactStepX adjustedContactForward
  apply continuous_finsetSum
  intro k _
  split_ifs <;> fun_prop

/-- The low-height endpoint overshoots the desired unperturbed span. -/
theorem adjustedContactSpan_low {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    5 + 4 * c + contactLengthTolerance ≤ adjustedContactSpan lengths (contactHeightLow c) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have h2 := (hf 2 (by norm_num)).1
  have h3 := (hf 3 (by norm_num)).1
  have h5 := (hf 5 (by norm_num)).1
  have h6 := (hf 6 (by norm_num)).1
  have h0 := hl 0 (by norm_num)
  have h1 := hl 1 (by norm_num)
  have h4 := hl 4 (by norm_num)
  have h7 := hl 7 (by norm_num)
  have h8 := hl 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- The high-height endpoint undershoots the desired unperturbed span. -/
theorem adjustedContactSpan_high {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    adjustedContactSpan lengths (contactHeightHigh c) ≤ 5 + 4 * c - contactLengthTolerance := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have h2 := (hf 2 (by norm_num)).2
  have h3 := (hf 3 (by norm_num)).2
  have h5 := (hf 5 (by norm_num)).2
  have h6 := (hf 6 (by norm_num)).2
  have h0 := hl' 0 (by norm_num)
  have h1 := hl' 1 (by norm_num)
  have h4 := hl' 4 (by norm_num)
  have h7 := hl' 7 (by norm_num)
  have h8 := hl' 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- All nine link lengths can be prescribed independently while both
endpoints remain fixed at any allowed span. -/
theorem adjustedContactSpan_exists {c span : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hspan : 5 + 4 * c - contactLengthTolerance ≤ span)
    (hspan' : span ≤ 5 + 4 * c + contactLengthTolerance) :
    ∃ h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c), adjustedContactSpan lengths h = span := by
  have hiv := intermediate_value_Icc' (contactHeight_order hc hc')
    (adjustedContactSpan_continuous lengths).continuousOn
  exact hiv ⟨(adjustedContactSpan_high hc hc' lengths hl hl').trans hspan,
    hspan'.trans (adjustedContactSpan_low hc hc' lengths hl hl')⟩

theorem adjustedContactVertex_end (lengths : ℕ → ℝ) (h : ℝ) :
    adjustedContactVertex lengths h 9 = contactPoint (adjustedContactSpan lengths h) 0 := by
  ext i
  fin_cases i
  · rfl
  · norm_num [adjustedContactVertex, contactPoint, Finset.sum_range_succ, adjustedContactStepY]

/-- The continued path has the prescribed actual Euclidean link lengths. -/
theorem adjustedContact_link_length {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k) {k : ℕ} (hk : k < 9) :
    dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) = lengths k := by
  have hlength : 0 ≤ lengths k := by
    have := hl k hk
    unfold contactLengthTolerance at this
    linarith
  have hlow : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh := contactHeightHigh_sq hc hc'
  have hh0 : 0 ≤ h := hlow.trans hh.1
  have hh2 : h ^ 2 ≤ contactHeightHigh c ^ 2 := by nlinarith [hh.2]
  have hmin := hl k hk
  have hmin2 : (1 - contactLengthTolerance) ^ 2 ≤ lengths k ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hmin)
      (show 0 ≤ lengths k + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ (c - 1 / 1000) ^ 2 := by nlinarith
  have hrad : 0 ≤ lengths k ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hmin2
    nlinarith
  have hroot : adjustedContactForward (lengths k) h ^ 2 = lengths k ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsq : dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) ^ 2 =
      lengths k ^ 2 := by
    unfold adjustedContactVertex
    rw [contactPoint_dist_sq]
    simp only [Finset.sum_range_succ, add_sub_cancel_left]
    unfold adjustedContactStepX adjustedContactStepY
    split_ifs <;> (try omega) <;> nlinarith
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h (k + 1))
    (adjustedContactVertex lengths h k) from dist_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactDisplacement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform displacement bounds for the explicit independent-length paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem adjustedContactForward_antitone {length h h' : ℝ} (hh : 0 ≤ h) (hle : h ≤ h') :
    adjustedContactForward length h' ≤ adjustedContactForward length h := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem adjustedContactForward_near {c h length : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance) :
    |adjustedContactForward length h - c| ≤ 11 / 10000 := by
  have hlow := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have hhigh := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have hlo : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh0 : 0 ≤ h := hlo.trans hh.1
  have ha := adjustedContactForward_antitone (length := length) hlo hh.1
  have hb := adjustedContactForward_antitone (length := length) hh0 hh.2
  apply abs_le.mpr
  constructor <;> linarith

theorem contactHeight_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    |h - contactSlopeHeight c| ≤ 1 / 250 := by
  have hbase := contactSlopeHeight_sq (by linarith : -1 ≤ c) (by linarith : c ≤ 1)
  have hlowsq := contactHeightLow_sq hc hc'
  have hhighsq := contactHeightHigh_sq hc hc'
  have hbase0 : 0 ≤ contactSlopeHeight c := Real.sqrt_nonneg _
  have hlow0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hbaseMin : 2 / 5 ≤ contactSlopeHeight c := by nlinarith
  have hlowMin : 2 / 5 ≤ contactHeightLow c := by nlinarith
  have hhighMin : 2 / 5 ≤ contactHeightHigh c := by nlinarith
  have hlowNear : contactSlopeHeight c - 1 / 250 ≤ contactHeightLow c := by nlinarith
  have hhighNear : contactHeightHigh c ≤ contactSlopeHeight c + 1 / 250 := by nlinarith
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem adjustedContactStepX_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k < 9) :
    |adjustedContactStepX lengths h k - contactStepX c k| ≤ 11 / 10000 := by
  unfold adjustedContactStepX contactStepX
  split_ifs
  · exact adjustedContactForward_near hc hc' hh (hl k hk) (hl' k hk)
  · apply abs_le.mpr
    have h1 := hl k hk
    have h2 := hl' k hk
    unfold contactLengthTolerance at h1 h2
    constructor <;> linarith

theorem adjustedContactStepY_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) (k : ℕ) :
    |adjustedContactStepY h k - contactStepY c k| ≤ 1 / 250 := by
  have hnear := contactHeight_near hc hc' hh
  unfold adjustedContactStepY contactStepY
  split_ifs
  · exact hnear
  · simpa only [neg_sub_neg, abs_sub_comm] using hnear
  · norm_num

theorem contact_sum_error {f g : ℕ → ℝ} {k : ℕ} {eta : ℝ}
    (h : ∀ j < k, |f j - g j| ≤ eta) :
    |(∑ j ∈ Finset.range k, f j) - ∑ j ∈ Finset.range k, g j| ≤ k * eta := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k, |f j - g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, eta := Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = _ := by simp

/-- A uniform displacement bound with room for moving the path origin. -/
theorem adjustedContactVertex_displacement {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ j < 9, 1 - contactLengthTolerance ≤ lengths j)
    (hl' : ∀ j < 9, lengths j ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k ≤ 9) :
    dist (adjustedContactVertex lengths h k) (contactPathVertex c k) < 1 / 25 := by
  have hx := contact_sum_error (k := k)
    (fun j hj => adjustedContactStepX_near hc hc' hh lengths hl hl' (by omega : j < 9))
  have hy := contact_sum_error (k := k)
    (fun j _ => adjustedContactStepY_near hc hc' hh j)
  have hkreal : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hx' : |adjustedContactVertex lengths h k 0 - contactPathVertex c k 0| ≤ 99 / 10000 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepX lengths h j) -
      ∑ j ∈ Finset.range k, contactStepX c j| ≤ 99 / 10000
    linarith
  have hy' : |adjustedContactVertex lengths h k 1 - contactPathVertex c k 1| ≤ 9 / 250 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepY h j) -
      ∑ j ∈ Finset.range k, contactStepY c j| ≤ 9 / 250
    linarith
  have hdist := contactPoint_dist_sq
    (∑ j ∈ Finset.range k, adjustedContactStepX lengths h j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h j)
    (∑ j ∈ Finset.range k, contactStepX c j)
    (∑ j ∈ Finset.range k, contactStepY c j)
  change dist (adjustedContactVertex lengths h k) (contactPathVertex c k) ^ 2 =
    (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 +
    (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 at hdist
  have hxSq : (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 ≤ (99 / 10000 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0))
      (by norm_num : (0 : ℝ) ≤ 99 / 10000)).mpr hx'
  have hySq : (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 ≤ (9 / 250 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1))
      (by norm_num : (0 : ℝ) ≤ 9 / 250)).mpr hy'
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h k) (contactPathVertex c k) from dist_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGadgets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two signed-edge contact gadgets. Each has twenty sites, nineteen
links, fixed original endpoints, and independently prescribed link lengths.
A negative input sign places the central partner off the backbone. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactGadgetSlope_bounds (negative : Bool) :
    3 / 4 ≤ contactGadgetSlope negative ∧ contactGadgetSlope negative ≤ 7 / 8 := by
  cases negative <;> norm_num [contactGadgetSlope]

theorem contactGadgetSpan_bounds (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    5 + 4 * contactGadgetSlope negative - contactLengthTolerance ≤ contactGadgetSpan negative central ∧
      contactGadgetSpan negative central ≤ 5 + 4 * contactGadgetSlope negative + contactLengthTolerance := by
  cases negative
  · simp only [contactGadgetSlope, contactGadgetSpan, Bool.false_eq_true, ite_false, if_false]
    constructor <;> linarith
  · norm_num [contactGadgetSlope, contactGadgetSpan, contactLengthTolerance]

theorem contactGadgetRightNode_position (negative : Bool) (central : ℝ)
    (leftLengths rightLengths : ℕ → ℝ) (leftHeight rightHeight : ℝ)
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central)
    (k : Fin 10) :
    contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (contactGadgetRightNode negative k) =
      contactPoint (contactGadgetRightOrigin negative central) 0 +
        adjustedContactVertex rightLengths rightHeight k.val := by
  by_cases hk : k = 0
  · subst k
    rw [contactGadgetRightNode, dite_eq_left rfl]
    cases negative
    · simp [contactGadgetPosition, contactGadgetSide, adjustedContactVertex, contactPoint]
    · change adjustedContactVertex leftLengths leftHeight 9 = contactPoint (17 / 2) 0 +
        adjustedContactVertex rightLengths rightHeight 0
      rw [adjustedContactVertex_end, hleft]
      simp [contactGadgetSpan, adjustedContactVertex, contactPoint]
  · rw [contactGadgetRightNode, dite_eq_right hk]
    change contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (k.val - 1 + 1) = _
    congr 2
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega

/-- Every physical link has its independently prescribed length. -/
theorem contactGadget_link_lengths (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    {leftHeight rightHeight : ℝ}
    (hleftHeight : leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hrightHeight : rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central) :
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.castSucc)) = leftLengths k.val) ∧
    dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide)
      (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9)) = central ∧
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.castSucc)) = rightLengths k.val) := by
  have hs := contactGadgetSlope_bounds negative
  have hcentral : 0 ≤ central := by unfold contactLengthTolerance at hc; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact adjustedContact_link_length hs.1 hs.2 hleftHeight leftLengths hl k.isLt
  · have hA : contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9) = contactPoint (contactGadgetSpan negative central) 0 := by
      change adjustedContactVertex leftLengths leftHeight 9 = _
      rw [adjustedContactVertex_end, hleft]
    rw [hA]
    have hsq : dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0) ^ 2 = central ^ 2 := by
      cases negative <;> simp only [contactGadgetSide, contactGadgetPosition, Sum.elim_inr,
        contactGadgetRightOrigin, contactGadgetSpan, Bool.false_eq_true, ite_false, if_false,
        ite_true, if_true, contactPoint_dist_sq] <;> ring
    nlinarith [show 0 ≤ dist (contactGadgetPosition negative central leftLengths rightLengths
      leftHeight rightHeight contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0)
      from dist_nonneg]
  · intro k
    rw [contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      dist_add_left]
    exact adjustedContact_link_length hs.1 hs.2 hrightHeight rightLengths hr k.isLt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform separation of contacts from different lattice edges. The estimates
use only fixed strip bounds, so the lattice size never enters their constants. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_coordinate_le_dist (p q : ContactPoint) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  have hdist := EuclideanSpace.dist_sq_eq p q
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hdist
  fin_cases i
  · change |p 0 - q 0| ≤ dist p q
    nlinarith [sq_nonneg (p 1 - q 1), abs_nonneg (p 0 - q 0),
      sq_abs (p 0 - q 0), show 0 ≤ dist p q from dist_nonneg]
  · change |p 1 - q 1| ≤ dist p q
    nlinarith [sq_nonneg (p 0 - q 0), abs_nonneg (p 1 - q 1),
      sq_abs (p 1 - q 1), show 0 ≤ dist p q from dist_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGadgetStability
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed nineteen-link gadgets retain the nonlink separation of the
base shapes. All estimates concern the actual coordinate constructions. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_axis_dist (x x' : ℝ) :
    dist (contactPoint x 0) (contactPoint x' 0) = |x - x'| := by
  have h := contactPoint_dist_sq x 0 x' 0
  nlinarith [sq_abs (x - x'), abs_nonneg (x - x'),
    show 0 ≤ dist (contactPoint x 0) (contactPoint x' 0) from dist_nonneg]

theorem contactPoint_vertical_dist (x y y' : ℝ) :
    dist (contactPoint x y) (contactPoint x y') = |y - y'| := by
  have h := contactPoint_dist_sq x y x y'
  nlinarith [sq_abs (y - y'), abs_nonneg (y - y'),
    show 0 ≤ dist (contactPoint x y) (contactPoint x y') from dist_nonneg]

theorem contactGadgetOrigin_near (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    dist (contactPoint (contactGadgetRightOrigin negative central) 0)
      (contactPoint (contactGadgetRightOrigin negative 1) 0) ≤ contactLengthTolerance := by
  rw [contactPoint_axis_dist]
  cases negative
  · apply abs_le.mpr
    simp only [contactGadgetRightOrigin, Bool.false_eq_true, ite_false, if_false]
    constructor <;> linarith
  · norm_num [contactGadgetRightOrigin, contactLengthTolerance]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediatorGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent prescribed lengths for the exact nineteen local edges
identified with the actual iterated mediator graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

theorem leftEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
      (G (localToContact (localRight (leftEdge k)))) =
        dist (G (Sum.inl k.succ)) (G (Sum.inl k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [leftEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, dist_comm] <;> first | rfl | exact dist_comm _ _

theorem rightEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
      (G (localToContact (localRight (rightEdge k)))) =
        dist (G (contactGadgetRightNode negative k.succ))
          (G (contactGadgetRightNode negative k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [rightEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, contactGadgetRightNode, contactGadgetSide,
      dist_comm] <;> first | rfl | exact dist_comm _ _

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform direct and inverse moduli for the nine-link height solve. The
four sloping links keep this one-dimensional solve quantitatively regular. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactHeight_interval_bounds {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    2 / 5 ≤ h ∧ h ≤ 3 / 4 := by
  have hl0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hu0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hl := contactHeightLow_sq hc hc'
  have hu := contactHeightHigh_sq hc hc'
  constructor
  · nlinarith [hh.1]
  · nlinarith [hh.2]

theorem adjustedContactForward_slope {length h₁ h₂ : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4) :
    (h₂ - h₁) / 5 ≤ adjustedContactForward length h₁ - adjustedContactForward length h₂ ∧
      adjustedContactForward length h₁ - adjustedContactForward length h₂ ≤ 2 * (h₂ - h₁) := by
  have h₁0 : 0 ≤ h₁ := by linarith
  have h₂0 : 0 ≤ h₂ := by linarith
  have h₁U : h₁ ≤ 3 / 4 := hh.trans hh₂
  have h₂L : 2 / 5 ≤ h₂ := hh₁.trans hh
  have hl0 : 0 ≤ length := by linarith
  have hl2lo : (99 / 100 : ℝ) ^ 2 ≤ length ^ 2 := by nlinarith
  have hl2hi : length ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by nlinarith
  have hr₁ : 0 ≤ length ^ 2 - h₁ ^ 2 := by nlinarith
  have hr₂ : 0 ≤ length ^ 2 - h₂ ^ 2 := by nlinarith
  let x₁ := adjustedContactForward length h₁
  let x₂ := adjustedContactForward length h₂
  have hx₁ : 0 ≤ x₁ := Real.sqrt_nonneg _
  have hx₂ : 0 ≤ x₂ := Real.sqrt_nonneg _
  have hx₁sq : x₁ ^ 2 = length ^ 2 - h₁ ^ 2 := Real.sq_sqrt hr₁
  have hx₂sq : x₂ ^ 2 = length ^ 2 - h₂ ^ 2 := Real.sq_sqrt hr₂
  have hx₁lo : 1 / 2 ≤ x₁ := by nlinarith
  have hx₂lo : 1 / 2 ≤ x₂ := by nlinarith
  have hx₁hi : x₁ ≤ 2 := by nlinarith
  have hx₂hi : x₂ ≤ 2 := by nlinarith
  have hxx : x₂ ≤ x₁ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg h₁0 h₂0)]
  have hid : (x₁ - x₂) * (x₁ + x₂) = (h₂ - h₁) * (h₁ + h₂) := by nlinarith
  change (h₂ - h₁) / 5 ≤ x₁ - x₂ ∧ x₁ - x₂ ≤ 2 * (h₂ - h₁)
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ 4 - (x₁ + x₂) by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ h₁ + h₂ - 4 / 5 by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ x₁ + x₂ - 1 by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 2 - (h₁ + h₂) by linarith)]

theorem adjustedContactSpan_broad_slope {h₁ h₂ : ℝ}
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    (h₂ - h₁) / 2 ≤ adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ∧
      adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ≤ 8 * (h₂ - h₁) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_slope
    (show 99 / 100 ≤ lengths k by have := hl k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    (show lengths k ≤ 101 / 100 by have := hl' k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    hh₁ hh hh₂
  have hf₂ := hf 2 (by norm_num)
  have hf₃ := hf 3 (by norm_num)
  have hf₅ := hf 5 (by norm_num)
  have hf₆ := hf 6 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  constructor <;> linarith [hf₂.1, hf₂.2, hf₃.1, hf₃.2, hf₅.1, hf₅.2, hf₆.1, hf₆.2]

theorem adjustedContactSpan_broad_inverse_error {h h₀ span : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4))
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hroot : adjustedContactSpan lengths h₀ = span) :
    |h - h₀| ≤ 2 * |adjustedContactSpan lengths h - span| := by
  rcases le_total h h₀ with hle | hle
  · have hs := (adjustedContactSpan_broad_slope hh.1 hle hh₀.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : 0 ≤ adjustedContactSpan lengths h - span := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonneg hx]
    linarith
  · have hs := (adjustedContactSpan_broad_slope hh₀.1 hle hh.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : adjustedContactSpan lengths h - span ≤ 0 := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos hx]
    linarith

theorem adjustedContactSpan_broad_lipschitz {h h' : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    |adjustedContactSpan lengths h - adjustedContactSpan lengths h'| ≤ 8 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh.1 hle hh'.2 lengths hl hl'
    have hs : 0 ≤ adjustedContactSpan lengths h - adjustedContactSpan lengths h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh'.1 hle hh.2 lengths hl hl'
    have hs : adjustedContactSpan lengths h - adjustedContactSpan lengths h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational evaluator for the one-dimensional height residual.
There are exactly four dyadic square-root calls; all other terms are exact. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem rootSample_error (e : Environment) (h : ℚ) (k : ℕ)
    (hl : 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(rootSample e h k : ℝ) - adjustedContactForward (lengthAt e k) h| ≤
      (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 := by
  have hlow : (99 / 100 : ℝ) ≤ lengthAt e k := by
    norm_num [contactLengthTolerance] at hl
    linarith
  have hrad : (0 : ℝ) ≤ (lengthAt e k : ℝ) ^ 2 - (h : ℝ) ^ 2 := by
    have hh0 : (0 : ℝ) ≤ h := by linarith [hh.1]
    nlinarith [hh.2]
  have hradQ : (0 : ℚ) ≤ (lengthAt e k) ^ 2 - h ^ 2 := by exact_mod_cast hrad
  have he := RationalSquareRoot.value_error (CalibratedEvaluation.rootPrecision e.1) hradQ
  simpa only [rootSample, adjustedContactForward, Rat.cast_sub, Rat.cast_pow] using he

private theorem four_errors {a b c d E : ℝ}
    (ha : |a| ≤ E) (hb : |b| ≤ E) (hc : |c| ≤ E) (hd : |d| ≤ E) :
    |a + b + c + d| ≤ 4 * E := by
  have h₁ := (abs_add_le a b).trans (add_le_add ha hb)
  have h₂ := (abs_add_le c d).trans (add_le_add hc hd)
  have h := (abs_add_le (a + b) (c + d)).trans (add_le_add h₁ h₂)
  rw [add_assoc (a + b) c d]
  exact h.trans_eq (by ring)

theorem approximation_error (e : Environment) (h : ℚ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(value e h : ℝ) - residual e h| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have h₂ := rootSample_error e h 2 (hl 2 (by norm_num)) hh
  have h₃ := rootSample_error e h 3 (hl 3 (by norm_num)) hh
  have h₅ := rootSample_error e h 5 (hl 5 (by norm_num)) hh
  have h₆ := rootSample_error e h 6 (hl 6 (by norm_num)) hh
  have heq : (value e h : ℝ) - residual e h =
      ((rootSample e h 2 : ℝ) - adjustedContactForward (lengthAt e 2) h) +
      ((rootSample e h 3 : ℝ) - adjustedContactForward (lengthAt e 3) h) +
      ((rootSample e h 5 : ℝ) - adjustedContactForward (lengthAt e 5) h) +
      ((rootSample e h 6 : ℝ) - adjustedContactForward (lengthAt e 6) h) := by
    norm_num [value, residual, adjustedContactSpan, adjustedContactStepX,
      Finset.sum_range_succ, Rat.cast_add, Rat.cast_sub]
    ring
  rw [heq]
  apply (four_errors h₂ h₃ h₅ h₆).trans
  have hb := mul_le_mul_of_nonneg_left (CalibratedEvaluation.root_budget e.1)
    (show (0 : ℝ) ≤ 4 by norm_num)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [show (e.1 : ℝ) + 1 ≠ 0 by positivity]

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightBisection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height search uses fixed rational endpoints, its concrete evaluator,
and a linear unary precision schedule. The reference height is supplied by
the already proved contact intermediate-value theorem. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem bisect_mem (e : Environment) (n : ℕ) :
    (bisect e n : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
  have hm := bisection_value_mem value e (tolerance e) (2 / 5) (3 / 4)
    (by norm_num) n
  have hm' : bisect e n ∈ Set.Icc (2 / 5 : ℚ) (3 / 4) := hm
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.1
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.2

theorem endpoint_signs (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    0 ≤ residual e (2 / 5) ∧ residual e (3 / 4) ≤ 0 := by
  have ha := (adjustedContactSpan_broad_slope (by norm_num) hh₀.1 hh₀.2
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  have hb := (adjustedContactSpan_broad_slope hh₀.1 hh₀.2 (by norm_num)
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  rw [hroot] at ha hb
  constructor <;> unfold residual <;> linarith [hh₀.1, hh₀.2]

theorem bisect_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) (n : ℕ) :
    |residual e (bisect e n)| ≤ 2 * ((e.1 : ℝ) + 1)⁻¹ +
      8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ n) := by
  have heval (q : ℚ) (hq : q ∈ Set.Icc (2 / 5 : ℚ) (3 / 4)) :
      |(value e q : ℝ) - residual e q| ≤ (tolerance e : ℝ) := by
    have hq' : (q : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
      constructor
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.1
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.2
    simpa only [tolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add,
      Rat.cast_natCast, one_div, Rat.cast_inv] using approximation_error e q hl hq'
  have hLip (r : ℝ) (hr : r ∈ Set.Icc (2 / 5) (3 / 4))
      (s : ℝ) (hs : s ∈ Set.Icc (2 / 5) (3 / 4)) :
      |residual e r - residual e s| ≤ 8 * |r - s| := by
    simpa only [residual, sub_sub_sub_cancel_right] using
      adjustedContactSpan_broad_lipschitz hr hs (fun k => (lengthAt e k : ℝ)) hl hl'
  have ha' : 0 ≤ residual e ((2 / 5 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  have hb' : residual e ((3 / 4 : ℚ) : ℝ) ≤ 0 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hb
  have hLip' (r : ℝ) (hr : r ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ))
      (s : ℝ) (hs : s ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ)) :
      |residual e r - residual e s| ≤ 8 * |r - s| :=
    hLip r (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hr)
      s (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hs)
  have he := BisectionProgram.residual value e
    (show 0 ≤ tolerance e by unfold tolerance; positivity)
    (show (2 / 5 : ℚ) ≤ 3 / 4 by norm_num) ha' hb'
    (show (0 : ℝ) ≤ 8 by norm_num) heval hLip' n
  simpa only [bisect, argument, tolerance, Rat.cast_div, Rat.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, one_div, Rat.cast_inv] using he

theorem scheduled_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) :
    |residual e (scheduledValue e)| ≤ (2 * ((e.1 : ℝ) + 1))⁻¹ := by
  have he := bisect_residual (refinedEnvironment e) hl hl' ha hb (iterations e)
  have he' : |residual e (scheduledValue e)| ≤
      2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ +
        8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) := by
    simpa only [scheduledValue, refinedEnvironment, residual, lengthAt, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using he
  have hS : (0 : ℝ) < (e.1 : ℝ) + 1 := by positivity
  have hn : (iterations e : ℝ) = 64 * ((e.1 : ℝ) + 1) := by
    simp only [iterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hn0 : (0 : ℝ) < iterations e := by rw [hn]; positivity
  have hfirst : 2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 8 * ((e.1 : ℝ) + 1))).mpr
    linarith
  have hsecond : 8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    calc
      _ ≤ 8 * (2 : ℝ)⁻¹ ^ iterations e := by
        rw [div_eq_mul_inv, inv_pow]
        gcongr
        norm_num
      _ ≤ 8 * ((iterations e : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (CoulombQuadratureSchedule.dyadic_le_inverse _) (by norm_num)
      _ ≤ 8 * (iterations e : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hn0 (by linarith)) (by norm_num)
      _ = (8 * ((e.1 : ℝ) + 1))⁻¹ := by
        rw [hn]
        field_simp [ne_of_gt hS]
        ring
  apply he'.trans ((add_le_add hfirst hsecond).trans _)
  simp only [mul_inv_rev]
  norm_num
  nlinarith [inv_pos.mpr hS]

theorem scheduled_height_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have hs := endpoint_signs e h₀ hl hl' hh₀ hroot
  have he := scheduled_residual e hl hl' hs.1 hs.2
  have hi := adjustedContactSpan_broad_inverse_error
    (bisect_mem (refinedEnvironment e) (iterations e)) hh₀
    (fun k => (lengthAt e k : ℝ)) hl hl' hroot
  have h := hi.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * (2 * ((e.1 : ℝ) + 1))⁻¹ := h
    _ = _ := by field_simp

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact vertices approximate the same exact height witness as
the deterministic height solve. This estimate preserves separation margins
when the requested precision is increased. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem forward_lipschitz {length h h' : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4)) :
    |adjustedContactForward length h - adjustedContactForward length h'| ≤ 2 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh.1 hle hh'.2
    have hs : 0 ≤ adjustedContactForward length h - adjustedContactForward length h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh'.1 hle hh.2
    have hs : adjustedContactForward length h - adjustedContactForward length h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

theorem stepX_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹)
    {k : ℕ} (hk : k < 9) :
    |(stepX e (scheduledValue e) k : ℝ) -
      adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ k| ≤
        3 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hs : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6
  · have hh := bisect_mem (refinedEnvironment e) (iterations e)
    have hlower : (99 / 100 : ℝ) ≤ lengthAt e k := by
      have := hl k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hupper : (lengthAt e k : ℝ) ≤ 101 / 100 := by
      have := hl' k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hsample := rootSample_error e (scheduledValue e) k (hl k hk) hh
    have hforward := forward_lipschitz hlower hupper hh hh₀
    have hdyadic : (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 ≤
        ((e.1 : ℝ) + 1)⁻¹ := (CalibratedEvaluation.root_budget e.1).trans (by
      apply inv_anti₀ (by positivity)
      nlinarith [show (0 : ℝ) ≤ e.1 from Nat.cast_nonneg e.1])
    have h := (abs_sub_le (rootSample e (scheduledValue e) k : ℝ)
      (adjustedContactForward (lengthAt e k) (scheduledValue e))
      (adjustedContactForward (lengthAt e k) h₀)).trans
        (add_le_add (hsample.trans hdyadic) (hforward.trans (mul_le_mul_of_nonneg_left he (by norm_num))))
    have h' : |(rootSample e (scheduledValue e) k : ℝ) -
        adjustedContactForward (lengthAt e k) h₀| ≤ 3 * ((e.1 : ℝ) + 1)⁻¹ := by
      calc
        _ ≤ ((e.1 : ℝ) + 1)⁻¹ + 2 * ((e.1 : ℝ) + 1)⁻¹ := h
        _ = _ := by ring
    simpa only [stepX, adjustedContactStepX, ite_eq_left hs] using h'
  · simp only [stepX, adjustedContactStepX, ite_eq_right hs, sub_self, abs_zero]
    positivity

theorem stepY_error (e : Environment) (h₀ : ℝ)
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹) (k : ℕ) :
    |(stepY (scheduledValue e) k : ℝ) - adjustedContactStepY h₀ k| ≤
      ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases h₁ : k = 2 ∨ k = 3
  · simpa only [stepY, adjustedContactStepY, ite_eq_left h₁] using he
  · by_cases h₂ : k = 5 ∨ k = 6
    · simpa only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_left h₂,
        Rat.cast_neg, neg_sub_neg, abs_sub_comm] using he
    · simp only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_right h₂, Rat.cast_zero,
        sub_zero, abs_zero]
      positivity

private theorem contactPoint_dist_le_abs (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ≤ |x - x'| + |y - y'| := by
  have hsq := contactPoint_dist_sq x y x' y'
  nlinarith [sq_abs (x - x'), sq_abs (y - y'),
    mul_nonneg (abs_nonneg (x - x')) (abs_nonneg (y - y')),
    show 0 ≤ dist (contactPoint x y) (contactPoint x' y') from dist_nonneg,
    abs_nonneg (x - x'), abs_nonneg (y - y')]

theorem vertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (vertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  have he := scheduled_height_error e h₀ hl hl' hh₀ hroot
  have hx : |(∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j| ≤
        (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, 3 * ((e.1 : ℝ) + 1)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact stepX_error e h₀ hl hl' hh₀ he (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
      _ = _ := by simp
  have hy : |(∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepY h₀ j| ≤
        (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, ((e.1 : ℝ) + 1)⁻¹ := by
        exact Finset.sum_le_sum (fun j _ => stepY_error e h₀ he j)
      _ = _ := by simp
  have hd := contactPoint_dist_le_abs
    (∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h₀ j)
  have hk' : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hb : (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) + (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right hk' (inv_nonneg.mpr
      (show (0 : ℝ) ≤ e.1 + 1 by positivity))]
  simpa only [vertexPoint, vertex, adjustedContactVertex, Rat.cast_sum] using
    hd.trans ((add_le_add hx hy).trans hb)

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactClosedCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational path keeps both original endpoints exact. Replacing its
last approximate prefix sum by the prescribed span improves its distance
to the exact reference path and does not change the polynomial program. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

theorem closedVertex_start (e : Environment) : closedVertex e 0 = (0, 0) := by
  simp [closedVertex, vertex]

theorem closedVertex_end (e : Environment) : closedVertex e 9 = (e.2.2, 0) := by
  simp [closedVertex]

theorem closedVertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (closedVertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hk9 : k = 9
  · subst k
    rw [adjustedContactVertex_end, hroot]
    simp only [closedVertexPoint, closedVertex_end, Rat.cast_zero, dist_self]
    positivity
  · simpa only [closedVertexPoint, closedVertex, ite_eq_right hk9, vertexPoint] using
      vertex_error e h₀ hl hl' hh₀ hroot hk

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGadget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational twenty-site gadget. The two paths share the same
rational prescribed span; their outer endpoints are exact and their
internal vertices approximate the original independent-length gadget. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGadget
open ContactHeightEvaluation

theorem span_cast (b : Bool) (c : ℚ) :
    (span b c : ℝ) = contactGadgetSpan b c := by
  cases b <;> simp [span, contactGadgetSpan, Rat.cast_div, Rat.cast_sub]

theorem origin_cast (b : Bool) (c : ℚ) :
    (origin b c : ℝ) = contactGadgetRightOrigin b c := by
  cases b <;> simp [origin, contactGadgetRightOrigin, Rat.cast_div, Rat.cast_add]

theorem point_left (x : Input) (k : Fin 10) :
    point x (Sum.inl k) = closedVertexPoint (leftEnvironment x) k.val := rfl

theorem point_right (x : Input) (k : Fin 9) :
    point x (Sum.inr (Sum.inl k)) =
      contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
        closedVertexPoint (rightEnvironment x) (k.val + 1) := by
  ext i
  fin_cases i <;>
    simp [point, position, closedVertexPoint, contactPoint, Rat.cast_add,
      origin_cast, PiLp.add_apply]

theorem point_side (x : Input) :
    point x contactGadgetSide =
      if x.2.1 then contactPoint (17 / 2) x.2.2.1
      else contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 := by
  cases hb : x.2.1 <;>
    simp [point, position, contactGadgetSide, hb, origin_cast, Rat.cast_div]

theorem point_start (x : Input) : point x (Sum.inl 0) = contactPoint 0 0 := by
  rw [point_left]
  simp [closedVertexPoint, closedVertex_start]

theorem point_end (x : Input) :
    point x (contactGadgetRightNode x.2.1 9) = contactPoint 17 0 := by
  have hnode : contactGadgetRightNode x.2.1 9 = Sum.inr (Sum.inl 8) := by
    simp [contactGadgetRightNode]
  rw [hnode, point_right]
  change contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
    closedVertexPoint (rightEnvironment x) 9 = _
  simp only [closedVertexPoint, closedVertex_end, rightEnvironment, span_cast, Rat.cast_zero]
  cases hb : x.2.1 <;> ext i <;> fin_cases i
  all_goals simp [contactGadgetRightOrigin, contactGadgetSpan, contactPoint, PiLp.add_apply]
  all_goals ring

theorem point_near_reference (x : Input) (hL hR : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance)
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hLroot : adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1)
    (hRroot : adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1)
    (s : ContactGadgetSite) :
    dist (point x s)
      (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
        36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hL' := contactHeight_interval_bounds hs.1 hs.2 hLmem
  have hR' := contactHeight_interval_bounds hs.1 hs.2 hRmem
  have hLroot' : adjustedContactSpan (leftLengths x) hL =
      ((leftEnvironment x).2.2 : ℝ) := by simpa only [leftEnvironment, span_cast] using hLroot
  have hRroot' : adjustedContactSpan (rightLengths x) hR =
      ((rightEnvironment x).2.2 : ℝ) := by simpa only [rightEnvironment, span_cast] using hRroot
  rcases s with k | (k | u)
  · rw [point_left]
    exact closedVertex_error (leftEnvironment x) hL hl hl' hL' hLroot'
      (by have := k.isLt; omega)
  · rw [point_right]
    change dist (_ + _) (_ + _) ≤ _
    rw [dist_add_left]
    exact closedVertex_error (rightEnvironment x) hR hr hr' hR' hRroot'
      (by have := k.isLt; omega)
  · cases u
    change dist (point x contactGadgetSide) _ ≤ _
    rw [point_side]
    change dist _ (if x.2.1 then _ else _) ≤ _
    rw [dist_self]
    positivity

theorem exists_reference (x : Input)
    (hc : 1 - contactLengthTolerance ≤ (x.2.2.1 : ℝ))
    (hc' : (x.2.2.1 : ℝ) ≤ 1 + contactLengthTolerance)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance) :
    ∃ hL hR,
      hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1 ∧
      adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1 ∧
      ∀ s, dist (point x s)
        (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
          36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hspan := contactGadgetSpan_bounds x.2.1 hc hc'
  obtain ⟨hL, hLmem, hLroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (leftLengths x) hl hl' hspan.1 hspan.2
  obtain ⟨hR, hRmem, hRroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (rightLengths x) hr hr' hspan.1 hspan.2
  exact ⟨hL, hR, hLmem, hRmem, hLroot, hRroot,
    point_near_reference x hL hR hl hl' hr hr' hLmem hRmem hLroot hRroot⟩

theorem reference_near_base (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (ll rr : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ ll k)
    (hl' : ∀ k < 9, ll k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rr k)
    (hr' : ∀ k < 9, rr k ≤ 1 + contactLengthTolerance)
    {hL hR : ℝ}
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative))) (s : ContactGadgetSite) :
    dist (contactGadgetPosition negative central ll rr hL hR s)
      (contactBaseGadgetPosition negative s) < 9 / 200 := by
  have hs := contactGadgetSlope_bounds negative
  rcases s with k | (k | ⟨⟩)
  · exact (adjustedContactVertex_displacement hs.1 hs.2 hLmem ll hl hl'
      (by have := k.isLt; omega)).trans (by norm_num)
  · have hp := adjustedContactVertex_displacement hs.1 hs.2 hRmem rr hr hr'
      (show k.val + 1 ≤ 9 by have := k.isLt; omega)
    have ho := contactGadgetOrigin_near negative hc hc'
    have hd := dist_add_add_le (contactPoint (contactGadgetRightOrigin negative central) 0)
      (adjustedContactVertex rr hR (k.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0)
      (contactPathVertex (contactGadgetSlope negative) (k.val + 1))
    change dist (_ + _) (_ + _) < _
    unfold contactLengthTolerance at ho
    linarith
  · cases negative
    · have ho := contactGadgetOrigin_near false hc hc'
      norm_num [contactGadgetRightOrigin, contactLengthTolerance] at ho
      change dist (contactPoint ((17 + central) / 2) 0) (contactPoint 9 0) < _
      linarith
    · change dist (contactPoint (17 / 2) central) (contactPoint (17 / 2) 1) < _
      rw [contactPoint_vertical_dist]
      have habs : |central - 1| ≤ contactLengthTolerance := abs_le.mpr ⟨by linarith, by linarith⟩
      exact habs.trans_lt (by norm_num [contactLengthTolerance])

end ContinuumCoulomb.ContactRationalGadget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact coordinates indexed by the actual nineteen local
mediator edges. Every link has a quantitative error and the nonedge margin
survives with a fixed minimum requested precision. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalLocal
open ContactMediator ContactRationalGadget

private theorem length_ofFn (f : Fin 9 → ℚ) (k : ℕ) (hk : k < 9) :
    ((List.ofFn f).drop k).headD 1 = f ⟨k, hk⟩ := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using hk)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem left_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    leftLengths (input P negative ℓ) k = (ℓ (leftEdge ⟨k, hk⟩) : ℝ) := by
  simp only [leftLengths, ContactHeightEvaluation.lengthAt, leftEnvironment, input]
  rw [length_ofFn _ k hk]

theorem right_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    rightLengths (input P negative ℓ) k = (ℓ (rightEdge ⟨k, hk⟩) : ℝ) := by
  simp only [rightLengths, ContactHeightEvaluation.lengthAt, rightEnvironment, input]
  rw [length_ofFn _ k hk]

private theorem distance_error {x y x' y' : ContactPoint} {E : ℝ}
    (hx : dist x x' ≤ E) (hy : dist y y' ≤ E) :
    |dist x y - dist x' y'| ≤ 2 * E := by
  have h := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at h
  exact h.trans (by linarith)

theorem exists_link_approximation (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    point P negative ℓ (localOld 0) = contactPoint 0 0 ∧
      point P negative ℓ (localOld 1) = contactPoint 17 0 ∧
      (∀ a, |dist (point P negative ℓ (localLeft (if negative then 0 else 1) a))
        (point P negative ℓ (localRight a)) - (ℓ a : ℝ)| ≤ 72 * ((P : ℝ) + 1)⁻¹) ∧
      (∀ s, dist (point P negative ℓ s)
        (contactBaseGadgetPosition negative (localToContact s)) <
          36 * ((P : ℝ) + 1)⁻¹ + 9 / 200) := by
  let x := input P negative ℓ
  have hl (k : ℕ) (hk : k < 9) : leftLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show leftLengths x k = _ from left_length P negative ℓ k hk]
    exact hℓ _
  have hr (k : ℕ) (hk : k < 9) : rightLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show rightLengths x k = _ from right_length P negative ℓ k hk]
    exact hℓ _
  obtain ⟨hL, hR, hLmem, hRmem, hLroot, hRroot, hnear⟩ := ContactRationalGadget.exists_reference x
    (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
    (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
    (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2)
  let G := contactGadgetPosition negative (ℓ (Sum.inl ())) (leftLengths x) (rightLengths x) hL hR
  have hlinks := contactGadget_link_lengths negative (hℓ (Sum.inl ())).1
    (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hr k hk).1)
    hLmem hRmem hLroot
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ContactRationalGadget.point_start x
  · simpa [point, localToContact, localOld, x, input, contactGadgetRightNode] using
      ContactRationalGadget.point_end x
  · intro a
    have he := distance_error (hnear (localToContact (localLeft (if negative then 0 else 1) a)))
      (hnear (localToContact (localRight a)))
    have hexact : dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a))) = (ℓ a : ℝ) := by
      obtain ⟨b, rfl⟩ := contactEdgeEquiv.surjective a
      rcases b with k | (⟨⟩ | k)
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
          (G (localToContact (localRight (leftEdge k)))) = (ℓ (leftEdge k) : ℝ)
        rw [leftEdge_distance]
        exact (hlinks.1 k).trans (left_length P negative ℓ k.val k.isLt)
      · change dist (G (Sum.inl 9)) (G contactGadgetSide) = _
        rw [dist_comm]
        exact hlinks.2.1
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
          (G (localToContact (localRight (rightEdge k)))) = (ℓ (rightEdge k) : ℝ)
        rw [rightEdge_distance]
        exact (hlinks.2.2 k).trans (right_length P negative ℓ k.val k.isLt)
    change |dist (ContactRationalGadget.point x _)
        (ContactRationalGadget.point x _) -
      dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a)))| ≤ 2 * (36 * ((P : ℝ) + 1)⁻¹) at he
    change |dist (ContactRationalGadget.point x _) (ContactRationalGadget.point x _) - _| ≤ _
    rw [hexact] at he
    exact he.trans_eq (by ring)
  · intro s
    have hb := ContactRationalGadget.reference_near_base negative (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
      (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2) hLmem hRmem (localToContact s)
    exact (dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt (hnear _) hb)

theorem near_base (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (s : LocalSite) :
    dist (point P negative ℓ s) (contactBaseGadgetPosition negative (localToContact s)) < 1 / 20 := by
  have h := (exists_link_approximation P negative ℓ hℓ).2.2.2 s
  have hsmall : 36 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 200 := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have hPR : (7200 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  linarith

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactLattice
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual gadget sites fit the common lattice strips. Together with
ContactStrips, this separates distinct edges without a size-dependent loss. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_eta (p : ContactPoint) : contactPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

/-- Every base-gadget site other than the two original vertices belongs to
the uniform internal strip. -/
theorem contactBaseGadget_internal_strip (negative : Bool) (x : ContactGadgetSite)
    (hleft : x ≠ Sum.inl 0) (hright : x ≠ contactGadgetRightNode negative 9) :
    ∃ p : ContactStripSite,
      contactBaseGadgetPosition negative x = contactPoint p.axial p.transverse := by
  have hs := contactGadgetSlope_bounds negative
  rcases x with i | (i | ⟨⟩)
  · have hi : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := fun h => hleft (congrArg Sum.inl (Fin.ext h))
      omega
    let p := leftContactStripSite (contactGadgetSlope negative) hs.1 hs.2 i.val hi
      (show i.val ≤ 9 by have := i.isLt; omega)
    exact ⟨p, (contactPoint_eta (contactPathVertex (contactGadgetSlope negative) i.val)).symm⟩
  · have hi8 : i.val ≠ 8 := by
      intro h
      have hi : i = 8 := Fin.ext h
      subst i
      apply hright
      norm_num [contactGadgetRightNode] <;> (simp; try rfl)
    have hi : i.val + 1 ≤ 8 := by have := i.isLt; omega
    have horigin : contactGadgetRightOrigin negative 1 + (5 + 4 * contactGadgetSlope negative) = 17 := by
      cases negative <;> norm_num [contactGadgetRightOrigin, contactGadgetSlope]
    let p := rightContactStripSite (contactGadgetSlope negative) (contactGadgetRightOrigin negative 1)
      hs.1 hs.2 horigin (i.val + 1) (by omega) hi
    refine ⟨p, ?_⟩
    change contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1) =
      contactPoint (contactGadgetRightOrigin negative 1 +
        contactPathVertex (contactGadgetSlope negative) (i.val + 1) 0)
        (contactPathVertex (contactGadgetSlope negative) (i.val + 1) 1)
    ext j
    fin_cases j <;> simp [contactPoint, PiLp.add_apply]
  · cases negative
    · let p : ContactStripSite := {
        axial := 9
        transverse := 0
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro h; exact False.elim (h rfl)
        off_axis_upper := by intro h; exact False.elim (h rfl) }
      exact ⟨p, rfl⟩
    · let p : ContactStripSite := {
        axial := 17 / 2
        transverse := 1
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro _; norm_num
        off_axis_upper := by intro _; norm_num }
      exact ⟨p, rfl⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rigid placements of the fixed contact strip on the square lattice.
Reversing an original edge reflects its axial coordinate; this keeps its
internal points in the same canonical strip. -/

noncomputable section
namespace ContinuumCoulomb

private theorem contact_dist_eq_of_sq_eq {p q x y : ContactPoint}
    (h : dist p q ^ 2 = dist x y ^ 2) : dist p q = dist x y := by
  nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := x) (y := y)]

theorem contactReflect_dist (p q : ContactPoint) :
    dist (contactReflect p) (contactReflect q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactReflect, contactReflect, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactHorizontal_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactHorizontal a p) (contactHorizontal a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactHorizontal, contactHorizontal, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactVertical_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactVertical a p) (contactVertical a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactVertical, contactVertical, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem ContactGridEdge.place_dist (e : ContactGridEdge) (p q : ContactPoint) :
    dist (e.place p) (e.place q) = dist p q := by
  cases e with
  | mk vertical anchor reversed =>
    cases vertical <;> cases reversed <;>
      simp [ContactGridEdge.place, contactHorizontal_dist, contactVertical_dist, contactReflect_dist]

/-- The orientation flag does not alter the strip containing an internal site. -/
theorem ContactGridEdge.place_strip (e : ContactGridEdge) (p : ContactStripSite) :
    ∃ q : ContactStripSite, e.place (contactPoint p.axial p.transverse) =
      if e.vertical then verticalContact e.anchor.1 e.anchor.2 q
      else horizontalContact e.anchor.1 e.anchor.2 q := by
  refine ⟨if e.reversed then p.reflect else p, ?_⟩
  cases h : e.reversed <;> cases v : e.vertical <;>
    simp [ContactGridEdge.place, h, v, contactReflect, contactHorizontal, contactVertical,
      horizontalContact, verticalContact, ContactStripSite.reflect]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing the independently adjusted nineteen-link gadgets along the
actual original lattice vertices. All fresh sites retain their source-edge
label under the explicit final-graph permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

/-- The independent local adjustments stay close to points in the exact
canonical strip belonging to their original source edge. -/
theorem globalPosition_internal_near_strip (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (e : Fin d.edges) (u : LocalInternal) :
    ∃ p : ContactStripSite, dist ((d.contactEdge e).place
      (contactPoint p.axial p.transverse))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u)))) < 1 / 20 := by
  have hleft : localToContact (Sum.inr u) ≠ Sum.inl 0 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    simp only [contactToLocal, Matrix.cons_val_zero, localOld, reduceCtorEq] at heq
  have hright : localToContact (Sum.inr u) ≠
      contactGadgetRightNode (edgeNegative d.bonds e) 9 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    cases hn : edgeNegative d.bonds e <;>
      simp [contactToLocal, contactGadgetRightNode, localOld] at heq
  obtain ⟨p, hp⟩ := contactBaseGadget_internal_strip (edgeNegative d.bonds e)
    (localToContact (Sum.inr u)) hleft hright
  refine ⟨p, ?_⟩
  rw [globalPosition_internal, ContactGridEdge.place_dist, ← hp, dist_comm]
  exact hP e (Sum.inr u)

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactExtent
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact realization preserves polynomial coordinate extent. -/

noncomputable section
namespace ContinuumCoulomb

/-- Every internal strip remains within sixteen coordinate units of its
canonical lower/left lattice endpoint. -/
theorem ContactGridEdge.strip_coordinate_bound (e : ContactGridEdge) (p : ContactStripSite)
    (i : Fin 2) :
    |e.place (contactPoint p.axial p.transverse) i - contactGridPoint e.anchor i| ≤ 16 := by
  obtain ⟨q, hq⟩ := e.place_strip p
  rw [hq]
  cases h : e.vertical <;> fin_cases i <;>
    simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, horizontalContact, verticalContact,
      contactGridPoint]
  all_goals
    dsimp [contactPoint]
    apply abs_le.mpr
    constructor <;> linarith [q.axial_lower, q.axial_upper, q.transverse_lower, q.transverse_upper]

/-- A source edge's canonical anchor is one of its two actual endpoints. -/
theorem SquareLatticeHeisenberg.contactEdge_anchor (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) :
    (d.contactEdge e).anchor = d.coordinate (d.left e) ∨
      (d.contactEdge e).anchor = d.coordinate (d.right e) := by
  cases h : (d.contactEdge e).reversed
  · left
    simpa only [ContactGridEdge.left, h, Bool.false_eq_true, ite_false, if_false] using d.contactEdge_left e
  · right
    simpa only [ContactGridEdge.right, h, ite_true, if_true] using d.contactEdge_right e

namespace ContactMediator

theorem globalSite_card (d : SquareLatticeHeisenberg) :
    Fintype.card (GlobalSite d) = d.vertices + 18 * d.edges := by
  simp only [GlobalSite, Fintype.card_fin]
  ring

private theorem abs_le_add_abs_sub (x y : ℝ) : |x| ≤ |x - y| + |y| := by
  have h := abs_add_le (x - y) y
  simpa only [sub_add_cancel] using h

/-- Uniform coordinate bounds of the source control the full final graph,
including all eighteen fresh sites per edge. -/
theorem globalPosition_coordinate_bound (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) {M : ℝ}
    (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (x : GlobalSite d) (i : Fin 2) :
    |globalPosition d P x i| ≤ 17 * M + 17 := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  cases x with
  | inl j =>
    rw [globalPosition_old, contactGridPoint_apply, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)]
    linarith [hcoord j i]
  | inr eu =>
    rcases eu with ⟨e, u⟩
    obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
    let z := (d.contactEdge e).place (contactPoint p.axial p.transverse)
    have hanchor : |(contactGridAxis (d.contactEdge e).anchor i : ℝ)| ≤ M := by
      rcases d.contactEdge_anchor e with h | h
      · rw [h]
        exact hcoord (d.left e) i
      · rw [h]
        exact hcoord (d.right e) i
    have hb : |contactGridPoint (d.contactEdge e).anchor i| ≤ 17 * M := by
      rw [contactGridPoint_apply, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)]
      exact mul_le_mul_of_nonneg_left hanchor (by norm_num)
    have hz : |z i| ≤ 17 * M + 16 := by
      have ht := abs_le_add_abs_sub (z i) (contactGridPoint (d.contactEdge e).anchor i)
      have hs := (d.contactEdge e).strip_coordinate_bound p i
      dsimp only [z] at ht ⊢
      linarith
    have hd := contactPoint_coordinate_le_dist z
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u)))) i
    have ht := abs_le_add_abs_sub
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))) i) (z i)
    rw [abs_sub_comm] at ht
    linarith

end ContactMediator
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational local gadgets are glued through the exact final-graph
permutation. All old lattice sites remain fixed; all nineteen edges per
source edge retain a controlled error and all nonedges retain the margin. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGlobal
open ContactMediator MediatorIteration

theorem coordinate_bound (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {M : ℝ} (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (x : GlobalSite d) (i : Fin 2) : |point d P ℓ x i| ≤ 17 * M + 17 :=
  globalPosition_coordinate_bound d (localPoints d P ℓ) hcoord
    (fun e s => ContactRationalLocal.near_base P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) hP (fun _ => hℓ _) s) x i

theorem rationalPlace_cast (e : ContactGridEdge) (p : ℚ × ℚ) :
    contactPoint (rationalPlace e p).1 (rationalPlace e p).2 =
      e.place (contactPoint p.1 p.2) := by
  cases hv : e.vertical <;> cases hr : e.reversed <;> ext i <;> fin_cases i <;>
    simp [rationalPlace, ContactGridEdge.place, hv, hr, contactReflect,
      contactVertical, contactHorizontal, contactPoint, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]

theorem position_cast (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (x : GlobalSite d) : contactPoint (position d P ℓ x).1 (position d P ℓ x).2 = point d P ℓ x := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  cases x with
  | inl i =>
    simp [position, point, contactGridPoint, Rat.cast_mul]
  | inr eu =>
    rcases eu with ⟨e, u⟩
    simp only [position, Equiv.symm_apply_apply, rationalPlace_cast, point,
      globalPosition_internal]
    rfl

end ContinuumCoulomb.ContactRationalGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactCalibratedGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaled rational contact coordinates retain the actual Coulomb
calibration, with the coordinate and scalar-evaluation errors added
explicitly. The gap follows from the proved separated-density estimate. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration
open scoped BigOperators

theorem position_cast (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) :
    contactPoint (position d P q ℓ x).1 (position d P q ℓ x).2 = point d P q ℓ x := by
  unfold position point
  rw [← ContactRationalGlobal.position_cast]
  ext i
  fin_cases i <;> simp [contactPoint, Rat.cast_mul]

theorem coordinate_bound (d : SquareLatticeHeisenberg) (P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {M : ℝ} (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (x : GlobalSite d) (i : Fin 2) : |point d P q ℓ x i| ≤ (q : ℝ) * (17 * M + 17) := by
  change |(q : ℝ) * ContactRationalGlobal.point d P ℓ x i| ≤ _
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]
  exact mul_le_mul_of_nonneg_left
    (ContactRationalGlobal.coordinate_bound d P ℓ hP hℓ hcoord x i)
    (by exact_mod_cast hq.le)

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactCanonicalEdge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical strip record has an explicit finite computation from its
two lattice endpoints. This identifies the selected record with the record used by rational
coordinate programs. -/

namespace ContinuumCoulomb

theorem canonicalContactEdge_endpoints (e : ContactGridEdge) :
    canonicalContactEdge e.left e.right = e := by
  rcases e with ⟨v, ⟨a, b⟩, r⟩
  cases v <;> cases r <;>
    simp [canonicalContactEdge, ContactGridEdge.left, ContactGridEdge.right,
      ContactGridEdge.upper]

theorem SquareLatticeHeisenberg.contactEdge_computation (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) :
    d.contactEdge e = canonicalContactEdge (d.coordinate (d.left e)) (d.coordinate (d.right e)) := by
  rw [← d.contactEdge_left e, ← d.contactEdge_right e, canonicalContactEdge_endpoints]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGeometryBlockSemantics
attribute [-simp] _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The serialized blocks are the original iterated graph's vertex array,
through the explicit site permutation. No graph relabeling is assumed. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ContactMediator

private theorem lookup_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem block_ofFn {n r : ℕ} (f : Fin n → ContactGadgetSite) (g : Fin r → EdgeInput) :
    block (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun i : Fin (r * n) => ContactPlacedGadgetProgram.position
        (g i.divNat) (f i.modNat)) := by
  apply List.ext_getElem
  · simp only [block, List.length_map, List.length_range, List.length_ofFn, Nat.mul_comm]
  · intro i h₁ h₂
    have hi : i < r * n := by simpa only [List.length_ofFn] using h₂
    have hiq : i / n < r := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hi)
    have hn : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      simp [this] at hi
    have him : i % n < n := Nat.mod_lt _ hn
    simp only [block, List.getElem_map, List.getElem_range, List.getElem_ofFn, List.length_ofFn]
    rw [lookup_ofFn g defaultEdge ⟨i / n, hiq⟩, List.map_ofFn]
    rw [lookup_ofFn (ContactPlacedGadgetProgram.position (g ⟨i / n, hiq⟩) ∘ f)
      (0, 0) ⟨i % n, him⟩]
    rfl

theorem literal_position (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (e : Fin d.edges) (u : LocalInternal) :
    ContactPlacedGadgetProgram.position (literalEdge d P ℓ e) (localToContact (Sum.inr u)) =
      ContactRationalGlobal.position d P ℓ (siteEquiv d.vertices d.edges (Sum.inr (e, u))) := by
  simp only [ContactRationalGlobal.position, Equiv.symm_apply_apply]
  rw [d.contactEdge_computation]
  rfl

theorem literal_old (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (i : Fin d.vertices) :
    oldPoint (d.coordinate i) =
      ContactRationalGlobal.position d P ℓ (siteEquiv d.vertices d.edges (Sum.inl i)) := by
  simp only [ContactRationalGlobal.position, Equiv.symm_apply_apply, oldPoint]

theorem firstIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 2)) :
    (firstIndex d i).val = d.vertices + i.val := by
  simp [firstIndex, siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, finProdFinEquiv]
  omega

theorem secondIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) :
    (secondIndex d i).val = d.vertices + d.edges * 2 + i.val := by
  simp [secondIndex, siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, spokeIndex, finProdFinEquiv]
  omega

theorem thirdFirstIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) :
    (thirdFirstIndex d i).val = d.vertices + d.edges * 2 + d.edges * 2 * 2 + i.val := by
  simp [thirdFirstIndex, siteEquiv, encodeSite, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, pathIndex, spokeIndex, finProdFinEquiv]
  omega

theorem thirdSecondIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 8)) :
    (thirdSecondIndex d i).val =
      d.vertices + d.edges * 2 + d.edges * 2 * 2 + d.edges * 4 + i.val := by
  simp [thirdSecondIndex, siteEquiv, encodeSite, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, pathIndex, spokeIndex, finProdFinEquiv]
  omega

theorem first_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block firstSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (firstIndex d i)) := by
  rw [firstSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat (Sum.inl i.modNat)

theorem second_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block secondSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (secondIndex d i)) := by
  rw [secondSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat (Sum.inr (Sum.inl (finProdFinEquiv.symm i.modNat)))

theorem thirdFirst_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block thirdFirstSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdFirstIndex d i)) := by
  rw [thirdFirstSites, block_ofFn]
  congr 1
  funext i
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  exact literal_position d P ℓ i.divNat (Sum.inr (Sum.inr (Sum.inl st.1, st.2)))

theorem thirdSecond_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block thirdSecondSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdSecondIndex d i)) := by
  rw [thirdSecondSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat
    (Sum.inr (Sum.inr (Sum.inr (finProdFinEquiv.symm
      (finProdFinEquiv.symm i.modNat : Fin 4 × Fin 2).1),
        (finProdFinEquiv.symm i.modNat : Fin 4 × Fin 2).2)))

theorem literal_blocks (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ
        (siteEquiv d.vertices d.edges (Sum.inl i))) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (firstIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (secondIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdFirstIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdSecondIndex d i)) := by
  unfold positions literalInput
  rw [List.map_ofFn, first_block, second_block, thirdFirst_block, thirdSecond_block]
  have hold : List.ofFn (oldPoint ∘ d.coordinate) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ
        (siteEquiv d.vertices d.edges (Sum.inl i))) := by
    congr 1
    funext i
    exact literal_old d P ℓ i
  rw [hold]

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactEdgeNumber
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-number formulas for the exact final-edge permutation. These
are the indices used to fetch calibrated lengths from the emitted list. -/

namespace ContinuumCoulomb.ContactMediator

theorem pathIndex_val (r : ℕ) (e : Fin r) (p : LocalPath) :
    (pathIndex r e p).val = pathNumber r e.val p := by
  rcases p with s | ⟨s, t⟩ <;>
    simp [pathIndex, pathNumber, spokeIndex, finProdFinEquiv] <;> ring

theorem encodeEdge_val (r : ℕ) (e : Fin r) (a : LocalEdge) :
    (encodeEdge r e a).val = edgeNumber r e.val a := by
  rcases a with u | (p | ⟨p, t⟩)
  · simp [encodeEdge, edgeNumber]
  · simp [encodeEdge, edgeNumber, pathIndex_val]
  · simp [encodeEdge, edgeNumber, spokeIndex, finProdFinEquiv, pathIndex_val, Nat.add_assoc]
    ring

end ContinuumCoulomb.ContactMediator

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactSourceInputCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw-list program uses exactly the original source endpoints and
exactly the calibrated lengths of the final mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.ContactSourceInputProgram
open ContactMediator

private theorem lookup_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem local_lookup (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) (negative : Bool) (a : LocalEdge) :
    ContactLocalInputProgram.lookup
      (P, (d.edges, (e.val, (negative, List.ofFn ℓ)))) a = ℓ (encodeEdge d.edges e a) := by
  unfold ContactLocalInputProgram.lookup
  rw [← encodeEdge_val]
  exact lookup_ofFn ℓ 1 (encodeEdge d.edges e a)

theorem local_record (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) (negative : Bool) :
    ContactLocalInputProgram.record (P, (d.edges, (e.val, (negative, List.ofFn ℓ)))) =
      ContactRationalLocal.input P negative (fun a => ℓ (encodeEdge d.edges e a)) := by
  simp only [ContactLocalInputProgram.record, ContactRationalLocal.input, local_lookup]

theorem literal_bond (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) :
    bond (e.val, literalInput d P ℓ) = ((d.left e).val, ((d.right e).val, d.coefficient e)) := by
  change ((List.ofFn (fun e : Fin d.edges =>
    ((d.left e).val, ((d.right e).val, d.coefficient e)))).drop e.val).headD _ = _
  exact lookup_ofFn _ _ e

theorem literal_edge (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) :
    edge (e.val, literalInput d P ℓ) = ContactGeometryBlockProgram.literalEdge d P ℓ e := by
  unfold edge
  rw [literal_bond]
  change Prod.mk
    (Prod.mk (((List.ofFn d.coordinate).drop (d.left e).val).headD (0, 0))
      (((List.ofFn d.coordinate).drop (d.right e).val).headD (0, 0)))
    (ContactLocalInputProgram.record (P, ((d.bonds.toList).length,
      (e.val, (decide (d.coefficient e < 0), List.ofFn ℓ))))) = _
  rw [lookup_ofFn, lookup_ofFn]
  have hlen : d.bonds.toList.length = d.edges := by simp [MediatorIteration.Bonds.toList]
  rw [hlen, local_record]
  rfl

theorem literal_edges (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    edges (literalInput d P ℓ) =
      List.ofFn (ContactGeometryBlockProgram.literalEdge d P ℓ) := by
  apply List.ext_getElem
  · simp [edges, literalInput, MediatorIteration.Bonds.toList]
  · intro i h₁ h₂
    have hi : i < d.edges := by simpa only [List.length_ofFn] using h₂
    simp only [edges, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact literal_edge d P ℓ ⟨i, hi⟩

theorem literal_positions (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) =
      ContactGeometryBlockProgram.positions (ContactGeometryBlockProgram.literalInput d P ℓ) := by
  unfold positions
  rw [literal_edges]
  rfl

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactPositionArray
attribute [-simp] _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal coordinate list has the exact final mediator enumeration,
including the original vertices. This identifies the machine output with
the geometric realization without an unproved permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ContactMediator

private theorem siteCount (d : SquareLatticeHeisenberg) :
    d.vertices + d.edges * 2 + d.edges * 2 * 2 + (d.edges * 2 + d.edges * 2 * 2) * 2 =
      d.vertices + d.edges * 2 + d.edges * 4 + d.edges * 4 + d.edges * 8 := by omega

theorem literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) = List.ofFn (ContactRationalGlobal.position d P ℓ) := by
  rw [literal_blocks]
  conv_rhs =>
    rw [List.ofFn_congr (siteCount d)]
    rw [List.ofFn_add, List.ofFn_add, List.ofFn_add, List.ofFn_add]
  simp only [List.append_assoc]
  refine congrArg₂ List.append ?_ (congrArg₂ List.append ?_
    (congrArg₂ List.append ?_ (congrArg₂ List.append ?_ ?_)))
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (siteEquiv d.vertices d.edges (Sum.inl i)).val = i.val
    simp [siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.vertexEquiv]
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (firstIndex d i).val = d.vertices + i.val
    exact firstIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (secondIndex d i).val = d.vertices + d.edges * 2 + i.val
    exact secondIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (thirdFirstIndex d i).val = d.vertices + d.edges * 2 + d.edges * 4 + i.val
    simpa only [Nat.mul_assoc] using thirdFirstIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (thirdSecondIndex d i).val =
      d.vertices + d.edges * 2 + d.edges * 4 + d.edges * 4 + i.val
    simpa only [Nat.mul_assoc] using thirdSecondIndex_val d i

end ContinuumCoulomb.ContactGeometryBlockProgram

namespace ContinuumCoulomb.ContactSourceInputProgram
open ContactMediator

theorem literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) = List.ofFn (ContactRationalGlobal.position d P ℓ) := by
  rw [literal_positions, ContactGeometryBlockProgram.literal_array]

theorem scaled_literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) :
    scaledPositions (q, literalInput d P ℓ) =
      List.ofFn (fun x => (q * (ContactRationalGlobal.position d P ℓ x).1,
        q * (ContactRationalGlobal.position d P ℓ x).2)) := by
  simp only [scaledPositions, literal_array, List.map_ofFn, Function.comp_def]

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input and query bounds for the automatic calibrated-distance program.
The unary evaluator range is a fixed polynomial in the source size. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration

theorem interval_order {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (k N : ℕ) :
    (interval ε c k N).1 ≤ (interval ε c k N).2 := by
  have hq : (0 : ℚ) ≤ RationalLogScale.value c k N :=
    mul_nonneg hc (Nat.cast_nonneg _)
  dsimp only [interval, CalibrationRationalBracket.endpoints]
  nlinarith [mul_nonneg hε hq]

theorem value_mem {ε c : ℚ} (rho k A B : ℕ) (x : Input)
    (hε : 0 ≤ ε) (hc : 0 ≤ c) :
    value rho ε c k A B x ∈ Set.Icc (interval ε c k x.1).1 (interval ε c k x.1).2 :=
  CalibratedEvaluation.scheduledValue_mem rho (environment k A B x)
    (interval ε c k x.1).1 (interval ε c k x.1).2 (interval_order hε hc k x.1)

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The very same rational scale used by the search gives the rational
near-unit lengths supplied to the contact-coordinate program. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration
open ExactQuantumFactoring.BitStackProgram

theorem spacing_positive {c : ℚ} (hc : 0 < c) (k N : ℕ) (hN : 0 < N) :
    0 < spacing c k N := by
  have hb : 0 < (N ^ k).bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (pow_pos hN k)
  exact mul_pos hc (by exact_mod_cast hb)

theorem normalizedValue_mem (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (k A B : ℕ) (x : Input) (hN : 0 < x.1) :
    normalizedValue rho ε c k A B x ∈ Set.Icc (1 - ε / 2) (1 + ε / 2) := by
  have hq := spacing_positive hc k x.1 hN
  have hm := value_mem (rho := rho) (k := k) (A := A) (B := B) x hε hc.le
  change (1 - ε / 2) ≤ value rho ε c k A B x / spacing c k x.1 ∧
    value rho ε c k A B x / spacing c k x.1 ≤ (1 + ε / 2)
  constructor
  · apply (le_div_iff₀ hq).mpr
    exact hm.1
  · apply (div_le_iff₀ hq).mpr
    exact hm.2

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The composed numerical program outputs the actual rational geometric
realization of the final mediator graph, in its original vertex order. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedContactProgram
open ContactMediator

theorem raw_graphInput (rho : ℕ) (ε c : ℚ) (k A B N P H : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) :
    rawInput rho ε c k A B (graphInput d N P H K) =
      ContactSourceInputProgram.literalInput d H (graphLengths rho ε c k A B N P d K) := by
  simp only [rawInput, graphInput, AutomaticCalibrationList.value, List.map_ofFn,
    ContactSourceInputProgram.literalInput, Function.comp_def]
  rfl

theorem value_graphInput (rho : ℕ) (ε c : ℚ) (k A B N P H : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) :
    value rho ε c k A B (graphInput d N P H K) =
      List.ofFn (fun x => ContactCalibratedGeometry.position d H
        (AutomaticCalibration.spacing c k N) (graphLengths rho ε c k A B N P d K) x) := by
  unfold value
  rw [raw_graphInput]
  exact ContactSourceInputProgram.scaled_literal_array d H
    (AutomaticCalibration.spacing c k N) (graphLengths rho ε c k A B N P d K)

theorem graphLengths_near_one (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (hεtol : (ε : ℝ) / 2 ≤ contactLengthTolerance) (k A B N P : ℕ)
    (hN : 0 < N) (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) (a : GlobalEdge d) :
    (graphLengths rho ε c k A B N P d K a : ℝ) ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
  obtain ⟨hl, hu⟩ := AutomaticCalibration.normalizedValue_mem rho hε hc k A B
    (N, (P, K a)) hN
  have hl' : (1 : ℝ) - (ε : ℝ) / 2 ≤ graphLengths rho ε c k A B N P d K a := by
    exact_mod_cast hl
  have hu' : (graphLengths rho ε c k A B N P d K a : ℝ) ≤ 1 + (ε : ℝ) / 2 := by
    exact_mod_cast hu
  constructor <;> linarith

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationMesh
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compatibility between polynomial hopping amplification and the
equal masses of the unit-nucleus Gauss mesh. -/

namespace ContinuumCoulomb.CalibrationMesh

theorem base_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ base n := by
  exact (by norm_num : 2 ≤ 2^30).trans (Nat.pow_le_pow_left hn 30)

theorem base_power_eq_mesh_cube (n k : ℕ) : base n ^ k = mesh n k ^ 3 := by
  simp only [base,mesh,← pow_mul]
  congr 1
  omega

theorem amplification_eq_mesh (rho n k : ℕ) :
    amplification rho n k = 8*(mesh n k:ℚ)^3/(rho:ℚ) := by
  have he : (base n:ℚ)^k = (mesh n k:ℚ)^3 := by
    exact_mod_cast base_power_eq_mesh_cube n k
  rw [amplification,he,prefactor]
  ring

end ContinuumCoulomb.CalibrationMesh

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SlowLogarithmicExtent
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic spacing contributes only a hundredth of the adjustable
exponent. This closes the final analytic parameter inequalities without a
circular dependence on the spatial extent. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

theorem hundred_mul_le_two_pow (q : ℕ) (hq : 11 ≤ q) : 100*(q+1) ≤ 2^q := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hq
  induction r with
  | zero => norm_num
  | succ r ih =>
    calc
      100*(11+(r+1)+1) ≤ 2*(100*(11+r+1)) := by omega
      _ ≤ 2*2^(11+r) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2^(11+(r+1)) := by rw [show 11+(r+1)=11+r+1 by omega,pow_succ]; omega

theorem exponent_le_slow_power (k : ℕ) (hk : 1100 ≤ k) {N : ℝ} (hN : 2 ≤ N) :
    (k : ℝ) ≤ N^(k/100) := by
  have hq : 11 ≤ k/100 := by omega
  have hkn : k ≤ 100*(k/100+1) := by omega
  have hpow : (k : ℝ) ≤ (2:ℝ)^(k/100) := by
    exact_mod_cast hkn.trans (hundred_mul_le_two_pow _ hq)
  exact hpow.trans (pow_le_pow_left₀ (by norm_num) hN _)

theorem slow_logarithmic_extent (k s : ℕ) (hk : 1100 ≤ k)
    {N : ℝ} (hN : 2 ≤ N) :
    2*(31*(k:ℝ)*Real.log N)*(17*N^s+17) ≤ N^(k/100+s+13) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlog := (Real.log_le_sub_one_of_pos hNp).trans (show N-1 ≤ N by linarith)
  have hlog0 := Real.log_nonneg hN1
  have hsize : 17*N^s+17 ≤ 34*N^s := by nlinarith [one_le_pow₀ hN1 (n := s)]
  have hkpow := exponent_le_slow_power k hk hN
  have hC : (2108:ℝ) ≤ N^12 :=
    (by norm_num : (2108:ℝ) ≤ 2^12).trans (pow_le_pow_left₀ (by norm_num) hN 12)
  calc
    _ ≤ 2*(31*N^(k/100)*N)*(34*N^s) := by gcongr
    _ = 2108*(N^(k/100)*N^s*N) := by ring
    _ ≤ N^12*(N^(k/100)*N^s*N) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = N^(k/100+s+13) := by
      rw [show k/100+s+13=12+(k/100+s+1) by omega]
      simp only [pow_add,pow_one]

theorem slow_extent_parameter_closure (C k : ℕ) (hC : 4*C ≤ k) :
    C+72*(k/100) ≤ k := by omega

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactPolynomialGeometry
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed source spacing and rational precision imply precisely the
separation and spatial growth used by the continuum comparison. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator

theorem precision_ge_7200 {N h : ℕ} (hN : 2 ≤ N) (hh : 13 ≤ h) : 7200 ≤ N^h := by
  calc
    7200 ≤ 2^13 := by norm_num
    _ ≤ N^13 := Nat.pow_le_pow_left hN 13
    _ ≤ N^h := Nat.pow_le_pow_right (by omega) hh

theorem planar_norm_le_two (x : ContactPoint) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ i, |x i| ≤ C) : ‖x‖ ≤ 2*C := by
  have hnorm : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
  have h0 := (sq_le_sq₀ (abs_nonneg (x 0)) hC).mpr (hx 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (x 1)) hC).mpr (hx 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg x,sq_nonneg C]

theorem polynomial_norm (d : SquareLatticeHeisenberg) {N k s P : ℕ}
    (hN : 2 ≤ N) (hk : 1100 ≤ k) {q : ℚ} (hq : 0 < q)
    (hqhi : (q:ℝ) ≤ 31*(k:ℝ)*Real.log N) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    (hcoord : ∀ j i, |(contactGridAxis (d.coordinate j) i:ℝ)| ≤ (N:ℝ)^s)
    (x : GlobalSite d) : ‖point d P q ℓ x‖ ≤ (N:ℝ)^(k/100+s+13) := by
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ (q:ℝ)*(17*(N:ℝ)^s+17) := by positivity
  calc
    _ ≤ 2*((q:ℝ)*(17*(N:ℝ)^s+17)) :=
      planar_norm_le_two _ hc (coordinate_bound d P hq ℓ hP hℓ hcoord x)
    _ ≤ 2*(31*(k:ℝ)*Real.log N)*(17*(N:ℝ)^s+17) := by
      have hm := mul_le_mul_of_nonneg_right hqhi (show 0 ≤ 17*(N:ℝ)^s+17 by positivity)
      nlinarith only [hm]
    _ ≤ _ := slow_logarithmic_extent k s hk hNR

theorem polynomial_separation (d : SquareLatticeHeisenberg) (W G P N k : ℕ)
    (hN : 2 ≤ N) {q : ℚ} (hq : 0 < q)
    (hqlo : (59/2:ℝ)*(k:ℝ)*Real.log N ≤ q) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    (x y : GlobalSite d) (hxy : x ≠ y) :
    25*(k:ℝ)*Real.log N ≤ ‖point d P q ℓ x-point d P q ℓ y‖ := by
  have hs := separation d W G P hq ℓ hP hℓ x y hxy
  rw [dist_eq_norm] at hs
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  nlinarith

end ContinuumCoulomb.ContactCalibratedGeometry

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

theorem manufactured_frequency_positive {rho : ℕ} (hrho : 0 < rho) :
    0 < GaussianFrequency.frequency rho := lt_of_lt_of_le zero_lt_one (manufactured_frequency_ge_one hrho)

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial common denominator absorbs both coefficient rounding
and all three mediator errors into one inverse-polynomial promise budget. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

theorem positive_threshold_gap (d : SquareLatticeHeisenberg) (W G : ℕ) {a b : ℚ}
    (hgap : 1 / (G : ℚ) ≤ b - a) :
    63 / 64 * (b - a) ≤ upperThreshold d W G b - lowerThreshold d W G a := by
  have heq : 1 / (128 * (G : ℚ)) + 1 / (128 * (G : ℚ)) =
      1 / 64 * (1 / (G : ℚ)) := by ring
  unfold upperThreshold lowerThreshold
  linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizationCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The machine-normalized source registers are the literal bond family
whose complete positive-spin spectral and promise estimates were proved. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open MediatorListProgram

theorem size_pos (d : BinaryHeisenberg) : 0 < size d := by
  unfold size
  omega

theorem polynomialPromise_gap (k : ℕ) (d : BinaryHeisenberg)
    (hp : d.PolynomialPromise k) :
    1 / ((size d ^ k : ℕ) : ℚ) ≤ d.upper.value - d.lower.value := by
  have he : (1 : ℝ) / ((size d ^ k : ℕ) : ℝ) ≤
      ((d.upper.value : ℝ) - (d.lower.value : ℝ)) := by
    simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, one_div] using hp.gap_bound
  have hq := Rat.cast_le (K := ℝ).mp
    (show (((1 / ((size d ^ k : ℕ) : ℚ)) : ℚ) : ℝ) ≤
      (((d.upper.value - d.lower.value) : ℚ) : ℝ) by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sub] using he)
  exact hq

end ContinuumCoulomb.SourceMetadataProgram

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size bounds for the actual binary source serialization. In particular,
the number of sites and edges is bounded by the input bit length. -/

namespace ContinuumCoulomb
open BinaryEncoding

namespace BinaryEncoding

theorem natural_length_pos (n : ℕ) : 0 < (natural.encode n).length := by
  rw [natural_length]
  omega

theorem integer_length_pos (z : ℤ) : 0 < (integer.encode z).length := by
  cases z <;> simp only [integer, List.length_cons] <;> omega

theorem list_count_le {α : Type*} (a : Codec α) (ha : ∀ x, 0 < (a.encode x).length)
    (xs : List α) : xs.length ≤ ((list a).encode xs).length := by
  have hsum : xs.length ≤ (xs.map (fun x => (a.encode x).length)).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hx := ha x
      omega
  rw [list_length]
  omega

end BinaryEncoding

theorem binaryHeisenbergEdge_length_pos (e : BinaryHeisenbergEdge) :
    0 < (binaryHeisenbergEdgeCodec.encode e).length := by
  change 0 < (natural.encode e.left ++
    (natural.encode e.right ++ binaryRationalCodec.encode e.coefficient)).length
  simp only [List.length_append]
  have h := natural_length_pos e.left
  omega

theorem binaryHeisenberg_count_le_length (d : BinaryHeisenberg) :
    d.coordinate.length + d.edges.length ≤ (binaryHeisenbergCodec.encode d).length := by
  have hc := list_count_le (pair integer integer)
    (fun p => by rw [pair_length]; have h := integer_length_pos p.1; omega) d.coordinate
  have he := list_count_le binaryHeisenbergEdgeCodec binaryHeisenbergEdge_length_pos d.edges
  change d.coordinate.length + d.edges.length ≤
    ((BinaryEncoding.list (pair integer integer)).encode d.coordinate ++
      ((BinaryEncoding.list binaryHeisenbergEdgeCodec).encode d.edges ++
        (binaryRationalCodec.encode d.lower ++ binaryRationalCodec.encode d.upper))).length
  simp only [List.length_append]
  omega

/-- The promised polynomial extent holds for every actual decoded lattice site. -/
theorem binaryHeisenberg_decoded_extent (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) (i : Fin (d.toSource h).vertices) :
    |(((d.toSource h).coordinate i).1 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ∧
      |(((d.toSource h).coordinate i).2 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k := by
  exact hp.coordinate_bound (d.coordinate.get i) (List.get_mem d.coordinate i)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source normalization and metadata programs give one fixed
polynomial coefficient exponent for the final positive-spin graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

attribute [local irreducible] MediatorParameters.finalWeight

theorem retained_count_le (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      d.edges.length := by
  have hf := List.length_filter_le SourceZeroFilter.keep
    (SourceNormalizedSpectrum.rounded (d.toSource h) (roundingDenominator k d))
  simpa only [SourceNormalizedSpectrum.retained, SourceNormalizedSpectrum.rounded,
    List.length_ofFn, BinaryHeisenberg.toSource] using hf

theorem positive_graph_count_bound (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    d.coordinate.length + 18 *
        (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length ∧
    19 * (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length ≤
      19 * (binaryHeisenbergCodec.encode d).length := by
  have hr := retained_count_le k d h
  have hc := binaryHeisenberg_count_le_length d
  constructor <;> omega

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGeometryBounds
attribute [-simp] _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial site counts, coordinate extent and coefficient ranges for
the literal normalized source passed to the contact realization. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ContactMediator

private theorem nineteen_mul_le_sixth (L : ℕ) : 19 * L ≤ (L + 2) ^ 6 := by
  have h19 : 19 ≤ (L + 2) ^ 5 :=
    (by norm_num : 19 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left (by omega) 5)
  calc
    19 * L ≤ (L + 2) ^ 5 * (L + 2) := Nat.mul_le_mul h19 (by omega)
    _ = (L + 2) ^ 6 := by ring

theorem geometricSource_count (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (Fintype.card (GlobalSite (geometricSource k d h)) : ℝ) ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ 6 := by
  have hc := (positive_graph_count_bound k d h).1
  have hp := hc.trans (nineteen_mul_le_sixth (binaryHeisenbergCodec.encode d).length)
  rw [globalSite_card]
  change ((d.coordinate.length + 18 *
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length : ℕ) : ℝ) ≤ _
  exact_mod_cast hp

theorem geometricSource_coordinates (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) (j : Fin (geometricSource k d h).vertices) (i : Fin 2) :
    |(contactGridAxis ((geometricSource k d h).coordinate j) i : ℝ)| ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ k := by
  have he := binaryHeisenberg_decoded_extent k d h hp j
  have hpow : ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  change |(contactGridAxis ((d.toSource h).coordinate j) i : ℝ)| ≤ _
  fin_cases i
  · exact he.1.trans hpow
  · exact he.2.trans hpow

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact semantics of the computed positive-spin source reduction: the
literal output has the full three-stage matrix and the proved rational
thresholds, including the common coefficient-rounding error. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram

theorem normalized_literal (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    normalized k d = literalInput (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  rw [normalized, normalized_eq k d h]
  unfold literalInput sourceFamily SourceNormalizedSpectrum.family
  rw [bonds_toList]
  rfl

theorem bonds_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).bonds =
      (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).toList := by
  change MediatorThreeStageProgram.finalBonds (normalized k d) = _
  rw [normalized_literal]
  exact (finalGraph_toList _ _ _).symm

theorem offset_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    offset k d = MediatorIteration.offset (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  unfold offset
  rw [normalized_literal, offset_toList]

theorem lower_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).lower = SourceNormalizedSpectrum.lowerThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.lower.value := by
  change d.lower.value - offset k d + error k d = _
  rw [offset_eq]
  rfl

theorem upper_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).upper = SourceNormalizedSpectrum.upperThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.upper.value := by
  change d.upper.value - offset k d - error k d = _
  rw [offset_eq]
  rfl

theorem output_gap (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    63 / 64 * (d.upper.value - d.lower.value) ≤ (output k d).upper - (output k d).lower := by
  rw [upper_eq k d h, lower_eq k d h]
  exact SourceNormalizedSpectrum.positive_threshold_gap _ _ _ (polynomialPromise_gap k d hp)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw-source program has exactly the normalized lattice geometry and
the full three-stage positive weights, including their original order. -/

noncomputable section
namespace ContinuumCoulomb.SourceContactProgram
open ContactMediator

theorem coordinates_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    d.coordinate = List.ofFn (SourceMetadataProgram.geometricSource s d hd).coordinate := by
  exact (List.ofFn_get d.coordinate).symm

theorem signedBonds_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.normalized s d).2 =
      (SourceMetadataProgram.geometricSource s d hd).bonds.toList := by
  rw [SourcePositiveProgram.normalized_literal s d hd]
  rfl

theorem weights_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2) =
      List.ofFn (weights s d hd) := by
  rw [SourcePositiveProgram.bonds_eq s d hd]
  simp only [MediatorIteration.Bonds.toList,List.map_ofFn,Function.comp_def]
  rfl

end ContinuumCoulomb.SourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorSourceContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefactor-aware program retains the exact final graph enumeration,
and calibrates its original weights at the physical unit-charge scale. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

theorem electron_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.output s d).vertices =
      Fintype.card (GlobalSite (SourceMetadataProgram.geometricSource s d hd)) := by
  rw [SourcePositiveProgram.vertices_eq s d hd]
  simp only [GlobalSite,Fintype.card_fin]
  rfl

theorem input_eq_graphInput (a : ℚ) (C s p h : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    input a C s p h d = CalibratedContactProgram.graphInput
      (SourceMetadataProgram.geometricSource s d hd)
      (CalibrationMesh.base (SourceContactProgram.size d))
      (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
      (SourceContactProgram.size d ^ h) (weights a s d hd) := by
  unfold input CalibratedContactProgram.graphInput
  rw [SourceContactProgram.coordinates_eq s d hd,SourceContactProgram.signedBonds_eq s d hd,
    SourceContactProgram.weights_eq s d hd,List.map_ofFn]
  rfl

theorem value_eq_array (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    value rho a C ε c s p h k A B d = List.ofFn (fun x =>
      ContactCalibratedGeometry.position (SourceMetadataProgram.geometricSource s d hd)
        (SourceContactProgram.size d ^ h)
        (AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)))
        (CalibratedContactProgram.graphLengths rho ε c k A B
          (CalibrationMesh.base (SourceContactProgram.size d))
          (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
          (SourceMetadataProgram.geometricSource s d hd) (weights a s d hd)) x) := by
  unfold value
  rw [input_eq_graphInput]
  exact CalibratedContactProgram.value_graphInput _ _ _ _ _ _ _ _ _ _ _

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SourceBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal completion of a many-spin source map on the one-spin branch.
The resulting reduction covers every valid source instance. -/

noncomputable section
namespace ContinuumCoulomb.SourceBranchProgram
open ExactQuantumFactoring.BitStackProgram

theorem positive_output_vertices (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hv : 2 ≤ d.coordinate.length) : 2 ≤ (SourcePositiveProgram.output s d).vertices := by
  rw [SourcePositiveProgram.vertices_eq s d hd]
  omega

end ContinuumCoulomb.SourceBranchProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePhysicalThreshold
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

theorem gap (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) (d : BinaryHeisenberg) :
    (value rho C ε c s p h k A B q d).2-(value rho C ε c s p h k A B q d).1 =
      CenteredPhysicalThreshold.amplification rho (SourceContactProgram.size d^(10*k))*
        (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)^2*
          ((SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower) := by
  exact AffinePhysicalThreshold.gap rho (input rho C ε c s p h k A B q d)

end ContinuumCoulomb.SourcePhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGridGeometry
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

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFinalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact final graph indexed by the literal output vertex count.
Changing only the proof of that count preserves every bond and weight. -/

noncomputable section

namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram ContactMediator

theorem graph_toList (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).toList=(output s d).bonds := by
  unfold graph
  erw [Bonds.castSites_toList]
  exact (bonds_eq s d hd).symm

theorem graph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).weight=SourceContactProgram.weights s d hd := by
  unfold graph
  erw [Bonds.castSites_weight]
  rfl

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGraphIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contact-site enumeration and the finite Hubbard graph use
one common electron index. Relabeling changes no bond or coordinate order. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration ContactMediator SourceMetadataProgram

theorem indexedGraph_toList (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) :
    (indexedGraph s d hd hm).toList=(output s d).bonds := by
  rw [indexedGraph,Bonds.castSites_toList,graph_toList]

theorem indexedGraph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) :
    (indexedGraph s d hd hm).weight=SourceContactProgram.weights s d hd := by
  rw [indexedGraph,Bonds.castSites_weight,graph_weight]

private theorem ofFn_finCongr {α : Type*} {n m : ℕ} (h : n=m) (f : Fin n → α) :
    List.ofFn (fun i => f ((finCongr h).symm i)) = List.ofFn f := by
  subst m
  rfl

theorem indexedSites_ofFn {α : Type*} (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) (f : GlobalSite (geometricSource s d hd) → α) :
    List.ofFn (fun i => f ((indexedSites s d hd hm).symm i))=List.ofFn f := by
  unfold indexedSites siteEquiv
  change List.ofFn (fun i => f ((finCongr (rawSiteCount s d hd)).symm
    ((finCongr hm).symm i)))=List.ofFn f
  exact (ofFn_finCongr hm (fun i => f ((finCongr (rawSiteCount s d hd)).symm i))).trans
    (ofFn_finCongr (rawSiteCount s d hd) f)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceIndexedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal nuclear program's planar sites, expressed in the same
index type as its finite Hubbard graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram ContactMediator

theorem sites_eq_indexed (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) :
    sites rho C eps c s p h k A B d =
      List.ofFn (indexedCoordinates rho C eps c s p h k A B d hd hm) := by
  unfold sites
  rw [PrefactorSourceContactProgram.value_eq_array]
  exact (SourcePositiveProgram.indexedSites_ofFn s d hd hm
    (rawSites rho C eps c s p h k A B d hd)).symm

theorem indexed_position (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) (i : Fin (m+1)) :
    PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i) =
      ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
        (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd)
        ((SourcePositiveProgram.indexedSites s d hd hm).symm i) := by
  exact ContactCalibratedGeometry.position_cast _ _ _ _ _

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceIndexedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual indexed source array inherits the exact separation and
polynomial norm estimates of its rational contact construction. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram ContactMediator

theorem contactSpacing_positive {c : ℚ} (hc : 0 < c) (k : ℕ) (d : BinaryHeisenberg) :
    0 < contactSpacing c k d :=
  AutomaticCalibration.spacing_positive hc k _
    (lt_of_lt_of_le (by decide : 0 < 2) (CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)))

theorem contactLengths_near_one (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (e : GlobalEdge (geometricSource s d hd)) :
    (contactLengths rho C eps c s p k A B d hd e:ℝ) ∈
      Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance) :=
  CalibratedContactProgram.graphLengths_near_one rho heps hc htol k A B
    (CalibrationMesh.base (SourceContactProgram.size d))
    (PrefactorCalibration.precision C (SourceContactProgram.size d^p))
    (lt_of_lt_of_le (by decide : 0 < 2) (CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)))
    (geometricSource s d hd) _ e

private theorem source_coordinate_bound (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) (j : Fin (geometricSource s d hd).vertices) (i : Fin 2) :
    |(contactGridAxis ((geometricSource s d hd).coordinate j) i:ℝ)| ≤
      (SourceContactProgram.size d:ℝ)^s := by
  have hN : (SourceContactProgram.size d:ℝ)=(binaryHeisenbergCodec.encode d).length+2 := by
    unfold SourceContactProgram.size SourceMetadataProgram.size
    push_cast
    ring
  rw [hN]
  exact geometricSource_coordinates s d hd hp j i

theorem indexed_norm_bound (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (hp : d.PolynomialPromise s)
    (hk : 1100 ≤ k) (hP : 7200 ≤ SourceContactProgram.size d^h)
    (hqhi : (contactSpacing c k d:ℝ) ≤ 31*(k:ℝ)*Real.log (SourceContactProgram.size d))
    {m : ℕ} (hm : (SourcePositiveProgram.output s d).vertices=m+1) (i : Fin (m+1)) :
    ‖PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i)‖ ≤
      (SourceContactProgram.size d:ℝ)^(k/100+s+13) := by
  rw [indexed_position]
  exact ContactCalibratedGeometry.polynomial_norm (geometricSource s d hd)
    (SourceContactProgram.size_ge_two d) hk (contactSpacing_positive hc k d) hqhi _ hP
    (contactLengths_near_one rho C heps hc htol s p k A B d hd)
    (source_coordinate_bound s d hd hp) _

theorem indexed_separation (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid)
    (hP : 7200 ≤ SourceContactProgram.size d^h)
    (hqlo : (59/2:ℝ)*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ contactSpacing c k d)
    {m : ℕ} (hm : (SourcePositiveProgram.output s d).vertices=m+1)
    (i j : Fin (m+1)) (hij : i ≠ j) :
    25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤
      ‖PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i)-
        PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm j)‖ := by
  rw [indexed_position,indexed_position]
  exact ContactCalibratedGeometry.polynomial_separation (geometricSource s d hd)
    (SourcePositiveProgram.sourceBound s d) (size d^s) (SourceContactProgram.size d^h)
    (SourceContactProgram.size d) k (SourceContactProgram.size_ge_two d)
    (contactSpacing_positive hc k d) hqlo _ hP
    (contactLengths_near_one rho C heps hc htol s p k A B d hd) _ _
    (fun he => hij ((SourcePositiveProgram.indexedSites s d hd hm).symm.injective he))

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceContactTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of nominal distances and hopping matrices to the
literal source's common vertex order. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram SourcePositiveProgram ContactMediator HubbardGlobal

theorem amplification_calibration (rho k : ℕ) (d : BinaryHeisenberg) :
    amplification rho k d=CalibrationMesh.amplification rho (SourceContactProgram.size d) k := by
  rw [amplification,CalibrationMesh.amplification_eq_mesh]
  rfl

theorem calibration_base_power (B : ℕ) (d : BinaryHeisenberg) :
    (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^B=
      (SourceContactProgram.size d:ℝ)^(30*B) := by
  simp only [CalibrationMesh.base,Nat.cast_pow,← pow_mul]

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHubbardEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-spin and scalar-offset identities for the literal source
bond list. These identify the Hubbard center with the computed threshold center. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open MediatorIteration HubbardGlobal

namespace SourcePhysicalThreshold

theorem exactHubbardEnergy_eq (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (F : Bonds (m+1) r) (t : Fin r → ℝ)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1) :
    exactHubbardEnergy rho C eps c s p h k A B q d u F t =
      (SourceNuclearProgram.amplification rho k d : ℝ)^2*(m+1:ℝ)*
        (slabPotential rho (slabHorizontal k d) (slabVertical k d) 0+
          ((-1/2:ℝ)+GaussianFrequency.frequency rho/2)) +
      (SourceNuclearProgram.amplification rho k d : ℝ)*
        (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
          (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
            (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
          (1/2:ℝ)*∑ i, ∑ j, localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
            (fun i => PlanarForcingProgram.position (u i)) i j) := by
  simp only [exactHubbardEnergy,CenteredPhysicalThreshold.actualOffset,
    CenteredPhysicalThreshold.actualReference,input,SourceNuclearProgram.amplification,
    hvertices,Nat.cast_add,Nat.cast_one,CoulombPairSum.exactTotal,localizedOffsiteCoulomb,
    slabHorizontal,slabVertical]
  ring

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceParameterSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous exponent choice for the actual source construction.
The spatial extent depends on the chosen calibration exponent, but only
through its hundredth; all numerical precisions are chosen afterwards. -/

namespace ContinuumCoulomb

theorem exists_source_exponent_threshold
    (qCloud qNonedge qGap qLeak qScale r s v B : ℕ) :
    ∃ kmin : ℕ, 1100 ≤ kmin ∧ ∀ k : ℕ, kmin ≤ k →
      let extent := s+k/100+13
      let p := 60*B+s+14
      qCloud+9*r+72*extent+v+p ≤ k ∧
      qNonedge+extent+(2*r+p+8) ≤ 5*k ∧
      qGap+2*B+s ≤ k ∧ qLeak ≤ k ∧ qScale ≤ k := by
  let C := qCloud+qNonedge+qGap+qLeak+qScale+9*r+72*(s+13)+v+
    (60*B+s+14)+2*B+8
  refine ⟨4*C+1100,by omega,fun k hk => ?_⟩
  have hC : 4*C ≤ k := by omega
  have hslow := ContactMediator.slow_extent_parameter_closure C k hC
  dsimp only
  dsimp only [C] at hslow
  omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceFiniteBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-Hamiltonian bounds used before selecting the source
geometry and numerical precision. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localLeakageBound_antitone (freq : ℝ) {a b : ℝ} (hab : a ≤ b) :
    localLeakageBound freq b ≤ localLeakageBound freq a := by
  unfold localLeakageBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))
    (MeasureTheory.integral_nonneg (fun _ => abs_nonneg _))

theorem exists_source_leakage_threshold {freq : ℝ} (hfreq : 0 < freq) (R : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (k : ℕ), q ≤ k → ∀ (N D : ℝ), 2 ≤ N →
      25*(k:ℝ)*Real.log N ≤ D → ∀ M : ℕ, (M:ℝ) ≤ N^R →
      5 ≤ D ∧ (M:ℝ)*localLeakageBound freq D ≤ localDualMass freq/2 := by
  obtain ⟨q,hq,hspacing⟩ := exists_localizedGram_spacing hfreq R
  refine ⟨q,by omega,fun k hk N D hN hD M hM => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hqk : (q:ℝ) ≤ 25*(k:ℝ) := by
    have hh : (q:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg k (α := ℝ)]
  have hqd : (q:ℝ)*Real.log N ≤ D := (mul_le_mul_of_nonneg_right hqk hlog).trans hD
  obtain ⟨hfive,hleak⟩ := hspacing N hN
  refine ⟨hfive.trans hqd,?_⟩
  exact (mul_le_mul hM (localLeakageBound_antitone freq hqd)
    (localLeakageBound_nonnegative freq D) (by positivity)).trans hleak

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceTargetHubbard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal positive source graph satisfies the finite Hubbard
approximation with uniform exponents fixed before its coordinates are chosen. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceMetadataProgram ContactMediator HubbardGlobal

private theorem source_size_cast (d : BinaryHeisenberg) :
    (SourceContactProgram.size d:ℝ)=(binaryHeisenbergCodec.encode d).length+2 := by
  unfold SourceContactProgram.size SourceMetadataProgram.size
  push_cast
  ring

theorem source_graph_site_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    ((output s d).vertices:ℝ) ≤ (SourceContactProgram.size d:ℝ)^6 := by
  rw [PrefactorSourceContactProgram.electron_count s d hd,source_size_cast]
  exact geometricSource_count s d hd

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceThresholdGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rational output gap is at least one at a fixed polynomial
amplification. The same scale also dominates the numerical error budget. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_source_gap_offset {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ s B k : ℕ, q+2*B+s ≤ k →
      ∀ N M : ℝ, 2 ≤ N → 0 ≤ M → M ≤ N →
      2*M^s ≤ (a*(N^k)^30)*((N^(30*B))⁻¹)^2 := by
  obtain ⟨q,hq,hbounds⟩ := exists_polynomial_constant_bounds (by positivity : 0 < a/2) 1
  refine ⟨q,by omega,fun s B k hk N M hN hM hMN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hratio := (hbounds N hN).1
  have hconst : 2 ≤ a*N^q := by
    have he := (inv_le_iff_one_le_mul₀ (pow_pos hN0 q)).mp hratio
    nlinarith
  rw [inv_pow]
  apply (le_mul_inv_iff₀ (sq_pos_of_pos (pow_pos hN0 (30*B)))).mpr
  calc
    2*M^s*(N^(30*B))^2 ≤ (a*N^q)*N^s*(N^(30*B))^2 := by
      gcongr
    _ = a*N^(q+s+60*B) := by
      rw [pow_add N (q+s) (60*B),pow_add N q s,
        show 60*B=(30*B)*2 by omega,pow_mul]
      ring
    _ ≤ a*(N^k)^30 := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (by omega)) ha.le

namespace SourcePhysicalThreshold

theorem gap_ge_one (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (hp : d.PolynomialPromise s)
    (hscale : 2*((SourceMetadataProgram.size d:ℝ)^s) ≤
      (SourceNuclearProgram.amplification rho k d:ℝ)*
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2) :
    (1:ℚ) ≤ (value rho C eps c s p h k A B q d).2-
      (value rho C eps c s p h k A B q d).1 := by
  have hsource := SourcePositiveProgram.output_gap s d hd hp
  have hgap := SourceMetadataProgram.polynomialPromise_gap s d hp
  have hG0 : (0:ℚ) < (SourceMetadataProgram.size d:ℚ)^s :=
    pow_pos (by exact_mod_cast SourceMetadataProgram.size_pos d) s
  have hpos : (0:ℝ) < (SourceMetadataProgram.size d:ℝ)^s := by exact_mod_cast hG0
  have hlow : (63:ℝ)/(64*((SourceMetadataProgram.size d:ℝ)^s)) ≤
      ((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower := by
    have hh : (63:ℚ)/64*(1/(SourceMetadataProgram.size d:ℚ)^s) ≤
        (SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower := by
      simpa only [Nat.cast_pow] using
        (mul_le_mul_of_nonneg_left hgap (by norm_num : (0:ℚ) ≤ 63/64)).trans hsource
    have hhR : (63:ℝ)/64*(1/(SourceMetadataProgram.size d:ℝ)^s) ≤
        ((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow,
        Rat.cast_natCast,Rat.cast_sub] using (Rat.cast_le (K := ℝ)).mpr hh
    convert hhR using 1 <;> first | rfl | ring
  let scale := (SourceNuclearProgram.amplification rho k d:ℝ)*
    (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2
  have hs : 0 ≤ scale := (by positivity : (0:ℝ) ≤ 2*(SourceMetadataProgram.size d:ℝ)^s).trans hscale
  have hprod := mul_le_mul hscale hlow (by positivity : (0:ℝ) ≤ 63/(64*(SourceMetadataProgram.size d:ℝ)^s)) hs
  have hone : (1:ℝ) ≤ scale*
      (((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower) := by
    have he : 2*(SourceMetadataProgram.size d:ℝ)^s*(63/(64*(SourceMetadataProgram.size d:ℝ)^s)) = 63/32 := by
      field_simp [hpos.ne']
      ring
    rw [he] at hprod
    linarith
  rw [gap]
  change (1:ℚ) ≤ SourceNuclearProgram.amplification rho k d *
    (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)^2 *
      ((SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower)
  dsimp only [scale] at hone
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_one,Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_natCast,Rat.cast_sub] using hone

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceConditionalReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A polynomial-time source-to-unit-Coulomb reduction under explicit
analytic hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceNuclearProgram HubbardGlobal

theorem exists_source_unit_reduction_with_planar_gap_oai
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (s : ℕ) :
    Nonempty (PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise s) unitCoulombPromise) := by
  obtain ⟨rho,hrho,U,Fnum,Knum,qCloud,_hqCloud,hcloud⟩ :=
    source_cloud_comparison hflow hp hv hdensity
  have ha : (0:ℝ) < 8/(rho:ℝ) := div_pos (by norm_num) (by exact_mod_cast hrho)
  have hfreq := manufactured_frequency_positive hrho
  obtain ⟨Aweight,B,v,qTarget,_hAw,_hB,_hv,_hqTarget,htarget⟩ :=
    exists_source_target_parameters rho hrho s (s+14)
  obtain ⟨qLeak,_hqLeak,hleak⟩ := exists_source_leakage_threshold hfreq 6
  obtain ⟨qN,qC,_hqN,_hqC,hmat⟩ := exists_indexed_matrix_offsets rho hrho
  obtain ⟨qGap,_hqGap,hgap⟩ := exists_source_gap_offset ha
  obtain ⟨qScale,_hqScale,hscale⟩ := exists_manufactured_scale_threshold ha
  obtain ⟨kmin,hmin,hthreshold⟩ :=
    exists_source_exponent_threshold qCloud qN qGap (qTarget+qLeak) qScale 6 s v B
  let eps : ℚ := 1/100000000
  have heps : 0 < eps := by norm_num [eps]
  have hepsSmall : eps ≤ 1/1000 := by norm_num [eps]
  have htol : (eps:ℝ)/2 ≤ contactLengthTolerance := by norm_num [eps,contactLengthTolerance]
  obtain ⟨C,A,c,k,_hC,hc,_hk,hkmin,hcal⟩ :=
    PrefactorSourceContactProgram.exists_source_calibration rho hrho eps heps hepsSmall s B kmin
  have hkminN : kmin ≤ k := by exact_mod_cast hkmin
  have hkBig : 1100 ≤ k := hmin.trans hkminN
  have hconstraints := hthreshold k hkminN
  let extent := s+k/100+13
  let p := 60*B+s+14
  let pc := 12+p+9
  let h := qC+30*k+30*Aweight+extent+(12+p+7)+15
  let ap := qCloud+465*k+12+v+p+34
  let f := SourceUnitCoulomb.value rho C U Fnum Knum eps c s pc h k A B p ap
  have hcorrect (d : BinaryHeisenberg) (hd : d.Valid) (hpoly : d.PolynomialPromise s)
      (hvertices : 2 ≤ d.coordinate.length) :
      (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value → f d ∈ unitCoulombPromise.yes) ∧
      ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) → f d ∈ unitCoulombPromise.no) := by
    have hMtwo := SourceBranchProgram.positive_output_vertices s d hd hvertices
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hMtwo
    let m := n+1
    have hm : (output s d).vertices=m+1 := by dsimp only [m]; omega
    let N := SourceContactProgram.size d
    let u := indexedCoordinates rho C eps c s pc h k A B d hd hm
    let uu := fun i => PlanarForcingProgram.position (u i)
    let graph := indexedGraph s d hd hm
    let τ := ((N:ℝ)^(30*B))⁻¹
    let t := fun e => -coulombHoppingTarget (GaussianFrequency.frequency rho) τ (graph.weight e)
      ‖uu (graph.left e)-uu (graph.right e)‖
    let D := 25*(k:ℝ)*Real.log N
    have hN : 2 ≤ N := SourceContactProgram.size_ge_two d
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by norm_num) hNR
    have hN1 : (1:ℝ) ≤ N := le_trans (by norm_num) hNR
    have hhk : qCloud+9*6+72*extent+v+p ≤ k := by
      simpa only [extent,p] using hconstraints.1
    have hhP : 13 ≤ h := by dsimp [h]; omega
    have hP : 7200 ≤ N^h := ContactCalibratedGeometry.precision_ge_7200 hN hhP
    have hspacing := (hcal d hd hpoly).1
    have hsites : sites rho C eps c s pc h k A B d=List.ofFn u :=
      sites_eq_indexed rho C eps c s pc h k A B d hd hm
    have hcount : (m+1:ℕ) ≤ (N:ℝ)^6 := by
      rw [← hm]
      exact source_graph_site_count s d hd
    have hnorm (i : Fin (m+1)) : ‖uu i‖ ≤ (N:ℝ)^extent := by
      have hn := indexed_norm_bound rho C heps.le hc htol s pc h k A B d hd hpoly hkBig hP hspacing.2 hm i
      simpa only [uu,u,extent,N,Nat.add_comm s (k/100)] using hn
    have hsep (i j : Fin (m+1)) (hij : i ≠ j) : D ≤ ‖uu i-uu j‖ :=
      indexed_separation rho C heps.le hc htol s pc h k A B d hd hP hspacing.1 hm i j hij
    have hqLeak : qLeak ≤ k := by omega
    obtain ⟨hD,hleakM⟩ := hleak k hqLeak N D hNR le_rfl (m+1) hcount
    have hleakTwo : 2*localLeakageBound (GaussianFrequency.frequency rho) D ≤
        localDualMass (GaussianFrequency.frequency rho)/2 := by
      have hMtwoR : (2:ℝ) ≤ (m+1:ℕ) := by exact_mod_cast (show 2 ≤ m+1 by dsimp [m]; omega)
      exact (mul_le_mul_of_nonneg_right hMtwoR
        (localLeakageBound_nonnegative (GaussianFrequency.frequency rho) D)).trans hleakM
    have hqTarget : qTarget ≤ k := by omega
    obtain ⟨hweights,ht,hfinite⟩ := htarget d hd hpoly m k hm hqTarget D uu le_rfl hsep
    have hFweight : graph.weight=SourceContactProgram.weights s d hd := indexedGraph_weight s d hd hm
    have hKw (e : ContactMediator.GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) :
        0 ≤ (SourceContactProgram.weights s d hd e:ℝ) ∧
          (SourceContactProgram.weights s d hd e:ℝ) ≤ (N:ℝ)^(30*Aweight) := by
      have hw := hweights e
      rw [hFweight] at hw
      exact ⟨(inv_nonneg.mpr (pow_nonneg hN0.le _)).trans hw.1,hw.2⟩
    have hnom (e : ContactMediator.GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) :
        let r := PrefactorSourceContactProgram.nominalDistance rho (CalibrationMesh.prefactor rho)
          C eps c s pc k A B d hd e
        |(amplification rho k d:ℝ)*planarHopping r-
          coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^(30*B))⁻¹
            (SourceContactProgram.weights s d hd e) r| ≤ ((N:ℝ)^pc+1)⁻¹ := by
      have hh := ((hcal d hd hpoly).2 pc e).2.2.2
      simpa only [amplification_calibration,calibration_base_power] using hh
    have hknMatrix : qN+extent+(12+p+8) ≤ 5*k := by
      simpa only [extent,p] using hconstraints.2.1
    have hmatrix := hmat C s pc h k A B (30*Aweight) (12+p+7) eps c d hd hpoly heps.le hc htol
      hkBig hhP (by dsimp only [extent] at hknMatrix ⊢; omega) (by dsimp [h,extent]; omega)
      (by dsimp [pc]; omega) hD hspacing hleakTwo hKw hnom m hm
    have hs : 1 ≤ (amplification rho k d:ℝ) := by
      rw [amplification_real]
      exact hscale k (by omega) N hNR
    have hMN : (SourceMetadataProgram.size d:ℝ) ≤ N := by
      dsimp only [N,SourceContactProgram.size]
      rw [Nat.cast_add,Nat.cast_one]
      linarith
    have hgapScale := hgap s B k (by omega) N (SourceMetadataProgram.size d) hNR
      (Nat.cast_nonneg _) hMN
    have houtputGap := SourcePhysicalThreshold.gap_ge_one rho C eps c s pc h k A B p d hd hpoly
      (by simpa only [amplification_real,Nat.cast_pow] using hgapScale)
    obtain ⟨ho,hlo,hhi⟩ := hcloud 6 extent v p k ap C s pc h A B p eps c d hhk
      (by dsimp [ap]; omega) m n u (by dsimp [m]) (by omega)
      hsites (by simpa only [Nat.cast_add,Nat.cast_one] using hcount) hnorm D le_rfl hsep graph.left graph.right t ht
      (by simpa only [Complex.ofReal_mul] using hmatrix) houtputGap
    have hu : Function.Injective u := by
      intro i j hij
      by_contra hne
      have hdistance := hD.trans (hsep i j hne)
      simp only [uu,hij,sub_self,norm_zero] at hdistance
      norm_num at hdistance
    have hground :
        ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B p d u graph t-
          (amplification rho k d:ℝ)*((N:ℝ)^p)⁻¹:ℝ):EReal) ≤
            unitGroundEnergy ((f d).toData ho) ∧
        unitGroundEnergy ((f d).toData ho) ≤
          ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B p d u graph t+
            (amplification rho k d:ℝ)*((N:ℝ)^p)⁻¹:ℝ):EReal) := by
      simp only [SourcePhysicalThreshold.exactHubbardEnergy_eq rho C eps c s pc h k A B p d u graph t hm]
      have hnR : (n+2:ℝ)=(m+1:ℝ) := by dsimp only [m]; push_cast; ring
      simpa only [hnR] using And.intro hlo hhi
    exact SourceUnitCoulomb.promise_of_hubbard_interval rho C U Fnum Knum hrho eps c
      s pc h k A B p ap p (s+14) d hd hpoly u hu hsites graph hm
      (indexedGraph_toList s d hd hm) t ho hs (by rfl) le_rfl (by rfl)
      (by simpa only [Nat.cast_pow] using hfinite) hground
  obtain ⟨yesOutput,noOutput,hyesOutput,hnoOutput⟩ := exists_atomic_yes_no
  exact ⟨FiniteSourceBranch.reduction yesOutput noOutput hyesOutput hnoOutput s f
    (SourceUnitCoulomb.program rho C U Fnum Knum eps c s pc h k A B p ap)
    (fun d hd hp hv hy => (hcorrect d hd hp hv).1 hy)
    (fun d hd hp hv hn => (hcorrect d hd hp hv).2 hn)⟩

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap_oai := @OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap_oai
