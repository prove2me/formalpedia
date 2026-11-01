-- Prove2me | solution 1 for OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:19:25.661914+00:00
-- url     : https://prove2.me/submissions/5de5bbb6-f23f-4286-a05b-f966989deec6

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_CalibratedEvaluation_scheduled_residual

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial scales and rational positive spokes for one actual
simultaneous singlet-mediator stage. The norm hypothesis concerns the
unchanged low-block terms; no spectral conclusion is assumed. -/

namespace ContinuumCoulomb.MediatorParameters
open scoped BigOperators Kronecker InnerProductSpace

theorem scale_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) : 0 < scale r W G := by
  unfold scale
  positivity

theorem scale_lower (r : ℕ) {W G : ℕ} (_hW : 0 < W) (hG : 0 < G) :
    16 * (r + 1) * W ≤ scale r W G := by
  have hrpow := Nat.le_self_pow (by decide : 3 ≠ 0) (r + 1)
  have hWpow := Nat.le_self_pow (by decide : 3 ≠ 0) W
  calc
    _ ≤ 1048576 * (r + 1) * W := by gcongr; norm_num
    _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 * G := by
      calc
        _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 := by gcongr
        _ ≤ _ := Nat.le_mul_of_pos_right _ hG
    _ = scale r W G := rfl

theorem canonical_amplitude_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (_hG : 0 < G)
    {J : ℝ} (hJ : |J| ≤ W) :
    signedMediatorAmplitude (delta r W G : ℝ) J ≤ 2 * (scale r W G : ℝ) * W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW2 : (W : ℝ) ≤ 2 * (W : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hJ.trans hW2)
    (show 0 ≤ 2 * (scale r W G : ℝ) ^ 2 by positivity)
  unfold signedMediatorAmplitude
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  unfold delta
  push_cast
  nlinarith only [hmul]

theorem canonical_amplitude_lower (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℝ} (hJ : 1 / (W : ℝ) ≤ |J|) :
    1 ≤ signedMediatorAmplitude (delta r W G : ℝ) J := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hSl : (W : ℝ) ≤ scale r W G := by
    have h := scale_lower r hW hG
    have : W ≤ scale r W G := by nlinarith
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hmul : 1 ≤ (W : ℝ) * |J| := by
    simpa only [mul_comm] using (div_le_iff₀ hWr).mp hJ
  have hSW : (W : ℝ) ≤ (scale r W G : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hSW (abs_nonneg J)
  unfold signedMediatorAmplitude
  apply Real.le_sqrt_of_sq_le
  unfold delta
  push_cast
  nlinarith

theorem rational_sqrt_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) ∧
      Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) < 1 / (2 : ℝ) ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  simpa only [hre] using DyadicRootProgram.value_error b q.num.toNat q.den q.pos

theorem spoke_error (r W G : ℕ) (J : ℚ) :
    0 ≤ signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) ∧
      signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) <
        1 / (2 : ℝ) ^ precision r G := by
  have h := rational_sqrt_error (precision r G)
    (show 0 ≤ radicand r W G J by unfold radicand; positivity)
  simpa only [spoke, radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_abs, signedMediatorAmplitude] using h

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorScaleBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete weight and inverse-weight bounds for the three mediator
stages. Each bound is a fixed polynomial in entering unary parameters. -/

namespace ContinuumCoulomb.MediatorParameters

theorem spoke_lower_half (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    (1 / 2 : ℝ) ≤ spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hpower : (2 : ℝ) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast Nat.le_self_pow (by unfold precision; omega : precision r G ≠ 0) 2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpower
  linarith

theorem spoke_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) :
    (spoke r W G J : ℝ) ≤ 2 * (scale r W G : ℝ) * W := by
  have he := (spoke_error r W G J).1
  have ha := canonical_amplitude_upper r hW hG hJ
  linarith

theorem secondWeight_two_le (r W G : ℕ) : 2 ≤ secondWeight r W G := by
  unfold secondWeight
  omega

theorem thirdWeight_two_le (r W G : ℕ) : 2 ≤ thirdWeight r W G := by
  unfold thirdWeight
  omega

theorem second_spoke_bounds (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ W) (hJlower : 1 / (W : ℝ) ≤ |(J : ℝ)|) :
    1 / (secondWeight r W G : ℝ) ≤ |(spoke r W G J : ℝ)| ∧
      |(spoke r W G J : ℝ)| ≤ secondWeight r W G := by
  have hl := spoke_lower_half r hW hG hJlower
  have hu := spoke_upper r hW hG hJ
  have htwo : (2 : ℝ) ≤ secondWeight r W G := by exact_mod_cast secondWeight_two_le r W G
  have hmax : 2 * (scale r W G : ℝ) * W ≤ secondWeight r W G := by
    exact_mod_cast (show 2 * scale r W G * W ≤ secondWeight r W G by unfold secondWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke r W G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_spoke_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G)
    {J : ℚ} (hJ : |(J : ℝ)| ≤ secondWeight r W G)
    (hJlower : 1 / (secondWeight r W G : ℝ) ≤ |(J : ℝ)|) :
    1 / (thirdWeight r W G : ℝ) ≤
        |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ∧
      |(spoke (2 * r) (secondWeight r W G) G J : ℝ)| ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hl := spoke_lower_half (2 * r) hW2 hG hJlower
  have hu := spoke_upper (2 * r) hW2 hG hJ
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  have hmax : 2 * (scale (2 * r) (secondWeight r W G) G : ℝ) * secondWeight r W G ≤
      thirdWeight r W G := by
    exact_mod_cast (show 2 * scale (2 * r) (secondWeight r W G) G * secondWeight r W G ≤
      thirdWeight r W G by unfold thirdWeight; omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ spoke (2 * r) (secondWeight r W G) G J)]
  exact ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans hl, hu.trans hmax⟩

theorem third_central_bounds (r : ℕ) {W G : ℕ} (hG : 0 < G) :
    1 / (thirdWeight r W G : ℝ) ≤ delta (2 * r) (secondWeight r W G) G ∧
      (delta (2 * r) (secondWeight r W G) G : ℝ) ≤ thirdWeight r W G := by
  have hW2 : 0 < secondWeight r W G := lt_of_lt_of_le (by norm_num) (secondWeight_two_le r W G)
  have hdelta : (1 : ℝ) ≤ delta (2 * r) (secondWeight r W G) G := by
    have hp : 0 < delta (2 * r) (secondWeight r W G) G := by
      unfold delta
      exact pow_pos (scale_pos (2 * r) hW2 hG) 2
    exact_mod_cast hp
  have htwo : (2 : ℝ) ≤ thirdWeight r W G := by exact_mod_cast thirdWeight_two_le r W G
  refine ⟨(one_div_le_one_div_of_le (by norm_num) htwo).trans (by linarith), ?_⟩
  exact_mod_cast (show delta (2 * r) (secondWeight r W G) G ≤ thirdWeight r W G by
    unfold thirdWeight; omega)

end ContinuumCoulomb.MediatorParameters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorIteration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual mediator stages. Only the original central bonds
survive the last subdivision; each original spoke becomes a nine-link
path, giving eighteen new spins and nineteen positive bonds per edge. -/

namespace ContinuumCoulomb.MediatorIteration
open Matrix MediatorGraph
open scoped BigOperators Kronecker InnerProductSpace

theorem join_weight_property {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (P : ℚ → Prop) (hF : ∀ e, P (F.weight e)) (hK : ∀ e, P (K.weight e)) :
    ∀ e, P ((join F K).weight e) := by
  intro e
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective e
  cases a with
  | inl a => simpa [join] using hF a
  | inr a => simpa [join] using hK a

theorem firstSpokes_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (secondBound r W G : ℝ) ≤ |((firstSpokes F W G).weight e : ℝ)| ∧
      |((firstSpokes F W G).weight e : ℝ)| ≤ secondBound r W G := by
  intro e
  exact MediatorParameters.second_spoke_bounds r hW hG (hJ _) (hJl _)

theorem secondPaths_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (thirdBound r W G : ℝ) ≤ |((secondPaths F W G).weight e : ℝ)| ∧
      |((secondPaths F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  apply join_weight_property _ _
    (fun J => 1 / (thirdBound r W G : ℝ) ≤ |(J : ℝ)| ∧ |(J : ℝ)| ≤ thirdBound r W G)
  · intro e
    have h := MediatorParameters.third_central_bounds r (W := W) hG
    change 1 / (thirdBound r W G : ℝ) ≤ |(deltaTwo r W G : ℝ)| ∧
      |(deltaTwo r W G : ℝ)| ≤ thirdBound r W G
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ deltaTwo r W G)]
    simpa only [deltaTwo, secondBound, thirdBound, Nat.mul_comm] using h
  · intro e
    have hbound := firstSpokes_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1
    have h := MediatorParameters.third_spoke_bounds r hG hbound.2 hbound.1
    simpa only [secondSpokes, spokes, secondBound, thirdBound, Nat.mul_comm] using h

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorPromise
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit final weight bounds and promise thresholds for the actual
three-stage positive-spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open scoped BigOperators InnerProductSpace

theorem finalGraph_lower {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, (1 / 2 : ℝ) ≤ (finalGraph F W G).weight e := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hdelta1 : (1 : ℝ) ≤ deltaOne r W G := by
    have hp : 0 < deltaOne r W G := by
      unfold deltaOne MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos r hW hG) 2
    exact_mod_cast hp
  have hdelta3 : (1 : ℝ) ≤ deltaThree r W G := by
    have hp : 0 < deltaThree r W G := by
      unfold deltaThree MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos _ hW3 hG) 2
    exact_mod_cast hp
  apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
  · intro e
    change (1 / 2 : ℝ) ≤ ((deltaOne r W G : ℚ) : ℝ)
    simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaOne r W G by linarith)
  · apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
    · intro e
      change (1 / 2 : ℝ) ≤ ((deltaThree r W G : ℚ) : ℝ)
      simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaThree r W G by linarith)
    · intro e
      exact MediatorParameters.spoke_lower_half _ hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).1

theorem finalGraph_upper {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, ((finalGraph F W G).weight e : ℝ) ≤ MediatorParameters.finalWeight r W G := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hr : r * 2 + r * 2 * 2 = 6 * r := by omega
  have hdelta1 : deltaOne r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaOne MediatorParameters.finalWeight
    omega
  have hdelta3 : deltaThree r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaThree thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  have hspoke : 2 * MediatorParameters.scale (r * 2 + r * 2 * 2) (thirdBound r W G) G * thirdBound r W G ≤
      MediatorParameters.finalWeight r W G := by
    unfold thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
  · intro e
    change ((deltaOne r W G : ℚ) : ℝ) ≤ _
    exact_mod_cast hdelta1
  · apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
    · intro e
      change ((deltaThree r W G : ℚ) : ℝ) ≤ _
      exact_mod_cast hdelta3
    · intro e
      have h := MediatorParameters.spoke_upper (r * 2 + r * 2 * 2) hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).2
      apply h.trans
      exact_mod_cast hspoke

end ContinuumCoulomb.MediatorIteration

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

end ContinuumCoulomb.ApproximateBisection

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
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

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

open scoped Convolution
open ContinuousLinearMap

theorem contDiff_partial {f : Position → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ (n+1) f) (v : Position) : ContDiff ℝ n (dirPartial f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
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

theorem integrable_mul_compact_of_continuousAt {f g : Position → ℝ}
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hc : Continuous (fun x => f x*g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · have he : (fun y => f y*g y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change g y = 0 at hy
        simp only [hy, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hc.integrable_of_hasCompactSupport (hgc.mono (Function.support_mul_subset_right f g))

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem integral_mul_coordinateLaplacian_eq {f φ : Position → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * coordinateLaplacian φ x) =
      ∫ x, coordinateLaplacian f x * φ x := by
  have hpφ (v : Position) : ContDiff ℝ ∞ (dirPartial φ v) :=
    contDiff_partial (by simpa using hφ) v
  have hppφ (v : Position) : ContDiff ℝ ∞ (dirPartial (dirPartial φ v) v) :=
    contDiff_partial (by simpa using hpφ v) v
  have hdφ (v : Position) := (hpφ v).differentiable (by simp)
  have hiφ (v : Position) := hasCompactSupport_partial hφc v
  have hpcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (dirPartial f v) x :=
    ((hf x hx).fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const
  have hppcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hpcont v x hx).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hleft (v : Position) : Integrable (fun x => f x*dirPartial (dirPartial φ v) v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x ((tsupport_dirPartial_subset φ v)
        (tsupport_dirPartial_subset (dirPartial φ v) v hx))).continuousAt)
      (hppφ v).continuous
      (hasCompactSupport_partial (hiφ v) v)
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x*φ x) :=
    integrable_mul_compact_of_continuousAt (hppcont v) hφ.continuous hφc
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hpcont v x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfg (v : Position) : Integrable (fun x => f x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x*φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hpcont v x hx).continuousAt)
      hφ.continuous hφc
  have hby (v : Position) :
      (∫ x, f x*dirPartial (dirPartial φ v) v x) = ∫ x, dirPartial (dirPartial f v) v x*φ x := by
    calc
      _ = -(∫ x, dirPartial f v x*dirPartial φ v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).differentiableAt (by norm_num))
          (fun x _ => hdφ v x)
      _ = _ := by
        have he : (∫ x, dirPartial f v x*dirPartial φ v x) =
            -(∫ x, dirPartial (dirPartial f v) v x*φ x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x hx => (hpcont v x hx).differentiableAt (by norm_num))
            (fun x _ => hφ.differentiable (by simp) x)
        rw [he, neg_neg]
  calc
    _ = ∫ x, ∑ a : Fin 3, f x*dirPartial (dirPartial φ (axis a)) (axis a) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateLaplacian_eq_partials (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt, Finset.mul_sum]
    _ = ∑ a : Fin 3, ∫ x, f x*dirPartial (dirPartial φ (axis a)) (axis a) x :=
      integral_finsetSum _ (fun a _ => hleft (axis a))
    _ = ∑ a : Fin 3, ∫ x, dirPartial (dirPartial f (axis a)) (axis a) x*φ x := by
      simp_rw [hby]
    _ = ∫ x, ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x*φ x :=
      (integral_finsetSum _ (fun a _ => hright (axis a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [coordinateLaplacian_eq_partials (hf x hx), Finset.sum_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

end NeutralAtom
end
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

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

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

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem integral_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, coulombKernel x*coordinateLaplacian φ x) = -(4*Real.pi*φ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hleft := regularizedKernel_integral_tendsto hε hεlim
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hφc)
  have hright := (regularizedCharge_tendsto_dirac hε hεlim hφ.continuous hφc).neg
  have he : (fun n => ∫ x, regularizedKernel (ε n) x*coordinateLaplacian φ x) =
      (fun n => -(∫ x, regularizedCharge (ε n) x*φ x)) := by
    funext n
    rw [integral_mul_coordinateLaplacian_eq
      (fun x _ => ((contDiff_regularizedKernel (hε n).ne').of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) hφ hφc]
    simp_rw [laplacian_regularizedKernel (hε n).ne', neg_mul, integral_neg]
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

theorem integral_translated_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Position) :
    (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x) = -(4*Real.pi*φ y) := by
  have ht : ContDiff ℝ ∞ (fun z => φ (z+y)) := hφ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have he := integral_coulombKernel_laplacian ht hc
  simp only [coordinateLaplacian_translate, zero_add] at he
  rw [← integral_add_right_eq_self (fun x => coulombKernel (x-y)*coordinateLaplacian φ x) y]
  simpa only [add_sub_cancel_right] using he

end NeutralAtom
end
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

theorem planarCenter_norm_sub (u v : PlanarPosition) : ‖planarCenter u - planarCenter v‖ = ‖u - v‖ := by
  rw [← planarCenter_sub, planarCenter_norm]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit exponential tail of the actual positive planar mode. Splitting
the Gaussian exponent avoids any assumed asymptotics for a special function. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_double_time (t : ℝ) (b : PlanarPosition) :
    planarHeatKernel t b =
      2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b := by
  unfold planarHeatKernel
  have h1 : -‖b‖ ^ 2 / (4 * t) = -‖b‖ ^ 2 / (8 * t) + -‖b‖ ^ 2 / (8 * t) := by ring
  have h2 : -‖b‖ ^ 2 / (4 * (2 * t)) = -‖b‖ ^ 2 / (8 * t) := by ring
  rw [h1, h2, Real.exp_add]
  ring

theorem planarHeatForcing_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖)
    (b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) * planarHeatKernel (2 * t) b := by
  by_cases hf : planarForcing (r - b) = 0
  · rw [hf, mul_zero]
    exact mul_nonneg (by positivity) (planarHeatKernel_positive (by positivity) b).le
  · have hs : ‖r - b‖ < 1 := lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h))
    have hn : ‖r‖ - 1 ≤ ‖b‖ := by
      have htriangle := norm_add_le (r - b) b
      rw [sub_add_cancel] at htriangle
      linarith
    have hsq : (‖r‖ - 1) ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have he : Real.exp (-‖b‖ ^ 2 / (8 * t)) ≤
        Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    calc
      _ ≤ planarHeatKernel t b :=
        mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)
      _ = 2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b :=
        planarHeatKernel_double_time t b
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
        (planarHeatKernel_positive (by positivity) b).le

theorem planarHeatAverage_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarHeatAverage t r ≤ 2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
  have hi := (planarHeatKernel_integrable (by positivity : 0 < 2 * t)).const_mul
    (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tail ht hr)
  simpa only [integral_const_mul, planarHeatKernel_integral (by positivity : 0 < 2 * t),
    mul_one, planarHeatAverage] using h

theorem planar_heat_tail_exponent {t d : ℝ} (ht : 0 < t) :
    d / 2 ≤ t / 2 + d ^ 2 / (8 * t) := by
  have he : t / 2 + d ^ 2 / (8 * t) - d / 2 = (2 * t - d) ^ 2 / (8 * t) := by
    field_simp
    ring
  have hp : 0 ≤ (2 * t - d) ^ 2 / (8 * t) := by positivity
  linarith

theorem planarHeatResolvent_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    Real.exp (-t) * planarHeatAverage t r ≤
      (2 * Real.exp (-(‖r‖ - 1) / 2)) * Real.exp (-(1 / 2 : ℝ) * t) := by
  have he : -t + (-((‖r‖ - 1) ^ 2) / (8 * t)) ≤ -(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t := by
    have hA : (‖r‖ - 1) / 2 ≤ t / 2 + (‖r‖ - 1) ^ 2 / (8 * t) :=
      planar_heat_tail_exponent ht
    rw [neg_div]
    linarith
  calc
    _ ≤ Real.exp (-t) * (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) :=
      mul_le_mul_of_nonneg_left (planarHeatAverage_tail ht hr) (Real.exp_pos _).le
    _ = 2 * Real.exp (-t + (-((‖r‖ - 1) ^ 2) / (8 * t))) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem planarResolventMode_exponential_tail {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ 4 * Real.exp (-(‖r‖ - 1) / 2) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (2 * Real.exp (-(‖r‖ - 1) / 2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatResolvent_tail ht hr)
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * t)) = 2 := by
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
    norm_num
  rw [integral_const_mul, he] at h
  nlinarith

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

theorem planar_tilt_envelope_sharp_upper (r : PlanarPosition) (v : ℝ)
    (hv : ∀ e : PlanarPosition, ‖e‖ < 1 →
      v ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2)) (hr : 1 ≤ ‖r‖) :
    v ≤ ‖r‖ * Real.exp (2 - ‖r‖) := by
  have hR : 0 < ‖r‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr
  let c : ℝ := (‖r‖ - 1) / ‖r‖ ^ 2
  let e : PlanarPosition := c • r
  have hc : 0 ≤ c := div_nonneg (by linarith) (sq_nonneg _)
  have hn : ‖e‖ = (‖r‖ - 1) / ‖r‖ := by
    rw [show e = c • r from rfl, norm_smul, Real.norm_of_nonneg hc]
    dsimp [c]
    field_simp
  have hi : inner ℝ e r = ‖r‖ - 1 := by
    rw [show e = c • r from rfl, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [c]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')
  have he : ‖e‖ < 1 := by
    rw [hn]
    exact (div_lt_one hR).2 (by linarith)
  have hdpos : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hden : 1 / ‖r‖ ≤ 1 - ‖e‖ ^ 2 := by
    have hsq : ‖e‖ ^ 2 ≤ ‖e‖ := by nlinarith [norm_nonneg e]
    have hid : 1 - ‖e‖ = 1 / ‖r‖ := by rw [hn]; field_simp; ring
    linarith
  have hinv : (1 - ‖e‖ ^ 2)⁻¹ ≤ ‖r‖ := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (one_div_pos.mpr hR) hden
    simpa only [one_div, inv_inv] using h
  have hexp : Real.exp (‖e‖ - inner ℝ e r) ≤ Real.exp (2 - ‖r‖) := by
    apply Real.exp_le_exp.mpr
    rw [hi]
    linarith
  calc
    _ ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) :=
      hv e he
    _ ≤ Real.exp (2 - ‖r‖) * ‖r‖ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hexp hinv (inv_nonneg.mpr hdpos.le) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem planarResolventMode_sharp_upper {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ ‖r‖ * Real.exp (2 - ‖r‖) :=
  planar_tilt_envelope_sharp_upper r (planarResolventMode r)
    (fun e he => planarResolventMode_tilt_bound e r he) hr

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLowerTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A matching lower exponential tail for the actual planar mode. Only the
positive forcing mass and the heat-time interval `[|r|/2,|r|/2+1]` are used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatAverage_other_integrable {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    Integrable (fun a => planarHeatKernel t (r - a) * planarForcing a) := by
  have h := (planarHeatAverage_integrand_integrable ht r).comp_sub_left r
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  rw [show r - (r - a) = a by abel]

theorem planarHeatAverage_other (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ a, planarHeatKernel t (r - a) * planarForcing a := by
  have h := integral_sub_left_eq_self
    (fun b => planarHeatKernel t b * planarForcing (r - b)) volume r
  unfold planarHeatAverage
  convert h.symm using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext a
  rw [show r - (r - a) = a by abel]

theorem planar_heat_lower_exponent {R t d : ℝ} (hR : 1 ≤ R)
    (ht₀ : R / 2 ≤ t) (ht₁ : t ≤ R / 2 + 1) (hd₀ : 0 ≤ d) (hd₁ : d ≤ R + 1) :
    t + d ^ 2 / (4 * t) ≤ R + 2 := by
  have ht : 0 < t := by linarith
  have hs : d ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hp : 0 ≤ (t - R / 2) * (R / 2 + 2 - t) :=
    mul_nonneg (by linarith) (by linarith)
  have hd : d ^ 2 / (4 * t) ≤ R + 2 - t :=
    (div_le_iff₀ (by positivity : 0 < 4 * t)).2 (by nlinarith)
  linarith

theorem planarHeatKernel_weighted_lower {r a : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ha : ‖a‖ ≤ 1)
    (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1) :
    Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2)) ≤
      Real.exp (-t) * planarHeatKernel t (r - a) := by
  have ht : 0 < t := by linarith
  have hnorm : ‖r - a‖ ≤ ‖r‖ + 1 := (norm_sub_le r a).trans (by linarith)
  have he : Real.exp (-(‖r‖ + 2)) ≤ Real.exp (-t + -‖r - a‖ ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.mpr
    have h := planar_heat_lower_exponent hr ht₀ ht₁ (norm_nonneg _) hnorm
    rw [neg_div]
    linarith
  have hden : 4 * Real.pi * t ≤ 2 * Real.pi * (‖r‖ + 2) := by
    nlinarith [Real.pi_pos]
  have hinv : (2 * Real.pi * (‖r‖ + 2))⁻¹ ≤ (4 * Real.pi * t)⁻¹ :=
    inv_anti₀ (by positivity) hden
  unfold planarHeatKernel
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-t + -‖r - a‖ ^ 2 / (4 * t)) * (4 * Real.pi * t)⁻¹ :=
      mul_le_mul he hinv (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

theorem planarHeatForcing_weighted_lower {r : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1)
    (a : PlanarPosition) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * planarForcing a ≤
      (Real.exp (-t) * planarHeatKernel t (r - a)) * planarForcing a := by
  by_cases hf : planarForcing a = 0
  · simp only [hf, mul_zero, le_refl]
  have ha : ‖a‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  exact mul_le_mul_of_nonneg_right (planarHeatKernel_weighted_lower hr ha ht₀ ht₁)
    (planarForcing_nonnegative a)

theorem planarHeatAverage_weighted_lower {r : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * (∫ a, planarForcing a) ≤
      Real.exp (-t) * planarHeatAverage t r := by
  have ht : 0 < t := by linarith
  have h := integral_mono
    (planarForcing_integrable.const_mul
      (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))))
    ((planarHeatAverage_other_integrable ht r).const_mul (Real.exp (-t)))
    (fun a => by simpa only [mul_assoc] using planarHeatForcing_weighted_lower hr ht₀ ht₁ a)
  simpa only [integral_const_mul, ← planarHeatAverage_other] using h

theorem planarResolventMode_sharp_lower_raw {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * (∫ a, planarForcing a) ≤
      planarResolventMode r := by
  have hsub : Set.Icc (‖r‖ / 2) (‖r‖ / 2 + 1) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    change 0 < t
    linarith [ht.1]
  have hi := (planarResolventMode_heat_integrable r).mono_set hsub
  have hl := setIntegral_ge_of_const_le_real measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne
    (fun t ht => planarHeatAverage_weighted_lower hr ht.1 ht.2) hi
  have hm := setIntegral_mono_set (planarResolventMode_heat_integrable r)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_pos _).le (planarHeatAverage_positive ht r).le)
    (Filter.Eventually.of_forall hsub)
  rw [Real.volume_real_Icc_of_le (by linarith), show ‖r‖ / 2 + 1 - ‖r‖ / 2 = 1 by ring,
    mul_one] at hl
  rw [planarResolventMode_heat_representation]
  exact hl.trans hm

theorem planarLowerTailConstant_positive : 0 < planarLowerTailConstant := by
  unfold planarLowerTailConstant
  exact div_pos (mul_pos (Real.exp_pos _) planarForcing_integral_positive) (by positivity)

theorem planarResolventMode_sharp_lower {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarLowerTailConstant / (‖r‖ + 2) * Real.exp (-‖r‖) ≤ planarResolventMode r := by
  convert planarResolventMode_sharp_lower_raw hr using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarLowerTailConstant
  rw [show -(‖r‖ + 2) = -2 + -‖r‖ by ring, Real.exp_add]
  field_simp

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

end ContinuumCoulomb.BisectionRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Gaussian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma gaussian_pos (a : ℝ) (x : Space) : 0 < gaussian a x := Real.exp_pos _
lemma gaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : gaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖x‖]
lemma gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by unfold gaussian; fun_prop
lemma gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  change Integrable (fun x : Space => Real.exp (-a*‖x‖^2))
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=Space)
    (show 0 < (a : ℂ).re from ha) 0 0).re
  change Integrable (fun x : Space => (Complex.exp (-(a:ℂ)*↑‖x‖^2 + 0 * ↑(inner ℝ (0:Space) x))).re) at H
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re, gaussian] using H
lemma gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x, gaussian a x) = (Real.pi/a)^(3/2:ℝ) := by
  simpa [gaussian] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V:=Space) ha
lemma kernel_gaussian_integral {d : Space} (hd : d ≠ 0) :
    ‖d‖⁻¹ = (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ, gaussian (t^2) d := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _)]
  field_simp

lemma gaussian_product (a : ℝ) (x y z : Space) :
    gaussian (2*a) (x-z)*gaussian (2*a) (y-z) =
      gaussian a (x-y)*gaussian (4*a) (z-(1/2:ℝ) • (x+y)) := by
  unfold gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    inner_smul_right, inner_add_right]
  rw [mul_pow, norm_add_sq_real]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

lemma gaussian_product_integrable {a : ℝ} (ha : 0 < a) (x y : Space) :
    Integrable (fun z => gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) := by
  simp_rw [gaussian_product]
  exact ((gaussian_integrable (by positivity : 0 < 4*a)).comp_sub_right _).const_mul _

lemma gaussian_convolution_identity {a : ℝ} (ha : 0 < a) (x y : Space) :
    (∫ z, gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) =
      gaussian a (x-y)*(Real.pi/(4*a))^(3/2:ℝ) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma integrable_gaussian_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : Space × Space => f p.1*f p.2*gaussian a (p.1-p.2)) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by
    apply Measurable.aestronglyMeasurable
    exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).mul
      ((gaussian_continuous a).measurable.comp (by fun_prop)))
  exact Filter.Eventually.of_forall (fun p => by
    simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (gaussian_le_one ha _))

lemma gaussian_square_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
  have hm' : Measurable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
    have h1 : Measurable (fun q : (Space × Space) × Space => f q.1.1*f q.1.2) :=
      (hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))
    apply h1.mul
    exact ((gaussian_continuous _).measurable.comp (by fun_prop)).mul
      ((gaussian_continuous _).measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => (gaussian_product_integrable ha p.1 p.2).const_mul (f p.1*f p.2))
  · have he (p : Space × Space) :
        (∫ z, ‖(f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))‖) =
          (‖f p.1‖*‖f p.2‖*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
      rw [integral_const_mul, gaussian_convolution_identity ha]
      ring
    simp_rw [he]
    exact (integrable_gaussian_pair hf.norm hm.norm ha.le).mul_const _

lemma gaussian_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2) := by
  have hi := gaussian_square_integrable hf hm ha
  have H := integral_integral_swap (f := fun (p : Space × Space) (z : Space) =>
    (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) hi
  have hleft (p : Space × Space) :
      (∫ z, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (f p.1*f p.2*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
    rw [integral_const_mul, gaussian_convolution_identity ha]
    ring
  have hright (z : Space) :
      (∫ p : Space × Space, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (∫ x, f x*gaussian (2*a) (x-z))^2 := by
    simp_rw [show ∀ p : Space × Space,
      (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z)) =
      (f p.1*gaussian (2*a) (p.1-z))*(f p.2*gaussian (2*a) (p.2-z)) from fun p => by ring]
    exact (integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Space => f x*gaussian (2*a) (x-z))
      (fun x : Space => f x*gaussian (2*a) (x-z))).trans (pow_two _).symm
  simp_rw [hleft, hright] at H
  rw [integral_mul_const] at H
  have hnonneg : 0 ≤ (∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2)) *
      (Real.pi/(4*a))^(3/2:ℝ) := H.symm ▸ integral_nonneg (fun z => sq_nonneg _)
  exact nonneg_of_mul_nonneg_left hnonneg (Real.rpow_pos_of_pos (by positivity) _)
lemma space_ae_distinct : ∀ᵐ p : Space × Space, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => by
    rw [ae_iff]
    simp only [not_not]
    have he : {y : Space | x = y} = {x} := by ext y; simp [eq_comm]
    change volume {y : Space | x = y} = 0
    rw [he, measure_singleton])

lemma gaussian_parameter_integrable {d : Space} (hd : d ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t^2) d) := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma gaussian_parameter_integral {d : Space} (hd : d ≠ 0) :
    (∫ t : ℝ, gaussian (t^2) d) = coulombKernel d * Real.sqrt Real.pi := by
  have H := kernel_gaussian_integral hd
  unfold coulombKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((Real.sqrt Real.pi)⁻¹*(∫ t : ℝ, gaussian (t^2) d))*Real.sqrt Real.pi := by field_simp
    _ = _ := by rw [← H]

lemma coulomb_gaussian_integrable_of_pair {f : Space → ℝ} (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    Integrable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
  have hm' : Measurable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
    apply ((hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))).mul
    unfold gaussian
    fun_prop
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [space_ae_distinct] with p hp
    exact (gaussian_parameter_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1*f p.2)
  · have hi := hp.norm.mul_const (Real.sqrt Real.pi)
    apply hi.congr
    filter_upwards [space_ae_distinct] with p hp
    simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
    ring

lemma coulomb_form_nonneg_of_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) := by
  have hi := coulomb_gaussian_integrable_of_pair hm hp
  have H := integral_integral_swap (f := fun (p : Space × Space) (t : ℝ) =>
    f p.1*f p.2*gaussian (t^2) (p.1-p.2)) hi
  have hl : (∫ p : Space × Space, ∫ t : ℝ, f p.1*f p.2*gaussian (t^2) (p.1-p.2)) =
      (∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2))*Real.sqrt Real.pi := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [space_ae_distinct] with p hp
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    ring
  rw [hl] at H
  have ht : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
  have hn : 0 ≤ ∫ t : ℝ, ∫ p : Space × Space, f p.1*f p.2*gaussian (t^2) (p.1-p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ht] with t ht
    exact gaussian_form_nonneg hf hm (sq_pos_of_ne_zero ht)
  rw [← H] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CoulombTest
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_zero {χ : Space → ℝ} {x : Space} (hx : x∉tsupport χ) :
    testCharge χ x=0 := by
  simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,neg_zero,zero_div]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_potential {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (y : Space) :
    (∫ x, coulombKernel (y-x)*testCharge χ x)=χ y := by
  have H := NeutralAtom.integral_translated_coulombKernel_laplacian hχ hc y
  have he : (fun x => coulombKernel (y-x)*testCharge χ x)=
      (fun x => -(NeutralAtom.coulombKernel (x-y)*NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)) := by
    funext x
    simp only [testCharge,coulombKernel,NeutralAtom.coulombKernel,norm_sub_rev]
    ring
  rw [he,integral_div,integral_neg,H]
  field_simp

end Coulomb

end

end
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

theorem pair_nonnegative (f : CoulombPacket) : 0 ≤ pair f f :=
  Coulomb.coulomb_form_nonneg_of_pair f.integrable f.continuous.measurable (joint_integrable f f)

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

theorem pair_add_right (f g h : CoulombPacket) : pair f (add g h) = pair f g + pair f h := by
  rw [pair_symmetric, pair_add_left, pair_symmetric g f, pair_symmetric h f]

theorem pair_smul_right (t : ℝ) (f g : CoulombPacket) : pair f (smul t g) = t * pair f g := by
  rw [pair_symmetric, pair_smul_left, pair_symmetric g f]

theorem pair_cauchy (f g : CoulombPacket) : pair f g ^ 2 ≤ pair f f * pair g g := by
  have h (t : ℝ) : 0 ≤ pair g g * (t * t) + (2 * pair f g) * t + pair f f := by
    have hn := pair_nonnegative (add f (smul t g))
    rw [pair_add_left, pair_add_right, pair_add_right, pair_smul_left,
      pair_smul_right, pair_smul_right, pair_symmetric g f, pair_smul_left] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero h
  dsimp only [discrim] at hd
  nlinarith only [hd]

end CoulombPacket
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

theorem pair_combinations {m n : ℕ} (f : Fin m → CoulombPacket) (g : Fin n → CoulombPacket)
    (d : Fin m → ℝ) (e : Fin n → ℝ) :
    pair (combination f d) (combination g e) =
      ∑ i, ∑ j, d i * e j * pair (f i) (g j) := by
  rw [pair_combination_left]
  simp_rw [pair_combination_right, Finset.mul_sum, mul_assoc]

theorem pair_test (f : CoulombPacket) (χ : Position → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    pair f (test χ hχ hc) = ∫ x, f x * χ x := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f (test χ hχ hc))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y, f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) = _
  rw [show (fun y => f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) =
      (fun y => f x * (Coulomb.coulombKernel (x - y) * Coulomb.testCharge χ y)) by funext y; ring,
    integral_const_mul, Coulomb.testCharge_potential hχ hc]

theorem test_pair_test (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) :
    pair (test χ hχ hcχ) (test ψ hψ hcψ) = ∫ x, Coulomb.testCharge χ x * ψ x :=
  pair_test _ _ hψ hcψ

theorem test_pair_orthogonal (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hd : Disjoint (tsupport χ) (tsupport ψ)) : pair (test χ hχ hcχ) (test ψ hψ hcψ) = 0 := by
  rw [test_pair_test]
  have hz (x : Position) : Coulomb.testCharge χ x * ψ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => Set.disjoint_left.mp hd hx hy), mul_zero]
    · rw [Coulomb.testCharge_zero hx, zero_mul]
  simp_rw [hz, integral_zero]

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Coulomb coercivity from disjoint compact tests and approximate
local duality. All integrals range over the whole Euclidean space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem test_combination_energy {m : ℕ} (χ : Fin m → Position → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K : ℝ} (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    pair (combination (fun i => test (χ i) (hχ i) (hc i)) d)
      (combination (fun i => test (χ i) (hχ i) (hc i)) d) ≤ K * ∑ i, d i ^ 2 := by
  classical
  rw [pair_combinations]
  have hentry (i j : Fin m) : pair (test (χ i) (hχ i) (hc i)) (test (χ j) (hχ j) (hc j)) =
      if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, if_true] using test_pair_test (χ i) (χ i) (hχ i) (hχ i) (hc i) (hc i)
    · rw [ite_eq_right hij]
      exact test_pair_orthogonal (χ i) (χ j) (hχ i) (hχ j) (hc i) (hc j) (hd i j hij)
  simp_rw [hentry]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  calc
    _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem gram_coercive_of_dual_lower {m : ℕ} (f : Fin m → CoulombPacket)
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdual : ∀ d : Fin m → ℝ, a * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, d i * d j * ∫ x, f i x * χ j x)
    (d : Fin m → ℝ) :
    (a ^ 2 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, pair (f i) (f j) * d i * d j := by
  let ρ := combination f d
  let η := combination (fun i => test (χ i) (hχ i) (hc i)) d
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : a * S ≤ pair ρ η := by
    rw [pair_combinations]
    simp_rw [pair_test]
    exact hdual d
  have hpair0 : 0 ≤ pair ρ η := (mul_nonneg ha hS).trans hpair
  have hsquare : (a * S) ^ 2 ≤ pair ρ η ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha hS) hpair0).mpr hpair
  have htest := test_combination_energy χ hχ hc hd henergy d
  have hQ : 0 ≤ pair ρ ρ := pair_nonnegative ρ
  have hbound : (a * S) ^ 2 ≤ pair ρ ρ * (K * S) :=
    hsquare.trans ((pair_cauchy ρ η).trans (mul_le_mul_of_nonneg_left htest hQ))
  have hcoercive : (a ^ 2 / K) * S ≤ pair ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have hcancel := (mul_le_mul_iff_left₀ hSpos).mp
        (show (a ^ 2 * S) * S ≤ (pair ρ ρ * K) * S by nlinarith only [hbound])
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hK).mpr hcancel
  change (a ^ 2 / K) * S ≤ pair (combination f d) (combination f d) at hcoercive
  rw [pair_combinations] at hcoercive
  convert hcoercive using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLeakage
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_fst_norm_le (x : Position) :
    ‖(positionSplitCoordinates x).1‖ ≤ ‖x‖ := by
  have h := positionSplitCoordinates_norm_sq x
  nlinarith [sq_nonneg (positionSplitCoordinates x).2, norm_nonneg x,
    norm_nonneg (positionSplitCoordinates x).1]

theorem continuumLocalizedMode_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    continuumLocalizedMode freq u x ≤ 4 * localizedAmplitudeBound freq *
      Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) := by
  have hp := div_le_div_of_nonneg_right (planarResolventMode_exponential_tail hr)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  have hv : verticalMode freq (positionSplitCoordinates x).2 ≤
      1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (positionSplitCoordinates x).2])
  change (planarResolventMode ((positionSplitCoordinates x).1 - u) /
    Real.sqrt (∫ r, planarResolventMode r ^ 2)) * verticalMode freq (positionSplitCoordinates x).2 ≤ _
  calc
    _ ≤ (4 * Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) /
        Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
          (1 / Real.sqrt (Real.sqrt (Real.pi / freq))) :=
      mul_le_mul hp hv (verticalMode_positive hfreq _).le (by positivity)
    _ = _ := by unfold localizedAmplitudeBound; ring

theorem localizedTailConstant_nonnegative (freq : ℝ) : 0 ≤ localizedTailConstant freq :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedDensity_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq *
      Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
  have h := (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (localizedAmplitudeBound_positive hfreq).le) (Real.exp_pos _).le)).mpr
    (continuumLocalizedMode_planar_tail hfreq u x hr)
  have he : Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) ^ 2 =
      Real.exp 1 * Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he] at h
  simpa only [localizedDensity, localizedTailConstant, mul_assoc] using h

theorem localizedDensity_near_other_center {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) (hx : ‖x - planarCenter v‖ ≤ R)
    (hsep : R + 1 ≤ ‖u - v‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq * Real.exp (R - ‖u - v‖) := by
  have hp : ‖(positionSplitCoordinates x).1 - v‖ ≤ R := by
    have h := (positionSplitCoordinates_fst_norm_le (x - planarCenter v)).trans hx
    simpa only [map_sub, planarCenter, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub] using h
  have ht : ‖u - v‖ ≤ ‖u - (positionSplitCoordinates x).1‖ +
      ‖(positionSplitCoordinates x).1 - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle u (positionSplitCoordinates x).1 v
  rw [norm_sub_rev u (positionSplitCoordinates x).1] at ht
  have hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖ := by linarith
  exact (localizedDensity_planar_tail hfreq u x hr).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))

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

theorem localizedTest_smooth {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (localizedTest χ u) := hχ.comp (contDiff_id.sub contDiff_const)

theorem localizedTest_hasCompactSupport {χ : Position → ℝ} (hc : HasCompactSupport χ)
    (u : PlanarPosition) : HasCompactSupport (localizedTest χ u) :=
  hc.comp_homeomorph (Homeomorph.subRight (planarCenter u))

theorem localizedTest_support {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u : PlanarPosition) :
    tsupport (localizedTest χ u) ⊆ Metric.closedBall (planarCenter u) R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hχx : χ (x - planarCenter u) ≠ 0 := hx
  have h := hs (subset_tsupport χ hχx)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using h

theorem localizedTest_disjoint {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u v : PlanarPosition)
    (hsep : 2 * R < ‖u - v‖) : Disjoint (tsupport (localizedTest χ u)) (tsupport (localizedTest χ v)) := by
  apply Set.disjoint_left.mpr
  intro x hxu hxv
  have hu := localizedTest_support hs u hxu
  have hv := localizedTest_support hs v hxv
  simp only [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have h : ‖planarCenter u - planarCenter v‖ ≤ ‖planarCenter u - x‖ + ‖x - planarCenter v‖ := by
    simpa only [dist_eq_norm] using dist_triangle (planarCenter u) x (planarCenter v)
  rw [norm_sub_rev (planarCenter u) x, planarCenter_norm_sub] at h
  linarith

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

theorem localizedDualPair_offsite {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (hsep : R + 1 ≤ ‖u - v‖) :
    |localizedDualPair freq u v χ| ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * (∫ x, |χ x|) := by
  have hpt (x : Position) : ‖localizedDensity freq u (x + planarCenter v) * χ x‖ ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * |χ x| := by
    by_cases hx : χ x = 0
    · simp only [hx, mul_zero, norm_zero, abs_zero, le_refl]
    have hn : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hx)
    have hb := localizedDensity_near_other_center hfreq u v (x + planarCenter v)
      (by simpa only [add_sub_cancel_right] using hn) hsep
    rw [norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter v)) (planarCenter v)]
  simp only [add_sub_cancel_right]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u (x + planarCenter v) * χ x)
    ((hχ.integrable_of_hasCompactSupport (μ := volume) hc).norm.const_mul
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

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

theorem localDualBump_support : tsupport (localDualBump : Position → ℝ) ⊆ Metric.closedBall 0 2 := by
  rw [localDualBump.tsupport_eq]
  exact Set.Subset.rfl

theorem localDualMass_positive {freq : ℝ} (hfreq : 0 < freq) : 0 < localDualMass freq := by
  have h0 : localDualBump (0 : Position) = 1 :=
    localDualBump.one_of_mem_closedBall (by simp [localDualBump])
  have h := localizedDualPair_diagonal_positive hfreq 0 localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump.nonneg' (by rw [h0]; norm_num)
  simpa only [localizedDualPair_diagonal, localDualMass] using h

theorem localLeakageBound_nonnegative (freq D : ℝ) : 0 ≤ localLeakageBound freq D :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem localDualPair_offsite {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    |localizedDualPair freq u v localDualBump| ≤ localLeakageBound freq D := by
  have h := localizedDualPair_offsite hfreq u v localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump_support (by linarith : (2 : ℝ) + 1 ≤ ‖u - v‖)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq)) (integral_nonneg (fun _ => abs_nonneg _)))

theorem localDualTests_disjoint {D : ℝ} (hD : 5 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    Disjoint (tsupport (localizedTest localDualBump u)) (tsupport (localizedTest localDualBump v)) :=
  localizedTest_disjoint localDualBump_support u v (by linarith)

theorem localizedDualMatrix_lower {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (s : Fin m → ℝ) :
    (localDualMass freq - m * localLeakageBound freq D) * ∑ i, s i ^ 2 ≤
      ∑ i, ∑ j, localizedDualPair freq (u i) (u j) localDualBump * s i * s j := by
  apply dualMatrix_quadratic_lower _ (localLeakageBound_nonnegative freq D)
  · intro i
    rw [localizedDualPair_diagonal]
    exact le_rfl
  · intro i j hij
    exact localDualPair_offsite hfreq hD (u i) (u j) (hsep i j hij)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coercivity of the actual full Coulomb Gram matrix of the localized
resolvent--Gaussian modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localizedPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    CoulombPacket.pair (localizedPacket hfreq u) (localizedPacket hfreq v) =
      localizedCoulombCoeff freq u v := by
  unfold CoulombPacket.pair localizedCoulombCoeff NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedDensity freq u x * localizedDensity freq v y * ‖x - y‖⁻¹ =
    localizedDensity freq u x * (‖x - y‖⁻¹ * localizedDensity freq v y)
  ring

theorem testCharge_localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) :
    Coulomb.testCharge (localizedTest χ u) x = Coulomb.testCharge χ (x - planarCenter u) := by
  unfold Coulomb.testCharge localizedTest
  simp only [sub_eq_add_neg, NeutralAtom.coordinateLaplacian_translate]

theorem localizedTest_energy (χ : Position → ℝ) (u : PlanarPosition) :
    (∫ x, Coulomb.testCharge (localizedTest χ u) x * localizedTest χ u x) =
      ∫ x, Coulomb.testCharge χ x * χ x := by
  simp_rw [testCharge_localizedTest]
  exact integral_sub_right_eq_self (fun x => Coulomb.testCharge χ x * χ x) (planarCenter u)

theorem localDualEnergyBound_positive : 0 < localDualEnergyBound := by
  unfold localDualEnergyBound
  positivity

theorem localizedGram_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D) (d : Fin m → ℝ) :
    ((localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound) *
      ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have h := CoulombPacket.gram_coercive_of_dual_lower (fun i => localizedPacket hfreq (u i))
    (fun i => localizedTest localDualBump (u i))
    (fun i => localizedTest_smooth localDualBump_smooth (u i))
    (fun i => localizedTest_hasCompactSupport localDualBump.hasCompactSupport (u i))
    (fun i j hij => localDualTests_disjoint hD (u i) (u j) (hsep i j hij))
    localDualEnergyBound_positive hmargin ?_ ?_ d
  · simpa only [localizedPacket_pair] using h
  · intro i
    rw [localizedTest_energy]
    exact (le_abs_self _).trans (by unfold localDualEnergyBound; linarith)
  · intro e
    have he := localizedDualMatrix_lower hfreq (by linarith : (3 : ℝ) ≤ D) u hsep e
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change e i * e j * localizedDualPair freq (u i) (u j) localDualBump = _
    ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramConstants
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive coercivity constant once the total off-site leakage is
at most half the common diagonal dual mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedGramConstant_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedGramConstant freq :=
  div_pos (sq_pos_of_pos (localDualMass_positive hfreq))
    (mul_pos (by norm_num) localDualEnergyBound_positive)

theorem localizedGram_uniform_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have ha := localDualMass_positive hfreq
  have hb : localDualMass freq / 2 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ localDualMass freq / 2) hmargin).mpr hb
  have hc : localizedGramConstant freq ≤
      (localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound := by
    calc
      _ = (localDualMass freq / 2) ^ 2 / localDualEnergyBound := by
        unfold localizedGramConstant
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hs localDualEnergyBound_positive.le
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun i _ => sq_nonneg (d i)))).trans
    (localizedGram_coercive hfreq hD u hsep hmargin d)

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-site specialization gives the positive denominator `U-v`
used by the Hubbard superexchange calibration. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombCoeff_gap {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombCoeff freq u v := by
  let centers : Fin 2 → PlanarPosition := ![u, v]
  let d : Fin 2 → ℝ := ![1, -1]
  have hs : ∀ i j : Fin 2, i ≠ j → D ≤ ‖centers i - centers j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hsep
    · change D ≤ ‖v - u‖
      simpa only [norm_sub_rev] using hsep
    · exact False.elim (hij rfl)
  have h := localizedGram_uniform_coercive hfreq hD centers hs (by simpa using hleak) d
  simp only [Fin.sum_univ_two, centers, d, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, neg_one_sq, mul_one, mul_neg, neg_neg] at h
  rw [localizedCoulombCoeff_symmetric hfreq v u,
    localizedCoulombCoeff_distance freq u u, localizedCoulombCoeff_distance freq v v] at h
  simp only [sub_self, norm_zero] at h
  nlinarith only [h]

theorem localizedCoulombProfile_gap {freq D d : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2) (hd : D ≤ d) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombProfile freq d := by
  have hn : ‖(0 : PlanarPosition) - d • planarAxis 0‖ = d := by
    rw [zero_sub, norm_neg, norm_smul, planarAxis_zero_norm,
      Real.norm_of_nonneg (by linarith : 0 ≤ d), mul_one]
  have h := localizedCoulombCoeff_gap hfreq hD hleak 0 (d • planarAxis 0) (by rw [hn]; exact hd)
  rwa [localizedCoulombCoeff_distance, hn] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHoppingBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matching exponential brackets for the actual contact hopping integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planar_contact_distance_bounds {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    d - 1 ≤ ‖r - d • planarAxis 0‖ ∧ ‖r - d • planarAxis 0‖ ≤ d + 1 := by
  have hn : ‖d • planarAxis 0‖ = d := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (by linarith)]
  have h₁ : d ≤ ‖r‖ + ‖r - d • planarAxis 0‖ := by
    calc
      _ = ‖r - (r - d • planarAxis 0)‖ := by rw [show r - (r - d • planarAxis 0) =
        d • planarAxis 0 by abel, hn]
      _ ≤ _ := norm_sub_le _ _
  have h₂ := norm_sub_le r (d • planarAxis 0)
  rw [hn] at h₂
  constructor <;> linarith

theorem planarHopping_mode_upper {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    planarResolventMode (r - d • planarAxis 0) ≤ (d + 1) * Real.exp (3 - d) := by
  obtain ⟨hlo, hhi⟩ := planar_contact_distance_bounds hr hd
  calc
    _ ≤ ‖r - d • planarAxis 0‖ * Real.exp (2 - ‖r - d • planarAxis 0‖) :=
      planarResolventMode_sharp_upper (by linarith)
    _ ≤ _ := mul_le_mul hhi (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_pos _).le (by linarith)

theorem planarHopping_mode_lower {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1)) ≤
      planarResolventMode (r - d • planarAxis 0) := by
  obtain ⟨hlo, hhi⟩ := planar_contact_distance_bounds hr hd
  have hfrac : planarLowerTailConstant / (d + 3) ≤
      planarLowerTailConstant / (‖r - d • planarAxis 0‖ + 2) :=
    div_le_div_of_nonneg_left planarLowerTailConstant_positive.le (by positivity) (by linarith)
  calc
    _ ≤ planarLowerTailConstant / (‖r - d • planarAxis 0‖ + 2) *
        Real.exp (-‖r - d • planarAxis 0‖) :=
      mul_le_mul hfrac (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (div_nonneg planarLowerTailConstant_positive.le (by positivity))
    _ ≤ _ := planarResolventMode_sharp_lower (by linarith)

theorem planarHoppingUpperConstant_positive : 0 < planarHoppingUpperConstant := by
  unfold planarHoppingUpperConstant
  exact div_pos (mul_pos (Real.exp_pos _) planarForcing_integral_positive)
    (mul_pos (by norm_num) planarResolventMode_square_integral_positive)

theorem planarHoppingLowerConstant_positive : 0 < planarHoppingLowerConstant := by
  unfold planarHoppingLowerConstant
  exact div_pos (mul_pos (mul_pos planarLowerTailConstant_positive (Real.exp_pos _))
    planarForcing_integral_positive)
    (mul_pos (by norm_num) planarResolventMode_square_integral_positive)

theorem planarHopping_sharp_upper {d : ℝ} (hd : 2 ≤ d) :
    planarHopping d ≤ planarHoppingUpperConstant * (d + 1) * Real.exp (-d) := by
  have hpt (r : PlanarPosition) : planarHoppingIntegrand d r ≤
      planarForcing r * ((d + 1) * Real.exp (3 - d)) := by
    by_cases hf : planarForcing r = 0
    · simp only [planarHoppingIntegrand, hf, zero_mul, le_refl]
    have hr : ‖r‖ ≤ 1 := le_of_lt (lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
    exact mul_le_mul_of_nonneg_left (planarHopping_mode_upper hr hd) (planarForcing_nonnegative r)
  have hi := integral_mono (planarHoppingIntegrand_integrable d)
    (planarForcing_integrable.mul_const ((d + 1) * Real.exp (3 - d))) hpt
  rw [integral_mul_const] at hi
  have hden : 0 ≤ 2 * ∫ r, planarResolventMode r ^ 2 := by
    positivity
  have h := div_le_div_of_nonneg_right hi hden
  unfold planarHopping planarHoppingUpperConstant
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 3 - d = 3 + -d by ring, Real.exp_add]
  ring

theorem planarHopping_sharp_lower {d : ℝ} (hd : 2 ≤ d) :
    planarHoppingLowerConstant / (d + 3) * Real.exp (-d) ≤ planarHopping d := by
  have hpt (r : PlanarPosition) :
      planarForcing r * (planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1))) ≤
        planarHoppingIntegrand d r := by
    by_cases hf : planarForcing r = 0
    · simp only [planarHoppingIntegrand, hf, zero_mul, le_refl]
    have hr : ‖r‖ ≤ 1 := le_of_lt (lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
    exact mul_le_mul_of_nonneg_left (planarHopping_mode_lower hr hd) (planarForcing_nonnegative r)
  have hi := integral_mono
    (planarForcing_integrable.mul_const
      (planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1))))
    (planarHoppingIntegrand_integrable d) hpt
  rw [integral_mul_const] at hi
  have hden : 0 ≤ 2 * ∫ r, planarResolventMode r ^ 2 := by
    positivity
  have h := div_le_div_of_nonneg_right hi hden
  unfold planarHopping planarHoppingLowerConstant
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [show -(d + 1) = -1 + -d by ring, Real.exp_add]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint brackets and an actual contact-hopping calibration. Quantitative
scale selection and the polynomial-time numerical implementation remain
separate steps; no calibration output is assumed. -/

noncomputable section
namespace ContinuumCoulomb

theorem planarHopping_short_scaled {D ε : ℝ} (hd : 2 ≤ (1 - ε) * D) :
    planarHoppingLowerConstant / ((1 - ε) * D + 3) * Real.exp (ε * D) ≤
      Real.exp D * planarHopping ((1 - ε) * D) := by
  have h := mul_le_mul_of_nonneg_left (planarHopping_sharp_lower hd) (Real.exp_pos D).le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  calc
    _ = (planarHoppingLowerConstant / ((1 - ε) * D + 3)) *
        (Real.exp D * Real.exp (-((1 - ε) * D))) := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring
    _ = _ := by ring

theorem planarHopping_long_scaled {D ε : ℝ} (hd : 2 ≤ (1 + ε) * D) :
    Real.exp D * planarHopping ((1 + ε) * D) ≤
      planarHoppingUpperConstant * ((1 + ε) * D + 1) * Real.exp (-ε * D) := by
  have h := mul_le_mul_of_nonneg_left (planarHopping_sharp_upper hd) (Real.exp_pos D).le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  calc
    _ = (planarHoppingUpperConstant * ((1 + ε) * D + 1)) *
        (Real.exp D * Real.exp (-((1 + ε) * D))) := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarPolynomialScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial amplification of the actual hopping brackets. A fixed
large power of the input-size parameter suffices; the well constants and
contact tolerance remain fixed. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planar_polynomial_brackets {A k : ℕ} {ε N : ℝ}
    (hε : 0 ≤ ε) (_hε₁ : ε ≤ 1) (hN : 2 ≤ N)
    (hd : 2 ≤ (1 - ε) * ((k : ℝ) * Real.log N))
    (hγ : 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1))
    (hlo : (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)))
    (hhi : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1))) :
    N ^ A ≤ Real.exp ((k : ℝ) * Real.log N) *
      planarHopping ((1 - ε) * ((k : ℝ) * Real.log N)) ∧
    Real.exp ((k : ℝ) * Real.log N) *
      planarHopping ((1 + ε) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  have hNpos : 0 < N := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hNpos).trans (by linarith)
  let γ : ℝ := (k : ℝ) * ε - ((A : ℝ) + 1)
  have hp : (2 : ℝ) ^ γ ≤ N ^ γ := Real.rpow_le_rpow (by norm_num) hN hγ
  have hloN : (k : ℝ) + 3 ≤ planarHoppingLowerConstant * N ^ γ :=
    hlo.trans (mul_le_mul_of_nonneg_left hp planarHoppingLowerConstant_positive.le)
  have hhiN : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤ N ^ γ := hhi.trans hp
  have hexp : Real.exp (ε * ((k : ℝ) * Real.log N)) = N ^ A * N * N ^ γ := by
    calc
      _ = N ^ ((A : ℝ) + 1 + γ) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        dsimp [γ]
        ring
      _ = (N ^ (A : ℝ) * N ^ (1 : ℝ)) * N ^ γ := by
        rw [Real.rpow_add hNpos, Real.rpow_add hNpos]
      _ = _ := by rw [Real.rpow_natCast, Real.rpow_one]
  have hshort : (1 - ε) * ((k : ℝ) * Real.log N) + 3 ≤ ((k : ℝ) + 3) * N := by
    have hD : (1 - ε) * ((k : ℝ) * Real.log N) ≤ (k : ℝ) * Real.log N := by
      nlinarith [mul_nonneg hk hlog]
    have hkn := mul_le_mul_of_nonneg_left hlogN hk
    nlinarith
  have hlong : (1 + ε) * ((k : ℝ) * Real.log N) + 1 ≤ (2 * (k : ℝ) + 1) * N := by
    have hD : (1 + ε) * ((k : ℝ) * Real.log N) ≤ 2 * ((k : ℝ) * Real.log N) := by
      nlinarith [mul_nonneg hk hlog]
    have hkn := mul_le_mul_of_nonneg_left hlogN hk
    nlinarith
  have hD : 0 ≤ (k : ℝ) * Real.log N := mul_nonneg hk hlog
  have horder : (1 - ε) * ((k : ℝ) * Real.log N) ≤
      (1 + ε) * ((k : ℝ) * Real.log N) := by nlinarith
  constructor
  · apply le_trans _ (planarHopping_short_scaled hd)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    calc
      _ ≤ N ^ A * (((k : ℝ) + 3) * N) :=
        mul_le_mul_of_nonneg_left hshort (pow_nonneg hNpos.le _)
      _ ≤ N ^ A * ((planarHoppingLowerConstant * N ^ γ) * N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hloN hNpos.le)
          (pow_nonneg hNpos.le _)
      _ = _ := by rw [hexp]; ring
  · apply le_trans (planarHopping_long_scaled (hd.trans horder))
    rw [show -ε * ((k : ℝ) * Real.log N) = -(ε * ((k : ℝ) * Real.log N)) by ring,
      Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), hexp]
    have hpA : N ^ A ≠ 0 := pow_ne_zero _ hNpos.ne'
    calc
      _ ≤ planarHoppingUpperConstant * ((2 * (k : ℝ) + 1) * N) :=
        mul_le_mul_of_nonneg_left hlong planarHoppingUpperConstant_positive.le
      _ ≤ N ^ γ * N := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hhiN hNpos.le
      _ = _ := by field_simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarScaleChoice
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single fixed polynomial exponent gives uniform hopping brackets for
every input size. Exponential domination selects that exponent once. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem exists_planar_scale_conditions_above (B : ℝ) (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ B ≤ (k : ℝ) ∧ 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1) ∧
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log 2) ∧
      (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) ∧
      planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htbase : Tendsto (fun k : ℕ => Real.exp ((ε * Real.log 2) * (k : ℝ)) / (k : ℝ))
      atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 (ε * Real.log 2) (mul_pos hε hlog)).comp hcast
  have ht : Tendsto (fun k : ℕ => (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) / (k : ℝ))
      atTop atTop := by
    convert htbase.const_mul_atTop (Real.exp_pos (-((A : ℝ) + 1) * Real.log 2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← mul_div_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  let bound : ℝ := max B (max 1 (max (((A : ℝ) + 1) / ε) (2 / ((1 - ε) * Real.log 2))))
  have hb : ∀ᶠ k : ℕ in atTop, bound ≤ (k : ℝ) := hcast.eventually (eventually_ge_atTop bound)
  have hr : ∀ᶠ k : ℕ in atTop,
      max (4 / planarHoppingLowerConstant) (3 * planarHoppingUpperConstant) ≤
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) / (k : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨k, hkb, hkr⟩ := (hb.and hr).exists
  have hkbB : B ≤ (k : ℝ) := (le_max_left _ _).trans hkb
  have hkb0 : max 1 (max (((A : ℝ) + 1) / ε) (2 / ((1 - ε) * Real.log 2))) ≤ (k : ℝ) :=
    (le_max_right _ _).trans hkb
  have hk₁ : (1 : ℝ) ≤ k := (le_max_left _ _).trans hkb0
  have hkp : (0 : ℝ) < k := by linarith
  have hkA : ((A : ℝ) + 1) / ε ≤ k :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hkb0)
  have hkD : 2 / ((1 - ε) * Real.log 2) ≤ k :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hkb0)
  have hlo := (le_div_iff₀ hkp).mp ((le_max_left _ _).trans hkr)
  have hhi := (le_div_iff₀ hkp).mp ((le_max_right _ _).trans hkr)
  have hmul := mul_le_mul_of_nonneg_left hlo planarHoppingLowerConstant_positive.le
  have heq : planarHoppingLowerConstant * ((4 / planarHoppingLowerConstant) * (k : ℝ)) =
      4 * (k : ℝ) := by field_simp [planarHoppingLowerConstant_positive.ne']
  rw [heq] at hmul
  refine ⟨k, by exact_mod_cast hkp, hkbB, ?_, ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr ((div_le_iff₀ hε).mp hkA)
  · have h := (div_le_iff₀ (mul_pos (sub_pos.mpr hε₁) hlog)).mp hkD
    nlinarith
  · exact (by linarith : (k : ℝ) + 3 ≤ 4 * (k : ℝ)).trans hmul
  · have hU := planarHoppingUpperConstant_positive
    nlinarith

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

theorem coulombHoppingTarget_bounds {freq D τ K d : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2) (hd : D ≤ d)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) :
    τ * Real.sqrt (K * localizedGramConstant freq) ≤ coulombHoppingTarget freq τ K d ∧
      coulombHoppingTarget freq τ K d ≤ τ * Real.sqrt (K * localizedCoulombProfile freq 0) := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (localizedCoulombProfile_gap hfreq hD hleak hd) hK)) hτ
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (sub_le_self _ (localizedCoulombProfile_nonnegative freq d)) hK)) hτ

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

theorem sqrt_polynomial_bounds {N K : ℝ} {A : ℕ} (hN : 1 ≤ N)
    (hKlo : (N ^ A)⁻¹ ≤ K) (hKhi : K ≤ N ^ A) :
    (N ^ A)⁻¹ ≤ Real.sqrt K ∧ Real.sqrt K ≤ N ^ A := by
  have hp : 1 ≤ N ^ A := one_le_pow₀ hN
  have hp0 : 0 < N ^ A := by positivity
  have hi : 0 ≤ (N ^ A)⁻¹ := inv_nonneg.mpr hp0.le
  have hi₁ : (N ^ A)⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact (by nlinarith only [hi, hi₁] : ((N ^ A)⁻¹) ^ 2 ≤ (N ^ A)⁻¹).trans hKlo
  · apply Real.sqrt_le_iff.mpr
    exact ⟨hp0.le, hKhi.trans (by nlinarith only [hp])⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTargetRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse-polynomial hopping scales give polynomial target ranges for
all polynomially bounded positive spin coefficients. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_coulomb_target_polynomial_bounds {freq : ℝ} (hfreq : 0 < freq) (A B : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℝ, 2 ≤ N → ∀ K : ℝ,
      (N ^ A)⁻¹ ≤ K → K ≤ N ^ A →
      (N ^ (B + A + L))⁻¹ ≤ (N ^ B)⁻¹ * Real.sqrt (K * localizedGramConstant freq) ∧
      (N ^ B)⁻¹ * Real.sqrt (K * localizedCoulombProfile freq 0) ≤ N ^ (B + A + L) := by
  obtain ⟨L, hL, hconstants⟩ := exists_polynomial_constant_bounds
    (Real.sqrt_pos.mpr (localizedGramConstant_positive hfreq))
    (Real.sqrt (localizedCoulombProfile freq 0))
  refine ⟨L, hL, fun N hN K hKlo hKhi => ?_⟩
  have hN₁ : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hK : 0 ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hKlo
  obtain ⟨hrootlo, hroothi⟩ := sqrt_polynomial_bounds hN₁ hKlo hKhi
  obtain ⟨hclo, hUhi⟩ := hconstants N hN
  have hτ : 0 ≤ (N ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
  constructor
  · rw [Real.sqrt_mul hK]
    calc
      _ = (N ^ B)⁻¹ * ((N ^ A)⁻¹ * (N ^ L)⁻¹) := by
        rw [pow_add, pow_add]
        simp only [mul_inv_rev]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hrootlo hclo (inv_nonneg.mpr (pow_nonneg hNp.le L)) (Real.sqrt_nonneg K)) hτ
  · have hτ₁ : (N ^ B)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hNp B)).mpr (one_le_pow₀ hN₁)
    calc
      _ ≤ Real.sqrt (K * localizedCoulombProfile freq 0) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ₁
          (Real.sqrt_nonneg (K * localizedCoulombProfile freq 0))
      _ = Real.sqrt K * Real.sqrt (localizedCoulombProfile freq 0) := Real.sqrt_mul hK _
      _ ≤ N ^ A * N ^ L := mul_le_mul hroothi hUhi (Real.sqrt_nonneg _) (pow_nonneg hNp.le A)
      _ = N ^ (A + L) := (pow_add N A L).symm
      _ ≤ _ := pow_le_pow_right₀ hN₁ (by omega)

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalLogScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational approximation to the logarithmic contact scale. Only a fixed
rational approximation to `log 2` is used. The input-dependent operation is
the bit length of a natural power, so no real logarithm is queried at runtime. -/

noncomputable section
namespace ContinuumCoulomb.RationalLogScale

theorem bitLength_log_error (m : ℕ) (hm : 0 < m) :
    0 ≤ ((m.bits.length : ℝ) * Real.log 2 - Real.log (m : ℝ)) ∧
      (m.bits.length : ℝ) * Real.log 2 - Real.log (m : ℝ) ≤ Real.log 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < m.size := Nat.size_pos.mpr hm
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hlo : 2 ^ s ≤ m := Nat.lt_size.mp (by omega)
  have hhi : m < 2 ^ (s + 1) := by simpa only [hs] using Nat.lt_size_self m
  have hloR : (2 : ℝ) ^ s ≤ m := by exact_mod_cast hlo
  have hhiR : (m : ℝ) < 2 ^ (s + 1) := by exact_mod_cast hhi
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ s) hloR
  have hh := Real.log_lt_log hmR hhiR
  rw [Real.log_pow] at hl hh
  simp only [Nat.size_eq_bits_len, hs, Nat.cast_succ] at *
  constructor <;> nlinarith

theorem exists_logTwo_approximation {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℚ, 0 < c ∧ |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc0, hc1⟩ := exists_rat_btwn
    (show (1 - ε / 4) * Real.log 2 < (1 + ε / 4) * Real.log 2 by
      nlinarith [mul_pos hε hlog])
  refine ⟨c, ?_, abs_le.mpr ⟨?_, ?_⟩⟩
  · have : (0 : ℝ) < c := (mul_pos (by linarith : 0 < 1 - ε / 4) hlog).trans hc0
    exact_mod_cast this
  · nlinarith
  · nlinarith

theorem relative_error (c : ℚ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 8 ≤ ε * (k : ℝ)) :
    |(value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ)| ≤
      ε * ((k : ℝ) * Real.log (N : ℝ)) := by
  have hNp : 0 < N := by omega
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hE0 : 0 ≤ (k : ℝ) * Real.log (N : ℝ) := mul_nonneg (Nat.cast_nonneg _) (hlog.le.trans hlogN)
  obtain ⟨hb0, hb1⟩ := bitLength_log_error (N ^ k) (pow_pos hNp k)
  rw [Nat.cast_pow, Real.log_pow] at hb0 hb1
  have htriangle := abs_add_le
    (((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2))
    (((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ))
  have hchange : |(value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ)| ≤
      (((N ^ k).bits.length : ℝ) * (ε / 4 * Real.log 2)) + Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (N ^ k).bits.length :
      (0 : ℝ) ≤ (N ^ k).bits.length)
    have habs : |((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2)| ≤
        ((N ^ k).bits.length : ℝ) * (ε / 4 * Real.log 2) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact hmul
    rw [show |((N ^ k).bits.length : ℝ) * Real.log 2 -
        (k : ℝ) * Real.log (N : ℝ)| =
        ((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ)
      from abs_of_nonneg hb0] at htriangle
    have heq : (value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ) =
        ((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2) +
          (((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ)) := by
      simp only [value, Rat.cast_mul, Rat.cast_natCast]
      ring
    rw [heq]
    exact htriangle.trans (add_le_add habs hb1)
  have hround : 2 * Real.log 2 ≤ ε / 4 * ((k : ℝ) * Real.log (N : ℝ)) := by
    have hcount : (2 : ℝ) ≤ ε / 4 * (k : ℝ) := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hcount hlog.le
    have h₂ := mul_le_mul_of_nonneg_left hlogN
      (show 0 ≤ ε / 4 * (k : ℝ) by positivity)
    nlinarith only [h₁, h₂]
  have hbit := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ ε / 4 by positivity)
  have hsmall : ε / 4 * Real.log 2 ≤ Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith : ε / 4 ≤ 1) hlog.le).trans_eq (one_mul _)
  have hscaled := mul_nonneg hε.le hE0
  nlinarith only [hchange, hbit, hsmall, hround, hscaled]

theorem relative_bounds (c : ℚ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 8 ≤ ε * (k : ℝ)) :
    (1 - ε) * ((k : ℝ) * Real.log (N : ℝ)) ≤ (value c k N : ℝ) ∧
      (value c k N : ℝ) ≤ (1 + ε) * ((k : ℝ) * Real.log (N : ℝ)) := by
  have h := abs_le.mp (relative_error c hε hε1 hc k N hN hk)
  constructor <;> nlinarith [h.1, h.2]

end ContinuumCoulomb.RationalLogScale

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationRationalBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational endpoints lie inside the permitted contact interval and outside
the smaller interval used for the analytic sign estimates. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

theorem endpoint_bounds {ε D q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hD : 0 ≤ D)
    (hqlo : (1 - ε / 16) * D ≤ q) (hqhi : q ≤ (1 + ε / 16) * D) :
    (1 - ε) * D ≤ (1 - ε / 2) * q ∧
      (1 - ε / 2) * q ≤ (1 - ε / 4) * D ∧
      (1 + ε / 4) * D ≤ (1 + ε / 2) * q ∧
      (1 + ε / 2) * q ≤ (1 + ε) * D := by
  have hc0 : 0 ≤ 1 - ε / 2 := by linarith
  have hc1 : 0 ≤ 1 + ε / 2 := by linarith
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have ha0 : 1 - ε ≤ (1 - ε / 2) * (1 - ε / 16) := by nlinarith [sq_nonneg ε]
  have ha1 : (1 - ε / 2) * (1 + ε / 16) ≤ 1 - ε / 4 := by nlinarith [sq_nonneg ε]
  have hb0 : 1 + ε / 4 ≤ (1 + ε / 2) * (1 - ε / 16) := by nlinarith
  have hb1 : (1 + ε / 2) * (1 + ε / 16) ≤ 1 + ε := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right ha0 hD).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqlo hc0)
  · exact (mul_le_mul_of_nonneg_left hqhi hc0).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha1 hD)
  · exact (mul_le_mul_of_nonneg_right hb0 hD).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqlo hc1)
  · exact (mul_le_mul_of_nonneg_left hqhi hc1).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb1 hD)

theorem rational_endpoint_bounds (ε c : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ (ε : ℝ) / 64 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 128 ≤ (ε : ℝ) * (k : ℝ)) :
    let D := (k : ℝ) * Real.log (N : ℝ)
    let p := endpoints ε (RationalLogScale.value c k N)
    (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.1 ≤ (1 - (ε : ℝ) / 4) * D ∧
      (1 + (ε : ℝ) / 4) * D ≤ p.2 ∧ p.2 ≤ (1 + (ε : ℝ)) * D := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hc' : |(c : ℝ) - Real.log 2| ≤ ((ε : ℝ) / 16) / 4 * Real.log 2 := by
    convert hc using 1 <;> first | rfl | ring
  have hk' : 8 ≤ ((ε : ℝ) / 16) * (k : ℝ) := by nlinarith
  obtain ⟨hlo, hhi⟩ := RationalLogScale.relative_bounds c
    (show 0 < (ε : ℝ) / 16 by positivity) (show (ε : ℝ) / 16 ≤ 1 by linarith)
    hc' k N hN hk'
  have hD : 0 ≤ (k : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  simpa only [endpoints, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using endpoint_bounds hεR hεR1 hD hlo hhi

end ContinuumCoulomb.CalibrationRationalBracket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationEndpointSigns
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational endpoints retain the analytic polynomial hopping brackets.
This uses the proved exponential envelopes and does not require monotonicity
of the hopping function. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

theorem brackets_of_larger_tolerance {A k : ℕ} {ε η N : ℝ}
    (hε : 0 ≤ ε) (hεη : ε ≤ η) (hη1 : η ≤ 1) (hN : 2 ≤ N)
    (hd : 2 ≤ (1 - η) * ((k : ℝ) * Real.log N))
    (hγ : 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1))
    (hlo : (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)))
    (hhi : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1))) :
    N ^ A ≤ N ^ k * planarHopping ((1 - η) * ((k : ℝ) * Real.log N)) ∧
      N ^ k * planarHopping ((1 + η) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  have he : (k : ℝ) * ε - ((A : ℝ) + 1) ≤ (k : ℝ) * η - ((A : ℝ) + 1) :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left hεη (Nat.cast_nonneg _)) _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  have h := planar_polynomial_brackets (hε.trans hεη) hη1 hN hd (hγ.trans he)
    (hlo.trans (mul_le_mul_of_nonneg_left hp planarHoppingLowerConstant_positive.le))
    (hhi.trans hp)
  have heq : Real.exp ((k : ℝ) * Real.log N) = N ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  simpa only [heq] using h

theorem exists_rational_hopping_brackets (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (A : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ N : ℕ, 2 ≤ N →
        let D := (k : ℝ) * Real.log (N : ℝ)
        let p := endpoints ε (RationalLogScale.value c k N)
        (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.1 ≤ (1 - (ε : ℝ) / 4) * D ∧
          (1 + (ε : ℝ) / 4) * D ≤ p.2 ∧ p.2 ≤ (1 + (ε : ℝ)) * D ∧
          (N : ℝ) ^ A ≤ (N : ℝ) ^ k * planarHopping p.1 ∧
          (N : ℝ) ^ k * planarHopping p.2 ≤ ((N : ℝ) ^ A)⁻¹ := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hcpos, hc⟩ := RationalLogScale.exists_logTwo_approximation
    (show (0 : ℝ) < (ε : ℝ) / 16 by positivity)
    (show (ε : ℝ) / 16 ≤ 1 by linarith)
  have hc' : |(c : ℝ) - Real.log 2| ≤ (ε : ℝ) / 64 * Real.log 2 := by
    convert hc using 1 <;> first | rfl | ring
  let B : ℝ := max kmin (max (128 / (ε : ℝ)) (2 / ((1 - (ε : ℝ)) * Real.log 2)))
  obtain ⟨k, hkpos, hkB, hγ, _hd, hlo, hhi⟩ := exists_planar_scale_conditions_above
    B A (show (0 : ℝ) < (ε : ℝ) / 4 by positivity)
    (show (ε : ℝ) / 4 < 1 by linarith)
  have hkmin : kmin ≤ (k : ℝ) := (le_max_left _ _).trans hkB
  have hkcount : 128 ≤ (ε : ℝ) * (k : ℝ) := by
    have hb : 128 / (ε : ℝ) ≤ (k : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hkB)
    nlinarith [(div_le_iff₀ hεR).mp hb]
  have hkfloor : 2 ≤ (1 - (ε : ℝ)) * ((k : ℝ) * Real.log 2) := by
    have hb : 2 / ((1 - (ε : ℝ)) * Real.log 2) ≤ (k : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hkB)
    have hm := (div_le_iff₀ (mul_pos (sub_pos.mpr hεR1) hlog)).mp hb
    nlinarith
  refine ⟨c, k, hcpos, hkpos, hkmin, fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hNR
  let D : ℝ := (k : ℝ) * Real.log (N : ℝ)
  let p := endpoints ε (RationalLogScale.value c k N)
  have hD : 0 < D := mul_pos (by exact_mod_cast hkpos) (hlog.trans_le hlogN)
  have hfloor : 2 ≤ (1 - (ε : ℝ)) * D := by
    have hm := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    exact hkfloor.trans (mul_le_mul_of_nonneg_left hm (sub_pos.mpr hεR1).le)
  obtain ⟨ha0, ha1, hb0, hb1⟩ := rational_endpoint_bounds ε c hε hε1.le hc' k N hN hkcount
  have har0 : 1 - (ε : ℝ) ≤ (p.1 : ℝ) / D := (le_div_iff₀ hD).mpr ha0
  have har1 : (p.1 : ℝ) / D ≤ 1 - (ε : ℝ) / 4 := (div_le_iff₀ hD).mpr ha1
  have hbr0 : 1 + (ε : ℝ) / 4 ≤ (p.2 : ℝ) / D := (le_div_iff₀ hD).mpr hb0
  have hbr1 : (p.2 : ℝ) / D ≤ 1 + (ε : ℝ) := (div_le_iff₀ hD).mpr hb1
  let ηa : ℝ := 1 - (p.1 : ℝ) / D
  let ηb : ℝ := (p.2 : ℝ) / D - 1
  have hηa : (ε : ℝ) / 4 ≤ ηa ∧ ηa ≤ (ε : ℝ) := by dsimp only [ηa]; constructor <;> linarith
  have hηb : (ε : ℝ) / 4 ≤ ηb ∧ ηb ≤ (ε : ℝ) := by dsimp only [ηb]; constructor <;> linarith
  have haeq : (1 - ηa) * D = (p.1 : ℝ) := by
    dsimp only [ηa]
    field_simp [hD.ne']; ring
  have hbeq : (1 + ηb) * D = (p.2 : ℝ) := by
    dsimp only [ηb]
    field_simp [hD.ne']; ring
  have hshort := brackets_of_larger_tolerance (show (0 : ℝ) ≤ (ε : ℝ) / 4 by positivity)
    hηa.1 (hηa.2.trans hεR1.le) hNR
    (hfloor.trans (mul_le_mul_of_nonneg_right (by linarith : 1 - (ε : ℝ) ≤ 1 - ηa) hD.le))
    hγ hlo hhi
  have hlong := brackets_of_larger_tolerance (show (0 : ℝ) ≤ (ε : ℝ) / 4 by positivity)
    hηb.1 (hηb.2.trans hεR1.le) hNR
    (hfloor.trans (mul_le_mul_of_nonneg_right (by linarith : 1 - (ε : ℝ) ≤ 1 - ηb) hD.le))
    hγ hlo hhi
  change (1 - (ε : ℝ)) * D ≤ (p.1 : ℝ) ∧ _
  refine ⟨ha0, ha1, hb0, hb1, ?_, ?_⟩
  · have hs : (N : ℝ) ^ A ≤ (N : ℝ) ^ k * planarHopping ((1 - ηa) * D) := hshort.1
    rwa [haeq] at hs
  · have hl : (N : ℝ) ^ k * planarHopping ((1 + ηb) * D) ≤ ((N : ℝ) ^ A)⁻¹ := hlong.2
    rwa [hbeq] at hl

end ContinuumCoulomb.CalibrationRationalBracket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibrationCoulombBrackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rational search intervals for the actual Coulomb-calibrated
hopping target. The fixed exponent simultaneously enforces the separated
two-site denominator and both endpoint signs. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

theorem exists_coulomb_brackets {freq : ℝ} (hfreq : 0 < freq)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (A B : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ N : ℕ, 2 ≤ N →
        let D := (k : ℝ) * Real.log (N : ℝ)
        let p := endpoints ε (RationalLogScale.value c k N)
        (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.2 ≤ (1 + (ε : ℝ)) * D ∧
          5 ≤ (1 - (ε : ℝ)) * D ∧
          (∀ r : ℝ, (p.1 : ℝ) ≤ r → localizedGramConstant freq ≤
            localizedCoulombProfile freq 0 - localizedCoulombProfile freq r) ∧
          (∀ K : ℚ, ((N : ℝ) ^ A)⁻¹ ≤ K → (K : ℝ) ≤ (N : ℝ) ^ A →
            0 ≤ (N : ℝ) ^ k * planarHopping p.1 -
              coulombHoppingTarget freq ((N : ℝ) ^ B)⁻¹ K p.1 ∧
            (N : ℝ) ^ k * planarHopping p.2 -
              coulombHoppingTarget freq ((N : ℝ) ^ B)⁻¹ K p.2 ≤ 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) < 1 := by exact_mod_cast hε1
  obtain ⟨L, _, hrange⟩ := exists_coulomb_target_polynomial_bounds hfreq A B
  obtain ⟨k₀, _, hspacing⟩ := exists_localizedGram_spacing hfreq 1
  obtain ⟨c, k, hc, hk, hkmin, hbracket⟩ := exists_rational_hopping_brackets
    ε hε hε1 (B + A + L) (max kmin ((k₀ : ℝ) / (1 - (ε : ℝ))))
  have hkmin' : kmin ≤ (k : ℝ) := (le_max_left _ _).trans hkmin
  have hkspacing : (k₀ : ℝ) / (1 - (ε : ℝ)) ≤ k := (le_max_right _ _).trans hkmin
  refine ⟨c, k, hc, hk, hkmin', fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  let D : ℝ := (k : ℝ) * Real.log (N : ℝ)
  let p := endpoints ε (RationalLogScale.value c k N)
  obtain ⟨ha0, ha1, hb0, hb1, haHop, hbHop⟩ := hbracket N hN
  have hlength : (k₀ : ℝ) * Real.log (N : ℝ) ≤ (1 - (ε : ℝ)) * D := by
    have hm := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sub_pos.mpr hεR1)).mp hkspacing) hlogN
    nlinarith only [hm]
  obtain ⟨hfive, hleak⟩ := hspacing N hNR
  have hleak₂ : 2 * localLeakageBound freq ((k₀ : ℝ) * Real.log (N : ℝ)) ≤
      localDualMass freq / 2 := by
    have hm := mul_le_mul_of_nonneg_right hNR
      (localLeakageBound_nonnegative freq ((k₀ : ℝ) * Real.log (N : ℝ)))
    exact hm.trans (by simpa only [pow_one] using hleak)
  have hsepA : (k₀ : ℝ) * Real.log (N : ℝ) ≤ (p.1 : ℝ) := hlength.trans ha0
  have hD0 : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hlogN
  have hab : (p.1 : ℝ) ≤ p.2 := by
    have horder : (1 - (ε : ℝ) / 4) * D ≤ (1 + (ε : ℝ) / 4) * D := by
      nlinarith [mul_nonneg hεR.le hD0]
    exact ha1.trans (horder.trans hb0)
  change (1 - (ε : ℝ)) * D ≤ (p.1 : ℝ) ∧ _
  refine ⟨ha0, hb1, hfive.trans hlength, ?_, ?_⟩
  · intro r hr
    exact localizedCoulombProfile_gap hfreq hfive hleak₂ (hsepA.trans hr)
  · intro K hKlo hKhi
    have hK : (0 : ℝ) ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hKlo
    have hτ : 0 ≤ ((N : ℝ) ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
    obtain ⟨htlo, hthi⟩ := hrange N hNR K hKlo hKhi
    have htargetA := coulombHoppingTarget_bounds hfreq hfive hleak₂ hsepA hτ hK
    have htargetB := coulombHoppingTarget_bounds hfreq hfive hleak₂ (hsepA.trans hab) hτ hK
    exact ⟨sub_nonneg.mpr ((htargetA.2.trans hthi).trans haHop),
      sub_nonpos.mpr (hbHop.trans (htlo.trans htargetB.1))⟩

end ContinuumCoulomb.CalibrationRationalBracket

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

theorem prefactor_positive {rho : ℕ} (hrho : 0 < rho) : 0 < prefactor rho := by
  unfold prefactor
  positivity

theorem base_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ base n := by
  exact (by norm_num : 2 ≤ 2^30).trans (Nat.pow_le_pow_left hn 30)

end ContinuumCoulomb.CalibrationMesh

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

theorem queryBound_coefficients (k A : ℕ) (N : ℕ) {K : ℚ}
    (hK : (K : ℝ) ≤ (N : ℝ) ^ A) : (K : ℝ) ≤ queryBound k A N := by
  have hcast : (N : ℝ) ^ A ≤ (queryBound k A N : ℝ) := by
    exact_mod_cast (show N ^ A ≤ queryBound k A N by unfold queryBound; omega)
  exact hK.trans hcast

theorem interval_query_bound {ε c : ℚ} (hε1 : ε ≤ 1) (k A N : ℕ)
    (ha : (1 - (ε : ℝ)) * ((k : ℝ) * Real.log N) ≤ (interval ε c k N).1)
    (hb : ((interval ε c k N).2 : ℝ) ≤ (1 + (ε : ℝ)) * ((k : ℝ) * Real.log N))
    (hN : 2 ≤ N) :
    -(queryBound k A N : ℝ) ≤ (interval ε c k N).1 ∧
      ((interval ε c k N).2 : ℝ) ≤ queryBound k A N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hD : 0 ≤ (k : ℝ) * Real.log N := mul_nonneg (Nat.cast_nonneg _) hlog
  have hlow : (0 : ℝ) ≤ (interval ε c k N).1 :=
    (mul_nonneg (sub_nonneg.mpr hεR1) hD).trans ha
  have hupper : ((interval ε c k N).2 : ℝ) ≤ 2 * k * N := by
    calc
      _ ≤ (1 + (ε : ℝ)) * ((k : ℝ) * Real.log N) := hb
      _ ≤ 2 * ((k : ℝ) * Real.log N) := by gcongr; linarith
      _ ≤ 2 * ((k : ℝ) * N) := by
        gcongr
        exact Real.log_le_self (by positivity)
      _ = _ := by ring
  have hbound : 2 * (k : ℝ) * N ≤ (queryBound k A N : ℝ) := by
    exact_mod_cast (show 2 * k * N ≤ queryBound k A N by unfold queryBound; omega)
  exact ⟨(neg_nonpos.mpr (Nat.cast_nonneg _)).trans hlow, hupper.trans hbound⟩

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_AutomaticCalibrationCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed polynomial-time distance program has the true Coulomb
calibration residual and geometric length bounds. All interval signs and
evaluation precision are discharged by the constructed program. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration

theorem exists_automatic_calibration (rho : ℕ) (hrho : 0 < rho)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (A B : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ (N P : ℕ) (K : ℚ), 2 ≤ N → ((N : ℝ) ^ A)⁻¹ ≤ K → (K : ℝ) ≤ (N : ℝ) ^ A →
        let d := value rho ε c k A B (N, (P, K))
        let D := (k : ℝ) * Real.log (N : ℝ)
        (1 - (ε : ℝ)) * D ≤ d ∧ (d : ℝ) ≤ (1 + (ε : ℝ)) * D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
              localizedCoulombProfile (GaussianFrequency.frequency rho) d ∧
          |(N : ℝ) ^ k * planarHopping d -
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N : ℝ) ^ B)⁻¹ K d| ≤
              ((P : ℝ) + 1)⁻¹ := by
  have hfreq : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  obtain ⟨c, k, hc, hk, hkmin, hbracket⟩ :=
    CalibrationRationalBracket.exists_coulomb_brackets hfreq ε hε hε1 A B kmin
  refine ⟨c, k, hc, hk, hkmin, ?_⟩
  intro N P K hN hKlo hKhi
  let x : Input := (N, (P, K))
  let e := environment k A B x
  let p := interval ε c k N
  obtain ⟨ha, hb, _, hgap, hsign⟩ := hbracket N hN
  have hmem := value_mem (rho := rho) (k := k) (A := A) (B := B)
    x hε.le hc.le
  have hleft : (p.1 : ℝ) ≤ value rho ε c k A B x := by exact_mod_cast hmem.1
  have hright : (value rho ε c k A B x : ℝ) ≤ p.2 := by exact_mod_cast hmem.2
  have hK0 : (0 : ℝ) ≤ K := (inv_nonneg.mpr (by positivity)).trans hKlo
  have hKQ : (0 : ℚ) ≤ K := by exact_mod_cast hK0
  have hKbound : (K : ℝ) ≤ queryBound k A N := queryBound_coefficients k A N hKhi
  have hτ : (0 : ℚ) ≤ ((N ^ B : ℕ) : ℚ)⁻¹ := by positivity
  have hNB : (1 : ℚ) ≤ ((N ^ B : ℕ) : ℚ) := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ N by omega) : 1 ≤ N ^ B)
  have hτ1 : (((N ^ B : ℕ) : ℚ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hNB
  have hab : p.1 ≤ p.2 := interval_order hε.le hc.le k N
  have hquery := interval_query_bound hε1.le k A N ha hb hN
  have hs := hsign K hKlo hKhi
  have hsignA : 0 ≤ CalibratedEvaluation.residual rho e p.1 := by
    simpa only [CalibratedEvaluation.residual, e, environment, x, p, interval,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using hs.1
  have hsignB : CalibratedEvaluation.residual rho e p.2 ≤ 0 := by
    simpa only [CalibratedEvaluation.residual, e, environment, x, p, interval,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using hs.2
  have herr := CalibratedEvaluation.scheduled_residual rho hrho e p.1 p.2
    hKQ hKbound hτ hτ1 hab hquery.1 hquery.2 hsignA hsignB
    (fun r hr => hgap r hr.1)
  refine ⟨ha.trans hleft, hright.trans hb, hgap _ hleft, ?_⟩
  simpa only [value, CalibratedEvaluation.residual, e, environment, x, p, interval,
    Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using herr

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorCalibration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive rational prefactor in the physical amplification is
absorbed into the requested edge weight. This retains the proved evaluator
and bisection, including their polynomial running times. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorCalibration

theorem normalizedValue_mem (rho : ℕ) (a : ℚ) (C : ℕ) {ε c : ℚ}
    (hε : 0 ≤ ε) (hc : 0 < c) (k A B : ℕ) (x : AutomaticCalibration.Input)
    (hN : 0 < x.1) : normalizedValue rho a C ε c k A B x ∈
      Set.Icc (1-ε/2) (1+ε/2) :=
  AutomaticCalibration.normalizedValue_mem rho hε hc k A B (input a C x) hN

theorem target_scale {a : ℝ} (ha : 0 < a) (freq τ K d : ℝ) :
    a*coulombHoppingTarget freq τ (K/a^2) d = coulombHoppingTarget freq τ K d := by
  unfold coulombHoppingTarget
  rw [show K/a^2*(localizedCoulombProfile freq 0-localizedCoulombProfile freq d) =
    (K*(localizedCoulombProfile freq 0-localizedCoulombProfile freq d))/a^2 by ring,
    Real.sqrt_div' _ (sq_nonneg a),Real.sqrt_sq ha.le]
  field_simp [ha.ne']

theorem weight_polynomial_range {a : ℚ} (ha : 0 < a) (A : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ (N : ℝ), 2 ≤ N → ∀ K : ℚ,
      (N^A)⁻¹ ≤ (K:ℝ) → (K:ℝ) ≤ N^A →
      (N^(A+L))⁻¹ ≤ (adjustedWeight a K:ℝ) ∧
        (adjustedWeight a K:ℝ) ≤ N^(A+L) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have ha2 : 0 < ((a:ℝ)^2)⁻¹ := inv_pos.mpr (sq_pos_of_pos haR)
  obtain ⟨L,hL,hbound⟩ := exists_polynomial_constant_bounds ha2 (((a:ℝ)^2)⁻¹)
  refine ⟨L,hL,fun N hN K hlo hhi => ?_⟩
  have hNp : 0 < N := by linarith
  have hK : (0:ℝ) ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hlo
  obtain ⟨hcl,hcu⟩ := hbound N hN
  have he : (adjustedWeight a K:ℝ) = (K:ℝ)*((a:ℝ)^2)⁻¹ := by
    rw [adjustedWeight,Rat.cast_div,Rat.cast_pow,div_eq_mul_inv]
  rw [he,pow_add,mul_inv_rev]
  constructor
  · have hm := mul_le_mul hlo hcl (inv_nonneg.mpr (pow_nonneg hNp.le L)) hK
    simpa only [mul_comm] using hm
  · exact mul_le_mul hhi hcu ha2.le (pow_nonneg hNp.le A)

theorem precision_error {a : ℝ} {C : ℕ} (_ha : 0 ≤ a) (hC : a ≤ C) (P : ℕ) :
    a*((precision C P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  rw [← div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ (P:ℝ)+1)
  simp only [precision,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  nlinarith

theorem exists_calibration (rho : ℕ) (hrho : 0 < rho)
    (a : ℚ) (ha : 0 < a) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (A B : ℕ) (kmin : ℝ) :
    ∃ (C L : ℕ) (c : ℚ) (k : ℕ), 0 < C ∧ 0 < L ∧ 0 < c ∧ 0 < k ∧ kmin ≤ (k:ℝ) ∧
      ∀ (N P : ℕ) (K : ℚ), 2 ≤ N → ((N:ℝ)^A)⁻¹ ≤ K → (K:ℝ) ≤ (N:ℝ)^A →
        let d := value rho a C ε c k (A+L) B (N,(P,K))
        let D := (k:ℝ)*Real.log (N:ℝ)
        (1-(ε:ℝ))*D ≤ d ∧ (d:ℝ) ≤ (1+(ε:ℝ))*D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0-
              localizedCoulombProfile (GaussianFrequency.frequency rho) d ∧
          |(a:ℝ)*(N:ℝ)^k*planarHopping d-
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d| ≤
              ((P:ℝ)+1)⁻¹ := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  obtain ⟨C,hC⟩ := exists_nat_gt (max 1 (a:ℝ))
  have hCp : 0 < C := by
    have hp : (0:ℝ) < C := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hC)
    exact_mod_cast hp
  have hCa : (a:ℝ) ≤ C := ((le_max_right _ _).trans_lt hC).le
  obtain ⟨L,hL,hweights⟩ := weight_polynomial_range ha A
  obtain ⟨c,k,hc,hk,hkmin,hcal⟩ := AutomaticCalibration.exists_automatic_calibration
    rho hrho ε hε hε1 (A+L) B kmin
  refine ⟨C,L,c,k,hCp,hL,hc,hk,hkmin,fun N P K hN hlo hhi => ?_⟩
  obtain ⟨hwl,hwu⟩ := hweights N (by exact_mod_cast hN) K hlo hhi
  obtain ⟨hdl,hdu,hgap,herror⟩ := hcal N (precision C P) (adjustedWeight a K) hN hwl hwu
  change (1-(ε:ℝ))*((k:ℝ)*Real.log (N:ℝ)) ≤
    AutomaticCalibration.value rho ε c k (A+L) B (N,(precision C P,adjustedWeight a K)) ∧ _
  refine ⟨hdl,hdu,hgap,?_⟩
  let d := AutomaticCalibration.value rho ε c k (A+L) B (N,(precision C P,adjustedWeight a K))
  have ht := target_scale haR (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d
  have hweight : (adjustedWeight a K:ℝ) = (K:ℝ)/(a:ℝ)^2 := by
    simp only [adjustedWeight,Rat.cast_div,Rat.cast_pow]
  rw [hweight] at herror
  change |(a:ℝ)*(N:ℝ)^k*planarHopping d-
    coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d| ≤ ((P:ℝ)+1)⁻¹
  calc
    _ = |(a:ℝ)*((N:ℝ)^k*planarHopping d-
        coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
          ((K:ℝ)/(a:ℝ)^2) d)| := by rw [mul_sub,ht]; congr 1; ring
    _ = (a:ℝ)*|(N:ℝ)^k*planarHopping d-
        coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
          ((K:ℝ)/(a:ℝ)^2) d| := by rw [abs_mul,abs_of_pos haR]
    _ ≤ (a:ℝ)*((precision C P:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_left herror haR.le
    _ ≤ ((P:ℝ)+1)⁻¹ := precision_error haR.le hCa P

end ContinuumCoulomb.PrefactorCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCoefficientRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-denominator source coefficient rounding, implemented by
actual integer/rational machine arithmetic. Nonzero rounded weights have
an inverse-polynomial lower bound without assuming one for the source. -/

namespace ContinuumCoulomb.SourceCoefficientRounding
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem coefficient_error {M : ℕ} (hM : 0 < M) (q : ℚ) :
    |q - coefficient M q| ≤ 1 / (2 * (M : ℚ)) := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have heq : q - coefficient M q = ((M : ℚ) * q - round ((M : ℚ) * q)) / M := by
    unfold coefficient
    field_simp
  rw [heq, abs_div, abs_of_pos hm]
  calc
    _ ≤ (1 / 2 : ℚ) / M := div_le_div_of_nonneg_right (abs_sub_round ((M : ℚ) * q)) hm.le
    _ = _ := by ring

theorem coefficient_nonzero_lower {M : ℕ} (hM : 0 < M) (q : ℚ)
    (hq : coefficient M q ≠ 0) : 1 / (M : ℚ) ≤ |coefficient M q| := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hk : round ((M : ℚ) * q) ≠ 0 := by
    intro hk
    apply hq
    simp only [coefficient, hk, Int.cast_zero, zero_div]
  have ha : (1 : ℤ) ≤ |round ((M : ℚ) * q)| := by
    have hp := abs_nonneg (round ((M : ℚ) * q))
    have hn := abs_ne_zero.mpr hk
    omega
  have ha' : (1 : ℚ) ≤ |(round ((M : ℚ) * q) : ℚ)| := by exact_mod_cast ha
  rw [coefficient, abs_div, abs_of_pos hm]
  exact div_le_div_of_nonneg_right ha' hm.le

theorem coefficient_upper {M W : ℕ} (hM : 0 < M) (q : ℚ) (hq : |q| ≤ W) :
    |coefficient M q| ≤ W + 1 := by
  have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have he := coefficient_error hM q
  have hhalf : (1 : ℚ) / (2 * M) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
  have h := abs_add_le (coefficient M q - q) q
  rw [sub_add_cancel] at h
  rw [abs_sub_comm] at he
  linarith

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceZeroFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem nonzero_mem (xs : List Bond) (e : Bond) (he : e ∈ xs.filter keep) : e.2.2 ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp he).2

end ContinuumCoulomb.SourceZeroFilter

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceNormalizedSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source rounding and zero deletion feed the complete three-stage
spin comparison. Only the source's upper coefficient and gap bounds are
needed; a nonzero lower coefficient bound is proved by rounding. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open Matrix MediatorIteration MediatorListProgram SourceBondLists
open scoped BigOperators

theorem family_bounds (d : SquareLatticeHeisenberg) {M W : ℕ} (hM : 0 < M)
    (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    ∀ e, 1 / ((M + W + 1 : ℕ) : ℝ) ≤ |((family d M).weight e : ℝ)| ∧
      |((family d M).weight e : ℝ)| ≤ (M + W + 1 : ℕ) := by
  intro e
  have he := List.get_mem (retained d M) e
  have hz := SourceZeroFilter.nonzero_mem (rounded d M) _ he
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  have hw : (family d M).weight e = SourceCoefficientRounding.coefficient M (d.coefficient i) := by
    exact congrArg (fun a : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond => a.2.2) hi.symm
  have hz' : SourceCoefficientRounding.coefficient M (d.coefficient i) ≠ 0 := by simpa only [← hi] using hz
  have hl : 1 / (M : ℝ) ≤ |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| := by
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_nonzero_lower hM (d.coefficient i) hz')
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] using hq
  have hq : |d.coefficient i| ≤ (W : ℚ) := by exact_mod_cast hW i
  have hu : |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| ≤ W + 1 := by
    exact_mod_cast SourceCoefficientRounding.coefficient_upper hM (d.coefficient i) hq
  rw [hw]
  constructor
  · exact (one_div_le_one_div_of_le (by exact_mod_cast hM)
      (by norm_cast; omega : (M : ℝ) ≤ (M + W + 1 : ℕ))).trans hl
  · have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast
    linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

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

theorem denominator_pos (r : ℕ) {G : ℕ} (hG : 0 < G) : 0 < denominator r G := by
  unfold denominator
  positivity

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

theorem polynomialPromise_weight (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    ∀ e, |((d.toSource h).coefficient e : ℝ)| ≤ (size d ^ k : ℕ) := by
  intro e
  simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, BinaryHeisenberg.toSource] using
    hp.weight_bound e

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialUnaryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the runtime bound of an actual unary-output procedure into a
single fixed power of the source input length, as needed by calibration. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

theorem natPolynomial_power_bound (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, p.eval n ≤ (n + 2) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 1, fun n => ?_⟩
    have hbase : 1 ≤ n + 2 := by omega
    have hpa : (n + 2) ^ a ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    have hpb : (n + 2) ^ b ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    rw [Polynomial.eval_add, pow_succ]
    calc
      p.eval n + q.eval n ≤ (n + 2) ^ (a + b) + (n + 2) ^ (a + b) :=
        Nat.add_le_add ((ha n).trans hpa) ((hb n).trans hpb)
      _ = (n + 2) ^ (a + b) * 2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  | monomial i c =>
    refine ⟨c + i, fun n => ?_⟩
    have hc : c ≤ (n + 2) ^ c :=
      (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left (by omega) c)
    rw [Polynomial.eval_monomial, pow_add]
    exact Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) i)

theorem unaryProcedure_power_bound {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) :
    ∃ k : ℕ, ∀ a, f a ≤ ((ea a).length + 2) ^ k := by
  obtain ⟨k, hk⟩ := natPolynomial_power_bound (Polynomial.X + p.bound)
  refine ⟨k, fun a => ?_⟩
  have h := p.output_length_le a
  simp only [unaryCode, List.length_replicate] at h
  exact h.trans (by simpa only [Polynomial.eval_add, Polynomial.eval_X] using hk (ea a).length)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePositiveBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem finalBound_power (k : ℕ) :
    ∃ A : ℕ, ∀ d, finalBound k d ≤ ((binaryHeisenbergCodec.encode d).length + 2) ^ A :=
  unaryProcedure_power_bound (finalBoundProgram k)

private theorem envWeight_congr (x : Env) (r W G n : ℕ) (h : x = (r, W, G, n)) :
    MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1 =
      MediatorParameters.finalWeight r W G := by
  cases h
  rfl

private theorem finalBound_of_env (k : ℕ) (d : BinaryHeisenberg) (r W G n : ℕ)
    (he : (SourceNormalizationProgram.normalized (input k d)).1 = (r, W, G, n)) :
    finalBound k d = MediatorParameters.finalWeight r W G := by
  exact envWeight_congr ((SourceNormalizationProgram.normalized (input k d)).1) r W G n he

theorem finalBound_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    finalBound k d = MediatorParameters.finalWeight
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
      (roundingDenominator k d + size d ^ k + 1) (size d ^ k) := by
  have he : (SourceNormalizationProgram.normalized (input k d)).1 =
      ((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length,
        roundingDenominator k d + size d ^ k + 1, size d ^ k, d.coordinate.length) :=
    congrArg Prod.fst (normalized_eq k d h)
  exact finalBound_of_env k d
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length
    (roundingDenominator k d + size d ^ k + 1) (size d ^ k) d.coordinate.length he

/-- One fixed exponent controls every final coefficient, even when the
original source contains zero or exponentially tiny rational coefficients. -/
theorem source_positive_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid),
      d.PolynomialPromise k → ∀ e,
      (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
        ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
      ((MediatorIteration.finalGraph
          (SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d))
          (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
        ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA⟩ := finalBound_power k
  refine ⟨A + 1, by omega, fun d h hp e => ?_⟩
  have hG : 0 < size d ^ k := pow_pos (size_pos d) k
  have hM : 0 < roundingDenominator k d :=
    SourceNormalizedSpectrum.denominator_pos d.edges.length hG
  have hW : 0 < roundingDenominator k d + size d ^ k + 1 := by omega
  have hB := SourceNormalizedSpectrum.family_bounds (d.toSource h) hM
    (polynomialPromise_weight k d h hp)
  have hlo := MediatorIteration.finalGraph_lower _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hhi := MediatorIteration.finalGraph_upper _ hW hG (fun i => (hB i).2) (fun i => (hB i).1) e
  have hsize : 2 ≤ (binaryHeisenbergCodec.encode d).length + 2 := by omega
  have hpow : (2 : ℝ) ≤ ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ (A + 1) := by
    exact_mod_cast hsize.trans (Nat.le_self_pow (by omega : A + 1 ≠ 0) _)
  constructor
  · have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow
    norm_num only [one_div] at hi
    exact hi.trans hlo
  · apply hhi.trans
    rw [← finalBound_eq k d h]
    have hn := (hA d).trans (Nat.pow_le_pow_right (by omega : 1 ≤
      (binaryHeisenbergCodec.encode d).length + 2) (by omega : A ≤ A + 1))
    exact_mod_cast hn

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGeometryBounds
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

theorem geometricSource_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid), d.PolynomialPromise k →
      ∀ e : GlobalEdge (geometricSource k d h),
        (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
          ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
        ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
          ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA, hweight⟩ := source_positive_weight_range k
  exact ⟨A, hA, hweight⟩

end ContinuumCoulomb.SourceMetadataProgram

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

theorem source_weight_range (s : ℕ) : ∃ A : ℕ, 0 < A ∧
    ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
    ∀ e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd),
      ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
        SourceContactProgram.weights s d hd e ∧
      (SourceContactProgram.weights s d hd e:ℝ) ≤
        (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A := by
  obtain ⟨A,hA,hweight⟩ := SourceMetadataProgram.geometricSource_weight_range s
  refine ⟨A,hA,fun d hd hp e => ?_⟩
  obtain ⟨hlo,hhi⟩ := hweight d hd hp e
  have hn : (1:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast (show 1 ≤ SourceContactProgram.size d from
      le_trans (by decide : 1 ≤ 2) (SourceContactProgram.size_ge_two d))
  have hbase : (SourceContactProgram.size d:ℝ) ≤
      CalibrationMesh.base (SourceContactProgram.size d) := by
    simp only [CalibrationMesh.base,Nat.cast_pow]
    exact le_self_pow₀ hn (by decide)
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ SourceContactProgram.size d) hbase A
  have hsize : (SourceContactProgram.size d:ℝ) =
      (binaryHeisenbergCodec.encode d).length + 2 := by
    simp only [SourceContactProgram.size,SourceMetadataProgram.size,Nat.cast_add,Nat.cast_one]
    ring
  have hlo' : ((SourceContactProgram.size d:ℝ)^A)⁻¹ ≤
      (SourceContactProgram.weights s d hd e:ℝ) := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hlo
  have hhi' : (SourceContactProgram.weights s d hd e:ℝ) ≤
      (SourceContactProgram.size d:ℝ)^A := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hhi
  refine ⟨?_,hhi'.trans hpow⟩
  have hpos : (0:ℝ) < (SourceContactProgram.size d:ℝ)^A := by positivity
  have hinv : ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
      ((SourceContactProgram.size d:ℝ)^A)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpos hpow
  exact hinv.trans hlo'

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorSpacing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nominal test at unit weight bounds the shared rational spacing even
when the particular source has no edges. No approximation certificate for
logarithm evaluation needs to be added to the construction interface. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorCalibration

theorem spacing_bounds (rho : ℕ) (a : ℚ) (C : ℕ) {ε c : ℚ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/1000) (hc : 0 < c)
    (k A B N P : ℕ) (hN : 2 ≤ N)
    (hlen :
      (1-(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) ≤
        value rho a C ε c k A B (CalibrationMesh.base N,(P,1)) ∧
      (value rho a C ε c k A B (CalibrationMesh.base N,(P,1)):ℝ) ≤
        (1+(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N))) :
    (59/2:ℝ)*(k:ℝ)*Real.log N ≤ AutomaticCalibration.spacing c k (CalibrationMesh.base N) ∧
      (AutomaticCalibration.spacing c k (CalibrationMesh.base N):ℝ) ≤ 31*(k:ℝ)*Real.log N := by
  let Q := AutomaticCalibration.spacing c k (CalibrationMesh.base N)
  let x : AutomaticCalibration.Input := (CalibrationMesh.base N,(P,1))
  let t := (normalizedValue rho a C ε c k A B x:ℝ)
  let r := (value rho a C ε c k A B x:ℝ)
  have hbase : 0 < CalibrationMesh.base N := lt_of_lt_of_le (by decide : 0 < 2)
    (CalibrationMesh.base_ge_two hN)
  have hQ : (0:ℝ) < Q := by exact_mod_cast AutomaticCalibration.spacing_positive hc k _ hbase
  have he : (Q:ℝ)*t=r := by
    dsimp only [t,r,normalizedValue,x,Q]
    push_cast
    field_simp [show (AutomaticCalibration.spacing c k (CalibrationMesh.base N):ℝ) ≠ 0 from hQ.ne']
  obtain ⟨htl,htu⟩ := normalizedValue_mem rho a C hε hc k A B x hbase
  have hεR : (0:ℝ) ≤ ε := by exact_mod_cast hε
  have hεRsmall : (ε:ℝ) ≤ 1/1000 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hεsmall
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have htlR : (1:ℝ)-(ε:ℝ)/2 ≤ t := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htl
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,t] using hh
  have htuR : t ≤ (1:ℝ)+(ε:ℝ)/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htu
    simpa only [Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,t] using hh
  have ht0 : (999/1000:ℝ) ≤ t := by linarith
  have ht1 : t ≤ (1001/1000:ℝ) := by linarith
  have hmul0 := mul_le_mul_of_nonneg_left ht0 hQ.le
  have hmul1 := mul_le_mul_of_nonneg_left ht1 hQ.le
  rw [he] at hmul0 hmul1
  have hlog : Real.log (CalibrationMesh.base N:ℝ)=30*Real.log N := by
    simp only [CalibrationMesh.base,Nat.cast_pow,Real.log_pow]
    norm_num
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  change (1-(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) ≤ r ∧
    r ≤ (1+(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) at hlen
  rw [hlog] at hlen
  have hl := mul_le_mul_of_nonneg_right hεRsmall hx
  constructor <;> nlinarith [hlen.1,hlen.2]

end ContinuumCoulomb.PrefactorCalibration

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceCalibrationBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed calibration retains both the source edge residuals and the
uniform shared spacing, including for source graphs with no retained edges. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

theorem exists_source_calibration_oai (rho : ℕ) (hrho : 0 < rho)
    (eps : ℚ) (heps : 0 < eps) (hepsSmall : eps ≤ 1/1000)
    (s B : ℕ) (kmin : ℝ) :
    ∃ (C A : ℕ) (c : ℚ) (k : ℕ), 0 < C ∧ 0 < c ∧ 0 < k ∧ kmin ≤ (k:ℝ) ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
      ((59/2:ℝ)*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤
        AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)) ∧
        (AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)):ℝ) ≤
          31*(k:ℝ)*Real.log (SourceContactProgram.size d)) ∧
      ∀ (p : ℕ) (e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd)),
        let r := nominalDistance rho (CalibrationMesh.prefactor rho) C eps c s p k A B d hd e
        let N := CalibrationMesh.base (SourceContactProgram.size d)
        let D := (k:ℝ)*Real.log N
        (1-(eps:ℝ))*D ≤ r ∧ (r:ℝ) ≤ (1+(eps:ℝ))*D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0-
              localizedCoulombProfile (GaussianFrequency.frequency rho) r ∧
          |(CalibrationMesh.amplification rho (SourceContactProgram.size d) k:ℝ)*planarHopping r-
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
              (SourceContactProgram.weights s d hd e) r| ≤
            ((SourceContactProgram.size d:ℝ)^p+1)⁻¹ := by
  have heps1 : eps < 1 := lt_of_le_of_lt hepsSmall (by norm_num)
  obtain ⟨A,hA,hweights⟩ := source_weight_range s
  obtain ⟨C,L,c,k,hC,_hL,hc,hk,hkmin,hcal⟩ := PrefactorCalibration.exists_calibration
    rho hrho (CalibrationMesh.prefactor rho) (CalibrationMesh.prefactor_positive hrho)
    eps heps heps1 A B kmin
  refine ⟨C,A+L,c,k,hC,hc,hk,hkmin,fun d hd hp => ?_⟩
  have hN := SourceContactProgram.size_ge_two d
  have hbase := CalibrationMesh.base_ge_two hN
  have hpwr : (1:ℝ) ≤ (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ CalibrationMesh.base (SourceContactProgram.size d) by omega))
  have hone := hcal (CalibrationMesh.base (SourceContactProgram.size d)) 0 1 hbase
    (by simpa only [Rat.cast_one] using inv_le_one_of_one_le₀ hpwr)
    (by simpa only [Rat.cast_one] using hpwr)
  refine ⟨PrefactorCalibration.spacing_bounds rho (CalibrationMesh.prefactor rho) C
    heps.le hepsSmall hc k (A+L) B (SourceContactProgram.size d) 0 hN ⟨hone.1,hone.2.1⟩,?_⟩
  intro p e
  obtain ⟨hlo,hhi⟩ := hweights d hd hp e
  have hm := hcal (CalibrationMesh.base (SourceContactProgram.size d))
    (SourceContactProgram.size d^p) (SourceContactProgram.weights s d hd e) hbase hlo hhi
  simpa only [nominalDistance,CalibrationMesh.amplification,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Nat.cast_pow] using hm

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration_oai := @OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration_oai
