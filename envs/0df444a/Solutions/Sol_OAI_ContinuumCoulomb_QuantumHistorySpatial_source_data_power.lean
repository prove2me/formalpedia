-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumHistorySpatial.source_data_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:39:38.908107+00:00
-- url     : https://prove2.me/submissions/ab8fb0b0-40c9-4889-ade0-f32286beb1df

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
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
import Mathlib.Topology.Order.Compact
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

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

theorem sqrt_perturbation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  apply Real.abs_le_sqrt
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  by_cases hab : a ≤ b
  · have hs := Real.sqrt_le_sqrt hab
    have hm := mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hs)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt (le_of_not_ge hab)
    have hm := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
    nlinarith

end ContinuumCoulomb.RationalSquareRoot

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient-height bounds for the fixed history expressions.
These bounds provide a polynomial precision budget before real evaluation. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar
open scoped BigOperators

theorem realHeight_nonnegative (x : RealScalar) : 0 ≤ realHeight x :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem height_nonnegative (x : Scalar) : 0 ≤ height x :=
  add_nonneg (realHeight_nonnegative _) (realHeight_nonnegative _)

theorem realHeight_add (x y : RealScalar) :
    realHeight (realAdd x y) ≤ realHeight x+realHeight y := by
  have ha := abs_add_le x.1 y.1
  have hb := abs_add_le x.2 y.2
  dsimp only [realHeight,realAdd]
  linarith

theorem realHeight_sub (x y : RealScalar) :
    realHeight (realSub x y) ≤ realHeight x+realHeight y := by
  simpa only [realSub,realHeight_neg] using realHeight_add x (realNeg y)

theorem realHeight_mul (x y : RealScalar) :
    realHeight (realMul x y) ≤ realHeight x*realHeight y := by
  have ha := abs_add_le (x.1*y.1) (x.2*y.2/2)
  have hb := abs_add_le (x.1*y.2) (x.2*y.1)
  norm_num only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℚ) < 2)] at ha hb
  dsimp only [realHeight,realMul]
  nlinarith [mul_nonneg (abs_nonneg x.2) (abs_nonneg y.2)]

theorem height_add (x y : Scalar) : height (add x y) ≤ height x+height y := by
  have ha := realHeight_add x.1 y.1
  have hb := realHeight_add x.2 y.2
  dsimp only [height,add]
  linarith

theorem height_sub (x y : Scalar) : height (sub x y) ≤ height x+height y := by
  simpa only [sub,height_neg] using height_add x (neg y)

theorem height_mul (x y : Scalar) : height (mul x y) ≤ height x*height y := by
  have hr := realHeight_sub (realMul x.1 y.1) (realMul x.2 y.2)
  have hi := realHeight_add (realMul x.1 y.2) (realMul x.2 y.1)
  have hrr := realHeight_mul x.1 y.1
  have hii := realHeight_mul x.2 y.2
  have hri := realHeight_mul x.1 y.2
  have hir := realHeight_mul x.2 y.1
  dsimp only [height,mul]
  nlinarith

theorem height_realPart (x : Scalar) : height (realPart x) ≤ height x := by
  simp only [height,realPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_right (realHeight_nonnegative _)

theorem height_imagPart (x : Scalar) : height (imagPart x) ≤ height x := by
  simp only [height,imagPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_left (realHeight_nonnegative _)

theorem height_sum (xs : List Scalar) : height (sum xs) ≤ (xs.map height).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    change height (add x (sum xs)) ≤ height x+(xs.map height).sum
    exact (height_add x (sum xs)).trans (add_le_add (le_refl (height x)) ih)

theorem height_product (xs : List Scalar) : height (product xs) ≤ (xs.map height).prod := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih =>
    change height (mul x (product xs)) ≤ height x*(xs.map height).prod
    exact (height_mul x (product xs)).trans
      (mul_le_mul_of_nonneg_left ih (height_nonnegative x))

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourAxis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common interface for the fixed X and Z exchange encodings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisScale_pos (a : Fin 2) : 0 < qmaFourAxisScale a := by
  fin_cases a <;> simp only [qmaFourAxisScale,Fin.zero_eta,ite_true, if_true,Fin.isValue,Fin.mk_one,
    Fin.reduceEq,ite_false, if_false]
  · positivity
  · norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCouplingScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration of the physical inter-block strength for either coupling sign. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCouplingSize_nonneg (a b : Fin 2) (j : ℝ) : 0 ≤ qmaFourCouplingSize a b j :=
  Real.sqrt_nonneg _

theorem qmaFourCouplingSize_square (a b : Fin 2) (j : ℝ) :
    (3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*qmaFourAxisScale b = |j| := by
  have ha := qmaFourAxisScale_pos a
  have hb := qmaFourAxisScale_pos b
  have hane : qmaFourAxisScale a ≠ 0 := ne_of_gt ha
  have hbne : qmaFourAxisScale b ≠ 0 := ne_of_gt hb
  have hden : 0 < 3*qmaFourAxisScale a*qmaFourAxisScale b := by positivity
  have hnon : 0 ≤ 8*|j|/(3*qmaFourAxisScale a*qmaFourAxisScale b) := by positivity
  rw [qmaFourCouplingSize,Real.sq_sqrt hnon]
  field_simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent operator bounds for the actual exchange encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisWeights_abs_sum (a : Fin 2) (p : Bool) :
    (∑ i, |qmaFourAxisWeights a p i|) ≤ 28 := by
  fin_cases a <;> cases p <;>
    norm_num [qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights,Fin.sum_univ_succ]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCouplingBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the physically calibrated inter-block interaction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisScale_bounds (a : Fin 2) : 1 ≤ qmaFourAxisScale a ∧ qmaFourAxisScale a ≤ 256 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · norm_num [qmaFourAxisScale]
    constructor <;> nlinarith
  · norm_num [qmaFourAxisScale]

theorem qmaFourCouplingSize_bound (a b : Fin 2) (j : ℝ) :
    qmaFourCouplingSize a b j ≤ 3*(1+|j|) := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hp : 1 ≤ qmaFourAxisScale a*qmaFourAxisScale b := by nlinarith
  have hr := qmaFourCouplingSize_nonneg a b j
  have he := qmaFourCouplingSize_square a b j
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (qmaFourCouplingSize a b j))
  have hsq : (qmaFourCouplingSize a b j)^2 ≤ (8/3)*|j| := by nlinarith
  have hj := abs_nonneg j
  nlinarith [sq_nonneg |j|]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the internal counterterm coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCouplingFactor_nonneg (a b : Fin 2) (t : ℝ) : 0 ≤ qmaFourCouplingFactor a b t := by
  unfold qmaFourCouplingFactor
  positivity

theorem qmaFourCouplingFactor_bound (a b : Fin 2) (t : ℝ) : qmaFourCouplingFactor a b t ≤ |t| := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hf := qmaFourCouplingFactor_nonneg a b t
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a := by nlinarith
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b := by
      exact le_mul_of_one_le_right (mul_nonneg hf (le_trans (by norm_num) ha)) hb
    _ = _ := he

theorem qmaFourAxisShift_abs_bound (a : Fin 2) (p : Bool) : |qmaFourAxisShift a p| ≤ 400 := by
  fin_cases a <;> cases p <;> norm_num [qmaFourAxisShift]

theorem qmaFourAxisScale_abs_bound (a : Fin 2) : |qmaFourAxisScale a| ≤ 256 := by
  rw [abs_of_pos (qmaFourAxisScale_pos a)]
  exact (qmaFourAxisScale_bounds a).2

theorem qmaFourAxisSign_abs (p : Bool) : |qmaFourAxisSign p| = 1 := by
  cases p <;> norm_num [qmaFourAxisSign]

theorem qmaFourCounterA_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterA a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterA,abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 256)*400 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisScale_abs_bound a)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem qmaFourCounterB_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterB a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterB,abs_mul,abs_mul,abs_mul,qmaFourAxisSign_abs,one_mul,
    abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 400)*256 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisScale_abs_bound b)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOnsite
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal physical exchanges encode the one-site and scalar X/Z terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {τ : Type*} [Fintype τ]

theorem qmaFourAxisFieldShift_abs (a : Fin 2) (t : ℝ) : |qmaFourAxisFieldShift a t| ≤ |t| := by
  unfold qmaFourAxisFieldShift
  split_ifs
  · simpa only [abs_zero] using abs_nonneg t
  · rw [abs_div]
    norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial magnitude bounds for the physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFieldEdgeWeight_bound (a : Fin 2) (t : ℝ) (k : Fin 3) :
    |qmaFieldEdgeWeight a t k| ≤ |t| := by
  have hs : 1 ≤ Real.sqrt 3 := by
    have hs0 := Real.sqrt_nonneg 3
    have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hd : |t/(2*Real.sqrt 3)| ≤ |t| := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt 3)]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt 3)).mpr
    nlinarith [abs_nonneg t]
  have hz : |t/2| ≤ |t| := by rw [abs_div]; norm_num
  by_cases ha : a = 0
  · subst a
    fin_cases k
    · simpa [qmaFieldEdgeWeight] using hd
    · simpa [qmaFieldEdgeWeight,neg_div] using hd
    · simp [qmaFieldEdgeWeight]
  · fin_cases k
    · simp [qmaFieldEdgeWeight,ha]
    · simp [qmaFieldEdgeWeight,ha]
    · simpa [qmaFieldEdgeWeight,ha,neg_div] using hz

theorem qmaFourAxisWeights_pointwise (a : Fin 2) (s : Bool) (p : Fin 4) :
    |qmaFourAxisWeights a s p| ≤ 28 :=
  (Finset.single_le_sum (fun q _ => abs_nonneg (qmaFourAxisWeights a s q))
    (Finset.mem_univ p)).trans (qmaFourAxisWeights_abs_sum a s)

theorem qmaFourEnergyOffset_bound (a b : Fin 2) (t : ℝ) :
    |qmaFourEnergyOffset a b t| ≤ 364800*|t| := by
  have ha := qmaFourAxisFieldShift_abs a (qmaFourCounterA a b t)
  have hb := qmaFourAxisFieldShift_abs b (qmaFourCounterB a b t)
  have hca := qmaFourCounterA_bound a b t
  have hcb := qmaFourCounterB_bound a b t
  have hm : |qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign t)| ≤ 160000*|t| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
    calc
      _ ≤ (|t| * 400)*400 := mul_le_mul
        (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum := abs_add_le (qmaFourAxisFieldShift a (qmaFourCounterA a b t))
    (qmaFourAxisFieldShift b (qmaFourCounterB a b t))
  have hsub := abs_sub
    (qmaFourAxisFieldShift a (qmaFourCounterA a b t)+qmaFourAxisFieldShift b (qmaFourCounterB a b t))
    (qmaFourCouplingFactor a b t*qmaFourAxisShift a true*qmaFourAxisShift b (qmaFourCouplingSign t))
  unfold qmaFourEnergyOffset
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational sampling of the fixed algebraic constants in the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

theorem inverseScale_mul (a : Fin 2) : inverseScale a*qmaFourAxisScale a = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale,qmaFourAxisScale]
    nlinarith
  · norm_num [inverseScale,qmaFourAxisScale]

theorem inverseScale_bounds (a : Fin 2) : 0 ≤ inverseScale a ∧ inverseScale a ≤ 1 := by
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale]
    constructor <;> nlinarith
  · norm_num [inverseScale]

theorem root_nonneg (k : ℕ) (q : ℚ) : 0 ≤ RationalSquareRoot.value (k,q) := by
  unfold RationalSquareRoot.value DyadicRootProgram.value
  positivity

theorem value_nonneg (k : ℕ) (a : Fin 2) : 0 ≤ value k a := by
  unfold value
  split_ifs
  · exact div_nonneg (root_nonneg k 3) (by norm_num)
  · norm_num

theorem value_error (k : ℕ) (a : Fin 2) :
    |(value k a:ℝ)-inverseScale a| ≤ (2:ℝ)⁻¹^k := by
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  norm_num only [Rat.cast_ofNat] at h
  by_cases ha : a = 0
  · simp only [value,inverseScale,ha,ite_true, if_true,Rat.cast_div,Rat.cast_ofNat]
    obtain ⟨hl,hu⟩ := abs_le.mp h
    apply abs_le.mpr
    constructor <;> linarith
  · simp [value,inverseScale,ha]

theorem value_bounds (k : ℕ) (a : Fin 2) : 0 ≤ (value k a:ℝ) ∧ (value k a:ℝ) ≤ 1 := by
  have hn : (0:ℝ) ≤ value k a := by exact_mod_cast value_nonneg k a
  refine ⟨hn,?_⟩
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases ha : a = 0
  · simp only [value,ha,ite_true, if_true,Rat.cast_div,Rat.cast_ofNat]
    have hh := (abs_le.mp h).2
    norm_num only [Rat.cast_ofNat] at hh
    nlinarith
  · norm_num [value,ha]

theorem product_error (k : ℕ) (a b : Fin 2) :
    |(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| ≤ 2*(2:ℝ)⁻¹^k := by
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have ha := value_error k a
  have hb := value_error k b
  have hav : |inverseScale a| ≤ 1 := by rw [abs_of_nonneg (inverseScale_bounds a).1]; exact (inverseScale_bounds a).2
  have hbv : |(value k b:ℝ)| ≤ 1 := by rw [abs_of_nonneg (value_bounds k b).1]; exact (value_bounds k b).2
  calc
    _ = |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)+inverseScale a*((value k b:ℝ)-inverseScale b)| := by
      congr 1
      ring
    _ ≤ |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)|+|inverseScale a*((value k b:ℝ)-inverseScale b)| := abs_add_le _ _
    _ = |(value k a:ℝ)-inverseScale a| * |(value k b:ℝ)|+
        |inverseScale a| * |(value k b:ℝ)-inverseScale b| := by rw [abs_mul,abs_mul]
    _ ≤ (2:ℝ)⁻¹^k*1+1*(2:ℝ)⁻¹^k := add_le_add
      (mul_le_mul ha hbv (abs_nonneg _) hd) (mul_le_mul hav hb (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem radicand_nonneg (k : ℕ) (a b : Fin 2) (t : ℚ) : 0 ≤ radicand k a b t := by
  unfold radicand
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg t)) (value_nonneg k a))
    (value_nonneg k b)

theorem coupling_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingSize a b t = Real.sqrt ((8/3)*|t| *inverseScale a*inverseScale b) := by
  unfold qmaFourCouplingSize
  congr 1
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have han := (qmaFourAxisScale_pos a).ne'
  have hbn := (qmaFourAxisScale_pos b).ne'
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) han) hbn)).mpr
  calc
    _ = 8*|t| *(inverseScale a*qmaFourAxisScale a)*(inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = _ := by ring

theorem radicand_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(radicand k a b t:ℝ)-(8/3)*|(t:ℝ)| *inverseScale a*inverseScale b| ≤
      (16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  simp only [radicand,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_abs]
  calc
    _ = |((8/3)*|(t:ℝ)|)*((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)| := by
      congr 1
      ring
    _ = ((8/3)*|(t:ℝ)|)*|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (8/3:ℝ)*|(t:ℝ)|)]
    _ ≤ ((8/3)*|(t:ℝ)|)*(2*(2:ℝ)⁻¹^k) :=
      mul_le_mul_of_nonneg_left (product_error k a b) (by positivity)
    _ = _ := by ring

theorem coupling_error (k l : ℕ) (a b : Fin 2) (t : ℚ) :
    |(coupling k l a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      (2:ℝ)⁻¹^l+Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k) := by
  have hr := RationalSquareRoot.value_error l (radicand_nonneg k a b t)
  have hs := RationalSquareRoot.sqrt_perturbation
    (show (0:ℝ) ≤ radicand k a b t by exact_mod_cast radicand_nonneg k a b t)
    (show 0 ≤ (8/3)*|(t:ℝ)| *inverseScale a*inverseScale b from
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (inverseScale_bounds a).1)
        (inverseScale_bounds b).1)
  rw [coupling_eq]
  exact (abs_sub_le _ _ _).trans (add_le_add hr (hs.trans (Real.sqrt_le_sqrt (radicand_error k a b t))))

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSampleAccuracy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear precision schedule for the literal four-spin coupling sampler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample

theorem calibrated_error (a b : Fin 2) (k : ℕ) (t : ℚ) :
    |(calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      2*(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
  have h := coupling_error (2*k+6) k a b t
  have he : (2:ℝ)⁻¹^(2*k+6) = ((2:ℝ)⁻¹^k)^2/64 := by
    rw [show 2*k+6=k*2+6 by omega,pow_add,pow_mul]
    norm_num
    ring
  have heps : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have hs : Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^(2*k+6)) ≤
      (1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he,mul_pow]
    have hb : |(t:ℝ)|/12 ≤ (1+|(t:ℝ)|)^2 := by nlinarith [abs_nonneg (t:ℝ),sq_nonneg |(t:ℝ)|]
    calc
      _ = (|(t:ℝ)|/12)*((2:ℝ)⁻¹^k)^2 := by ring
      _ ≤ (1+|(t:ℝ)|)^2*((2:ℝ)⁻¹^k)^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  change |(coupling (2*k+6) k a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤ _
  apply h.trans
  have hp := mul_nonneg (abs_nonneg (t:ℝ)) heps
  linarith

theorem calibrated_nonneg (a b : Fin 2) (k : ℕ) (t : ℚ) : 0 ≤ calibrated a b (k,t) :=
  root_nonneg _ _

theorem calibrated_bound (a b : Fin 2) (k : ℕ) (t : ℚ) :
    |(calibrated a b (k,t):ℝ)| ≤ 5*(1+|(t:ℝ)|) := by
  have h := (abs_le.mp (calibrated_error a b k t)).2
  have hc := qmaFourCouplingSize_bound a b (t:ℝ)
  have he : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he' := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2*(1+|(t:ℝ)|))
  have hp : (0:ℝ) ≤ calibrated a b (k,t) := by exact_mod_cast calibrated_nonneg a b k t
  rw [abs_of_nonneg hp]
  linarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCountertermSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterms use only rational arithmetic and the fixed inverse-scale sample. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

theorem factor_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingFactor a b t = |t| *inverseScale a*inverseScale b := by
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ = qmaFourCouplingFactor a b t*(inverseScale a*qmaFourAxisScale a)*
        (inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = (qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b)*inverseScale a*inverseScale b := by ring
    _ = _ := by rw [he]

theorem counterA_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterA a b t = |t| *inverseScale b*qmaFourAxisShift b (qmaFourCouplingSign t) := by
  rw [qmaFourCounterA,factor_eq]
  calc
    _ = |t| *inverseScale b*(inverseScale a*qmaFourAxisScale a)*qmaFourAxisShift b (qmaFourCouplingSign t) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

theorem counterB_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterB a b t = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true := by
  rw [qmaFourCounterB,factor_eq]
  calc
    _ = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true*
        (inverseScale b*qmaFourAxisScale b) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

theorem shift_cast (a : Fin 2) (p : Bool) : (shift a p:ℝ) = qmaFourAxisShift a p := by
  unfold shift qmaFourAxisShift
  split_ifs <;> norm_num

theorem polarity_cast (t : ℚ) : (polarity t:ℝ) = qmaFourAxisSign (qmaFourCouplingSign (t:ℝ)) := by
  by_cases ht : t ≤ 0
  · have htR : (t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]
  · have htR : ¬(t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]

theorem sign_cast (t : ℚ) : decide (t ≤ 0) = qmaFourCouplingSign (t:ℝ) := by
  unfold qmaFourCouplingSign
  congr 1
  exact propext (by exact_mod_cast (Iff.rfl : t ≤ 0 ↔ t ≤ 0))

theorem factor_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ)| ≤ 2*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [factor_eq]
  simp only [factor,Rat.cast_mul,Rat.cast_abs]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by rw [abs_mul,abs_abs]
    _ ≤ |(t:ℝ)| *(2*(2:ℝ)⁻¹^k) := mul_le_mul_of_nonneg_left (product_error k a b) (abs_nonneg _)
    _ = _ := by ring

theorem counterA_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)-qmaFourCounterA a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterA_eq]
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k b:ℝ)-inverseScale b)*qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k b:ℝ)-inverseScale b| *|qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| := by
      rw [abs_mul,abs_mul,abs_abs]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k b) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)-qmaFourCounterB a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterB_eq]
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)-inverseScale a)*qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))*
        qmaFourAxisShift a true) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))| *
        |qmaFourAxisShift a true| := by
      rw [abs_mul,abs_mul,abs_mul,abs_abs]
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisShift a true| := by
      rw [qmaFourAxisSign_abs,mul_one]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k a) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFieldSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational evaluation of each internal physical field coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open Matrix

theorem inverseScale_field : 64*inverseScale 0 = 1/(2*Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num only [inverseScale,ite_true]
  field_simp
  nlinarith

theorem fieldX_error (k : ℕ) (t : ℚ) :
    |(fieldX k t:ℝ)-(t:ℝ)/(2*Real.sqrt 3)| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have he : (t:ℝ)/(2*Real.sqrt 3) = 64*(t:ℝ)*inverseScale 0 := by
    rw [mul_comm 64 (t:ℝ),mul_assoc,inverseScale_field]
    ring
  rw [he]
  simp only [fieldX,Rat.cast_mul,Rat.cast_ofNat]
  calc
    _ = 64*|(t:ℝ)| *|(value k 0:ℝ)-inverseScale 0| := by
      rw [show 64*(t:ℝ)*(value k 0:ℝ)-64*(t:ℝ)*inverseScale 0 =
        (64*(t:ℝ))*((value k 0:ℝ)-inverseScale 0) by ring,abs_mul,abs_mul]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (value_error k 0) (by positivity)

theorem fieldValue_error (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a t e:ℝ)-qmaFieldEdgeWeight a (t:ℝ) e| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  by_cases ha : a = 0
  · fin_cases e
    · simpa [fieldValue,qmaFieldEdgeWeight,ha] using fieldX_error k t
    · simpa [fieldValue,qmaFieldEdgeWeight,ha,neg_div,neg_add_eq_sub,abs_sub_comm] using fieldX_error k t
    · simp [fieldValue,qmaFieldEdgeWeight,ha]
  · fin_cases e <;> simp [fieldValue,qmaFieldEdgeWeight,ha,Rat.cast_div]

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOffsetSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error bounds for the sampled counterterm fields and their scalar shifts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem counterA_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k b).1]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k b).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k a).1,qmaFourAxisSign_abs,mul_one]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k a).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem shiftValue_error (a : Fin 2) (q : ℚ) (x : ℝ) :
    |(shiftValue a q:ℝ)-qmaFourAxisFieldShift a x| ≤ |(q:ℝ)-x| := by
  by_cases ha : a = 0
  · simp [shiftValue,qmaFourAxisFieldShift,ha]
  · simp only [shiftValue,qmaFourAxisFieldShift,ha,ite_false, if_false,Rat.cast_div,Rat.cast_ofNat]
    rw [← sub_div,abs_div]
    norm_num

theorem offset_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ)| ≤
      320800*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have ha := (shiftValue_error a (counterA k a b t) (qmaFourCounterA a b (t:ℝ))).trans
    (counterA_error k a b t)
  have hb := (shiftValue_error b (counterB k a b t) (qmaFourCounterB a b (t:ℝ))).trans
    (counterB_error k a b t)
  have hc : |((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| ≤ 320000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((2*|(t:ℝ)| *(2:ℝ)⁻¹^k)*400)*400 := mul_le_mul
        (mul_le_mul (factor_error k a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (by positivity)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : (offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ) =
      ((shiftValue a (counterA k a b t):ℝ)-qmaFourAxisFieldShift a (qmaFourCounterA a b (t:ℝ)))+
      ((shiftValue b (counterB k a b t):ℝ)-qmaFourAxisFieldShift b (qmaFourCounterB a b (t:ℝ)))-
      ((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ)) := by
    simp only [offset,qmaFourEnergyOffset,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,shift_cast,sign_cast]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  calc
    _ ≤ (400*|(t:ℝ)| *(2:ℝ)⁻¹^k+400*|(t:ℝ)| *(2:ℝ)⁻¹^k)+320000*|(t:ℝ)| *(2:ℝ)⁻¹^k :=
      add_le_add (add_le_add ha hb) hc
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational values for every edge of the actual physical exchange family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped Classical BigOperators

theorem stencil_cast (a : Fin 2) (s : Bool) (p : Fin 4) :
    (stencil a s p:ℝ) = qmaFourAxisWeights a s p := by
  fin_cases a <;> cases s <;> fin_cases p <;>
    norm_num [stencil,qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights]

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellCrossings
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact finite set of crossing cells, selected from the route visits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingCells_card : P.crossingCells.card ≤ ∑ e, (P.length e-1) := by
  calc
    _ ≤ (Finset.univ.image P.cell).card := Finset.card_filter_le _ _
    _ ≤ Fintype.card P.Interior := (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := by simp [Interior,Fintype.card_sigma]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathWeightBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial coefficient bounds for one physical path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaPathOffset_abs_le {J L : ℝ} (hL : 1 ≤ L) (hJ : |J| ≤ L) :
    |qmaPathOffset J| ≤ 4*L^2 := by
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaPathOffset; positivity)]
  unfold qmaPathOffset
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortCrossingSelection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select and remove the actual finite crossing cells in a completed rational
port graph. The gadget terminals are existing physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingCells_card_le {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    P.crossingCells.card ≤ Fintype.card G.Edge*D := by
  calc
    _ ≤ ∑ e, (P.length e-1) := P.crossingCells_card
    _ ≤ ∑ _e : G.Edge, D := Finset.sum_le_sum (fun e _ => (Nat.sub_le _ _).trans (hD e))
    _ = _ := by simp

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program computes the final coefficient envelope;
the exponent in the source promise is uniform over all inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

theorem latticeBound_power (D : ℕ) : ∃ a : ℕ, ∀ x : LatticeInput,
    latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2 ≤ ((latticeInputCode x).length+2)^a :=
  unaryProcedure_power_bound (latticeBoundProgram D)

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (i : Fin (sites c hT a).length) :
    (supportEquiv c hT a i).val = (sites c hT a).get i := rfl

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelPipeline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed six-stage literal sparse-word compiler. The final stage assigns
a private mediator to every two-local term before the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelPipeline
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData QuantumOrderedLabelFamily

theorem output_length (x : Input) : (output x).2.length=12544*x.2.2.length := by
  simp only [output,privateStep,thirdStep,yyStep,subdivisionStep,value,family_length]
  omega

end ContinuumCoulomb.QuantumOrderedLabelPipeline

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw four-spin compiler with its full-space spectral guarantee. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open Matrix
open scoped BigOperators Classical

theorem pack_weight {n : ℕ} (t : QMAXZTerm n) (J : ℚ) : (pack t J).2.2.2 = J := by
  cases t <;> rfl

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedWeightBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial envelopes for the literal four- and seven-word gadgets.
Only the term count, input coefficient bound and unary precision enter these
envelopes.  No bound on the Hilbert-space dimension is used. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped BigOperators Classical

theorem weightEnvelope_nonneg {R B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B) :
    0 ≤ weightEnvelope R B := by unfold weightEnvelope; positivity

theorem weightEnvelope_mono {R S B C : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hRS : R ≤ S) (hBC : B ≤ C) : weightEnvelope R B ≤ weightEnvelope S C := by
  have hS : 0 ≤ S := hR.trans hRS
  unfold weightEnvelope
  gcongr

private theorem input_square_bound {j B : ℚ} (_hB : 0 ≤ B) (hj : |j| ≤ B) :
    j^2 ≤ B^2 := by
  have h := abs_le.mp hj
  nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (by linarith : 0 ≤ B+j)]

private theorem middle_bound (B : ℚ) : B ≤ 1+B^2 := by
  nlinarith [sq_nonneg (B-1)]

theorem four_weight_bound {R j B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hj : |j| ≤ B) (k : Fin 4) :
    |QuantumPolarizedSubdivision.weight R j k| ≤ weightEnvelope R B := by
  have hj2 := input_square_bound hB hj
  have hR3 : 0 ≤ R^3 := pow_nonneg hR _
  have hR2B : 0 ≤ R^2*B := mul_nonneg (sq_nonneg R) hB
  have hRB2 : 0 ≤ R*B^2 := mul_nonneg hR (sq_nonneg B)
  have hRB : R*|j| ≤ R*(1+B^2) :=
    mul_le_mul_of_nonneg_left (hj.trans (middle_bound B)) hR
  fin_cases k
  · change |R^2/2+1+(j/2)^2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^2/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R| ≤ _
    rw [abs_of_nonneg hR]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R*j/2| ≤ _
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg hR]
    norm_num only [abs_of_pos (by norm_num : (0:ℚ) < 2)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]

theorem seven_weight_bound {R j B : ℚ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hj : |j| ≤ B) (k : Fin 7) :
    |QuantumPolarizedThird.weight R j k| ≤ weightEnvelope R B := by
  have hj2 := input_square_bound hB hj
  have hR3 : 0 ≤ R^3 := pow_nonneg hR _
  have hR2B : 0 ≤ R^2*B := mul_nonneg (sq_nonneg R) hB
  have hRB2 : 0 ≤ R*B^2 := mul_nonneg hR (sq_nonneg B)
  have hRj2 : R*j^2 ≤ R*B^2 := mul_le_mul_of_nonneg_left hj2 hR
  have hRB : R*|j| ≤ R*(1+B^2) :=
    mul_le_mul_of_nonneg_left (hj.trans (middle_bound B)) hR
  have hR2j : R^2*|j| ≤ R^2*B := mul_le_mul_of_nonneg_left hj (sq_nonneg R)
  fin_cases k
  · change |R^3/2+R*(1+(j/2)^2)| ≤ _
    rw [abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^3/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R*j| ≤ _
    rw [abs_mul,abs_of_nonneg hR]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2/2-(1+(j/2)^2)| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |-R^2/2| ≤ _
    rw [neg_div]
    rw [abs_neg,abs_of_nonneg (by positivity)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg R)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]
  · change |R^2*j/2| ≤ _
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg R)]
    norm_num only [abs_of_pos (by norm_num : (0:ℚ) < 2)]
    unfold weightEnvelope
    nlinarith [sq_nonneg R,sq_nonneg B]

theorem scaleEnvelope_nonneg (m : ℕ) {B : ℚ} (_hB : 0 ≤ B) (N : ℕ) :
    0 ≤ scaleEnvelope m B N := by unfold scaleEnvelope; positivity

theorem stepEnvelope_nonneg (m : ℕ) {B : ℚ} (hB : 0 ≤ B) (N : ℕ) :
    0 ≤ stepEnvelope m B N := weightEnvelope_nonneg (scaleEnvelope_nonneg m hB N) hB

variable {κ : Type} [Fintype κ]

theorem scale_le_envelope (J : κ → ℚ) {m : ℕ} {B : ℚ} (_hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) :
    QuantumOrderedSubdivision.scale J N ≤ scaleEnvelope m B N := by
  have hs : (∑ e, (1+|J e|)^2) ≤ (m:ℚ)*(1+B)^2 := calc
    _ ≤ ∑ _e : κ, (1+B)^2 := by
      apply Finset.sum_le_sum
      intro e _
      gcongr
      exact hJ e
    _ = (Fintype.card κ:ℚ)*(1+B)^2 := by simp
    _ ≤ (m:ℚ)*(1+B)^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (sq_nonneg _)
  unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget scaleEnvelope
  gcongr

theorem subdivision_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : κ × Fin 4) :
    |QuantumOrderedSubdivision.outputCoefficient J N p| ≤ stepEnvelope m B N := by
  have hR : 0 ≤ QuantumOrderedSubdivision.scale J N := by
    unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget
    positivity
  exact (four_weight_bound hR hB (hJ p.1) p.2).trans
    (weightEnvelope_mono hR hB (scale_le_envelope J hB hm hJ N) le_rfl)

theorem third_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : κ × Fin 7) :
    |QuantumOrderedThird.outputCoefficient J N p| ≤ stepEnvelope m B N := by
  have hR : 0 ≤ QuantumOrderedSubdivision.scale J N := by
    unfold QuantumOrderedSubdivision.scale QuantumOrderedSubdivision.budget
    positivity
  exact (seven_weight_bound hR hB (hJ p.1) p.2).trans
    (weightEnvelope_mono hR hB (scale_le_envelope J hB hm hJ N) le_rfl)

theorem pipelineBound_nonneg (m : ℕ) {B : ℚ} (hB : 0 ≤ B) (N k : ℕ) :
    0 ≤ pipelineBound m B N k := by
  induction k with
  | zero => exact hB
  | succ k ih => exact stepEnvelope_nonneg _ ih _

theorem pipeline_coefficient_bound (J : κ → ℚ) {m : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ B) (N : ℕ) (p : OutputTerm κ) :
    |coefficient J N p| ≤ pipelineBound m B N 5 := by
  have hm0 : Fintype.card κ ≤ 3136*m := by omega
  have hm1 : Fintype.card (κ × Fin 4) ≤ 3136*m := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hm2 : Fintype.card (ThreeTerm κ) ≤ 3136*m := by
    simp only [ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have hm3 : Fintype.card (TwoTerm κ) ≤ 3136*m := by
    simp only [TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have hm4 : Fintype.card (XZThreeTerm κ) ≤ 3136*m := by
    simp only [XZThreeTerm,TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
    omega
  have h1 (e : κ × Fin 4) :
      |QuantumOrderedTwoStage.firstCoefficient J N e| ≤ pipelineBound m B N 1 :=
    subdivision_coefficient_bound J hB hm0 hJ N e
  have h2 (e : ThreeTerm κ) : |threeCoefficient J N e| ≤ pipelineBound m B N 2 :=
    subdivision_coefficient_bound (QuantumOrderedTwoStage.firstCoefficient J N)
      (pipelineBound_nonneg m hB N 1) hm1 h1 N e
  have h3 (e : TwoTerm κ) : |twoCoefficient J N e| ≤ pipelineBound m B N 3 :=
    third_coefficient_bound (threeCoefficient J N)
      (pipelineBound_nonneg m hB N 2) hm2 h2 N e
  have h4 (e : XZThreeTerm κ) : |xzThreeCoefficient J N e| ≤ pipelineBound m B N 4 :=
    subdivision_coefficient_bound (twoCoefficient J N)
      (pipelineBound_nonneg m hB N 3) hm3 h3 N e
  exact third_coefficient_bound (xzThreeCoefficient J N)
    (pipelineBound_nonneg m hB N 4) hm4 h4 N p

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedFinalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integer polynomial bound for the complete six-stage ordered compiler,
including the private-pair subdivision before the physical four-spin step. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

theorem weightNat_cast (R B : ℕ) : (weightNat R B:ℚ)=weightEnvelope R B := by
  simp only [weightNat,weightEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_one]

theorem scaleNat_cast (m B N : ℕ) : (scaleNat m B N:ℚ)=scaleEnvelope m B N := by
  simp only [scaleNat,scaleEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_one,Nat.cast_ofNat]

theorem stepNat_cast (m B N : ℕ) : (stepNat m B N:ℚ)=stepEnvelope m B N := by
  simp only [stepNat,stepEnvelope,weightNat_cast,scaleNat_cast]

theorem pipelineNat_cast (m B N k : ℕ) : (pipelineNat m B N k:ℚ)=pipelineBound m B N k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pipelineNat,stepNat_cast,ih,pipelineBound]

theorem outputTerm_card {κ : Type} [Fintype κ] :
    Fintype.card (OutputTerm κ)=3136*Fintype.card κ := by
  simp only [OutputTerm,XZThreeTerm,TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
  ring

theorem private_coefficient_bound {κ : Type} [Fintype κ] (J : κ → ℚ)
    {m B : ℕ} (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ (B:ℚ))
    (N : ℕ) (p : OutputTerm κ × Fin 4) :
    |QuantumOrderedPrivate.outputCoefficient (coefficient J N) N p| ≤
      (pipelineNat m B N 6:ℚ) := by
  have hB : (0:ℚ) ≤ B := Nat.cast_nonneg B
  have hc := pipeline_coefficient_bound J hB hm hJ N
  have hcount : Fintype.card (OutputTerm κ) ≤ 3136*m := by
    rw [outputTerm_card]
    exact Nat.mul_le_mul_left 3136 hm
  have h := subdivision_coefficient_bound (coefficient J N)
    (pipelineBound_nonneg m hB N 5) hcount hc N p
  change |QuantumOrderedSubdivision.outputCoefficient (coefficient J N) N p| ≤
    (stepNat (3136*m) (pipelineNat m B N 5) N:ℚ)
  rw [stepNat_cast,pipelineNat_cast]
  exact h

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the actual rational four-spin coefficients. The
sampling precision does not enter these bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample

theorem fieldValue_abs (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a t e:ℝ)| ≤ 65*|(t:ℝ)| := by
  have h := (abs_sub_abs_le_abs_sub (fieldValue k a t e:ℝ)
    (qmaFieldEdgeWeight a (t:ℝ) e)).trans (fieldValue_error k a t e)
  have hw := qmaFieldEdgeWeight_bound a (t:ℝ) e
  have hp : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 64*|(t:ℝ)|)
  linarith

theorem crossValue_abs (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) :
    |(crossValue k r a b t p q:ℝ)| ≤ 3920*|(r:ℝ)| *(1+|(t:ℝ)|) := by
  have hs : |(stencil a true p:ℝ)| * |(stencil b (decide (t≤0)) q:ℝ)| ≤ 784 := by
    rw [stencil_cast,stencil_cast]
    exact (mul_le_mul (qmaFourAxisWeights_pointwise a true p)
      (qmaFourAxisWeights_pointwise b _ q) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simp only [crossValue,Rat.cast_mul,abs_mul]
  calc
    _ ≤ (|(r:ℝ)| *(5*(1+|(t:ℝ)|)))*784 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (calibrated_bound a b k t) (abs_nonneg _)) hs
        (by positivity) (by positivity)
    _ = _ := by ring

theorem shiftValue_abs (a : Fin 2) (t : ℚ) : |(shiftValue a t:ℝ)| ≤ |(t:ℝ)| := by
  by_cases h : a=0
  · simp [shiftValue,h]
  · simp only [shiftValue,h,ite_false, if_false,Rat.cast_div,Rat.cast_ofNat,abs_div]
    norm_num

theorem offset_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(offset k a b t:ℝ)| ≤ 685600*|(t:ℝ)| := by
  have h := (abs_sub_abs_le_abs_sub (offset k a b t:ℝ)
    (qmaFourEnergyOffset a b (t:ℝ))).trans (offset_error k a b t)
  have hw := qmaFourEnergyOffset_bound a b (t:ℝ)
  have hp : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 320800*|(t:ℝ)|)
  linarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawOutputBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial magnitude envelopes for every actual physical edge and scalar
offset in the rational four-spin output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram

theorem field_bond_abs (k : ℕ) (i : ℕ) (a : Fin 2) (J : ℚ)
    (b : Bond) (hb : b ∈ field k i a J) : |(b.2.2:ℝ)| ≤ 65*|(J:ℝ)| := by
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  exact fieldValue_abs k a J e

theorem cross_bond_abs (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ)
    (e : Bond) (he : e ∈ cross k r i j a b J) :
    |(e.2.2:ℝ)| ≤ 3920*|(r:ℝ)| *(1+|(J:ℝ)|) := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp he
  exact crossValue_abs k r a b J _ _

theorem bonds_abs (x : Input) (e : Bond) (he : e ∈ bonds x) :
    |(e.2.2:ℝ)| ≤ 3920*|(x.1.2:ℝ)| *(1+|(x.2.2.2.2:ℝ)|)+26000*|(x.2.2.2.2:ℝ)| := by
  dsimp only [bonds] at he
  split_ifs at he with hp hf
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact (cross_bond_abs _ _ _ _ _ _ _ e he).trans
          (le_add_of_nonneg_right (by positivity))
      · have h := (field_bond_abs _ _ _ _ e he).trans
          (mul_le_mul_of_nonneg_left (counterA_abs _ _ _ _) (by norm_num : (0:ℝ) ≤ 65))
        nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
    · have h := (field_bond_abs _ _ _ _ e he).trans
        (mul_le_mul_of_nonneg_left (counterB_abs _ _ _ _) (by norm_num : (0:ℝ) ≤ 65))
      nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
  · have h := field_bond_abs _ _ _ _ e he
    nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
  · simp only [List.not_mem_nil] at he

theorem scalar_abs (x : Input) : |(scalar x:ℝ)| ≤ 685600*|(x.2.2.2.2:ℝ)| := by
  dsimp only [scalar]
  split_ifs
  · simpa only [Rat.cast_neg,abs_neg] using offset_abs x.1.1 _ _ x.2.2.2.2
  · simp only [Rat.cast_neg,abs_neg]
    exact (shiftValue_abs _ _).trans (by nlinarith [abs_nonneg (x.2.2.2.2:ℝ)])
  · nlinarith [abs_nonneg (x.2.2.2.2:ℝ)]

theorem termBondsList_abs (k : ℕ) (r : ℚ) (xs : List Raw) {B : ℝ}
    (_hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : Bond) (he : e ∈ termBondsList ((k,r),xs)) :
    |(e.2.2:ℝ)| ≤ 3920*|(r:ℝ)| *(1+B)+26000*B := by
  obtain ⟨ys,hys,he⟩ := List.mem_flatten.mp he
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hys
  exact (bonds_abs ((k,r),t) e he).trans (by gcongr <;> exact hw t ht)

theorem termScalarList_abs (k : ℕ) (r : ℚ) (xs : List Raw) {B : ℝ}
    (_hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(termScalarList ((k,r),xs):ℝ)| ≤ 685600*xs.length*B := by
  induction xs with
  | nil => simp [termScalarList]
  | cons t xs ih =>
    have ht := hw t (by simp)
    have hs := ih (by intro u hu; exact hw u (by simp [hu]))
    simp only [termScalarList,List.map_cons,List.sum_cons,Rat.cast_add]
    change |(scalar ((k,r),t):ℝ)+(termScalarList ((k,r),xs):ℝ)| ≤ _
    apply (abs_add_le _ _).trans
    have h := (scalar_abs ((k,r),t)).trans
      (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 685600))
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one] using
      (show |(scalar ((k,r),t):ℝ)|+|(termScalarList ((k,r),xs):ℝ)| ≤
        685600*((xs.length:ℝ)+1)*B by nlinarith)

theorem fullBonds_abs (n k : ℕ) (r : ℚ) (xs : List Raw) {R B : ℝ}
    (hR : |(r:ℝ)| ≤ R) (hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : Bond) (he : e ∈ fullBonds (n,(k,r),xs)) :
    |(e.2.2:ℝ)| ≤ outputBound n xs.length R B := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  rcases List.mem_append.mp he with hp | ht
  · obtain ⟨ys,hys,he⟩ := List.mem_flatten.mp hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hys
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    change |((r^2:ℚ):ℝ)| ≤ _
    rw [Rat.cast_pow,abs_of_nonneg (sq_nonneg (r:ℝ))]
    have hr2 : (r:ℝ)^2 ≤ R^2 := by nlinarith [abs_le.mp hR]
    unfold outputBound
    nlinarith [sq_nonneg R,(Nat.cast_nonneg n : (0:ℝ) ≤ n),
      (Nat.cast_nonneg xs.length : (0:ℝ) ≤ xs.length)]
  · have h := (termBondsList_abs k r xs hB hw e ht).trans
      (show 3920*|(r:ℝ)| *(1+B)+26000*B ≤ 3920*R*(1+B)+26000*B by gcongr)
    unfold outputBound
    nlinarith [sq_nonneg R,(Nat.cast_nonneg n : (0:ℝ) ≤ n),
      (Nat.cast_nonneg xs.length : (0:ℝ) ≤ xs.length)]

theorem fullScalar_abs (n k : ℕ) (r : ℚ) (xs : List Raw) {R B : ℝ}
    (hR : |(r:ℝ)| ≤ R) (hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(fullScalar (n,(k,r),xs):ℝ)| ≤ outputBound n xs.length R B := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hr2 : (r:ℝ)^2 ≤ R^2 := by nlinarith [abs_le.mp hR]
  have hs := termScalarList_abs k r xs hB hw
  simp only [fullScalar,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ (r:ℝ)^2*((n:ℝ)*6))]
  unfold outputBound
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (n:ℝ)*6 by positivity)
  nlinarith [sq_nonneg R]

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawEnvelope
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A natural polynomial envelope for the actual rational raw compiler.
Only the raw term count, coefficient magnitude and unary precision enter it. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange

theorem mass_nonneg (xs : List Raw) : 0 ≤ mass xs := by
  exact List.sum_nonneg (by intro q hq; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq; exact abs_nonneg _)

theorem mass_bound (xs : List Raw) {B : ℝ} (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    (mass xs:ℝ) ≤ xs.length*B := by
  induction xs with
  | nil => simp [mass]
  | cons t xs ih =>
    have ht := hw t (by simp)
    have hs := ih (by intro u hu; exact hw u (by simp [hu]))
    simp only [mass,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_abs,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    change |(t.2.2.2:ℝ)|+(mass xs:ℝ) ≤ _
    nlinarith

theorem scale_nat_bound (N : ℕ) (xs : List Raw) (B : ℕ)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(scale N xs:ℝ)| ≤ scaleNat xs.length B N := by
  have hm := mass_bound xs hw
  have hm0 : (0:ℝ) ≤ mass xs := by exact_mod_cast mass_nonneg xs
  have hb0 : (0:ℝ) ≤ budget xs := by
    simp only [budget,size,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]
    positivity
  have hb : (budget xs:ℝ) ≤ budgetNat xs.length B := by
    simp only [budget,size,budgetNat,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_ofNat,Rat.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    gcongr
  simp only [scale,scaleNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [abs_of_nonneg (by positivity)]
  gcongr

theorem outputNat_cast (n m B N : ℕ) :
    (outputNat n m B N:ℝ)=outputBound n m (scaleNat m B N) B := by
  simp only [outputNat,outputBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat,Nat.cast_one]

theorem compile_bond_bound (n N B : ℕ) (xs : List Raw)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : MediatorListProgram.Bond) (he : e ∈ (compile (n,N,xs)).1) :
    |(e.2.2:ℝ)| ≤ outputNat n xs.length B N := by
  rw [outputNat_cast]
  exact fullBonds_abs n (bits (n,N,xs)) (scale N xs) xs
    (scale_nat_bound N xs B hw) (Nat.cast_nonneg B) hw e he

theorem compile_scalar_bound (n N B : ℕ) (xs : List Raw)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |((compile (n,N,xs)).2:ℝ)| ≤ outputNat n xs.length B N := by
  rw [outputNat_cast]
  exact fullScalar_abs n (bits (n,N,xs)) (scale N xs) xs
    (scale_nat_bound N xs B hw) (Nat.cast_nonneg B) hw

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientEnvelopeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs for the logical and physical coefficient bounds.
The only arguments are qubit count, term count, initial magnitude and precision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientEnvelopeProgram
open ExactQuantumFactoring.BitStackProgram

theorem polynomial_bound : ∃ a : ℕ, ∀ x : Input, value x ≤ (inputCode x).length.succ.succ^a :=
  unaryProcedure_power_bound program

end ContinuumCoulomb.QuantumCoefficientEnvelopeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rational-register bounds for the actual fixed-arity Pauli
trace.  These supply an explicit precision budget before scalar sampling. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar
open scoped BigOperators Classical

theorem height_finiteSum {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteSum f) ≤ ∑ a, height (f a) := by
  calc
    _ ≤ ∑ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteSum,enumerate,List.map_map,List.map_ofFn,List.sum_ofFn,
        Function.comp_apply] using
        height_sum ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.sum_comp (fun a => height (f a))

theorem height_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteProduct f) ≤ ∏ a, height (f a) := by
  calc
    _ ≤ ∏ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteProduct,enumerate,List.map_map,List.map_ofFn,List.prod_ofFn,
        Function.comp_apply] using
        height_product ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.prod_comp (fun a => height (f a))

theorem height_pauli (μ : Fin 4) (a b : Fin 2) : height (pauli μ a b) ≤ 1 := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,height,realHeight,rat,realRat,neg,realNeg,imaginary]

theorem height_word {ι : Type} [Fintype ι]
    (w : ι → Fin 4) (s t : ι → Fin 2) : height (word w s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  exact Finset.prod_le_one (fun _ _ => height_nonnegative _)
    (fun _ _ => height_pauli _ _ _)

theorem height_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    height (coefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  have hcell (s t : ι → Fin 2) : height (mul (A s t) (word w t s)) ≤ C := by
    calc
      _ ≤ height (A s t)*height (word w t s) := height_mul _ _
      _ ≤ height (A s t)*1 :=
        mul_le_mul_of_nonneg_left (height_word _ _ _) (height_nonnegative _)
      _ ≤ C := by simpa using hA s t
  have hsum : height (finiteSum (fun s : ι → Fin 2 =>
      finiteSum (fun t : ι → Fin 2 => mul (A s t) (word w t s)))) ≤
      ∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C := by
    apply (height_finiteSum _).trans
    apply Finset.sum_le_sum
    intro s _
    exact (height_finiteSum _).trans (Finset.sum_le_sum (fun t _ => hcell s t))
  have hp : 0 < (2:ℚ)^Fintype.card ι := pow_pos (by norm_num) _
  calc
    _ ≤ height (rat ((2:ℚ)^Fintype.card ι)⁻¹)*
        height (finiteSum (fun s => finiteSum (fun t => mul (A s t) (word w t s)))) :=
      height_mul _ _
    _ ≤ ((2:ℚ)^Fintype.card ι)⁻¹*(∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C) := by
      rw [height_rat,abs_of_pos (inv_pos.mpr hp)]
      exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
      field_simp

theorem realHeight_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (realCoefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  apply le_trans (le_add_of_nonneg_right (realHeight_nonnegative (coefficient A w).2))
  exact height_coefficient A w C hA

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalDegreeReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full degree-three reduction has exact rational output coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaRationalInitialScale_cast {m : ℕ} (J : Fin m → ℚ) (constant N : ℚ) :
    (qmaRationalInitialScale J constant N:ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|))
        (|(constant:ℝ)|+4*∑ e, (1+|(J e:ℝ)|)^2) N := by
  simp [qmaRationalInitialScale,qmaRoutingScale]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered rational data for the degree-three fork compiler. Original centers
retain their numbers. Each pair of active ports receives two consecutive new
spin numbers, and an unpaired port remains active at its original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem pairBonds_length (n i : ℕ) (R : ℚ) (p : Pair) :
    (pairBonds n i R p).length=4 := rfl

theorem addedBonds_length (s : State) (R : ℚ) :
    (addedBonds s R).length=4*pairCount s.2.2.2 := by
  unfold addedBonds
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,pairBonds_length,List.map_const',List.length_range,
    List.sum_replicate,smul_eq_mul,catalog_length]
  omega

theorem next_bonds_length (N : ℚ) (s : State) :
    (next N s).2.1.length=s.2.1.length+4*pairCount s.2.2.2 := by
  change (s.2.1++addedBonds s (scale N s)).length=_
  rw [List.length_append,addedBonds_length]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained part of a literal fork state has exactly the coefficient
budget and finite exchange matrix used by the parallel-fork estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

theorem background_weights (s : State) : (background s).map (fun b => b.2.2)=retained s := by
  simp only [background,retained,List.map_append]
  congr 1
  simp only [unpairedBonds,starBonds,List.map_flatten,List.map_map,Function.comp_def]
  have h := ExactQuantumFactoring.BitStackProgram.map_range_getD s.2.2.2 []
    (fun ps => (unpaired ps).map Prod.snd)
  simpa only [groupAt,List.map_flatten,List.map_map,Function.comp_def] using
    congrArg List.flatten h

theorem background_sum (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (f : ℚ → ℚ) :
    (∑ e, f ((backgroundGraph s hb hn).weight e))=((retained s).map f).sum := by
  change (∑ e : Fin (background s).length, f ((background s).get e).2.2)=_
  rw [← List.sum_ofFn]
  have hl := List.ofFn_getElem_eq_map (background s) (fun b => f b.2.2)
  simp only [List.get_eq_getElem] at hl ⊢
  rw [hl]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (background_weights s)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bond packet emitted for parallel forks has the exact full-space
Hamiltonian used in the calibrated perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

theorem graphScale_cast {r m : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ) (c N : ℚ) :
    (graphScale w J K c N : ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|))
        (3*(∑ a, |(w a:ℝ)|)+|(c:ℝ)|+
          12*∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2) (N:ℝ) := by
  unfold graphScale qmaRoutingScale
  push_cast
  rfl

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListEnvelope
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumForkList.budgetNat_cast _root_.OAI.ContinuumCoulomb.QuantumForkList.radiusNat_cast _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient envelopes for the parallel fork used by the literal
compiler. Both retained bonds and active pairs fit the same size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

theorem graphScale_abs_bound {m r : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ)
    (c N : ℚ) (hN : 0 ≤ N) {M L T : ℝ} (hm : (m:ℝ) ≤ M) (hr : (r:ℝ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ e, |(w e:ℝ)| ≤ L) (hJ : ∀ e, |(J e:ℝ)| ≤ L)
    (hK : ∀ e, |(K e:ℝ)| ≤ L) :
    |(graphScale w J K c N:ℝ)| ≤ forkRadius M L T := by
  have hM : 0 ≤ M := (Nat.cast_nonneg m).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hret : (∑ e, |(w e:ℝ)|) ≤ M*L := by
    calc
      _ ≤ ∑ _e : Fin m, L := Finset.sum_le_sum (fun e _ => hw e)
      _ = (m:ℝ)*L := by simp
      _ ≤ M*L := mul_le_mul_of_nonneg_right hm hL0
  have hlin : (∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|)) ≤ M*(1+4*L) := by
    calc
      _ ≤ ∑ _e : Fin r, (1+4*L) := Finset.sum_le_sum (fun e _ => by linarith [hJ e,hK e])
      _ = (r:ℝ)*(1+4*L) := by simp [mul_add]
      _ ≤ M*(1+4*L) := mul_le_mul_of_nonneg_right hr (by positivity)
  have hsq : (∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2) ≤ M*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _e : Fin r, (1+2*L)^2 := Finset.sum_le_sum (fun e _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hJ e,hK e]) 2)
      _ = (r:ℝ)*(1+2*L)^2 := by simp
      _ ≤ M*(1+2*L)^2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
  let A : ℝ := 3*∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|)
  let D : ℝ := 3*(∑ e, |(w e:ℝ)|)+|(c:ℝ)|+12*∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ forkBudget M L := by dsimp [A,D,forkBudget]; linarith
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [graphScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp only [forkRadius]
  nlinarith

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational scale is exactly the scale appearing in the checked
parallel-fork theorem, including all retained odd-port coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

theorem catalog_weights_sum (gs : Groups) (f : ℚ → ℚ → ℚ) :
    (((catalog gs).map Prod.snd).map (fun p => f p.1.2 p.2.2)).sum =
      ∑ e : Fin (pairCount gs), f (actualJ gs e) (actualK gs e) := by
  rw [List.map_map]
  change ((catalog gs).map (fun p => f p.2.1.2 p.2.2.2)).sum=_
  rw [← ExactQuantumFactoring.BitStackProgram.map_range_getD (catalog gs)
    (0,((0,0),(0,0))) (fun p => f p.2.1.2 p.2.2.2),catalog_length,range_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hc := catalog_pairEquiv gs (localPair gs e)
  rw [show pairEquiv gs (localPair gs e)=e from (pairEquiv gs).apply_symm_apply e] at hc
  rw [hc]
  rfl

theorem scale_eq_graphScale (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    scale N s = graphScale (backgroundGraph s hb hn).weight
      (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N := by
  have hL : (((catalog s.2.2.2).map Prod.snd).map pairLinear).sum =
      ∑ e, (1+2*|actualJ s.2.2.2 e|+2*|actualK s.2.2.2 e|) :=
    catalog_weights_sum s.2.2.2 (fun J K => 1+2*|J|+2*|K|)
  have hS : (((catalog s.2.2.2).map Prod.snd).map pairSquare).sum =
      ∑ e, (1+|actualJ s.2.2.2 e|+|actualK s.2.2.2 e|)^2 :=
    catalog_weights_sum s.2.2.2 (fun J K => (1+|J|+|K|)^2)
  have hw : (∑ e : Fin (background s).length, |((background s).get e).2.2|) =
      ((retained s).map abs).sum := background_sum s hb hn abs
  change scale N s = graphScale (fun e : Fin (background s).length => ((background s).get e).2.2)
    (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N
  dsimp only [scale,graphScale]
  rw [hL,hS,hw]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded, loop-free ordinary bonds survive the actual list transformation.
Together with port separation this supplies every hypothesis of the next
full-space fork comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem unpairedBonds_valid {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (b : Bond) (hb : b ∈ unpairedBonds gs) : b.1 < n ∧ b.2.1 < n ∧ b.1 ≠ b.2.1 := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  have hp' : p ∈ groupAt gs i := List.mem_of_mem_drop hp
  obtain ⟨j,hj,hp⟩ := List.getElem_of_mem hp'
  have he : portAt (groupAt gs i) j=p := (portAt_eq_getElem _ _ hj).trans hp
  have hbound := h.bounded ⟨i,hi'⟩ ⟨j,hj⟩
  have hne := h.disjoint ⟨i,hi'⟩ ⟨i,hi'⟩ ⟨j,hj⟩
  rw [he] at hbound hne
  exact ⟨lt_of_lt_of_le hi' h.centers,hbound,hne⟩

theorem next_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    SourceBondLists.bounded (next N s).1 (background (next N s)) ∧
      ∀ b ∈ background (next N s), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (next N s),
      b.1 < (next N s).1 ∧ b.2.1 < (next N s).1 ∧ b.1 ≠ b.2.1 := by
    intro b hmem
    change b ∈ (s.2.1++addedBonds s (scale N s))++unpairedBonds (next N s).2.2.2 at hmem
    rcases List.mem_append.mp hmem with hold | hport
    · rcases List.mem_append.mp hold with hold | hnew
      · have hm : b ∈ background s := List.mem_append_left _ hold
        have hbb := hb b hm
        have hnn := hn b hm
        rw [next_count]
        exact ⟨lt_of_lt_of_le hbb.1 (Nat.le_add_right _ _),
          lt_of_lt_of_le hbb.2 (Nat.le_add_right _ _),hnn⟩
      · exact addedBonds_valid s h (scale N s) b hnew
    · exact unpairedBonds_valid (next_validPorts N s h) b hport
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

theorem iterate_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (k : ℕ) :
    SourceBondLists.bounded (iterate N k s).1 (background (iterate N k s)) ∧
      ∀ b ∈ background (iterate N k s), b.1 ≠ b.2.1 := by
  induction k with
  | zero => exact ⟨hb,hn⟩
  | succ k ih =>
    exact next_background_valid _ (iterate_validPorts N s h k) ih.1 ih.2 N

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal odd subdivision satisfies all hypotheses needed to iterate
the full-space fork estimate. Its fresh singlets have distinct endpoints. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem initial_background_valid (n : ℕ) (bs : List Bond) (c N : ℚ) :
    SourceBondLists.bounded (initial n bs c N).1 (background (initial n bs c N)) ∧
      ∀ b ∈ background (initial n bs c N), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (initial n bs c N),
      b.1 < (initial n bs c N).1 ∧ b.2.1 < (initial n bs c N).1 ∧ b.1 ≠ b.2.1 := by
    intro b hb
    rcases List.mem_append.mp hb with hs | hp
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
      have he' := List.mem_range.mp he
      dsimp only [initial]
      omega
    · exact unpairedBonds_valid (initial_validPorts n bs c N) b hp
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_mem (bs : List Bond) (j : ℕ) (hj : j < 2*bs.length) :
    initialBond bs j ∈ bs := by
  have hi : j/2 < bs.length := by omega
  simp only [initialBond,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem initialEndpoint_bound (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (j : ℕ) (hj : j < 2*bs.length) : initialEndpoint bs j < n := by
  have h := hb _ (initialBond_mem bs j hj)
  unfold initialEndpoint
  split
  · exact h.1
  · exact h.2

theorem initial_center_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (j : Fin (2*bs.length)) (f : ℕ → ℕ → M) :
    (∑ i : Fin n, if initialEndpoint bs j.val=i.val then f i.val j.val else 0) =
      f (initialEndpoint bs j.val) j.val := by
  let e : Fin n := ⟨initialEndpoint bs j.val,initialEndpoint_bound n bs hb j.val j.isLt⟩
  rw [Finset.sum_eq_single e]
  · simp only [e,ite_true, if_true]
  · intro i _ hi
    exact ite_eq_right (fun h => hi (Fin.ext h.symm))
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem initial_group_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : ℕ → Port → M) :
    ((List.range n).map (fun i => ((initialGroup n bs R i).map (f i)).sum)).sum =
      ((List.range (2*bs.length)).map (fun j =>
        f (initialEndpoint bs j) (n+j,initialWeight bs R j))).sum := by
  simp only [initialGroup,List.map_map,Function.comp_def,initialIndices_sum,range_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ =>
    initial_center_sum n bs hb j (fun i k => f i (n+k,initialWeight bs R k)))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial scale has exactly the coefficient budget used in
the rational simultaneous path estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialScale_eq (N : ℚ) (bs : List Bond) (c : ℚ) :
    initialScale N bs c=qmaRationalInitialScale (fun e : Fin bs.length => (bs.get e).2.2) c N := by
  unfold initialScale qmaRationalInitialScale
  rw [initial_list_sum,initial_list_sum]

theorem initialScale_cast (N : ℚ) (bs : List Bond) (c : ℚ) :
    (initialScale N bs c:ℝ)=
      qmaRoutingScale (3*∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|))
        (|(c:ℝ)|+4*∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2) (N:ℝ) := by
  rw [initialScale_eq,qmaRationalInitialScale_cast]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSize
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial size bounds for the actual finite lists. A fixed number of
rounds grows the spin and bond counts linearly in the initial active-port mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem portMass_sum (gs : Groups) :
    portMass gs=∑ i : Fin gs.length, (groupAt gs i.val).length := by
  have h := congrArg List.sum
    (ExactQuantumFactoring.BitStackProgram.map_range_getD gs [] List.length)
  simpa only [portMass,groupAt,range_sum] using h.symm

theorem pairCount_le_portMass (gs : Groups) : pairCount gs ≤ portMass gs := by
  have he : pairCount gs=∑ i : Fin gs.length, (groupAt gs i.val).length/2 := by
    simpa only [LocalPair,Fintype.card_sigma,Fintype.card_fin] using (localPair_card gs).symm
  rw [he,portMass_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.div_le_self _ _)

theorem next_portMass_le (N : ℚ) (s : State) : portMass (next N s).2.2.2 ≤ portMass s.2.2.2 := by
  change (((List.range s.2.2.2.length).map (nextGroup s.1 (scale N s) s.2.2.2)).map List.length).sum ≤ _
  simp only [List.map_map,Function.comp_def,nextGroup_length,range_sum]
  rw [portMass_sum]
  exact Finset.sum_le_sum (fun i _ => by omega)

theorem iterate_portMass_le (N : ℚ) (s : State) (k : ℕ) :
    portMass (iterate N k s).2.2.2 ≤ portMass s.2.2.2 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (next_portMass_le N (iterate N k s)).trans ih

theorem iterate_count_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1 ≤ s.1+2*k*portMass s.2.2.2 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hp := (pairCount_le_portMass (iterate N k s).2.2.2).trans (iterate_portMass_le N s k)
    change (iterate N k s).1+2*pairCount (iterate N k s).2.2.2 ≤ _
    calc
      _ ≤ (s.1+2*k*portMass s.2.2.2)+2*portMass s.2.2.2 := by omega
      _ = s.1+2*(k+1)*portMass s.2.2.2 := by ring

theorem iterate_bonds_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.1.length ≤ s.2.1.length+4*k*portMass s.2.2.2 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hp := (pairCount_le_portMass (iterate N k s).2.2.2).trans (iterate_portMass_le N s k)
    rw [iterate,next_bonds_length]
    calc
      _ ≤ (s.2.1.length+4*k*portMass s.2.2.2)+4*portMass s.2.2.2 := by omega
      _ = s.2.1.length+4*(k+1)*portMass s.2.2.2 := by ring

theorem sum_ones {α : Type*} (xs : List α) : (xs.map (fun _ => (1:ℕ))).sum=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
    omega

theorem activeBonds_length (gs : Groups) : (activeBonds gs).length=portMass gs := by
  simp only [activeBonds,List.length_flatten,List.map_map,Function.comp_def,starBonds,List.length_map,
    range_sum,portMass_sum]

theorem initial_portMass (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) : portMass (initial n bs c N).2.2.2=2*bs.length := by
  have h := initial_group_sum n bs hb (initialScale N bs c) (fun _ _ => (1:ℕ))
  simp only [sum_ones,List.length_range] at h
  change (((List.range n).map (initialGroup n bs (initialScale N bs c))).map List.length).sum = _
  simpa only [List.map_map,Function.comp_def] using h

theorem initial_iterate_count_le (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) (k : ℕ) :
    (iterate N k (initial n bs c N)).1 ≤ n+2*bs.length+4*k*bs.length := by
  have h := iterate_count_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at h
  change (iterate N k (initial n bs c N)).1 ≤ n+2*bs.length+2*k*(2*bs.length) at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem initial_iterate_bonds_le (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) (k : ℕ) :
    ((iterate N k (initial n bs c N)).2.1++
      activeBonds (iterate N k (initial n bs c N)).2.2.2).length ≤
        3*bs.length+8*k*bs.length := by
  have h := iterate_bonds_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at h
  have hm := iterate_portMass_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at hm
  have hi : (initial n bs c N).2.1.length=bs.length := by
    simp only [initial,List.length_map,List.length_range]
  rw [hi] at h
  rw [List.length_append,activeBonds_length]
  calc
    _ ≤ (bs.length+4*k*(2*bs.length))+2*bs.length := Nat.add_le_add h hm
    _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient bounds for the actual ordered lists, including every active
port and the scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem groupAt_mem (gs : Groups) (i : ℕ) (hi : i<gs.length) : groupAt gs i ∈ gs := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem CoefficientBound.port (s : State) {L : ℝ} (h : CoefficientBound s L)
    (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length) :
    |((portAt (groupAt s.2.2.2 i.val) j.val).2:ℝ)| ≤ L := by
  rw [portAt_eq_getElem _ _ j.isLt]
  exact h.active _ (groupAt_mem _ _ i.isLt) _ (List.getElem_mem j.isLt)

theorem CoefficientBound.actualJ (s : State) {L : ℝ} (h : CoefficientBound s L)
    (e : Fin (pairCount s.2.2.2)) : |(actualJ s.2.2.2 e:ℝ)| ≤ L :=
  h.port s (localPair s.2.2.2 e).1 (localFirst s.2.2.2 e)

theorem CoefficientBound.actualK (s : State) {L : ℝ} (h : CoefficientBound s L)
    (e : Fin (pairCount s.2.2.2)) : |(actualK s.2.2.2 e:ℝ)| ≤ L :=
  h.port s (localPair s.2.2.2 e).1 (localSecond s.2.2.2 e)

theorem unpairedBonds_length_le (gs : Groups) :
    (unpairedBonds gs).length ≤ portMass gs := by
  simp only [unpairedBonds,List.length_flatten,List.map_map,Function.comp_def,
    starBonds,List.length_map,unpaired_length,range_sum,portMass_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mod_le _ _)

theorem CoefficientBound.background (s : State) {L : ℝ} (h : CoefficientBound s L)
    (b : Bond) (hb : b ∈ background s) : |(b.2.2:ℝ)| ≤ L := by
  rcases List.mem_append.mp hb with hold | hnew
  · exact h.ordinary b hold
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hnew
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact h.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _ (List.mem_of_mem_drop hp)

theorem scale_abs_bound (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hM : (s.2.1.length+portMass s.2.2.2:ℕ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) :
    |(scale N s:ℝ)| ≤ forkRadius M L T := by
  have hm : ((background s).length:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show (background s).length ≤ s.2.1.length+portMass s.2.2.2 by
      simpa only [background,List.length_append] using
        Nat.add_le_add_left (unpairedBonds_length_le s.2.2.2) s.2.1.length)
  have hr : (pairCount s.2.2.2:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show pairCount s.2.2.2 ≤ s.2.1.length+portMass s.2.2.2 by
      have := pairCount_le_portMass s.2.2.2
      omega)
  rw [scale_eq_graphScale s hb hn N]
  exact graphScale_abs_bound _ _ _ _ _ hN hm hr hL hT hc.scalar
    (fun e => hc.background s _ (List.get_mem _ _)) (hc.actualJ s) (hc.actualK s)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkWeightBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient growth of the repeatable fork stage is polynomial. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaForkOffset_abs_le {J K L : ℝ} (hL : 1 ≤ L) (hJ : |J| ≤ L) (hK : |K| ≤ L) :
    |qmaForkOffset J K| ≤ 7*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hK2 : K^2 ≤ L^2 := by nlinarith [sq_abs K,mul_self_le_mul_self (abs_nonneg K) hK]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaForkOffset; positivity)]
  unfold qmaForkOffset
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextWeights
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumForkList.budgetNat_cast _root_.OAI.ContinuumCoulomb.QuantumForkList.coefficientNat_cast _root_.OAI.ContinuumCoulomb.QuantumForkList.radiusNat_cast _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The emitted ordinary bonds, active ports and constant have one explicit
polynomial envelope. The bound applies to the literal rational transition. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem two_mul_abs_le {a b P : ℝ} (hP : 0 ≤ P) (ha : |a| ≤ P) (hb : |b| ≤ P) :
    |2*a*b| ≤ 2*P^2 := by
  rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h := mul_le_mul ha hb (abs_nonneg b) hP
  nlinarith

theorem pairBonds_abs_le (n i : ℕ) (R : ℚ) (p : Pair) {P : ℝ}
    (hP : 0 ≤ P) (hR : |(R:ℝ)| ≤ P)
    (hJ : |(p.1.2:ℝ)| ≤ P) (hK : |(p.2.2:ℝ)| ≤ P)
    (b : Bond) (hb : b ∈ pairBonds n i R p) : |(b.2.2:ℝ)| ≤ 2*P^2 := by
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · push_cast
    exact two_mul_abs_le hP hJ hK
  · push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := mul_self_le_mul_self (abs_nonneg (R:ℝ)) hR
    nlinarith [sq_abs (R:ℝ)]
  · push_cast
    exact two_mul_abs_le hP hR hJ
  · push_cast
    exact two_mul_abs_le hP hR hK

theorem next_scalar_abs_le (s : State) (N : ℚ) {L P : ℝ}
    (hc : CoefficientBound s L) (hP : 1 ≤ P) (hLP : L ≤ P)
    (hR : |(scale N s:ℝ)| ≤ P) :
    |((next N s).2.2.1:ℝ)| ≤ L+10*(pairCount s.2.2.2:ℝ)*P^2 := by
  have hP0 : 0 ≤ P := by linarith
  have hoff : ((((catalog s.2.2.2).map Prod.snd).map pairOffset).sum:ℝ) =
      ∑ e : Fin (pairCount s.2.2.2),
        qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ) := by
    change (((((catalog s.2.2.2).map Prod.snd).map
      (fun p => 3/4+3*p.1.2^2+3*p.2.2^2)).sum:ℚ):ℝ)=_
    rw [catalog_weights_sum s.2.2.2 (fun J K => 3/4+3*J^2+3*K^2)]
    push_cast
    rfl
  have hsum : |∑ e : Fin (pairCount s.2.2.2),
      qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ)| ≤
        (pairCount s.2.2.2:ℝ)*(7*P^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : Fin (pairCount s.2.2.2), 7*P^2 :=
        Finset.sum_le_sum (fun e _ => qmaForkOffset_abs_le hP
          ((hc.actualJ s e).trans hLP) ((hc.actualK s e).trans hLP))
      _ = _ := by simp
  have hR2 : (scale N s:ℝ)^2 ≤ P^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg (scale N s:ℝ)) hR,sq_abs (scale N s:ℝ)]
  have heq : ((next N s).2.2.1:ℝ)=(s.2.2.1:ℝ)+
      (∑ e : Fin (pairCount s.2.2.2),
        qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ))+
      3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2 := by
    change ((s.2.2.1+(((catalog s.2.2.2).map Prod.snd).map pairOffset).sum+
      3*(pairCount s.2.2.2:ℚ)*(scale N s)^2:ℚ):ℝ)=_
    rw [Rat.cast_add,Rat.cast_add,hoff]
    push_cast
    rfl
  rw [heq]
  have ha := abs_add_le (s.2.2.1:ℝ) (∑ e : Fin (pairCount s.2.2.2),
    qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ))
  have hb := abs_add_le ((s.2.2.1:ℝ)+(∑ e : Fin (pairCount s.2.2.2),
    qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ)))
    (3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2)] at hb
  nlinarith [hc.scalar,mul_le_mul_of_nonneg_left hR2
    (by positivity : 0 ≤ (pairCount s.2.2.2:ℝ))]

theorem next_coefficientBound (s : State) (hs : ValidPorts s.1 s.2.2.2) (N : ℚ)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (hN : 0 ≤ N)
    {M L T : ℝ} (hM : ((s.2.1.length+portMass s.2.2.2:ℕ):ℝ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) :
    CoefficientBound (next N s) (forkCoefficient M L T) := by
  let P := forkRadius M L T
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hM
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hB0 : 0 ≤ forkBudget M L := by unfold forkBudget; positivity
  have hLP : L ≤ P := by
    have hx : 0 ≤ 16*(forkBudget M L)^3*T := by positivity
    dsimp [P,forkRadius]
    linarith
  have hP : 1 ≤ P := hL.trans hLP
  have hP0 : 0 ≤ P := by linarith
  have hR : |(scale N s:ℝ)| ≤ P := scale_abs_bound s hb hn N hN hM hL hT hc
  have hp : (pairCount s.2.2.2:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show pairCount s.2.2.2 ≤ s.2.1.length+portMass s.2.2.2 by
      have := pairCount_le_portMass s.2.2.2
      omega)
  have hlarge : 2*P^2 ≤ forkCoefficient M L T := by
    dsimp [forkCoefficient]
    nlinarith [mul_nonneg hM0 (sq_nonneg P)]
  have hPL : P ≤ forkCoefficient M L T := by
    have hPP : P ≤ P^2 := by nlinarith
    calc
      P ≤ P^2 := hPP
      _ ≤ 2*P^2 := by nlinarith [sq_nonneg P]
      _ ≤ _ := hlarge
  constructor
  · have h := next_scalar_abs_le s N hc hP hLP hR
    have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg P)
    dsimp [forkCoefficient]
    nlinarith [sq_nonneg P]
  · intro b hmem
    change b ∈ s.2.1++addedBonds s (scale N s) at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · exact (hc.ordinary b hold).trans (hLP.trans hPL)
    obtain ⟨bs,hbs,hnew⟩ := List.mem_flatten.mp hnew
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
    have hi' : i < pairCount s.2.2.2 := by
      simpa only [catalog_length] using List.mem_range.mp hi
    rw [catalog_actualSite hs ⟨i,hi'⟩] at hnew
    exact (pairBonds_abs_le s.1 i (scale N s) _ hP0 hR
      ((hc.actualJ s _).trans hLP) ((hc.actualK s _).trans hLP) b hnew).trans hlarge
  · intro ps hps p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hps
    rcases List.mem_append.mp hp with hfresh | hold
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hfresh
      exact hR.trans hPL
    · exact (hc.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _
        (List.mem_of_mem_drop hold)).trans (hLP.trans hPL)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListIterateWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating a fixed number of literal fork rounds preserves a polynomial
coefficient bound. Size uses one uniform envelope for all intermediate lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem forkCoefficient_one_le {M L T : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) :
    1 ≤ forkCoefficient M L T := by
  have h : 0 ≤ (10*M+2)*(forkRadius M L T)^2 := by positivity
  unfold forkCoefficient
  linarith

theorem coefficientEnvelope_one_le {M L T : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) (k : ℕ) :
    1 ≤ coefficientEnvelope M L T k := by
  induction k with
  | zero => exact hL
  | succ k ih => exact forkCoefficient_one_le hM ih

theorem iterate_mass_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.1.length+portMass (iterate N k s).2.2.2 ≤
      s.2.1.length+(4*k+1)*portMass s.2.2.2 := by
  have hb := iterate_bonds_le N s k
  have hp := iterate_portMass_le N s k
  calc
    _ ≤ s.2.1.length+4*k*portMass s.2.2.2+portMass s.2.2.2 := Nat.add_le_add hb hp
    _ = _ := by ring

theorem iterate_coefficientBound (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1)
    (N : ℚ) (hN : 0 ≤ N) {M L T : ℝ} (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) (k : ℕ)
    (hm : ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) ≤ M) :
    CoefficientBound (iterate N k s) (coefficientEnvelope M L T k) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    have hkle : s.2.1.length+(4*k+1)*portMass s.2.2.2 ≤
        s.2.1.length+(4*(k+1)+1)*portMass s.2.2.2 := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have hcast : ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) ≤
        ((s.2.1.length+(4*(k+1)+1)*portMass s.2.2.2:ℕ):ℝ) := by exact_mod_cast hkle
    have hm' := hcast.trans hm
    have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hm'
    have hp := iterate_background_valid s hs hb hn N k
    have hmass : (((iterate N k s).2.1.length+
        portMass (iterate N k s).2.2.2:ℕ):ℝ) ≤
        ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) := by
      exact_mod_cast iterate_mass_le N s k
    exact next_coefficientBound (iterate N k s) (iterate_validPorts N s hs k) N
      hp.1 hp.2 hN (hmass.trans hm')
      (coefficientEnvelope_one_le hM0 hL k) hT (ih hm')

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialWeights
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumForkList.budgetNat_cast _root_.OAI.ContinuumCoulomb.QuantumForkList.coefficientNat_cast _root_.OAI.ContinuumCoulomb.QuantumForkList.radiusNat_cast _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first odd subdivision satisfies the same polynomial envelope as
the subsequent fork rounds, with its actual rational coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialScale_abs_bound (bs : List Bond) (c N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hm : (bs.length:ℝ) ≤ M) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) :
    |(initialScale N bs c:ℝ)| ≤ forkRadius M L T := by
  have hM : 0 ≤ M := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hlin : (∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|)) ≤ M*(1+4*L) := by
    calc
      _ ≤ ∑ _e : Fin bs.length, (1+4*L) :=
        Finset.sum_le_sum (fun e _ => by linarith [hw (bs.get e) (List.get_mem bs e)])
      _ = (bs.length:ℝ)*(1+4*L) := by simp [mul_add]
      _ ≤ M*(1+4*L) := mul_le_mul_of_nonneg_right hm (by positivity)
  have hsq : (∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2) ≤ M*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _e : Fin bs.length, (1+2*L)^2 :=
        Finset.sum_le_sum (fun e _ => pow_le_pow_left₀ (by positivity)
          (by linarith [hw (bs.get e) (List.get_mem bs e)]) 2)
      _ = (bs.length:ℝ)*(1+2*L)^2 := by simp
      _ ≤ M*(1+2*L)^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  let A := 3*∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|)
  let D := |(c:ℝ)|+4*∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hextra : 0 ≤ 3*M*L+8*M*(1+2*L)^2 := by positivity
  have hAD : A+D+1 ≤ forkBudget M L := by
    dsimp only [A,D,forkBudget]
    linarith
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [initialScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp only [forkRadius]
  nlinarith

theorem initial_coefficientBound (n : ℕ) (bs : List Bond) (c N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hm : (bs.length:ℝ) ≤ M) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) :
    CoefficientBound (initial n bs c N) (forkCoefficient M L T) := by
  let P := forkRadius M L T
  have hM : 0 ≤ M := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hB0 : 0 ≤ forkBudget M L := by unfold forkBudget; positivity
  have hLP : L ≤ P := by
    have hx : 0 ≤ 16*(forkBudget M L)^3*T := by positivity
    dsimp [P,forkRadius]
    linarith
  have hP : 1 ≤ P := hL.trans hLP
  have hP0 : 0 ≤ P := by linarith
  have hR : |(initialScale N bs c:ℝ)| ≤ P := initialScale_abs_bound bs c N hN hm hL hT hc hw
  have hR2 : (initialScale N bs c:ℝ)^2 ≤ P^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hR,sq_abs (initialScale N bs c:ℝ)]
  have hlarge : 2*P^2 ≤ forkCoefficient M L T := by
    dsimp [forkCoefficient]
    nlinarith [mul_nonneg hM (sq_nonneg P)]
  have hPP : P ≤ 2*P^2 := by nlinarith
  have hoff : (((bs.map (fun b => 3/4+3*b.2.2^2)).sum:ℚ):ℝ)=
      ∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ) := by
    rw [initial_list_sum]
    push_cast
    rfl
  have hsum : |∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ)| ≤
      (bs.length:ℝ)*(4*P^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : Fin bs.length, 4*P^2 := Finset.sum_le_sum (fun e _ =>
        qmaPathOffset_abs_le hP ((hw _ (List.get_mem _ _)).trans hLP))
      _ = _ := by simp
  constructor
  · have heq : ((initial n bs c N).2.2.1:ℝ)=(c:ℝ)+
        (∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ))+
        3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2 := by
      change ((c+(bs.map (fun b => 3/4+3*b.2.2^2)).sum+
        3*(bs.length:ℚ)*(initialScale N bs c)^2:ℚ):ℝ)=_
      rw [Rat.cast_add,Rat.cast_add,hoff]
      push_cast
      rfl
    rw [heq]
    have ha := abs_add_le (c:ℝ) (∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ))
    have hb := abs_add_le ((c:ℝ)+(∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ)))
      (3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2)
    rw [abs_of_nonneg (by positivity : 0 ≤ 3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2)] at hb
    have hprod := mul_le_mul_of_nonneg_left hR2 (Nat.cast_nonneg bs.length)
    have hmprod := mul_le_mul_of_nonneg_right hm (sq_nonneg P)
    dsimp only [forkCoefficient]
    nlinarith [sq_nonneg P]
  · intro b hb
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    change |(((initialScale N bs c)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hR2.trans ((by nlinarith [sq_nonneg P] : P^2 ≤ 2*P^2).trans hlarge)
  · intro ps hps p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hps
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hj' := (initialIndices_mem bs i j hj).1
    have hmem : initialBond bs j ∈ bs := by
      have hq : j/2<bs.length := by omega
      unfold initialBond
      rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hq,Option.getD_some]
      exact List.getElem_mem hq
    change |(initialWeight bs (initialScale N bs c) j:ℝ)| ≤ _
    by_cases hj0 : j%2=0
    · simpa only [initialWeight,ite_eq_left hj0] using hR.trans (hPP.trans hlarge)
    · simp only [initialWeight,ite_eq_right hj0]
      push_cast
      exact (two_mul_abs_le hP0 hR ((hw _ hmem).trans hLP)).trans hlarge

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single explicit coefficient envelope for every edge in the actual
output, including the retained active-star edges, and for its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem CoefficientBound.full (s : State) {L : ℝ} (h : CoefficientBound s L)
    (b : Bond) (hb : b ∈ s.2.1++activeBonds s.2.2.2) : |(b.2.2:ℝ)| ≤ L := by
  rcases List.mem_append.mp hb with hold | hnew
  · exact h.ordinary b hold
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hnew
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact h.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _ hp

theorem initial_iterate_coefficientBound (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (c N : ℚ) (hN : 0 ≤ N)
    {L T : ℝ} (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : |(c:ℝ)| ≤ L) (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) (D : ℕ) :
    CoefficientBound (iterate N D (initial n bs c N)) (outputCoefficient bs.length D L T) := by
  let M : ℝ := ((8*D+3)*bs.length:ℕ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hm : (bs.length:ℝ) ≤ M := by
    have hn : bs.length ≤ (8*D+3)*bs.length := by
      simpa only [one_mul] using
        (Nat.mul_le_mul_right bs.length (by omega : 1 ≤ 8*D+3))
    dsimp only [M]
    exact_mod_cast hn
  have hi := initial_coefficientBound n bs c N hN hm hL hT hc hw
  have hv := initial_background_valid n bs c N
  have hmass : ((((initial n bs c N).2.1.length+
      (4*D+1)*portMass (initial n bs c N).2.2.2):ℕ):ℝ) ≤ M := by
    rw [initial_portMass n bs hb c N]
    have hlen : (initial n bs c N).2.1.length=bs.length := by
      simp only [initial,List.length_map,List.length_range]
    rw [hlen]
    dsimp only [M]
    exact_mod_cast (show bs.length+(4*D+1)*(2*bs.length) ≤ (8*D+3)*bs.length from
      le_of_eq (by ring))
  exact iterate_coefficientBound _ (initial_validPorts n bs c N) hv.1 hv.2 N hN
    (forkCoefficient_one_le hM0 hL) hT hi D hmass

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs compute the coefficient envelopes. For each fixed
number of rounds, the complete numerical envelope is polynomial in its inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

theorem outputCoefficientNat_power (D : ℕ) : ∃ a : ℕ, ∀ x : QuantumCoefficientPrograms.Input,
    outputCoefficientNat x.1 D x.2.1 x.2.2 ≤ ((QuantumCoefficientPrograms.inputCode x).length+2)^a :=
  unaryProcedure_power_bound (outputCoefficientNatProgram D)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-density local input list yields the actual degree-three
spatial output, with its full Hamiltonian and fixed density constant. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

namespace SpatialInput
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

theorem model_rows : I.model.rows=rows := rfl

theorem model_width : I.model.width=width := rfl

end SpatialInput
end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual rational-register history entries.
The only matrix multiplication takes place on the five-site propagation
core, with at most32 intermediate configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem height_identity {α : Type} [DecidableEq α] (s t : α) :
    height (identity s t) ≤ 1 := by
  by_cases h : s = t <;> simp [identity,h]

theorem height_hadamard (s t : Fin 2) : height (hadamard s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [hadamard,mul,realMul,realSub,realAdd,realNeg,sqrtHalf,
      rat,realRat,height,realHeight]

theorem height_phaseT (s t : Fin 2) : height (phaseT s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [phaseT,mul,realMul,realSub,realAdd,realNeg,QuantumAlgebraicScalar.add,sqrtHalf,
      rat,realRat,imaginary,height,realHeight]

private theorem height_single_product (n : ℕ) (i : Fin n)
    (A : Fin 2 → Fin 2 → Scalar) (hA : ∀ s t, height (A s t) ≤ 2)
    (s t : SourceSpinBasis n) :
    height (finiteProduct (fun k => if k = i then A (s k) (t k)
      else identity (s k) (t k))) ≤ 2 := by
  apply (height_finiteProduct _).trans
  calc
    _ ≤ ∏ k : Fin n, if k = i then (2:ℚ) else 1 := by
      apply Finset.prod_le_prod (fun _ _ => height_nonnegative _)
      intro k _
      by_cases h : k = i
      · simpa only [h,ite_true, if_true] using hA (s k) (t k)
      · simpa only [h,ite_false, if_false] using height_identity (s k) (t k)
    _ = 2 := by simp

theorem height_gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) :
    height (gate work g s t) ≤ 2 := by
  cases g with
  | hadamard i => exact height_single_product _ _ _ height_hadamard s t
  | phaseT i => exact height_single_product _ _ _ height_phaseT s t
  | controlledNot i j =>
    dsimp only [gate]
    split_ifs <;> norm_num

theorem height_delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) : height (delta c t s r) ≤ 3 := by
  dsimp only [delta]
  split_ifs
  · apply (height_sub _ _).trans
    have hm := height_mul
      (identity (s ∘ Sum.inl) (r ∘ Sum.inl))
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    have hi := height_identity s (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) r)
    have hj := height_identity (s ∘ Sum.inl) (r ∘ Sum.inl)
    have hg := height_gate c.work (c.gates.getD t.val (.hadamard 0))
      (s ∘ Sum.inr) (r ∘ Sum.inr)
    have hn := height_nonnegative
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    nlinarith
  · norm_num

theorem propagation_configurations (c : QMACircuit) (t : Fin c.gates.length) :
    Fintype.card (QMASupportBasis (qmaPropagationSites c t)) ≤ 32 := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (qmaPropagationSites_card c t)
  simpa only [QMASupportBasis,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    show (2:ℕ)^5 = 32 by norm_num] using h

theorem height_propagationCore (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMASupportBasis (qmaPropagationSites c t)) :
    height (propagationCore c t s r) ≤ 288 := by
  have hentry (u : QMASupportBasis (qmaPropagationSites c t)) :
      height (mul (adjoint (deltaCore c t) s u) (deltaCore c t u r)) ≤ 9 := by
    apply (height_mul _ _).trans
    simp only [adjoint,height_conj,deltaCore]
    calc
      _ ≤ (3:ℚ)*3 := mul_le_mul (height_delta c t _ _) (height_delta c t _ _)
        (height_nonnegative _) (by norm_num)
      _ = 9 := by norm_num
  have hsum := (height_finiteSum (fun u =>
    mul (adjoint (deltaCore c t) s u) (deltaCore c t u r))).trans
      (Finset.sum_le_sum (fun u _ => hentry u))
  have hcard : (Fintype.card (QMASupportBasis (qmaPropagationSites c t)):ℚ) ≤ 32 :=
    Nat.cast_le.mpr (propagation_configurations c t)
  change height (finiteSum _) ≤ 288
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  linarith

theorem height_lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (s t : ι → Fin 2) :
    height (lift S A s t) ≤ height (A (fun i => s i.val) (fun i => t i.val)) := by
  apply (height_mul _ _).trans
  simpa using mul_le_mul_of_nonneg_left
    (height_identity (fun i : {i // i ∉ S} => s i.val) (fun i => t i.val))
    (height_nonnegative (A (fun i => s i.val) (fun i => t i.val)))

theorem historyHeight_nonnegative (c : QMACircuit) : 0 ≤ historyHeight c := by
  unfold historyHeight
  positivity

theorem height_distributed (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c)
    (s r : QMACircuitQubit c → Fin 2) :
    height (distributed c τ a s r) ≤ historyHeight c := by
  have h14 : (14:ℚ) ≤ historyHeight c := by
    unfold historyHeight
    have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    linarith
  rcases a with i | (b | (i | (u | t)))
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · by_cases hb : b = 0
    · simp only [distributed,hb,ite_true, if_true,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
    · simp only [distributed,hb,ite_false, if_false,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · apply (height_mul _ _).trans
    have hl := (height_lift _ (propagationCore c t) s r).trans
      (height_propagationCore c t _ _)
    have hw : 0 ≤ ((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    rw [height_rat,abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left hl hw).trans
    unfold historyHeight
    linarith

theorem height_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    height (localY n i s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  apply Finset.prod_le_one (fun _ _ => height_nonnegative _)
  intro k _
  by_cases h : k = i
  · simpa only [h,ite_true, if_true] using height_pauli 2 (s k) (t k)
  · simpa only [h,ite_false, if_false] using height_identity (s k) (t k)

theorem height_rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (s t : Fin n ⊕ ι → Fin 2) :
    height (rebit n i A s t) ≤ 2*height (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_localY n i (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hR := height_realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hJ := height_imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hYR := height_mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
    (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hIR := height_mul (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hN := height_mul (neg imaginary)
    (mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
      (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))))
  simp only [height_neg,height_imaginary,one_mul] at hN
  apply (height_add _ _).trans
  nlinarith [height_nonnegative (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))),
    height_nonnegative (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))]

theorem height_pairY (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) :
    height (pairY n i j s t) ≤ 1 := by
  have hp := (height_mul (QuantumFixedPauli.pauli 2 (s i) (t i)) (QuantumFixedPauli.pauli 2 (s j) (t j))).trans
    (mul_le_mul (height_pauli 2 (s i) (t i)) (height_pauli 2 (s j) (t j))
      (height_nonnegative _) (by norm_num))
  have hδ : height (rat (if ∀ k, k ≠ i → k ≠ j → s k = t k then 1 else 0)) ≤ 1 := by
    split_ifs <;> norm_num
  apply (height_mul _ _).trans
  simpa using mul_le_mul hp hδ (height_nonnegative _) (by norm_num)

theorem height_referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (s t : Fin (n+1) ⊕ ι → Fin 2) :
    height (referenceEdge n i s t) ≤ 1 := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hS := height_sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl))
  have hhalf := height_mul (rat (1/2))
    (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))
  norm_num only [height_rat,abs_of_pos (by norm_num : (0:ℚ) < 1/2)] at hhalf
  have hB : height (mul (rat (1/2))
      (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
        (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))) ≤ 1 := by
    linarith
  apply (height_mul _ _).trans
  simpa using mul_le_mul hB (height_identity (s ∘ Sum.inr) (t ∘ Sum.inr))
    (height_nonnegative _) (by norm_num)

theorem height_orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2) :
    height (orderedTerm c hT a s t) ≤ 2*historyHeight c := by
  cases a with
  | inl i =>
    exact (height_rebit _ _ _ s t).trans
      (mul_le_mul_of_nonneg_left (height_distributed c _ _ _ _) (by norm_num))
  | inr i =>
    apply (height_referenceEdge _ _ s t).trans
    have h : (14:ℚ) ≤ historyHeight c := by
      unfold historyHeight
      have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
      linarith
    linarith

theorem height_orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a)) :
    height (orderedCore c hT a s t) ≤ 2*historyHeight c :=
  height_orderedTerm c hT a _ _

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit unary precision controls the total error of all actual
ordered-history coefficients.  The precision is polynomial in the circuit
size and the requested inverse error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators Classical

theorem coefficientBudget_cast (c : QMACircuit) :
    (coefficientBudget c:ℚ) = 128*historyHeight c := by
  simp only [coefficientBudget,historyHeight,Nat.cast_mul,Nat.cast_add,
    Nat.cast_one,Nat.cast_ofNat]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

theorem qubits_index (c : QMACircuit) :
    QuantumOrderedLabelTable.index (qubits c)=QuantumOrderedSupport.siteNumber c := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · change qmaHistoryReferenceWork c+1+((c.gates.length+2)+i.val) =
      qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val
    omega

theorem termCount_eq (c : QMACircuit) :
    termCount c=4096*(4*c.gates.length+2*c.work+9) := by
  rw [termCount,referenceCount_eq]
  have h : patternCount=4096 := by
    norm_num [patternCount,Pattern,Fintype.card_fun]
  rw [h,Nat.mul_comm]

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history word is obtained by zipping its literal
site-number list with a fixed local pattern. No spectator basis occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem local_word_at {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) (i : Fin n) :
    QuantumPaddedLocal.word S e m w (e i).val=QuantumPaddedPauli.paddedWord n m w i := by
  simp only [QuantumPaddedLocal.word,qmaPauliExtend,dite_eq_left (e i).property]
  apply congrArg (QuantumPaddedPauli.paddedWord n m w)
  apply e.injective
  rw [Equiv.apply_symm_apply]

private theorem map_get_zip {α β γ : Type} (xs : List α) (g : α → β)
    (f : Fin xs.length → γ) :
    (List.ofFn (fun i => (g (xs.get i),f i)))= (xs.map g).zip (List.ofFn f) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem source_tag (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT p.1) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT p.1).zip
        (localLabels (QuantumOrderedSupport.sites c hT p.1).length
          (6-(QuantumOrderedSupport.sites c hT p.1).length)
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)) := by
  let xs := QuantumOrderedSupport.sites c hT p.1
  let e := QuantumOrderedSupport.supportEquiv c hT p.1
  let v : QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p
  let w := widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2
  have hw (i : Fin xs.length) :
      v (xs.get i)=
        QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i := by
    have hi := QuantumOrderedSupport.supportEquiv_apply c hT p.1 i
    change (e i).val=xs.get i at hi
    rw [← hi]
    exact local_word_at _ e _ w i
  change xs.map (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val)) = _
  calc
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),(v (xs.get i)).val)) :=
      (List.ofFn_getElem_eq_map xs
        (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val))).symm
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),
          (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)) := by
      apply congrArg List.ofFn
      funext i
      rw [hw]
    _ = _ := map_get_zip xs (QuantumOrderedSupport.siteNumber c)
      (fun i => (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryXZBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient control for the actual sampled verifier history throughout
the five fixed gadget stages. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar
open scoped Classical

private theorem halfRoot_bounds (k : ℕ) :
    0 ≤ RationalSquareRoot.value (k,1/2) ∧ RationalSquareRoot.value (k,1/2) ≤ 1 := by
  have hv : RationalSquareRoot.value (k,(1/2:ℚ)) = DyadicRootProgram.value k 1 2 := by
    norm_num [RationalSquareRoot.value]
  rw [hv]
  constructor
  · unfold DyadicRootProgram.value
    positivity
  · have h := (DyadicRootProgram.value_error k 1 2 (by omega)).1
    have hs : Real.sqrt ((1:ℝ)/2) ≤ 1 := (Real.sqrt_le_iff).mpr (by norm_num)
    have ht : (DyadicRootProgram.value k 1 2:ℝ) ≤ 1 := by
      norm_num only [Nat.cast_one,Nat.cast_ofNat] at h
      linarith
    exact_mod_cast ht

theorem sample_height_bound (k : ℕ) (x : RealScalar) : |sample k x| ≤ realHeight x := by
  have h := halfRoot_bounds k
  calc
    _ ≤ |x.1|+|x.2*RationalSquareRoot.value (k,1/2)| := abs_add_le _ _
    _ = |x.1|+|x.2| * RationalSquareRoot.value (k,1/2) := by
      rw [abs_mul,abs_of_nonneg h.1]
    _ ≤ |x.1|+|x.2| * 1 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left h.2 (abs_nonneg _))
    _ = realHeight x := by simp only [realHeight,mul_one]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedSampling
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal padded history table has the same polynomial scalar budget
as the supported expansion, and its rational samples approximate the actual
full-space history energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped BigOperators Classical

section ScalarTable

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedHistory.finDecision
private theorem padded_height (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar)
    (w : Fin (n+m) → Fin 4) (C : ℚ) (hC : 0 ≤ C)
    (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (QuantumPaddedTable.coefficient n m (matrixData A) w) ≤ 2^n*C := by
  let v := QuantumPaddedPauli.restrictWord n m w
  have hE : (fun s t : Fin n → Fin 2 => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  have hV : realHeight (realCoefficient A v) ≤ (2:ℚ)^n*C := by
    simpa only [Fintype.card_fin] using realHeight_coefficient A v C hA
  unfold QuantumPaddedTable.coefficient
  change realHeight (if Even (qmaPauliYCount v) then
    realMul (realRat (((4:ℚ)^m)⁻¹))
      (realCoefficient (fun s t => entry (matrixData A) s t) v) else realRat 0) ≤ _
  rw [hE]
  split_ifs
  · have hr : |((4:ℚ)^m)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc
      _ ≤ realHeight (realRat (((4:ℚ)^m)⁻¹))*realHeight (realCoefficient A v) :=
        realHeight_mul _ _
      _ ≤ 1*realHeight (realCoefficient A v) := by
        rw [realHeight_rat]
        exact mul_le_mul_of_nonneg_right hr (realHeight_nonnegative _)
      _ ≤ (2:ℚ)^n*C := by simpa only [one_mul] using hV
  · simpa only [realHeight_rat,abs_zero] using mul_nonneg (pow_nonneg (by norm_num) n) hC

theorem scalar_height (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    realHeight (scalar c hT p) ≤ (coefficientBudget c:ℚ) := by
  have h := padded_height _ _ (orderedTable c hT p.1)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)
    (2*historyHeight c) (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    (fun s t => height_orderedCore c hT p.1 _ _)
  have hp : (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length ≤ 64 := by
    exact (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2)
      (QuantumOrderedSupport.sites_length c hT p.1)).trans_eq (by norm_num)
  change realHeight (scalar c hT p) ≤ _ at h
  calc
    _ ≤ (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length*(2*historyHeight c) := h
    _ ≤ 64*(2*historyHeight c) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    _ = (coefficientBudget c:ℚ) := by rw [coefficientBudget_cast]; ring

end ScalarTable

theorem sampledWeight_bound (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : Term c) : |sampledWeight k c hT p| ≤ (coefficientBudget c:ℚ) :=
  (sample_height_bound k (scalar c hT p)).trans (scalar_height c hT p)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem uniformPacket_eq (x : Input) (h : x.2.1.length ≤ 6) :
    uniformPacket x=packet x.2.1.length (6-x.2.1.length) x := by
  generalize hn : x.2.1.length=n at *
  interval_cases n <;> simp only [uniformPacket,hn] <;> norm_num

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.finDecision
private theorem labels_eq_zip (n m : ℕ) (w : Fin (n+m) → Fin 4)
    (xs : List ℕ) (hlen : xs.length=n) :
    labels n m w xs = xs.zip (localLabels n m w) := by
  apply List.ext_getElem
  · simp [labels,localLabels,hlen]
  · intro i hi hj
    have hi' : i < xs.length := by simpa only [labels,List.length_ofFn,← hlen] using hi
    simp only [labels,localLabels,List.getElem_ofFn,List.getElem_zip]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]

theorem entry_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin ((QuantumOrderedSupport.sites c hT a).length+
      (6-(QuantumOrderedSupport.sites c hT a).length)) → Fin 4) :
    entry (QuantumOrderedSupport.sites c hT a).length
      (6-(QuantumOrderedSupport.sites c hT a).length) w
      (k,QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) =
    let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
    (QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p),sampledWeight k c hT p) := by
  let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
  have hw : widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2 = w :=
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).apply_symm_apply w
  apply Prod.ext
  · change labels _ _ w (QuantumOrderedSupport.encodedSites c hT a) = _
    rw [labels_eq_zip _ _ w _ (by simp only [QuantumOrderedSupport.encodedSites,List.length_map])]
    have hs := source_tag c hT p
    change QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT a).zip (localLabels _ _
        (widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2)) at hs
    rw [hw] at hs
    exact hs.symm
  · change sample k (QuantumPaddedTable.coefficient _ _ _ w) = _
    unfold sampledWeight
    apply congrArg (sample k)
    unfold scalar
    rw [hw]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

theorem packet_reindex (n : ℕ) (hn : n ≤ 6) (x : Input) :
    packet n (6-n) x = List.ofFn (fun j => entry n (6-n) (packetPatterns n hn j) x) := by
  simp only [packet,enumerate,List.map_ofFn,Function.comp_def]
  rw [List.ofFn_congr (pattern_card n hn)]
  rfl

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.tableFinDecision
theorem sourceEntries_table (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    sourceEntries k c hT =
      QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
        (fun p => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT) := by
  unfold sourceEntries QuantumOrderedLabelTable.table sourceTerms
  simp only [Equiv.trans_apply]
  let entryAt (j : Fin (QuantumOrderedSourceIndex.referenceCount c) ×
      Fin QuantumOrderedSourceIndex.patternCount) :=
    let p := Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
      (fun i => (packetPatterns _ (QuantumOrderedSupport.sites_length c hT
        (QuantumOrderedSourceIndex.reference c i))).trans
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT
            (QuantumOrderedSourceIndex.reference c i))).symm) j
    (QuantumOrderedLabelData.tag
      (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
      (QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT p),sampledWeight k c hT p)
  change _ = List.ofFn (fun i => entryAt (finProdFinEquiv.symm i))
  rw [QuantumOrderedLabelTable.product_table entryAt]
  dsimp only [entryAt]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  let a := QuantumOrderedSourceIndex.reference c i
  have hn := QuantumOrderedSupport.sites_length c hT a
  rw [uniformPacket_eq _ (by
    simpa only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map] using hn)]
  rw [show (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)).2.1.length =
    (QuantumOrderedSupport.sites c hT a).length by
      simp only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map,a]]
  change packet (QuantumOrderedSupport.sites c hT a).length
    (6-(QuantumOrderedSupport.sites c hT a).length) (sourceInput k c hT a) = _
  rw [packet_reindex _ hn]
  apply congrArg List.ofFn
  funext j
  have h := entry_source k c hT a (packetPatterns _ hn j)
  simpa only [sourceInput,sourceWord,Equiv.trans_apply,Equiv.prodShear_apply,
    Equiv.symm_apply_apply,
    QuantumOrderedSourceIndex.qubits_index] using h

theorem sourceEntries_length (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    (sourceEntries k c hT).length = QuantumOrderedSourceIndex.termCount c := by
  rw [sourceEntries_table]
  simp only [QuantumOrderedLabelTable.table,List.length_ofFn,
    QuantumOrderedSourceIndex.termCount]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

theorem historyQubits_eq (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    historyQubits c hT N=4*(qubitCount c+3717*termCount c) := by
  unfold historyQubits historyInput QuantumOrderedLabelCompile.qubitCount
  rw [QuantumOrderedLabelPipeline.output_qubits,sourceEntries_length]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier compiler, through the specified planar lattice.
The final precision pays for every early and routing error; the scalar offset
is removed from both thresholds exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumForkList QuantumAlgebraicHistory
open scoped Classical

-- Keep the fixed density symbolic; expanding it as a numeral is unnecessary.
attribute [local irreducible] spatialDensity

theorem routeRounds_eq : QMASpatialExchangeModel.routeLengthBound
    (spatialDensity rawDensity historyDegree) (27*spatialDensity rawDensity historyDegree) =
      routeRounds := routeRoundValue.property

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial envelopes apply to the actual emitted rational graph,
with the same six-stage table and four-spin instructions used by its energy proof. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n m : ℕ}

theorem rawInput_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup) (N : ℕ) :
    rawInput (N,n,table e (index q) xs w J) =
      (finalCount n m,N,QuantumRawExchange.packed
        (QuantumOrderedRawBlock.terms
          (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
          (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w)))
        (fun i => finalCoefficient J N (terms6 e i))) := by
  unfold rawInput outputCount rawEntries labelEntries classify
  simp only [Function.comp_apply,QuantumOrderedLabelTable.output_table q e xs w J hlen hdup N]
  rw [packed_table]
  rfl

omit [DecidableEq κ] in
theorem final_raw_weights (e : Fin m ≃ κ) (J : κ → ℚ) {B : ℕ}
    (hJ : ∀ p, |J p| ≤ (B:ℚ)) (N : ℕ) :
    ∀ i, |(finalCoefficient J N (terms6 e i):ℝ)| ≤ QuantumOrderedXZ.pipelineNat m B N 6 := by
  have hm : Fintype.card κ ≤ m := le_of_eq ((Fintype.card_congr e).symm.trans (Fintype.card_fin m))
  intro i
  exact_mod_cast QuantumOrderedXZ.private_coefficient_bound J hm hJ N (terms6 e i)

theorem output_coefficients (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    {B : ℕ} (hJ : ∀ p, |J p| ≤ (B:ℚ)) (N : ℕ) :
    |((output (N,n,table e (index q) xs w J)).2:ℝ)| ≤ coefficientEnvelope n m B N ∧
      ∀ b ∈ (output (N,n,table e (index q) xs w J)).1,
        |(b.2.2:ℝ)| ≤ coefficientEnvelope n m B N := by
  let t := QuantumOrderedRawBlock.terms
    (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
    (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
  let c := fun i => finalCoefficient J N (terms6 e i)
  let bs := QuantumRawExchange.packed t c
  have hlenbs : bs.length=12544*m := by
    simp only [bs,QuantumRawExchange.packed,List.length_ofFn]
    ring
  have hw : ∀ b ∈ bs, |(b.2.2.2:ℝ)| ≤ QuantumOrderedXZ.pipelineNat m B N 6 := by
    intro b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [QuantumRawExchange.pack_weight]
    exact final_raw_weights e J hJ N i
  change _ ≤ (coefficientEnvelope n m B N:ℝ) ∧ _
  unfold output
  simp only [Function.comp_apply]
  rw [rawInput_table q e xs w J hlen hdup N]
  constructor
  · have h := QuantumRawExchange.compile_scalar_bound (finalCount n m) N
      (QuantumOrderedXZ.pipelineNat m B N 6) bs hw
    rw [hlenbs] at h
    conv at h => rhs; rw [finalCount_eq]
    exact h
  · intro b hb
    have h := QuantumRawExchange.compile_bond_bound (finalCount n m) N
      (QuantumOrderedXZ.pipelineNat m B N 6) bs hw b hb
    rw [hlenbs] at h
    conv at h => rhs; rw [finalCount_eq]
    exact h

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size and coefficient bounds for the same full spatial graph that is routed
to the lattice. Active-star bonds and the scalar offset are included. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList.SpatialInput
open scoped Classical
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

theorem model_size : I.model.n+Fintype.card I.model.Term ≤
    I.n+5*I.bonds.length+12*D*I.bonds.length := by
  have hn := initial_iterate_count_le I.n I.bonds I.bounded I.constant I.precision D
  have he := initial_iterate_bonds_le I.n I.bonds I.bounded I.constant I.precision D
  change I.state.1+Fintype.card (Fin (fullList I.state).length) ≤ _
  rw [Fintype.card_fin]
  calc
    _ ≤ (I.n+2*I.bonds.length+4*D*I.bonds.length)+
        (3*I.bonds.length+8*D*I.bonds.length) := Nat.add_le_add hn he
    _ = _ := by ring

theorem model_coefficientBound {L T : ℝ} (hN : 0 ≤ I.precision)
    (hL : 1 ≤ L) (hT : |(I.precision:ℝ)| ≤ T)
    (hc : |(I.constant:ℝ)| ≤ L) (hw : ∀ b ∈ I.bonds, |(b.2.2:ℝ)| ≤ L) :
    I.model.exchangeGraph.CoefficientBound (outputCoefficient I.bonds.length D L T) := by
  have h := initial_iterate_coefficientBound I.n I.bonds I.bounded I.constant I.precision
    hN hL hT hc hw D
  constructor
  · exact h.scalar
  · intro e
    exact h.full I.state ((fullList I.state).get e) (List.get_mem _ e)

theorem model_nat_coefficientBound {L T : ℕ} (hN : 0 ≤ I.precision)
    (hL : 1 ≤ L) (hT : |(I.precision:ℝ)| ≤ T)
    (hc : |(I.constant:ℝ)| ≤ L) (hw : ∀ b ∈ I.bonds, |(b.2.2:ℝ)| ≤ L) :
    I.model.exchangeGraph.CoefficientBound
      (outputCoefficientNat I.bonds.length D L T) := by
  rw [outputCoefficientNat_cast]
  exact I.model_coefficientBound hN (by exact_mod_cast hL) hT hc hw

end ContinuumCoulomb.QuantumForkList.SpatialInput

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

theorem history_output_bound (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    |((historyOutput c hT N).2:ℝ)| ≤ historyCoefficientBudget c N ∧
      ∀ b ∈ (historyOutput c hT N).1, |(b.2.2:ℝ)| ≤ historyCoefficientBudget c N := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  exact QuantumOrderedLabelCompile.output_coefficients (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT)
    (sampledWeight (QuantumAlgebraicHistory.samplePrecision c N) c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1)
    (fun p => sampledWeight_bound _ c hT p) N

theorem input_bonds (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).bonds=(historyOutput (qmaSparseCircuit c) hT N).1 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_constant (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).constant=(historyOutput (qmaSparseCircuit c) hT N).2 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_n (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).n=historyQubits (qmaSparseCircuit c) hT N := by
  unfold historyQubits historyInput
  rw [sourceEntries_table]
  rfl

private theorem outputNat_one (n m B N : ℕ) : 1 ≤ QuantumRawExchange.outputNat n m B N := by
  dsimp only [QuantumRawExchange.outputNat]
  omega

theorem historyCoefficientBudget_one (c : QMACircuit) (N : ℕ) :
    1 ≤ historyCoefficientBudget c N := outputNat_one _ _ _ _

theorem model_coefficientBound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).exchangeGraph.CoefficientBound
      (outputCoefficientNat (input c hc hT hne N).bonds.length historyDegree
        (historyCoefficientBudget (qmaSparseCircuit c) N) N) := by
  have hb := history_output_bound (qmaSparseCircuit c) hT N
  have hp : (input c hc hT hne N).precision=(N:ℚ) := rfl
  apply (input c hc hT hne N).model_nat_coefficientBound
    (by rw [hp]; exact_mod_cast Nat.zero_le N)
    (historyCoefficientBudget_one _ N)
    (by rw [hp,Rat.cast_natCast,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  · rw [input_constant]
    exact hb.1
  · rw [input_bonds]
    exact hb.2

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPromisePowers
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small power bounds for the unary tuples used by the actual coefficient
programs. The exponent is independent of the particular verifier. -/

namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

private theorem tuple_power (n k : ℕ) :
    16*(n+2)^k ≤ (n+2)^(k+4) := by
  have h : 16 ≤ (n+2)^4 := by
    simpa using (Nat.pow_le_pow_left (show 2 ≤ n+2 by omega) 4)
  rw [pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left ((n+2)^k) h

theorem inputCode_power {n k m L T : ℕ}
    (hm : m ≤ (n+2)^k) (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    (inputCode (m,L,T)).length+2 ≤ (n+2)^(k+4) := by
  have hp : 1 ≤ (n+2)^k := Nat.one_le_pow k (n+2) (by omega)
  calc
    _ ≤ 16*(n+2)^k := by
      simp only [inputCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      omega
    _ ≤ _ := tuple_power n k

theorem latticeInputCode_power {n k m r L T : ℕ}
    (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    (latticeInputCode (m,r,L,T)).length+2 ≤ (n+2)^(k+4) := by
  have hp : 1 ≤ (n+2)^k := Nat.one_le_pow k (n+2) (by omega)
  calc
    _ ≤ 16*(n+2)^k := by
      simp only [latticeInputCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      omega
    _ ≤ _ := tuple_power n k

theorem input_function_power {f : Input → ℕ} {a : ℕ}
    (hf : ∀ x, f x ≤ ((inputCode x).length+2)^a)
    {n k m L T : ℕ} (hm : m ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    f (m,L,T) ≤ (n+2)^((k+4)*a) := by
  calc
    _ ≤ ((inputCode (m,L,T)).length+2)^a := hf _
    _ ≤ ((n+2)^(k+4))^a := Nat.pow_le_pow_left (inputCode_power hm hL hT) a
    _ = _ := (pow_mul _ _ _).symm

theorem lattice_function_power {f : LatticeInput → ℕ} {a : ℕ}
    (hf : ∀ x, f x ≤ ((latticeInputCode x).length+2)^a)
    {n k m r L T : ℕ} (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    f (m,r,L,T) ≤ (n+2)^((k+4)*a) := by
  calc
    _ ≤ ((latticeInputCode (m,r,L,T)).length+2)^a := hf _
    _ ≤ ((n+2)^(k+4))^a := Nat.pow_le_pow_left (latticeInputCode_power hm hr hL hT) a
    _ = _ := (pow_mul _ _ _).symm

end ContinuumCoulomb.QuantumCoefficientPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial powers for the actual history coefficients. These
bounds are in the retained history-qubit count, not in an auxiliary circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory
open QuantumCoefficientPrograms

theorem parameterEnvelope_power (rounds : ℕ) : ∃ k : ℕ, ∀ n,
    parameterEnvelope rounds n ≤ (n+2)^k := by
  let p : Polynomial ℕ := Polynomial.X+8192*Polynomial.X+
    128*(14+288*((14*(Polynomial.X+1)+8)*Polynomial.X))+
    Polynomial.C (60*(rounds+9))*(Polynomial.X+1)+1
  obtain ⟨k,hk⟩ := natPolynomial_power_bound p
  refine ⟨k,fun n => ?_⟩
  simpa only [p,parameterEnvelope,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_natCast,Polynomial.eval_ofNat,
    Polynomial.eval_one] using hk n

theorem termCount_bound (c : QMACircuit) : termCount c ≤ 8192*qubitCount c := by
  rw [termCount_eq,qubitCount_eq]
  omega

theorem parameters_le_envelope (rounds : ℕ) (c : QMACircuit) :
    qubitCount c ≤ parameterEnvelope rounds (qubitCount c) ∧
    termCount c ≤ parameterEnvelope rounds (qubitCount c) ∧
    coefficientBudget c ≤ parameterEnvelope rounds (qubitCount c) ∧
    finalPrecision rounds c ≤ parameterEnvelope rounds (qubitCount c) := by
  have hwork : c.work+1 ≤ qubitCount c+1 := by rw [qubitCount_eq]; omega
  have htime : c.gates.length ≤ qubitCount c := by rw [qubitCount_eq]; omega
  have ht := termCount_bound c
  have hb : coefficientBudget c ≤
      128*(14+288*((14*(qubitCount c+1)+8)*qubitCount c)) := by
    unfold coefficientBudget
    gcongr
  have hp : finalPrecision rounds c ≤ 60*(rounds+9)*(qubitCount c+1) := by
    unfold finalPrecision
    gcongr
  unfold parameterEnvelope
  omega

theorem parameters_power (rounds : ℕ) : ∃ k : ℕ, ∀ c : QMACircuit,
    qubitCount c ≤ (qubitCount c+2)^k ∧
    termCount c ≤ (qubitCount c+2)^k ∧
    coefficientBudget c ≤ (qubitCount c+2)^k ∧
    finalPrecision rounds c ≤ (qubitCount c+2)^k := by
  obtain ⟨k,hk⟩ := parameterEnvelope_power rounds
  refine ⟨k,fun c => ?_⟩
  obtain ⟨h₁,h₂,h₃,h₄⟩ := parameters_le_envelope rounds c
  exact ⟨h₁.trans (hk _),h₂.trans (hk _),h₃.trans (hk _),h₄.trans (hk _)⟩

theorem historyCoefficientBudget_power (rounds : ℕ) : ∃ k : ℕ, ∀ c : QMACircuit,
    historyCoefficientBudget c (finalPrecision rounds c) ≤ (qubitCount c+2)^k := by
  obtain ⟨a,ha⟩ := parameters_power rounds
  obtain ⟨b,hb⟩ := QuantumCoefficientEnvelopeProgram.polynomial_bound
  refine ⟨(a+4)*b,fun c => ?_⟩
  obtain ⟨hn,hm,hB,hN⟩ := ha c
  exact lattice_function_power hb hn hm hB hN

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawOutputSize
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear size bounds for the actual emitted four-spin bond list, before
fixed-round degree reduction. All zero-weight entries are counted. -/

noncomputable section
namespace ContinuumCoulomb

private theorem flatten_map_length_bound {α β : Type} (xs : List α) (f : α → List β)
    (K : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ K) :
    (xs.map f).flatten.length ≤ K*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith

namespace QuantumRawExchange

theorem fullBonds_length (n k : ℕ) (r : ℚ) (xs : List Raw) :
    (fullBonds (n,(k,r),xs)).length ≤ 6*n+22*xs.length := by
  have hp : (penalty n r).length ≤ 6*n := by
    simpa only [penalty,List.length_range] using
      flatten_map_length_bound (List.range n) (penaltyBlock r) 6
        (by intro i hi; simp only [penaltyBlock,List.length_ofFn]; exact le_rfl)
  have ht : (termBondsList ((k,r),xs)).length ≤ 22*xs.length :=
    flatten_map_length_bound xs (fun t => bonds ((k,r),t)) 22 (fun _ _ => bonds_length _)
  simpa only [fullBonds,List.length_append] using Nat.add_le_add hp ht

theorem compile_length (n N : ℕ) (xs : List Raw) :
    (compile (n,N,xs)).1.length ≤ 6*n+22*xs.length :=
  fullBonds_length n (bits (n,N,xs)) (scale N xs) xs

end QuantumRawExchange

namespace QuantumOrderedLabelCompile

theorem rawEntries_length (x : Input) : (rawEntries x).length = 12544*x.2.2.length := by
  simp only [rawEntries,Function.comp_apply,classify,List.length_map,labelEntries]
  exact QuantumOrderedLabelPipeline.output_length x

theorem output_length (x : Input) :
    (output x).1.length ≤ 6*(x.2.1+3717*x.2.2.length)+22*(12544*x.2.2.length) := by
  have h := QuantumRawExchange.compile_length (outputCount x) x.1 (rawEntries x)
  rw [rawEntries_length] at h
  simpa only [output,Function.comp_apply,rawInput,outputCount,
    QuantumOrderedLabelPipeline.output_qubits] using h

end QuantumOrderedLabelCompile

namespace QuantumPaddedLabelProgram
open QuantumOrderedSourceIndex

theorem historyOutput_length (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    (historyOutput c hT N).1.length ≤
      6*(qubitCount c+3717*termCount c)+22*(12544*termCount c) := by
  have h := QuantumOrderedLabelCompile.output_length (historyInput c hT N)
  simpa only [historyOutput,historyInput,sourceEntries_length] using h

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear size and box bounds for the exact spatial graph before routing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumPaddedLabelProgram QuantumForkList

theorem history_bonds_linear (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    (historyOutput c hT N).1.length ≤ rawBondFactor*qubitCount c := by
  have h := historyOutput_length c hT N
  have hm := termCount_bound c
  calc
    _ ≤ 6*(qubitCount c+3717*termCount c)+22*(12544*termCount c) := h
    _ ≤ 6*(qubitCount c+3717*(8192*qubitCount c))+
        22*(12544*(8192*qubitCount c)) := by gcongr
    _ = _ := by unfold rawBondFactor; ring

theorem model_size_linear (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).n+Fintype.card (model c hc hT hne N).Term ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c) := by
  have h := (input c hc hT hne N).model_size
  rw [input_n,historyQubits_eq,input_bonds] at h
  have hb := history_bonds_linear (qmaSparseCircuit c) hT N
  have hm := termCount_bound (qmaSparseCircuit c)
  calc
    _ ≤ 4*(qubitCount (qmaSparseCircuit c)+3717*termCount (qmaSparseCircuit c))+
        5*(historyOutput (qmaSparseCircuit c) hT N).1.length+
        12*historyDegree*(historyOutput (qmaSparseCircuit c) hT N).1.length := h
    _ ≤ 4*(qubitCount (qmaSparseCircuit c)+3717*(8192*qubitCount (qmaSparseCircuit c)))+
        5*(rawBondFactor*qubitCount (qmaSparseCircuit c))+
        12*historyDegree*(rawBondFactor*qubitCount (qmaSparseCircuit c)) := by gcongr
    _ = _ := by unfold spatialSizeFactor; ring

theorem model_rows_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).rows ≤ qubitCount (qmaSparseCircuit c) := by
  rw [model,SpatialInput.model_rows,qubitCount_eq]
  change (qmaNearestCircuit c).gates.length ≤
    3*(qmaSparseCircuit c).gates.length+
      2*(c.work+(qmaNearestCircuit c).gates.length*(c.work+1))+8
  nlinarith

theorem model_width_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).width ≤ qubitCount (qmaSparseCircuit c) := by
  rw [model,SpatialInput.model_width,qubitCount_eq]
  change c.work ≤ 3*(qmaSparseCircuit c).gates.length+
    2*(c.work+(qmaNearestCircuit c).gates.length*(c.work+1))+8
  omega

theorem model_box_bound {A B n : ℕ} (M : QMASpatialExchangeModel A B)
    (hr : M.rows ≤ n) (hw : M.width ≤ n) :
    256*M.bufferedWidth ≤ boxFactor A B*(n+1) ∧
    256*M.bufferedHeight ≤ boxFactor A B*(n+1) := by
  constructor
  · calc
      _ = 256*(8*(9*B+9))*A*(M.rows+1) := by unfold QMASpatialExchangeModel.bufferedWidth; ring
      _ ≤ 256*(8*(9*B+9))*(A+1)*(n+1) := by gcongr; omega
      _ = _ := rfl
  · calc
      _ = 256*(8*(9*B+9))*1*(M.width+1) := by unfold QMASpatialExchangeModel.bufferedHeight; ring
      _ ≤ 256*(8*(9*B+9))*(A+1)*(n+1) := by gcongr; omega
      _ = _ := rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGeometryPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform power bounds all finite geometric inputs of the actual
history-to-lattice coefficient program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumForkList QuantumPaddedLabelProgram

attribute [local irreducible] spatialDensity

private theorem geometryEnvelope_parts (A B D R n : ℕ) :
    rawBondFactor*n ≤ geometryEnvelope A B D R n ∧
    spatialSizeFactor D*n ≤ geometryEnvelope A B D R n ∧
    spatialSizeFactor D*n*R ≤ geometryEnvelope A B D R n ∧
    boxFactor A B*(n+1) ≤ geometryEnvelope A B D R n := by
  unfold geometryEnvelope
  omega

theorem geometryEnvelope_power (A B D R : ℕ) : ∃ k : ℕ, ∀ n,
    geometryEnvelope A B D R n ≤ (n+2)^k := by
  let p : Polynomial ℕ := Polynomial.C rawBondFactor*Polynomial.X+
    Polynomial.C (spatialSizeFactor D)*Polynomial.X+
    Polynomial.C (spatialSizeFactor D*R)*Polynomial.X+
    Polynomial.C (boxFactor A B)*(Polynomial.X+1)+1
  obtain ⟨k,hk⟩ := natPolynomial_power_bound p
  refine ⟨k,fun n => ?_⟩
  have h := hk n
  simp only [p,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (unfold geometryEnvelope; ring)

private theorem crossing_card_bound {A B R : ℕ} (M : QMASpatialExchangeModel A B)
    (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (hR : QMASpatialExchangeModel.routeLengthBound A B=R) :
    (M.portRouteData hA hd).crossingCells.card ≤ Fintype.card M.Term*R := by
  have h := (M.portRouteData hA hd).crossingCells_card_le (M.bufferedPath_length hd)
  change _ ≤ Fintype.card M.Term*QMASpatialExchangeModel.routeLengthBound A B at h
  rw [hR] at h
  exact h

theorem model_geometry_power : ∃ k : ℕ, ∀ (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ),
    (input c hc hT hne N).bonds.length ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    Fintype.card (model c hc hT hne N).Term ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    ((model c hc hT hne N).portRouteData finalDensity_pos
      (model_degree c hc hT hne N)).crossingCells.card ≤
        (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne N).bufferedWidth ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne N).bufferedHeight ≤ (qubitCount (qmaSparseCircuit c)+2)^k := by
  obtain ⟨k,hk⟩ := geometryEnvelope_power (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree) historyDegree routeRounds
  refine ⟨k,fun c hc hT hne N => ?_⟩
  have hb := history_bonds_linear (qmaSparseCircuit c) hT N
  rw [← input_bonds c hc hT hne N] at hb
  have hs := model_size_linear c hc hT hne N
  have he : Fintype.card (model c hc hT hne N).Term ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c) := by omega
  have hx := model_box_bound (model c hc hT hne N)
    (model_rows_bound c hc hT hne N) (model_width_bound c hc hT hne N)
  have hr := crossing_card_bound (model c hc hT hne N) finalDensity_pos
    (model_degree c hc hT hne N) routeRounds_eq
  have hr' : ((model c hc hT hne N).portRouteData finalDensity_pos
      (model_degree c hc hT hne N)).crossingCells.card ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c)*routeRounds :=
    hr.trans (Nat.mul_le_mul_right routeRounds he)
  have hp := hk (qubitCount (qmaSparseCircuit c))
  obtain ⟨hb',he',hr'',hx'⟩ := geometryEnvelope_parts (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree) historyDegree routeRounds
    (qubitCount (qmaSparseCircuit c))
  exact ⟨hb.trans (hb'.trans hp),he.trans (he'.trans hp),hr'.trans (hr''.trans hp),
    hx.1.trans (hx'.trans hp),hx.2.trans (hx'.trans hp)⟩

theorem outputCoefficientNat_one (m D L T : ℕ) : 1 ≤ outputCoefficientNat m D L T := by
  have h (M L T k : ℕ) (hL : 1 ≤ L) : 1 ≤ envelopeNat M L T k := by
    induction k with
    | zero => exact hL
    | succ k ih => dsimp only [envelopeNat,coefficientNat]; omega
  exact h _ _ _ _ (by dsimp only [coefficientNat]; omega)

theorem outputCoefficientNat_of_power {D a n k m L T : ℕ}
    (h : ∀ x : QuantumCoefficientPrograms.Input, outputCoefficientNat x.1 D x.2.1 x.2.2 ≤
      ((QuantumCoefficientPrograms.inputCode x).length+2)^a)
    (hm : m ≤ (n+2)^k) (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    outputCoefficientNat m D L T ≤ (n+2)^((k+4)*a) :=
  QuantumCoefficientPrograms.input_function_power h hm hL hT

theorem latticeBound_of_power {D a n k m r L T : ℕ}
    (h : ∀ x : QuantumCoefficientPrograms.LatticeInput,
      QuantumCoefficientPrograms.latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2 ≤
        ((QuantumCoefficientPrograms.latticeInputCode x).length+2)^a)
    (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    QuantumCoefficientPrograms.latticeBound D m r L T ≤ (n+2)^((k+4)*a) :=
  QuantumCoefficientPrograms.lattice_function_power h hm hr hL hT

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySourcePowers
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal coefficient programs and the exact geometry admit a common
polynomial exponent, uniform over verifier circuits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory QuantumForkList QuantumPaddedLabelProgram
open QuantumCoefficientPrograms

theorem source_data_power_oai : ∃ k : ℕ, ∀ (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []), ∃ L : ℕ,
    1 ≤ L ∧ (model c hc hT hne (latticePrecision c)).exchangeGraph.CoefficientBound L ∧
    256*(model c hc hT hne (latticePrecision c)).bufferedWidth ≤
      (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne (latticePrecision c)).bufferedHeight ≤
      (qubitCount (qmaSparseCircuit c)+2)^k ∧
    latticeBound routeRounds (Fintype.card (model c hc hT hne (latticePrecision c)).Term)
      ((model c hc hT hne (latticePrecision c)).portRouteData finalDensity_pos
        (model_degree c hc hT hne (latticePrecision c))).crossingCells.card L (latticePrecision c) ≤
          (qubitCount (qmaSparseCircuit c)+2)^k := by
  obtain ⟨g,hg⟩ := model_geometry_power
  obtain ⟨a,ha⟩ := historyCoefficientBudget_power totalRounds
  obtain ⟨b,hb⟩ := parameters_power totalRounds
  obtain ⟨d,hd⟩ := outputCoefficientNat_power historyDegree
  obtain ⟨e,he⟩ := latticeBound_power routeRounds
  let k₁ := g+a+b
  let k₂ := k₁+(k₁+4)*d
  refine ⟨k₂+(k₂+4)*e,fun c hc hT hne => ?_⟩
  let n := qubitCount (qmaSparseCircuit c)
  let N := latticePrecision c
  let L := outputCoefficientNat (input c hc hT hne N).bonds.length historyDegree
    (historyCoefficientBudget (qmaSparseCircuit c) N) N
  have lift {i j : ℕ} (h : i ≤ j) : (n+2)^i ≤ (n+2)^j :=
    pow_le_pow_right₀ (by omega : 1 ≤ n+2) h
  obtain ⟨hm,ht,hr,hx,hy⟩ := hg c hc hT hne N
  have hraw := ha (qmaSparseCircuit c)
  have hN := (hb (qmaSparseCircuit c)).2.2.2
  have hL : L ≤ (n+2)^((k₁+4)*d) := outputCoefficientNat_of_power hd
    (hm.trans (lift (by dsimp [k₁]; omega)))
    (hraw.trans (lift (by dsimp [k₁]; omega)))
    (hN.trans (lift (by dsimp [k₁]; omega)))
  have hf : latticeBound routeRounds (Fintype.card (model c hc hT hne N).Term)
      ((model c hc hT hne N).portRouteData finalDensity_pos
        (model_degree c hc hT hne N)).crossingCells.card L N ≤
      (n+2)^((k₂+4)*e) := latticeBound_of_power he
    (ht.trans (lift (by dsimp [k₂,k₁]; omega)))
    (hr.trans (lift (by dsimp [k₂,k₁]; omega)))
    (hL.trans (lift (by dsimp [k₂]; omega)))
    (hN.trans (lift (by dsimp [k₂,k₁]; omega)))
  exact ⟨L,outputCoefficientNat_one _ _ _ _,model_coefficientBound c hc hT hne N,
    hx.trans (lift (by dsimp [k₂,k₁]; omega)),
    hy.trans (lift (by dsimp [k₂,k₁]; omega)),
    hf.trans (lift (by omega))⟩

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumHistorySpatial.source_data_power_oai := @OAI.ContinuumCoulomb.QuantumHistorySpatial.source_data_power_oai
