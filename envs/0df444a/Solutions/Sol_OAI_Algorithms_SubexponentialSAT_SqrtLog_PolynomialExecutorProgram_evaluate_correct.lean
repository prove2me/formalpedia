-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:06:54.069759+00:00
-- url     : https://prove2.me/submissions/57af6273-902e-4b2c-b2f7-9c0f9a82db12

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S136

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PolynomialAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable dense univariate polynomial arithmetic

Lists store coefficients from constant term upwards. Trailing zeroes are allowed.
The instrumented algorithms return their value and the number of coefficient-ring
additions and multiplications they actually perform. List manipulation and primitive
bit costs are separate. Recursive results are bound once and reused.
-/

namespace SubexponentialSAT.PolynomialAlgorithm

variable {R : Type*}

section Algorithms

variable [Semiring R]

theorem coeff_truncate (D : ℕ) (P : List R) (n : ℕ) :
    coeff (truncate D P) n = if n < D then coeff P n else 0 := by
  induction D generalizing P n with
  | zero => simp [truncate, coeff]
  | succ D ih =>
      cases P with
      | nil => simp [truncate, coeff]
      | cons a P =>
          cases n with
          | zero => simp [truncate, coeff]
          | succ n => simpa [truncate, coeff] using ih P n

end Algorithms

section Semantics

variable [CommSemiring R]

theorem coeff_denote_truncate (D : ℕ) (P : List R) (n : ℕ) :
    (denote (truncate D P)).coeff n =
      if n < D then (denote P).coeff n else 0 := by
  simp only [coeff_denote, coeff_truncate]

@[simp] theorem denote_truncate (D : ℕ) (P : List R) :
    denote (truncate D P) = SubexponentialSAT.Truncation.trunc D (denote P) := by
  ext n
  simp only [coeff_denote_truncate, SubexponentialSAT.Truncation.coeff_trunc]

end Semantics

end SubexponentialSAT.PolynomialAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dense univariate arithmetic through represented coefficient callbacks

Code words need no ring structure. Every scalar operation is a call to the
supplied implementation, and the returned counters are added along the actual
execution. These are callback counters, not a primitive-machine runtime theorem.
-/

namespace SubexponentialSAT.SubexpDensePolynomial

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

theorem addRun_correct (P Q : List C) :
    decodeList ops (addRun ops P Q).1 =
      PolynomialAlgorithm.add (decodeList ops P) (decodeList ops Q) := by
  induction P generalizing Q with
  | nil => simp [addRun, decodeList, PolynomialAlgorithm.add, PolynomialAlgorithm.addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addRun, decodeList, PolynomialAlgorithm.add, PolynomialAlgorithm.addWithCost]
      | cons b Q =>
          simp only [addRun, decodeList, List.map_cons, ops.add_correct]
          change (ops.decode a + ops.decode b) :: decodeList ops (addRun ops P Q).1 = _
          rw [ih]
          rfl

@[simp] theorem addRun_length (P Q : List C) :
    (addRun ops P Q).1.length = max P.length Q.length := by
  rw [← decodeList_length ops, addRun_correct, PolynomialAlgorithm.length_add]
  simp

end SubexponentialSAT.SubexpDensePolynomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial semantics of the triangular update schedule used by the
actual convolution controller. This file assigns no execution costs. -/

namespace SubexponentialSAT.SubexpConvolutionAlgebra

open Polynomial
open TruncatedConvolution

section Algebra

variable {R : Type*} [CommSemiring R]

theorem denote_modify_add (acc : List R) (i : ℕ) (a : R) (hi : i < acc.length) :
    PolynomialAlgorithm.denote (acc.modify i (fun c => a + c)) = PolynomialAlgorithm.denote acc + monomial i a := by
  induction acc generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
      cases i with
      | zero =>
          simp only [List.modify_zero_cons, PolynomialAlgorithm.denote_cons,
            monomial_zero_left, map_add]
          ring
      | succ i =>
          simp only [List.modify_succ_cons, PolynomialAlgorithm.denote_cons]
          rw [ih i (by simpa using hi), mul_add, X_mul_monomial]
          ring

theorem denote_addProduct (i : ℕ) (a b : R) (acc : List R) (hi : i < acc.length) :
    PolynomialAlgorithm.denote (addProduct (· + ·) (· * ·) i a b acc) =
      PolynomialAlgorithm.denote acc + monomial i (a * b) :=
  denote_modify_add acc i (a * b) hi

theorem denote_row (a : R) (i : ℕ) (Q acc : List R)
    (hfit : i + Q.length ≤ acc.length) :
    PolynomialAlgorithm.denote (row (· + ·) (· * ·) a i Q acc) =
      PolynomialAlgorithm.denote acc + X ^ i * C a * PolynomialAlgorithm.denote Q := by
  induction Q generalizing i acc with
  | nil => simp [row]
  | cons b bs ih =>
      rw [row, ih]
      · rw [denote_addProduct i a b acc (by simp only [List.length_cons] at hfit; omega),
          PolynomialAlgorithm.denote_cons, ← C_mul_X_pow_eq_monomial, map_mul, pow_succ]
        ring
      · simp only [addProduct_length]
        simp only [List.length_cons] at hfit
        omega

theorem trunc_C_mul (D : ℕ) (a : R) (P : Polynomial R) :
    Truncation.trunc D (C a * P) = C a * Truncation.trunc D P := by
  ext n
  by_cases hn : n < D <;> simp [Truncation.coeff_trunc, coeff_C_mul, hn]

theorem trunc_X_mul (D : ℕ) (P : Polynomial R) :
    Truncation.trunc (D + 1) (X * P) = X * Truncation.trunc D P := by
  ext n
  cases n <;> simp [Truncation.coeff_trunc, coeff_X_mul]

theorem trunc_zero_order (P : Polynomial R) : Truncation.trunc 0 P = 0 := by
  ext n
  simp

theorem denote_rows (Q : List R) (i fuel : ℕ) (P acc : List R)
    (hfit : i + fuel ≤ acc.length) :
    PolynomialAlgorithm.denote (rows (· + ·) (· * ·) Q i fuel P acc) =
      PolynomialAlgorithm.denote acc + X ^ i * Truncation.trunc fuel (PolynomialAlgorithm.denote P * PolynomialAlgorithm.denote Q) := by
  induction fuel generalizing i P acc with
  | zero => simp [rows, trunc_zero_order]
  | succ fuel ih =>
      cases P with
      | nil => simp [rows]
      | cons a rest =>
          rw [rows, ih]
          · rw [denote_row]
            · rw [show PolynomialAlgorithm.denote (Q.take (fuel + 1)) =
                  Truncation.trunc (fuel + 1) (PolynomialAlgorithm.denote Q) from
                    PolynomialAlgorithm.denote_truncate (fuel + 1) Q]
              simp only [PolynomialAlgorithm.denote_cons, add_mul, mul_assoc,
                Truncation.trunc_add, trunc_C_mul, trunc_X_mul, pow_succ]
              ring
            · simp only [List.length_take]
              omega
          · simp only [row_length]
            omega

/-- The actual schedule computes the degree-below-D part of the product,
with exactly D stored coefficients, including trailing zeros. -/
theorem run_denote (D : ℕ) (P Q : List R) :
    PolynomialAlgorithm.denote (run 0 (· + ·) (· * ·) D P Q) =
      Truncation.trunc D (PolynomialAlgorithm.denote P * PolynomialAlgorithm.denote Q) := by
  rw [run, denote_rows Q 0 D P _ (by simp)]
  simp

end Algebra

section Decode

variable {C R : Type*} [CommSemiring R]
    (decode : C → R) (add mul : C → C → C)
    (hadd : ∀ a b, decode (add a b) = decode a + decode b)
    (hmul : ∀ a b, decode (mul a b) = decode a * decode b)

include hadd hmul

theorem map_addProduct (i : ℕ) (a b : C) (acc : List C) :
    (addProduct add mul i a b acc).map decode =
      addProduct (· + ·) (· * ·) i (decode a) (decode b) (acc.map decode) := by
  induction acc generalizing i with
  | nil => simp [addProduct]
  | cons c cs ih =>
      cases i with
      | zero => simp [addProduct, hadd, hmul]
      | succ i => simpa [addProduct] using congrArg (decode c :: ·) (ih i)

theorem map_row (a : C) (i : ℕ) (Q acc : List C) :
    (row add mul a i Q acc).map decode =
      row (· + ·) (· * ·) (decode a) i (Q.map decode) (acc.map decode) := by
  induction Q generalizing i acc with
  | nil => rfl
  | cons b bs ih =>
      simp only [row, List.map_cons, ih, map_addProduct decode add mul hadd hmul]

theorem map_rows (Q : List C) (i fuel : ℕ) (P acc : List C) :
    (rows add mul Q i fuel P acc).map decode =
      rows (· + ·) (· * ·) (Q.map decode) i fuel (P.map decode) (acc.map decode) := by
  induction fuel generalizing i P acc with
  | zero => rfl
  | succ fuel ih =>
      cases P with
      | nil => rfl
      | cons a rest =>
          simp only [rows, List.map_cons, ih, map_row decode add mul hadd hmul, List.map_take]

theorem run_correct (zero : C) (hzero : decode zero = 0) (D : ℕ) (P Q : List C) :
    PolynomialAlgorithm.denote ((run zero add mul D P Q).map decode) =
      Truncation.trunc D (PolynomialAlgorithm.denote (P.map decode) * PolynomialAlgorithm.denote (Q.map decode)) := by
  simp only [run, map_rows decode add mul hadd hmul, List.map_replicate, hzero]
  exact run_denote D (P.map decode) (Q.map decode)

end Decode

end SubexponentialSAT.SubexpConvolutionAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramMul
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dense convolution and old-compatible cached-array services.
The local pair premise is an actual fixed-command trace; all scans, writes,
copies, counter steps, and final halts are included by the audited controller.
A concrete native ring-pair instantiation is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*}

theorem result_correct [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (P Q : List C) :
    SubexponentialSAT.PolynomialAlgorithm.denote ((result ops.program J P Q).map ops.decode) =
      SubexponentialSAT.Truncation.trunc J (SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode) *
        SubexponentialSAT.PolynomialAlgorithm.denote (Q.map ops.decode)) := by
  apply SubexponentialSAT.SubexpConvolutionAlgebra.run_correct
  · exact ops.add_correct
  · exact ops.mul_correct
  · exact ops.zero_correct

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial meanings of the exact coefficient-list outputs. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost

theorem add_correct {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (P Q : List C) :
    SubexponentialSAT.PolynomialAlgorithm.denote ((SubexponentialSAT.SubexpDensePolynomial.addProgram ops.program P Q).1.map ops.decode) =
      SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode) +
        SubexponentialSAT.PolynomialAlgorithm.denote (Q.map ops.decode) := by
  rw [SubexponentialSAT.SubexpDensePolynomial.addProgram_run]
  have h := SubexponentialSAT.SubexpDensePolynomial.addRun_correct ops P Q
  change ((SubexponentialSAT.SubexpDensePolynomial.addRun ops P Q).1.map ops.decode) = _ at h
  rw [h, SubexponentialSAT.PolynomialAlgorithm.denote_add]
  rfl

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem trunc_degree_lt (D : ℕ) (f : A[X]) :
    (Truncation.trunc D f).degree < (D : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro n hn
  simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]

theorem X_pow_dvd_sub_trunc (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f - Truncation.trunc D f := by
  rw [X_pow_dvd_iff]
  intro n hn
  simp [Truncation.coeff_trunc, hn]

/-- Coefficient truncation and monic remainder are the same operation. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : A[X]) :
    Truncation.trunc D f = f %ₘ (X ^ D) := by
  nontriviality A
  have hself : Truncation.trunc D f %ₘ (X ^ D) = Truncation.trunc D f := by
    apply (modByMonic_eq_self_iff (monic_X.pow D)).2
    rw [degree_X_pow]
    exact trunc_degree_lt D f
  exact ((modByMonic_eq_of_dvd_sub (monic_X.pow D)
    (X_pow_dvd_sub_trunc D f)).trans hself).symm

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTruncatedGeometric
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Keeping every geometric-inverse intermediate below degree D preserves
the existing inverse formula. The loop itself is the already executable
`TruncatedInverse.geometricLoop`; these are its semantic invariants. -/

namespace SubexponentialSAT.SubexpTruncatedGeometric

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem trunc_mul_trunc (D : ℕ) (P Q : Polynomial R) :
    Truncation.trunc D (Truncation.trunc D P * Truncation.trunc D Q) =
      Truncation.trunc D (P * Q) := by
  have h₁ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D P) Q
  have h₂ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D Q)
    (Truncation.trunc D P)
  have h : (X : Polynomial R) ^ D ∣ P * Q - Truncation.trunc D P * Truncation.trunc D Q := by
    convert dvd_add h₁ h₂ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [TruncatedInverse.trunc_eq_modByMonic D (Truncation.trunc D P * Truncation.trunc D Q),
    TruncatedInverse.trunc_eq_modByMonic D (P * Q)]
  exact (Polynomial.modByMonic_eq_of_dvd_sub (monic_X.pow D) h).symm

end SubexponentialSAT.SubexpTruncatedGeometric

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePaddingSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-width bit padding and dense polynomial coefficients

The literal loader pads or truncates a flat payload to a whole number of
coefficient cells. This file identifies that operation at the cell level.
Preservation of a complete polynomial requires its degree to be below the
number of retained cells; this condition is explicit before any Taylor shift.
-/

namespace SubexponentialSAT.SubexpDensePaddingSpec

open ModularArithmetic

section Denotation

variable {C R : Type*} [CommSemiring R]
variable (decode : C → R) (zero : C) (hzero : decode zero = 0)

include hzero

theorem coeff_padCells (cellCount : ℕ) (xs : List C) (i : ℕ) :
    PolynomialAlgorithm.coeff ((padCells zero cellCount xs).map decode) i =
      if i < cellCount then PolynomialAlgorithm.coeff (xs.map decode) i else 0 := by
  induction cellCount generalizing xs i with
  | zero => simp [padCells, PolynomialAlgorithm.coeff]
  | succ n ih =>
      cases xs <;> cases i <;>
        simp only [padCells, List.map_nil, List.map_cons, PolynomialAlgorithm.coeff,
          hzero, Nat.zero_lt_succ, ite_true, if_true, Nat.succ_lt_succ_iff, ih, ite_self]

theorem denote_padCells (cellCount : ℕ) (xs : List C) :
    PolynomialAlgorithm.denote ((padCells zero cellCount xs).map decode) =
      Truncation.trunc cellCount (PolynomialAlgorithm.denote (xs.map decode)) := by
  ext i
  simp only [PolynomialAlgorithm.coeff_denote, Truncation.coeff_trunc,
    coeff_padCells decode zero hzero]

end Denotation

section Expressions

variable {B S R : Type*} [CommRing R]

/-- Truncated arithmetic is sound even if intermediate expressions have
higher degree than the final row. The local invariant can be fixed cell
length, so arithmetic laws are needed only on well-formed operands. -/
theorem evalWith_correct (cellCount : ℕ) (Good : S → Prop)
    (literal : B → S) (add mul : S → S → S)
    (denote : S → Polynomial R) (meaning : B → Polynomial R)
    (hliteral : ∀ b, Good (literal b) ∧
      denote (literal b) = Truncation.trunc cellCount (meaning b))
    (hadd : ∀ x y, Good x → Good y → Good (add x y) ∧
      denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, Good x → Good y → Good (mul x y) ∧
      denote (mul x y) = Truncation.trunc cellCount (denote x * denote y))
    (e : Algorithm.Expr B) :
    Good (evalWith literal add mul e) ∧
      denote (evalWith literal add mul e) =
        Truncation.trunc cellCount ((e.map meaning).eval) := by
  induction e with
  | lit b => exact hliteral b
  | add e f he hf =>
      obtain ⟨hg, hd⟩ := hadd _ _ he.1 hf.1
      refine ⟨hg, ?_⟩
      change denote (add (evalWith literal add mul e) (evalWith literal add mul f)) =
        Truncation.trunc cellCount ((e.map meaning).eval + (f.map meaning).eval)
      rw [hd, he.2, hf.2, Truncation.trunc_add]
  | mul e f he hf =>
      obtain ⟨hg, hd⟩ := hmul _ _ he.1 hf.1
      refine ⟨hg, ?_⟩
      change denote (mul (evalWith literal add mul e) (evalWith literal add mul f)) =
        Truncation.trunc cellCount ((e.map meaning).eval * (f.map meaning).eval)
      rw [hd, he.2, hf.2, SubexpTruncatedGeometric.trunc_mul_trunc]

end Expressions

end SubexponentialSAT.SubexpDensePaddingSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable coefficient-array meaning of the row postfix interpreter.
Literal padding and all arithmetic operate on stored coefficient words. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

theorem evaluate_correct_oai {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C)) :
    (evaluate ops.program J e).length = J ∧
      meaning ops (evaluate ops.program J e) =
        SubexponentialSAT.Truncation.trunc J ((e.map (meaning ops)).eval) := by
  apply SubexponentialSAT.SubexpDensePaddingSpec.evalWith_correct J (fun P : List C => P.length = J)
    (loadValue ops.program J) (addValue ops.program) (mulValue ops.program J)
    (meaning ops) (meaning ops)
  · intro P
    exact ⟨SubexponentialSAT.SubexpDensePaddingSpec.padCells_length _ _ _,
      SubexponentialSAT.SubexpDensePaddingSpec.denote_padCells ops.decode ops.zeroRun.1 ops.zero_correct J P⟩
  · intro P Q hP hQ
    refine ⟨?_, DensePolynomialProgram.add_correct ops P Q⟩
    change (SubexponentialSAT.SubexpDensePolynomial.addProgram ops.program P Q).1.length = J
    rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length, hP, hQ, Nat.max_self]
  · intro P Q _ _
    exact ⟨DensePolynomialProgram.result_length ops.program J P Q,
      DensePolynomialProgram.result_correct ops J P Q⟩

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct_oai.{u_1, u_2}
