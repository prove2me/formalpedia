-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:10:08.695283+00:00
-- url     : https://prove2.me/submissions/b330d6dc-f6c9-455b-a08a-2fc04be5ad10

import Mathlib
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Model_corrected_denote
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_localScan_localFactor

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpResidueInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable inversion by finite-field powering and nilpotent correction

The algorithm uses only scalar additions and multiplications, with explicit
finite loops. It constructs the entire inverse-difference table needed by CRT.
Its counters are ring-operation counts, not an assertion of machine time.
-/

namespace SubexponentialSAT.SubexpResidueInverse

open scoped BigOperators

section Algorithm

variable {A : Type*} [CommRing A]

theorem geometricHorner_value (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).1 = ∑ i ∈ Finset.range n, z ^ i := by
  induction n with
  | zero => simp [geometricHornerWithCost]
  | succ n ih => simpa [geometricHornerWithCost, ih] using (@geom_sum_succ A _ z n).symm

theorem inverseWithCost_value (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).1 =
      NilpotentDefect.geometricInverse a (a ^ (q - 2)) μ := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_value,
    geometricHorner_value, NilpotentDefect.geometricInverse]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end Algorithm

end SubexponentialSAT.SubexpResidueInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem hornerValue_decode {C A : Type*} [CommRing A] (decode : C → A)
    (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (z one seed : C) (hone : decode one = 1) (hseed : decode seed = 0) (n : ℕ) :
    decode ((hornerValue mulOp addOp z one)^[n] seed) =
      ∑ i ∈ Finset.range n, decode z ^ i := by
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [hornerValue, ha, hm, hone, ih]
      simpa only [mul_comm] using (@geom_sum_succ A _ (decode z) n).symm

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem inverseValue_decode {C A : Type*} [CommRing A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (zero one minusOne a : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (q precision : ℕ) :
    decode (inverseValue mulOp addOp zero one minusOne a (q-2) precision) =
      (SubexponentialSAT.SubexpResidueInverse.inverseWithCost q precision (decode a)).1 := by
  rw [SubexponentialSAT.SubexpResidueInverse.inverseWithCost_value]
  simp only [inverseValue, hm, hornerValue_decode decode mulOp addOp hm ha _ one zero ho hz,
    iterate_mul_decode decode mulOp hm, ho, one_mul, ha, hn,
    SubexponentialSAT.NilpotentDefect.geometricInverse]
  have he : decode a ^ (q - 2) * decode a * -1 + 1 = 1 - decode a * decode a ^ (q - 2) := by ring
  rw [he, mul_comm]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCorrectionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic invariants for the fixed-width local CRT preparation. Every
intermediate polynomial product may be truncated to D coefficients. The
constant coefficient is inverted once by the executable residue algorithm. -/

namespace SubexponentialSAT.SubexpLocalCorrectionAlgebra

open Polynomial
open scoped BigOperators

theorem padded_denote {C R : Type*} [CommRing R]
    (decode : C → R) (zero low high : C) (hz : decode zero = 0) (D : ℕ) :
    PolynomialAlgorithm.denote ((padded zero low high D).map decode) =
      Truncation.trunc D (Polynomial.C (decode low) + X * Polynomial.C (decode high)) := by
  cases D with
  | zero => simp [padded, SubexpConvolutionAlgebra.trunc_zero_order]
  | succ D =>
      cases D with
      | zero =>
          ext k
          cases k <;> simp [padded, Truncation.coeff_trunc, PolynomialAlgorithm.denote_cons
            ]
      | succ n =>
          simp only [padded, List.map_cons, List.map_replicate, hz,
            PolynomialAlgorithm.denote_cons, SubexpConvolutionAlgebra.denote_replicate_zero,
            mul_zero, add_zero]
          ext k
          cases k with
          | zero => simp [Truncation.coeff_trunc]
          | succ k => cases k <;> simp [Truncation.coeff_trunc ]

end SubexponentialSAT.SubexpLocalCorrectionAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

variable {A C : Type*}

theorem run_after_skip (f : A → C → A) (cs : List C) (a : A) :
    (run f cs ⟨a, [], false⟩).value = cs.foldl f a := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simpa [run, next] using ih (f a c)

/-- The physical index/marker traversal includes exactly all nodes except the
indexed one. An out-of-range index simply includes all nodes. -/
theorem run_skip_index (f : A → C → A) (cs : List C) (skip : List Bool) (a : A) :
    (run f cs ⟨a, skip, true⟩).value = (cs.eraseIdx skip.length).foldl f a := by
  induction cs generalizing skip a with
  | nil => simp [run]
  | cons c cs ih =>
    cases skip with
    | nil => simpa [run, next] using run_after_skip f cs a
    | cons bit rest => simpa [run, next] using ih rest (f a c)

end SubexponentialSAT.SubexpNodeScanControl

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length array instantiation of the local Hermite algebra. The
constructor and head split are exact identities of physical bit strings. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

theorem coefficients_eq_padded {C : Type*} (z low high : C) (J : ℕ) :
    Constructor.coefficients z low high J = SubexponentialSAT.SubexpLocalCorrectionAlgebra.padded z low high J := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> rfl

theorem padded_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z low high : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (padded z low high J) =
      Truncation.trunc J (C (decode low) + X*C (decode high)) := by
  change SubexponentialSAT.PolynomialAlgorithm.denote ((Constructor.coefficients z low high J).map decode) = _
  rw [coefficients_eq_padded]
  exact SubexponentialSAT.SubexpLocalCorrectionAlgebra.padded_denote decode z low high hz J

theorem constant_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z a : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (constant z a J) = Truncation.trunc J (C (decode a)) := by
  simpa only [constant, hz, map_zero, mul_zero, add_zero] using padded_denote decode z a z hz J

theorem linear_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z one a : Coeff B d)
    (hz : decode z = 0) (ho : decode one = 1) (J : ℕ) :
    denote decode (linear z one a J) = Truncation.trunc J (X + C (decode a)) := by
  simpa only [linear, ho, map_one, mul_one, add_comm] using padded_denote decode z a one hz J

theorem mul_denote {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.mul ops.program P Q) =
      Truncation.trunc J (denote ops.decode P * denote ops.decode Q) :=
  DensePolynomialProgram.result_correct ops J P.1 Q.1

theorem head_decode {B d J : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (P : Poly B d J) (c : Coeff B d)
    (rest : List (Coeff B d)) (hP : P.1 = c :: rest) :
    decode c = (denote decode P).coeff 0 := by
  simp [denote, hP, SubexponentialSAT.PolynomialAlgorithm.denote_cons]

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramModelCorrectness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

variable {B d J : ℕ} {R : Type*} [CommRing R]

theorem inverseCoefficient_decode (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (hn : ops.decode minusOne = -1) (q t : ℕ) :
    ops.decode (inverseCoefficient ops minusOne c q t) =
      (SubexponentialSAT.SubexpResidueInverse.inverseWithCost q t (ops.decode c)).1 := by
  exact inverseValue_decode ops.decode (scalarMul ops) (scalarAdd ops)
    ops.mul_correct ops.add_correct ops.zeroRun.1 ops.oneRun.1 minusOne c
    ops.zero_correct ops.one_correct hn q t

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical local factor and correction have the canonical Hermite
meaning independently of the encoded representative of their head word. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

theorem factorCode_denote (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d) (J : ℕ) (i : Fin Q) :
    Model.denote ops.decode (factorCode ops minusOne nodes J i) =
      Truncation.trunc J (TruncatedInverse.localFactor (fun j => ops.decode (nodes j)) J i) := by
  have hone : Model.denote ops.decode (Model.constant ops.zeroRun.1 ops.oneRun.1 J) =
      Truncation.trunc J (1 : R[X]) := by
    simpa [ops.one_correct] using Model.constant_denote ops.decode ops.zeroRun.1 ops.oneRun.1 ops.zero_correct J
  have h := localScan_localFactor ops.decode (Model.denote ops.decode)
    (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
    ops.mul_correct ops.add_correct J
    (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J)
    (Model.mul_denote ops) (fun c => Model.linear_denote ops.decode ops.zeroRun.1 ops.oneRun.1 c
      ops.zero_correct ops.one_correct J) minusOne hn nodes i
    (List.replicate i.val false) (by simp) (Model.constant ops.zeroRun.1 ops.oneRun.1 J) hone
  simpa only [SubexpNodeScanControl.run_skip_index, List.length_replicate, factorCode] using h

theorem corrected_denote_oai (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d)
    (q t J : ℕ) (jets : Fin Q → Model.Poly B d J) (i : Fin Q)
    (c : Coeff B d) (rest : List (Coeff B d))
    (hhead : (factorCode ops minusOne nodes J i).1 = c :: rest) :
    Model.denote ops.decode (Model.corrected ops minusOne c q t
      (factorCode ops minusOne nodes J i) (jets i)) =
      TruncatedInverse.correction (fun j => ops.decode (nodes j)) J
        (inverse (fun j => ops.decode (nodes j)) q t J)
        (fun j => Model.denote ops.decode (jets j)) i := by
  have hf := factorCode_denote ops minusOne hn nodes J i
  have hc := Model.head_decode ops.decode (factorCode ops minusOne nodes J i) c rest hhead
  rw [hf] at hc
  rw [Model.corrected_denote ops minusOne c q t _ _ _ hn hf,
    Model.inverseCoefficient_decode ops minusOne c hn q t, hc]
  rfl

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote_oai.{u_1}
