-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:42:19.411722+00:00
-- url     : https://prove2.me/submissions/3f61511f-48ce-44ea-b6c7-f9fb2e8bfbd8

import Mathlib
import Definitions.Def_OAIQ081S022
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S100
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Model_add_denote

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
open SubexpTruncatedGeometric

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrectionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The jet loop runs J times independently of the scalar precision t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators
open SubexponentialSAT.SubexpTruncatedGeometric

 theorem truncatedHorner_denote {S R : Type*} [CommRing R]
    (J : ℕ) (zero one z : S) (mulOp addOp : S → S → S) (denote : S → R[X])
    (Z : R[X]) (hzero : denote zero = 0) (hone : denote one = Truncation.trunc J 1)
    (hz : denote z = Truncation.trunc J Z)
    (ha : ∀ a b, denote (addOp a b) = denote a + denote b)
    (hm : ∀ a b, denote (mulOp a b) = Truncation.trunc J (denote a * denote b)) (n : ℕ) :
    denote ((hornerValue mulOp addOp z one)^[n] zero) =
      Truncation.trunc J (∑ i ∈ Finset.range n, Z^i) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [hornerValue, ha, hm, ih, hz, hone, trunc_mul_trunc,
        ← Truncation.trunc_add]
      congr 1
      simpa only [mul_comm] using (@geom_sum_succ R[X] _ Z n).symm

theorem correctionValue_denote {S R : Type*} [CommRing R]
    (J : ℕ) (zero one negInverse inverse factor jet : S)
    (mulOp addOp : S → S → S) (denote : S → R[X]) (P Jet : R[X]) (a : R)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc J 1)
    (hneg : denote negInverse = Truncation.trunc J (C (-a)))
    (hinv : denote inverse = Truncation.trunc J (C a))
    (hfactor : denote factor = Truncation.trunc J P) (hjet : denote jet = Jet)
    (ha : ∀ x y, denote (addOp x y) = denote x + denote y)
    (hm : ∀ x y, denote (mulOp x y) = Truncation.trunc J (denote x * denote y)) :
    denote (correctionValue mulOp addOp zero one negInverse inverse factor jet J) =
      TruncatedInverse.correctedJet P Jet a J := by
  let z := addOp (mulOp factor negInverse) one
  have hz : denote z = Truncation.trunc J (1 - C a * P) := by
    dsimp [z]
    rw [ha, hm, hfactor, hneg, trunc_mul_trunc, hone, ← Truncation.trunc_add]
    congr 1
    simp only [map_neg]
    ring
  have hs := truncatedHorner_denote J zero one z mulOp addOp denote _ hzero hone hz ha hm J
  change denote (mulOp (mulOp ((hornerValue mulOp addOp z one)^[J] zero) inverse) jet) = _
  rw [hm, hm, hs, hinv, trunc_mul_trunc, hjet]
  simp only [TruncatedInverse.correctedJet, TruncatedInverse.inverse]
  congr 1
  rw [mul_comm]
  congr 1
  rw [mul_comm]
  rfl

end SubexponentialSAT.SqrtLog.CRTLocalProgram

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

theorem zero_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (zero z J) = 0 := by
  simp [denote, zero, List.map_replicate, hz, SubexponentialSAT.SubexpConvolutionAlgebra.denote_replicate_zero]

theorem mul_denote {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.mul ops.program P Q) =
      Truncation.trunc J (denote ops.decode P * denote ops.decode Q) :=
  DensePolynomialProgram.result_correct ops J P.1 Q.1

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

theorem corrected_denote_oai (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (q t : ℕ) (factor jet : Poly B d J)
    (P : R[X]) (hn : ops.decode minusOne = -1)
    (hfactor : denote ops.decode factor = Truncation.trunc J P) :
    denote ops.decode (corrected ops minusOne c q t factor jet) =
      TruncatedInverse.correctedJet P (denote ops.decode jet)
        (ops.decode (inverseCoefficient ops minusOne c q t)) J := by
  apply correctionValue_denote J _ _ _ _ _ _ _ _ (denote ops.decode) P _ _
  · exact zero_denote ops.decode ops.zeroRun.1 ops.zero_correct J
  · simpa only [ops.one_correct, map_one] using
      constant_denote ops.decode ops.zeroRun.1 ops.oneRun.1 ops.zero_correct J
  · have h := constant_denote ops.decode ops.zeroRun.1
      (scalarMul ops (inverseCoefficient ops minusOne c q t) minusOne) ops.zero_correct J
    simpa only [scalarMul, RepresentedRing.program, ops.mul_correct, hn, mul_neg_one] using h
  · exact constant_denote ops.decode ops.zeroRun.1 _ ops.zero_correct J
  · exact hfactor
  · rfl
  · exact add_denote ops
  · exact mul_denote ops

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote_oai.{u_1}
