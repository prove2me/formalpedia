-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:05:03.408373+00:00
-- url     : https://prove2.me/submissions/b1f8ede4-8a8e-4c9c-90c3-9ca140d27bc5

import Mathlib
import Definitions.Def_OAIQ081S135
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic invariant for the actual fixed-width polynomial Horner fold.
Truncation at every multiplication is valid for the final shifted polynomial. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open Polynomial

private theorem nativeFold_eq_foldl {A : Type*} (step : A → A → A)
    (cs : List A) (seed : A) : HornerProgram.fold step cs seed=cs.foldl step seed := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih => exact ih (step seed c)

/-- Instantiate with the native fixed-length dense polynomial services. The
premises state decoded arithmetic laws, rather than providing a shift oracle. -/
theorem shifted_horner_denote {C A R : Type*} [CommRing R]
    (D : ℕ) (decode : C → R) (denote : A → Polynomial R)
    (lift : C → A) (zero x : A) (theta : R) (mul add : A → A → A)
    (hz : denote zero=0)
    (hx : denote x=Truncation.trunc D (X+Polynomial.C theta))
    (hc : ∀ c, denote (lift c)=Truncation.trunc D (Polynomial.C (decode c)))
    (hm : ∀ a b, denote (mul a b)=Truncation.trunc D (denote a*denote b))
    (ha : ∀ a b, denote (add a b)=denote a+denote b)
    (cs : List C) :
    denote (HornerProgram.fold (HornerProgram.stepValue mul add x)
      (cs.map lift).reverse zero) =
      Truncation.trunc D ((PolynomialAlgorithm.denote (cs.map decode)).comp (X+Polynomial.C theta)) := by
  rw [nativeFold_eq_foldl,List.foldl_reverse]
  induction cs with
  | nil => simp [hz]
  | cons c cs ih =>
      simp only [List.map_cons,List.foldr_cons]
      change denote (add (mul _ x) (lift c)) = _
      rw [ha,hm,ih,hx,hc,SubexpTruncatedGeometric.trunc_mul_trunc,
        ←Truncation.trunc_add]
      congr 1
      simp only [PolynomialAlgorithm.denote,Polynomial.add_comp,Polynomial.mul_comp,
        Polynomial.C_comp,Polynomial.X_comp]
      ring

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual fixed-length polynomial services instantiate the shifted-row
machine. Its semantic result follows from the executed Horner fold. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem shiftedValue_denote {B d : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (J : ℕ) (theta : Coeff B d)
    (P : List (Coeff B d)) :
    CRTLocalProgram.Model.denote ops.decode (shiftedValue ops.program J theta P) =
      Truncation.trunc J ((PolynomialAlgorithm.denote (P.map ops.decode)).comp
        (Polynomial.X+Polynomial.C (ops.decode theta))) := by
  exact PerturbationProgram.shifted_horner_denote J ops.decode
    (CRTLocalProgram.Model.denote ops.decode)
    (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)
    (CRTLocalProgram.Model.zero ops.zeroRun.1 J)
    (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J)
    (ops.decode theta) (Fixed.mul ops.program) (Fixed.add ops.program)
    (CRTLocalProgram.Model.zero_denote ops.decode _ ops.zero_correct J)
    (CRTLocalProgram.Model.linear_denote ops.decode _ _ _ ops.zero_correct ops.one_correct J)
    (fun c => CRTLocalProgram.Model.constant_denote ops.decode _ c ops.zero_correct J)
    (CRTLocalProgram.Model.mul_denote ops) (CRTLocalProgram.Model.add_denote ops) P

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and exact denotation of the reversed, unnormalized coefficient
stream emitted by the new perturbation assembly. Zero coefficients remain. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse PerturbationProgram
open scoped BigOperators

variable {C R : Type*} [CommRing R]

theorem tail_polynomial (ops : RepresentedRing C R) (cs : List C) :
    Polynomial.X * polynomial ops cs.tail = polynomial ops cs -
      Polynomial.C ((polynomial ops cs).coeff 0) := by
  cases cs with
  | nil => simp [polynomial,SubexponentialSAT.SubexpDensePolynomial.decodeList]
  | cons c cs =>
      simp [polynomial,SubexponentialSAT.SubexpDensePolynomial.decodeList,
        SubexponentialSAT.PolynomialAlgorithm.denote_cons]

/-- Removing the actual array's constant slot commutes with its Z truncation.
This concerns the shifted array, not truncation before shifting. -/
theorem tail_polynomial_eq_trunc_delta (ops : RepresentedRing C R)
    (J : ℕ) (cs : List C) (p : Polynomial R) (theta : R)
    (hp : polynomial ops cs = Truncation.trunc J
      (p.comp (Polynomial.X + Polynomial.C theta))) :
    Polynomial.X * polynomial ops cs.tail =
      Truncation.trunc J (Moments.rowDelta p theta) := by
  rw [tail_polynomial,hp]
  ext j
  by_cases hj : j=0
  · subst j
    simp
  · simp [Polynomial.coeff_C,hj,Moments.rowDelta]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual fixed-array Horner output is already valid Stored data.
The native order is reversed and zero coefficients are deliberately kept. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

variable {B d n : ℕ} {R : Type*} [CommRing R]

theorem shifted_tail_polynomial_oai (ops : RepresentedRing (Coeff B d) R)
    (J : ℕ) (theta : Coeff B d) (p : List (Coeff B d)) :
    Polynomial.X * polynomial ops (shiftedValue ops.program J theta p).val.tail =
      Truncation.trunc J (Moments.rowDelta (polynomial ops p) (ops.decode theta)) := by
  apply tail_polynomial_eq_trunc_delta
  exact shiftedValue_denote ops J theta p

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial_oai.{u_1}
