-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:42:18.120409+00:00
-- url     : https://prove2.me/submissions/1b5225d5-6c44-4d23-b5f2-b98b475911ab

import Mathlib
import Definitions.Def_OAIQ081S100

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

theorem add_denote_oai {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.add ops.program P Q) = denote ops.decode P + denote ops.decode Q :=
  DensePolynomialProgram.add_correct ops P.1 Q.1

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote_oai.{u_1}
