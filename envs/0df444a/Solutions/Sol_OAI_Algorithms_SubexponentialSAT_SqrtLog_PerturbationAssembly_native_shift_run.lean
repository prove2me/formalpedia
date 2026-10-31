-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:25:49.964873+00:00
-- url     : https://prove2.me/submissions/d3cf04ba-474e-4812-98d0-374527ebc357

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S150
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Fixed_add_spec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Fixed_mul_spec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_shift_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The constructor's bit string is precisely a padded coefficient array. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

private theorem encode_replicate {B degree : ℕ} (z : Coeff B degree)
    (hz : RingProgram.flat z = List.replicate (degree*B) false) (n : ℕ) :
    encode (List.replicate n z) = List.replicate (n*(degree*B)) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,encode_cons,hz,ih,← List.replicate_add]
      congr 1
      ring

theorem encode_coefficients {B degree : ℕ} (zero low high : Coeff B degree)
    (hz : RingProgram.flat zero = List.replicate (degree*B) false) (J : ℕ) :
    encode (coefficients zero low high J) =
      Counter.paddedBits (degree*B) (RingProgram.flat low) (RingProgram.flat high) J := by
  cases J with
  | zero => rfl
  | succ J =>
      cases J with
      | zero => simp [coefficients,Counter.paddedBits]
      | succ n => simp [coefficients,Counter.paddedBits,encode_replicate zero hz n,List.append_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

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

theorem padded_encode {B d : ℕ} (z low high : Coeff B d)
    (hz : RingProgram.flat z = List.replicate (d*B) false) (J : ℕ) :
    Fixed.encode (padded z low high J) =
      Constructor.Counter.paddedBits (d*B) (RingProgram.flat low) (RingProgram.flat high) J :=
  Constructor.encode_coefficients z low high hz J

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

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

/-- Native multiply/add contracts are discharged here. The only remaining
premises describe the runtime scalar row, constants, caches, and scratch. -/
theorem native_shift_run_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
    (hrow : s 219=HornerProgram.encodePolynomial RingProgram.flat P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift Fixed.mulCommand AddService.command)
      (shiftBudget P.length J (d*baseWidth p t)
        (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)) s
      (Function.update (Function.update s 219 []) 240
        (Fixed.encode (shiftedValue ops J theta P))) := by
  apply shift_run s RingProgram.flat Fixed.encode
    (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)
    Fixed.mulCommand AddService.command (Fixed.mul ops) (Fixed.add ops)
    (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)
    J (d*baseWidth p t)
  · exact Fixed.mul_spec p t M cache ops table hB hz hadd hmul s J scalarWidth frame
      H hempty h121 h122 hcache hJcount
  · exact Fixed.add_spec p t M cache ops table hB hadd s J scalarWidth frame H
  · exact RingProgram.flat_length
  · exact Fixed.encode_length
  · intro c
    simpa [PerturbationProgram.Padding.cell,hzero,CRTLocalProgram.Model.constant] using
      (CRTLocalProgram.Model.padded_encode ops.zeroRun.1 c ops.zeroRun.1 hzero J).symm
  all_goals assumption

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run_oai
