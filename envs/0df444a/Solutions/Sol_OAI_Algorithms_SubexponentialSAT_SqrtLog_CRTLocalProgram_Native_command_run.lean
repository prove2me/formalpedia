-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:40:54.378789+00:00
-- url     : https://prove2.me/submissions/0d628f24-5d8c-4eb8-9088-fda1d1cf3b9c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_localCommand_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Fixed_add_spec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Fixed_mul_spec

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

theorem head_split {B d J : ℕ} (P : Poly B d J) (hJ : 0 < J) :
    ∃ (c : Coeff B d) (rest : List (Coeff B d)),
      P.1 = c :: rest ∧ Fixed.encode P = RingProgram.flat c ++ DensePolynomialProgram.encode rest ∧
        rest.length + 1 = J := by
  cases hP : P.1 with
  | nil => have h := P.2; rw [hP] at h; simp at h; omega
  | cons c rest =>
      refine ⟨c, rest, rfl, ?_, ?_⟩
      · simp [Fixed.encode, hP, DensePolynomialProgram.encode_cons]
      · have h := P.2
        simpa [hP] using h

theorem constant_zero {B d : ℕ} (z : Coeff B d) (J : ℕ) :
    constant z z J = zero z J := by
  apply Subtype.ext
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [constant, padded, zero, Constructor.coefficients, List.replicate_succ]

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact zero bytes for the native padded-polynomial constructors. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem toNat_false (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_cache_bits (p t : ℕ) [Fact p.Prime] (cache : RingProgram.ScalarCache p t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t) :
    cache.zero.val = List.replicate (baseWidth p t) false := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [cache.zero.property]
  · have hv := congrArg ZMod.val cache.zero_correct
    have hnum : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val = 0 := by
      simpa only [wordValue,ZMod.val_natCast,Nat.mod_eq_of_lt hz,ZMod.val_zero] using hv
    rw [hnum,toNat_false]

private theorem flatten_replicate_false (d B : ℕ) :
    (List.replicate d (List.replicate B false)).flatten = List.replicate (d*B) false := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
      congr 1
      ring

theorem flat_constant_zero {B : ℕ} (z : Word B)
    (hz : z.val = List.replicate B false) (d : ℕ) :
    RingProgram.flat (fun _ : Fin d => z) = List.replicate (d*B) false := by
  simp only [RingProgram.flat,hz,List.ofFn_const]
  exact flatten_replicate_false d B

theorem model_zero_bits (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t) :
    RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false := by
  change RingProgram.flat (fun _ : Fin d => cache.zero) = _
  exact flat_constant_zero cache.zero (zero_cache_bits 3 t cache hz) d

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual native scalar and polynomial programs instantiate every local
service. The remaining hypotheses concern bytes and clean workspace. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram

theorem command_run_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J q : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
    (hbuffers : ∀ i, s (bufferPorts i) = [])
    (minusOne theta : Coeff (baseWidth 3 t) d) (cs : List (Coeff (baseWidth 3 t) d))
    (jet : Model.Poly (baseWidth 3 t) d J)
    (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hminus : s 211 = RingProgram.flat minusOne) (htheta : s 213 = RingProgram.flat theta)
    (hcs : s 214 = cs.flatMap RingProgram.flat) (hjet : s 225 = Fixed.encode jet)
    (hJ : s 243 = List.replicate J true) (hJcache : (s 193).length = J)
    (hzeroCache : s 192 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (s 209).length = q-2) (hprecision : (s 212).length = t)
    (hclean : ∀ i ∈ localWork, s i = []) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
        (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
      (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
    ∃ (c : Coeff (baseWidth 3 t) d) (rest : List (Coeff (baseWidth 3 t) d)),
      factor.1 = c :: rest ∧
      ExecutesIn command (budget cs.length (s 216).length q t d J) s
        (Function.update s 244 (Fixed.encode (Model.corrected ops minusOne c q t factor jet))) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
        (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
      (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
  have hz : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth 3 t) false :=
    DensePolynomialProgram.model_zero_bits t a M cache hcanon
  have hsm : ServiceSpec s RingProgram.flat HornerProgram.Services.multiply (Model.scalarMul ops)
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d) :=
    HornerProgram.Services.multiply_spec 3 t M cache hcanon (HornerProgram.modelTable t a M cache) s hscalar
  have hsa : ServiceSpec s RingProgram.flat HornerProgram.Services.add (Model.scalarAdd ops)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d) :=
    HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hscalar
  have hpm : ServiceSpec s Fixed.encode Fixed.mulCommand (Fixed.mul ops.program)
      (nativeMulBudget J d (baseWidth 3 t)) :=
    Fixed.mul_spec 3 t M cache ops.program (HornerProgram.modelTable t a M cache) hB hcanon
      (fun _ _ => rfl) (fun _ _ => rfl) s J scalarWidth frame hpoly hbuffers
      (hclean 121 (by simp [localWork])) (hclean 122 (by simp [localWork])) hzeroCache hJcache
  have hpa : ServiceSpec s Fixed.encode AddService.command (Fixed.add ops.program)
      (AddService.budget d (baseWidth 3 t) J J) :=
    Fixed.add_spec 3 t M cache ops.program (HornerProgram.modelTable t a M cache) hB
      (fun _ _ => rfl) s J scalarWidth frame hpoly
  obtain ⟨c,rest,hhead,hbits,hlen⟩ := Model.head_split factor hJpos
  refine ⟨c,rest,hhead,?_⟩
  have h := localCommand_run s RingProgram.flat Fixed.encode
    (fun c => Model.constant ops.zeroRun.1 c J) (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J)
    HornerProgram.Services.multiply HornerProgram.Services.add Fixed.mulCommand AddService.command
    (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program) (Fixed.add ops.program)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t)) J (Nat.mul_pos hd hB)
    hsm hsa hpm hpa RingProgram.flat_length (fun p => (Fixed.encode_length p).le)
    ops.zeroRun.1 ops.oneRun.1 minusOne theta c cs jet (DensePolynomialProgram.encode rest)
    (fun c => Model.padded_encode ops.zeroRun.1 c ops.zeroRun.1 hz J)
    (fun c => Model.padded_encode ops.zeroRun.1 c ops.oneRun.1 hz J)
    hzero hz hone hminus htheta hcs hJ hjet
    (by
      rw [Model.constant_zero]
      change s 192 = Fixed.encode (Model.zero
        (RingProgram.modelProgram t a M cache).zeroRun.1 J)
      simpa only [Fixed.encode, Model.zero] using hzeroCache)
    hclean (fun _ => hbits)
  simpa only [command, budget, hexponent, hprecision, ite_eq_right (Nat.ne_of_gt hJpos),
    Model.corrected, Model.inverseCoefficient, Model.constant_zero] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run_oai
