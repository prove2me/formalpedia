-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:41:15.118291+00:00
-- url     : https://prove2.me/submissions/58c37258-adbc-4a5c-9d2e-ec34c35dc040
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_PairSpec_pairSpec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpConvolutionControl_command_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem buffers_frame (base : Store) (w : Buffers) (j : Fin 256)
    (hj : ¬ ∃ i, bufferPorts i = j) : buffers base w j = base j :=
  Function.extend_apply' _ _ _ hj

theorem buffers_update (base : Store) (w : Buffers) (i : Fin 11) (v : List Bool) :
    buffers base (Function.update w i v) = Function.update (buffers base w) (bufferPorts i) v :=
  ProgramLinking.extend_update bufferPorts.injective w base i v

@[simp] theorem buffers_104 (base : Store) (w : Buffers) : buffers base w 104 = base 104 :=
  buffers_frame base w 104 (by decide)
@[simp] theorem buffers_120 (base : Store) (w : Buffers) : buffers base w 120 = base 120 :=
  buffers_frame base w 120 (by decide)
@[simp] theorem buffers_121 (base : Store) (w : Buffers) : buffers base w 121 = base 121 :=
  buffers_frame base w 121 (by decide)
@[simp] theorem buffers_122 (base : Store) (w : Buffers) : buffers base w 122 = base 122 :=
  buffers_frame base w 122 (by decide)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialServiceControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical marshalling for a reusable truncated-product service. Cached
operands, a zero array, and the unary dimension occupy 240--243. The native
convolution buffers are restored after each invocation and the result goes
to 244. All copying, clearing, and reversal is performed by fixed programs. -/

namespace SubexponentialSAT.SubexpPolynomialServiceControl

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl

theorem prepare_run (s : Store)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h106 : s 106 = []) (h120 : s 120 = []) :
    ExecutesIn prepare
      (7 * ((s 240).length + (s 241).length + (s 242).length + (s 243).length) + 20)
      s (prepared s) := by
  let s₁ := Function.update s 100 (s 240)
  let s₂ := Function.update s₁ 101 (s 241)
  let s₃ := Function.update s₂ 102 (s 242)
  have h₁ : ExecutesIn (copy 240 100) (7 * (s 240).length + 5) s s₁ := by
    simpa [s₁, h100] using copy_run 240 100 s (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (copy 241 101) (7 * (s 241).length + 5) s₁ s₂ := by
    simpa [s₁, s₂, h101] using copy_run 241 101 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have h₃ : ExecutesIn (copy 242 102) (7 * (s 242).length + 5) s₂ s₃ := by
    simpa [s₁, s₂, s₃, h102] using copy_run 242 102 s₂
      (by decide) (by decide) (by decide) (by simp [s₂, s₁, h120])
  have h₄ : ExecutesIn (copy 243 106) (7 * (s 243).length + 5) s₃ (prepared s) := by
    simpa [s₁, s₂, s₃, prepared, h106] using copy_run 243 106 s₃
      (by decide) (by decide) (by decide) (by simp [s₃, s₂, s₁, h120])
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  convert h using 1
  · rfl
  · ring

theorem finish_run (s : Store) (out : List Bool)
    (h101 : s 101 = []) (h102 : s 102 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn finish (2 * (s 241).length + 6 * out.length + 9)
      (multiplied s out) (Function.update s 244 out) := by
  let s₁ := Function.update s 102 out
  let s₂ := Function.update s 245 out.reverse
  have he₁ : Function.update (multiplied s out) 101 [] = s₁ := by
    funext i
    by_cases h : i = 101 <;> simp [multiplied, s₁, h, h101, Function.update_apply]
  have h₁ : ExecutesIn (clear 101) (2 * (s 241).length + 3) (multiplied s out) s₁ := by
    have h := clear_run 101 (multiplied s out)
    rw [he₁] at h
    simpa [multiplied] using h
  have he₂ : Function.update (Function.update s₁ 102 []) 245
      ((s₁ 102).reverse ++ s₁ 245) = s₂ := by
    funext i
    by_cases h : i = 102 <;> simp [s₁, s₂, h, h102, h245, Function.update_apply]
  have h₂ : ExecutesIn (transfer 102 245) (3 * out.length + 3) s₁ s₂ := by
    have h := transfer_run 102 245 s₁ (by decide)
    rw [he₂] at h
    simpa [s₁] using h
  have he₃ : Function.update (Function.update s₂ 245 []) 244
      ((s₂ 245).reverse ++ s₂ 244) = Function.update s 244 out := by
    funext i
    by_cases h : i = 245 <;> simp [s₂, h, h245, h244, Function.update_apply]
  have h₃ : ExecutesIn (transfer 245 244) (3 * out.length + 3) s₂
      (Function.update s 244 out) := by
    have h := transfer_run 245 244 s₂ (by decide)
    rw [he₃] at h
    simpa [s₂] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  · rfl
  · ring

/-- This composition theorem charges the actual native multiplication
execution and every bit moved around it. The multiplication premise is an
execution of the supplied fixed command, not a polynomial-result oracle. -/
theorem command_run (multiply : Code) (K : ℕ) (s : Store) (out : List Bool)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h106 : s 106 = []) (h120 : s 120 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hmul : ExecutesIn multiply K (prepared s) (multiplied s out)) :
    ExecutesIn (command multiply)
      (K + 7 * ((s 240).length + (s 242).length + (s 243).length) +
        9 * (s 241).length + 6 * out.length + 29)
      s (Function.update s 244 out) := by
  have h := (prepare_run s h100 h101 h102 h106 h120).seq
    (hmul.seq (finish_run s out h101 h102 h244 h245))
  convert h using 1
  · rfl
  · ring

end SubexponentialSAT.SubexpPolynomialServiceControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite-program execution of the padded triangular convolution.
The generic local pair contract is instantiated separately by the concrete
quartic multiplier and persistent-cell update service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

/-- Specialization to an actual zero-initialized D-cell output array. -/
theorem initialized_command_run (pair : Code) (base : Store) (encode : C → List Bool)
    (zero : C) (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q : List C) (hP : P.length = D) (hQ : Q.length = D)
    (hleft : w 0 = encodeArray encode P) (hright : w 1 = encodeArray encode Q)
    (hacc : w 2 = encodeArray encode (List.replicate D zero))
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
      (buffers base (finishedBuffers w
        (encodeArray encode (TruncatedConvolution.run zero add mul D P Q)))) :=
  command_run pair base encode add mul D W pairCost hpair hencode hwidth h120 h121 h122
    w P Q (List.replicate D zero) hP hQ (by simp) hleft hright hacc hcount h4 h3 h6 h7 h8 h9 h10

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialMultiplyService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable concrete multiplication service for local CRT loops. The
native convolution workspace is empty again on return; only output 244 is
changed. Runtime polynomial arrays and the unary dimension are cached in
240--243. This module composes physical copy/clear loops with the actual
quartic convolution program. -/

namespace SubexponentialSAT.SubexpPolynomialMultiplyService

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

theorem empty_buffers (s : Store) (hempty : ∀ i, s (bufferPorts i) = []) :
    buffers s (fun _ => []) = s := by
  classical
  funext j
  by_cases hj : ∃ i, bufferPorts i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [hempty]
  · exact buffers_frame s _ j hj

theorem prepared_eq_buffers (s : Store) (hempty : ∀ i, s (bufferPorts i) = []) :
    SubexpPolynomialServiceControl.prepared s = buffers s (nativeInput s) := by
  have hw : nativeInput s = Function.update (Function.update (Function.update
      (Function.update (fun _ : Fin 11 => []) 0 (s 240)) 1 (s 241)) 2 (s 242)) 5 (s 243) := by
    funext i
    fin_cases i <;> simp [nativeInput]
  rw [hw, buffers_update, buffers_update, buffers_update, buffers_update, empty_buffers s hempty]
  rfl

theorem multiplied_eq_buffers (s : Store) (out : List Bool)
    (hempty : ∀ i, s (bufferPorts i) = []) :
    SubexpPolynomialServiceControl.multiplied s out =
      buffers s (finishedBuffers (nativeInput s) out) := by
  have hw : finishedBuffers (nativeInput s) out =
      Function.update (Function.update (fun _ : Fin 11 => []) 1 (s 241)) 2 out := by
    funext i
    fin_cases i <;> simp [nativeInput, finishedBuffers]
  rw [hw, buffers_update, buffers_update, empty_buffers s hempty]
  rfl

end SubexponentialSAT.SubexpPolynomialMultiplyService

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

/-- Actual native execution conditional only on the separately checked local
ring multiply-and-accumulate command. No array operation is free. -/
theorem mul_service_eval {B degree : ℕ}
    (pair : Code) (s : Store) (ops : RingProgram (Coeff B degree))
    (J pairCost : ℕ) (P Q : List (Coeff B degree))
    (hpair : PairSpec pair s RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J pairCost)
    (hwidth : (s 104).length = degree * B)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) :
    ExecutesIn (mulCommand pair) (mulBudget J (degree * B) pairCost - 1) s
      (Function.update s 244 (encode (result ops J P Q))) := by
  let out := encode (result ops J P Q)
  let K := convolutionBudget J (degree * B) pairCost
  have hmul : ExecutesIn (SubexponentialSAT.SubexpConvolutionControl.command pair) K
      (SubexponentialSAT.SubexpPolynomialServiceControl.prepared s)
      (SubexponentialSAT.SubexpPolynomialServiceControl.multiplied s out) := by
    rw [SubexponentialSAT.SubexpPolynomialMultiplyService.prepared_eq_buffers s hempty,
      SubexponentialSAT.SubexpPolynomialMultiplyService.multiplied_eq_buffers s out hempty]
    exact initialized_command_run pair s RingProgram.flat ops.zeroRun.1
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
      J (degree * B) pairCost hpair RingProgram.flat_length hwidth h120 h121 h122
      (SubexponentialSAT.SubexpPolynomialMultiplyService.nativeInput s) P Q hP hQ
      hleft hright hzero hJ rfl rfl rfl rfl rfl rfl rfl
  have h := SubexponentialSAT.SubexpPolynomialServiceControl.command_run
    (SubexponentialSAT.SubexpConvolutionControl.command pair) K s out
    (hempty 0) (hempty 1) (hempty 2) (hempty 5) h120 h244 h245 hmul
  convert h using 1
  · rfl
  · rw [hleft, hright, hzero, hJ]
    simp only [out, encode_length, result_length, List.length_replicate, hP, hQ]
    dsimp only [K, mulBudget]
    simp only [Nat.mul_assoc]
    omega

theorem mul_service_trace {B degree : ℕ}
    (pair : Code) (s : Store) (ops : RingProgram (Coeff B degree))
    (J pairCost : ℕ) (P Q : List (Coeff B degree))
    (hpair : PairSpec pair s RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J pairCost)
    (hwidth : (s 104).length = degree * B)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) (regs : Fin 16 → Bool) :
    ∃ n ≤ mulBudget J (degree * B) pairCost, ∃ regs',
      Trace (mulProgram pair) n
        ((⟨regs,s⟩ : Data).withPC (some (mulProgram pair).entry))
        ((⟨regs',Function.update s 244 (encode (result ops J P Q))⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := mul_service_eval pair s ops J pairCost P Q hpair hwidth hempty
    h120 h121 h122 h244 h245 hP hQ hleft hright hzero hJ regs
  refine ⟨n+1, ?_, rf, compiled_halt_trace he 240 244⟩
  have hp : 0 < mulBudget J (degree * B) pairCost := by unfold mulBudget; omega
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static native arithmetic readiness, independent of the final service
composition. The two polynomial caches do not participate in readiness. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod
variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))


omit [Fact (Nat.Prime p)] in
/-- Readiness only inspects native arithmetic ports; the two protected
polynomial caches may vary while the native arithmetic frame is retained. -/
theorem BaseReady.frame_except_caches {base s : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (hf : ∀ i : Fin 256, i.val < 205 → i ≠ 192 → i ≠ 193 → s i = base i) :
    BaseReady p t M cache table s scalarWidth frame := by
  constructor
  · intro i h8 h9
    have hp : (RingCall.ports i).val < 205 ∧ RingCall.ports i ≠ 192 ∧ RingCall.ports i ≠ 193 := by
      exact (by decide : ∀ j : Fin 32, (RingCall.ports j).val < 205 ∧
        RingCall.ports j ≠ 192 ∧ RingCall.ports j ≠ 193) i
    rw [hf _ hp.1 hp.2.1 hp.2.2]
    exact H.high i h8 h9
  · intro i
    have hp : (SubexponentialSAT.SubexpConvolutionPair.lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)).val < 20 := i.isLt
    rw [hf _ (by omega) (by intro he; rw [he] at hp; norm_num at hp)
      (by intro he; rw [he] at hp; norm_num at hp)]
    exact H.low i
  · rw [hf 104 (by decide) (by decide) (by decide)]; exact H.width
  · exact H.scalarWidthLength
  · rw [hf 204 (by decide) (by decide) (by decide)]; exact H.degreeLength
  · rw [hf 120 (by decide) (by decide) (by decide)]; exact H.scratch
  · intro i hlo hhi
    rw [hf i (by omega) (by intro he; subst i; norm_num at hhi)
      (by intro he; subst i; norm_num at hhi)]
    exact H.work i hlo hhi


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {degree : ℕ}
  (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
  (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

theorem native_mul_trace (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (P Q : List (Coeff (baseWidth p t) degree))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h121 : s 121 = []) (h122 : s 122 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) (regs : Fin 16 → Bool) :
    ∃ n ≤ nativeMulBudget J degree (baseWidth p t), ∃ regs',
      Trace nativeMulProgram n
        ((⟨regs,s⟩ : Data).withPC (some nativeMulProgram.entry))
        ((⟨regs',Function.update s 244 (encode (result ops J P Q))⟩ : Data).withPC none) :=
  mul_service_trace Pair.command s ops J (Pair.budget degree (baseWidth p t) J) P Q
    (PairSpec.pairSpec p t M cache ops table hB hz hadd hmul s scalarWidth frame H J)
    H.width hempty H.scratch h121 h122 h244 h245 hP hQ hleft hright hzero hJ regs

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length coefficient-array carriers for the local CRT/Horner loops.
The multiplication service obtains its zero array and length from protected
caches192/193. The relocation is in the finite instruction table, so no tape
copy is charged or hidden by the change of physical port names. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

omit [Fact (Nat.Prime p)] in
private theorem ready_frame (base s : Store) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame)
    (hf : CRTLocalProgram.LowFrame base s) :
    PairSpec.BaseReady p t M cache table (s ∘ ports) scalarWidth frame := by
  apply PairSpec.BaseReady.frame_except_caches p t M cache table H
  intro i hi h192 h193
  have h242 : i ≠ 242 := by intro h; subst i; norm_num at hi
  have h243 : i ≠ 243 := by intro h; subst i; norm_num at hi
  simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,h192,h193,h242,h243]
    using hf i hi

/-- No high cache invariant is assumed by the service: only the protected
low workspace, encoded operands, and its two empty output buffers. -/
theorem mul_spec_oai (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (base : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame)
    (hempty : ∀ i, base (bufferPorts i) = [])
    (h121 : base 121 = []) (h122 : base 122 = [])
    (hzero : base 192 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1))
    (hJ : (base 193).length = J) :
    CRTLocalProgram.ServiceSpec base (encode (J:=J)) mulCommand (mul ops)
      (nativeMulBudget J degree (baseWidth p t)) := by
  intro s P Q hf hP hQ h244 h245 regs
  have Hs := ready_frame p t M cache table base s scalarWidth frame H hf
  have he : ∀ i, (s ∘ ports) (bufferPorts i) = [] := by
    intro i
    have hh := hf (bufferPorts i) (by fin_cases i <;> decide)
    have hh2 := hempty i
    fin_cases i <;> simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,bufferPorts] using hh.trans hh2
  have hz' : (s ∘ ports) 242 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1) := by
    simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 192 (by decide)).trans hzero
  have hJ' : ((s ∘ ports) 243).length = J := by
    simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,hf 193 (by decide)] using hJ
  obtain ⟨n,hn,rf,ht⟩ := native_mul_trace p t M cache ops table hB hz hadd hmul
    (s ∘ ports) J P.1 Q.1 scalarWidth frame Hs he
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 121 (by decide)).trans h121)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using (hf 122 (by decide)).trans h122)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using h244)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def] using h245)
    P.2 Q.2
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,encode] using hP)
    (by simpa [Function.comp_def,ports,relocation,Equiv.swap_apply_def,encode] using hQ) hz' hJ' regs
  let d : Data := ⟨regs,s⟩
  have hc := eval_call_from_state nativeMulProgram id ports d Function.injective_id ports.injective ht
  have hext : Function.extend ports (s ∘ ports) s = s :=
    congrArg StructuredProgram.State.stacks (embedState_project id ports d Function.injective_id ports.injective)
  have hout : (embedState id ports d
      (⟨rf,Function.update (s ∘ ports) 244 (DensePolynomialProgram.encode (result ops J P.1 Q.1))⟩ : Data)).stacks =
      Function.update s 244 (encode (mul ops P Q)) := by
    change Function.extend ports _ s = _
    rw [ProgramLinking.extend_update ports.injective,hext]
    rfl
  let final := embedState id ports d
    (⟨rf,Function.update (s ∘ ports) 244 (DensePolynomialProgram.encode (result ops J P.1 Q.1))⟩ : Data)
  have heq : final = (⟨final.regs,Function.update s 244 (encode (mul ops P Q))⟩ : Data) :=
    SubexponentialSAT.SubexpScanPrimitives.state_ext rfl hout
  refine ⟨n,final.regs,hn,?_⟩
  change Eval mulCommand n d final at hc
  rw [heq] at hc
  exact hc


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec_oai
