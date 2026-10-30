-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:42:40.389889+00:00
-- url     : https://prove2.me/submissions/4ea9f550-118a-4ebc-a9b1-286b60e3ae88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Pair_command_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The encoded-array decomposition used by the actual convolution
product-and-update command. No scalar algebra or execution cost is assumed. -/

namespace SubexponentialSAT.SubexpConvolutionEncoding

theorem modify_split {C : Type*} (acc : List C) (i : ℕ) (hi : i < acc.length) :
    ∃ (earlier : List C) (c : C) (rest : List C),
      earlier.length = i ∧ acc = earlier ++ c :: rest ∧
      ∀ f : C → C, acc.modify i f = earlier ++ f c :: rest := by
  induction acc generalizing i with
  | nil => simp at hi
  | cons a acc ih =>
      cases i with
      | zero => exact ⟨[], a, acc, rfl, rfl, fun _ => rfl⟩
      | succ i =>
          obtain ⟨earlier, c, rest, hlen, heq, hmod⟩ := ih i (by simpa using hi)
          refine ⟨a :: earlier, c, rest, ?_, ?_, ?_⟩
          · simp [hlen]
          · simp [heq]
          · intro f
            simp only [List.modify_succ_cons, hmod, List.cons_append]

theorem encode_addProduct_split {C : Type*}
    (encode : C → List Bool) (width : ℕ) (hwidth : ∀ c, (encode c).length = width)
    (add mul : C → C → C) (acc : List C) (i : ℕ) (a b : C)
    (hi : i < acc.length) :
    ∃ (earlier : List (List Bool)) (c : C) (rest : List Bool),
      earlier.length = i ∧
      (∀ bits ∈ earlier, bits.length = width) ∧
      encodeArray encode acc = earlier.flatten ++ (encode c ++ rest) ∧
      encodeArray encode (TruncatedConvolution.addProduct add mul i a b acc) =
        earlier.flatten ++ (encode (add (mul a b) c) ++ rest) := by
  obtain ⟨earlier, c, rest, hlen, heq, hmod⟩ := modify_split acc i hi
  refine ⟨earlier.map encode, c, encodeArray encode rest, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · intro bits hbits
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hbits
    exact hwidth x
  · simp [encodeArray, heq]
  · rw [TruncatedConvolution.addProduct, hmod]
    simp [encodeArray]

end SubexponentialSAT.SubexpConvolutionEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPairSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete instantiation of the convolution controller's local pair
contract. The base contains only static arithmetic data and empty work space;
the eleven controller buffers may vary on every invocation. -/

namespace SubexponentialSAT.SubexpConvolutionPairSpec

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem buffers_below (base : Store) (w : Buffers) (j : Fin 256) (hj : j.val < 100) :
    buffers base w j = base j := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun i : Fin 256 => i.val) hi
  fin_cases i <;> simp [bufferPorts] at hv <;> omega

theorem buffers_work (base : Store) (w : Buffers) (j : Fin 256)
    (hlo : 112 ≤ j.val) (hhi : j.val ≤ 119) : buffers base w j = base j := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun i : Fin 256 => i.val) hi
  fin_cases i <;> simp [bufferPorts] at hv <;> omega

end SubexponentialSAT.SubexpConvolutionPairSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPairSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge the convolution controller's local contract with the concrete
native extension-ring multiply-and-accumulate program. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpConvolutionPairSpec
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem buffers_high (base : Store) (w : Buffers) (j : Fin 32)
    (h8 : j ≠ 8) (h9 : j ≠ 9) :
    buffers base w (RingCall.ports j) = base (RingCall.ports j) := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hdis : ∀ (i : Fin 11) (j : Fin 32), j ≠ 8 → j ≠ 9 →
      bufferPorts i ≠ RingCall.ports j := by decide
  exact hdis i j h8 h9 hi

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

/-- Every varying controller buffer receives the same actual fixed pair
program. The only side condition on the base is its concrete static layout. -/
theorem pairSpec_oai (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (base : Store)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : BaseReady p t M cache table base scalarWidth frame) (D : ℕ) :
    PairSpec Pair.command base RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) D
      (Pair.budget degree (baseWidth p t) D) := by
  intro w a b acc hlen hi hacc ha hb regs
  have hin : (w 3).length < acc.length := by omega
  obtain ⟨earlier, c, rest, hearlier, hrows, hsplit, hnext⟩ :=
    SubexpConvolutionEncoding.encode_addProduct_split RingProgram.flat
      (degree * baseWidth p t) RingProgram.flat_length
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) acc (w 3).length a b hin
  let d : Data := ⟨regs, buffers base w⟩
  have hready : Pair.Ready p t M cache table (buffers base w) a b c earlier rest
      (base 104) (w 3) scalarWidth frame := by
    constructor
    · intro j
      by_cases hj8 : j = 8
      · subst j
        simpa [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
          RingScan.serviceTapes] using ha
      · by_cases hj9 : j = 9
        · subst j
          simpa [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
            RingScan.serviceTapes] using hb
        · rw [buffers_high base w j hj8 hj9]
          have hh := H.high j hj8 hj9
          fin_cases j <;> simp_all [RingScan.serviceState,RingScan.serviceWorkState,RingScan.serviceTapes]
    · intro i
      rw [buffers_below base w _ (by
        dsimp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts]
        have := i.isLt
        omega)]
      exact H.low i
    ·
      rw [buffers_102, hacc]
      exact hsplit
    · exact buffers_103 base w
    · exact hearlier.symm
    · exact buffers_104 base w
    · exact H.width
    · simpa only [H.width] using hrows
    · exact H.scalarWidthLength
    · rw [buffers_frame]
      · exact H.degreeLength
      · intro h
        obtain ⟨i,hi⟩ := h
        fin_cases i <;> simp [bufferPorts] at hi
    · rw [buffers_120]
      exact H.scratch
    · intro j hlo hhi
      rw [buffers_work base w j hlo hhi]
      exact H.work j hlo hhi
  obtain ⟨n,rf,hn,he⟩ := Pair.command_run p t M cache ops table hB hz hadd hmul
    (buffers base w) a b c earlier rest (base 104) (w 3) scalarWidth frame hready regs
  let e : Data := ⟨rf, Function.update (Function.update (Function.update (buffers base w)
    198 []) 199 []) 102 (earlier.flatten ++
      (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest))⟩
  have hfinal : e.stacks = buffers base
      (Function.update (Function.update (Function.update w 9 []) 10 []) 2
        (encodeArray RingProgram.flat
          (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
            (w 3).length a b acc))) := by
    dsimp only [e]
    rw [buffers_update, buffers_update, buffers_update]
    change Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (earlier.flatten ++
          (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest)) =
      Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (encodeArray RingProgram.flat
          (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
            (w 3).length a b acc))
    exact congrArg
      (fun record : List Bool =>
        Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
          102 record) hnext.symm
  refine ⟨n, e.regs, hn.trans ?_, ?_⟩
  · unfold Pair.budget Cell.eventBudget
    gcongr
  · have heq : e = (⟨e.regs, buffers base
        (Function.update (Function.update (Function.update w 9 []) 10 []) 2
          (encodeArray RingProgram.flat
            (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
              (w 3).length a b acc)))⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hfinal
    change Eval Pair.command n (⟨regs,buffers base w⟩ : Data) e at he
    rw [heq] at he
    exact he

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec_oai
