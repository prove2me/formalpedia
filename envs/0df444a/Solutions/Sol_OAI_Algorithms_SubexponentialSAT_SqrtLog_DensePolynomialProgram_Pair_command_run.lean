-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:41:47.881008+00:00
-- url     : https://prove2.me/submissions/eaaf29e6-8cfc-4864-9b5d-45d24c9b2d0f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S153
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Cell_updateCell_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramRingCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed native extension-ring multiplication for the dense convolution
controller. Its live operands are 198/199, result200, persistent degree204.
The private 32-stack ring workspace is separated from the array controller. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t)

theorem native_run (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (s : Store) (degree width : List Bool) (hd : degree.length = d)
    (hw : width.length = baseWidth p t)
    (hs : ∀ i, s (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i) :
    ExecutesIn native (RingScan.serviceMulBudget (baseWidth p t) d+1) s
      (Function.update (Function.update (Function.update (Function.update s 198 []) 199 [])
        139 []) 200 (RingProgram.flat
          (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)) := by
  intro regs
  let start := RingScan.serviceState (regs ∘ registers) M.bits []
    (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val
    (RingTriple.tableEncoding table)
  obtain ⟨rf,n,hn,ht⟩ := RingScan.serviceMulProgram_run p t M cache hz table x y
    (regs ∘ registers) degree width hd hw
  have hp : projectState registers ports (⟨regs,s⟩ : Data) = start := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; exact hs i
  have hc := eval_call_from_state RingScan.serviceMulProgram registers ports
    (⟨regs,s⟩ : Data) registers.injective ports.injective (by simpa only [hp] using ht)
  let output := RingProgram.flat
    (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1
  have hout : (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
      (RingTriple.tableEncoding table)).stacks =
      Function.update (Function.update (Function.update (Function.update start.stacks
        8 []) 9 []) 11 []) 0 output := by
    funext i
    fin_cases i <;> simp [start, RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes]
  have hi : Function.extend ports start.stacks s = s := extend_agree ports start.stacks s hs
  have he : embedState registers ports (⟨regs,s⟩ : Data)
      (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
        (RingTriple.tableEncoding table)) =
      (⟨Function.extend registers rf regs,
        Function.update (Function.update (Function.update (Function.update s 198 []) 199 [])
          139 []) 200 output⟩ : Data) := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · change Function.extend ports _ s = _
      rw [hout, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hi]
      rfl
  change Eval native n (⟨regs,s⟩ : Data)
    (embedState registers ports (⟨regs,s⟩ : Data)
      (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
        (RingTriple.tableEncoding table))) at hc
  rw [he] at hc
  exact ⟨n, Function.extend registers rf regs, hn, hc⟩

theorem command_run (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (s : Store) (width : List Bool) (hd : (s 204).length = d)
    (hw : width.length = baseWidth p t) (h120 : s 120 = [])
    (hs : ∀ i, s (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) [] width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i) :
    ExecutesIn command (budget (baseWidth p t) d) s
      (Function.update (Function.update (Function.update s 198 []) 199 []) 200
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)) := by
  have h139 : s 139 = [] := hs 11
  let next := Function.update s 139 (s 204)
  have h1 : ExecutesIn (copy 204 139) (7*d+5) s next := by
    simpa [next,hd,h139] using copy_run 204 139 s (by decide) (by decide) (by decide) h120
  have hnext : ∀ i, next (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) (s 204) width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i := by
    intro i
    have hi := hs i
    fin_cases i <;> simp [next,ports,port,RingScan.serviceState,
      RingScan.serviceWorkState,RingScan.serviceTapes] at hi ⊢ <;> exact hi
  have h2 := native_run p t M cache hz table x y next (s 204) width hd hw hnext
  have he : Function.update (Function.update (Function.update (Function.update next 198 []) 199 [])
      139 []) 200 (RingProgram.flat
          (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1) =
      Function.update (Function.update (Function.update s 198 []) 199 []) 200
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1) := by
    funext i
    by_cases hi : i = 139 <;> simp [next,Function.update_apply,hi,h139]
  rw [he] at h2
  exact h1.seq h2

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lowPort_injective : Function.Injective lowPort := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 256 => i.val) h)

theorem moveProduct_eval (d : Data) (h8 : d.stacks 8 = []) (h119 : d.stacks 119 = []) :
    Eval moveProduct (6 * (d.stacks 200).length + 6) d (moveOut d) := by
  have h1 := transfer_eval d (200 : Fin 256) 119 (0 : Fin 16) 1 (by decide) (by decide)
  have h2 := transfer_eval (afterTransfer d 200 119 0 1)
    (119 : Fin 256) 8 (0 : Fin 16) 1 (by decide) (by decide)
  have he : afterTransfer (afterTransfer d 200 119 0 1) 119 8 0 1 = moveOut d := by
    apply state_ext
    · simp [afterTransfer, moveOut, StackRoutines.readRegs_reset]
    · funext j
      by_cases h8j : j = 8
      · subst j
        simp [afterTransfer, moveOut, StackRoutines.transferStacks, h8, h119]
      · by_cases h119j : j = 119
        · subst j
          simp [afterTransfer, moveOut, StackRoutines.transferStacks, h119]
        · simp [afterTransfer, moveOut, StackRoutines.transferStacks, h8j, h119j]
  have hlen : ((afterTransfer d 200 119 0 1).stacks 119).length =
      (d.stacks 200).length := by simp [afterTransfer, StackRoutines.transferStacks, h119]
  simpa only [moveProduct, he, hlen,
    show ∀ n : ℕ, (3*n+3)+(3*n+3)=6*n+6 by omega] using h1.seq h2

theorem embed_low_input (d : Data) : embedState id lowPort d (lowState d) = d := by
  apply embedState_eq_of_ports id lowPort d d _ Function.injective_id lowPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; rfl
  · intro i hi; rfl

theorem embed_low_output (d : Data) (e : State 16 128) (record : List Bool)
    (he : e.stacks = Function.update (Function.update (lowState d).stacks 8 []) 102 record) :
    embedState id lowPort d e =
      (⟨e.regs, Function.update (Function.update d.stacks (lowPort 8) [])
        (lowPort 102) record⟩ : Data) := by
  apply embedState_eq_of_ports id lowPort d _ _ Function.injective_id lowPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    rw [he]
    simp [lowState, Function.update_apply, lowPort_injective.eq_iff]
  · intro i hi
    have h8 : i ≠ lowPort 8 := fun h => hi ⟨8, h.symm⟩
    have h102 : i ≠ lowPort 102 := fun h => hi ⟨102, h.symm⟩
    simp [h8, h102]

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

/-- This is the concrete bit-command execution for one pair; all coefficient
arithmetic calls are the native programs, never abstract ring operations. -/
theorem command_run_oai (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (a b c : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p t M cache table s a b c earlier rest widthWord indexWord scalarWidth frame) :
    ExecutesIn command (budget degree (baseWidth p t) indexWord.length) s
      (Function.update (Function.update (Function.update s 198 []) 199 []) 102
        (earlier.flatten ++ (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest))) := by
  intro regs
  let product := (ops.mulRun a b).1
  obtain ⟨n1,r1,hn1,he1⟩ := RingCall.command_run p t M cache hz table a b s scalarWidth
    H.degreeLength H.scalarWidthLength H.scratch H.high regs
  rw [← hmul] at he1
  let d1 : Data := ⟨r1,Function.update (Function.update (Function.update s 198 []) 199 [])
    200 (RingProgram.flat product)⟩
  let d2 := moveOut d1
  have h8 : s 8 = [] := H.low 8
  have h200 : s 200 = [] := H.high 0
  have h18 : d1.stacks 8 = [] := by simp [d1,h8]
  have h119 : d1.stacks 119 = [] := by simpa [d1] using H.work 119 (by decide) (by decide)
  have he2 := moveProduct_eval d1 h18 h119
  have hlen : (d1.stacks 200).length = degree * baseWidth p t := by simp [d1]
  have hf (j : Fin 128) (hj : j ≠ 8) : (lowState d2).stacks j = s (lowPort j) := by
    have h8j : lowPort j ≠ 8 := fun h => hj (lowPort_injective h)
    have hv : (lowPort j).val < 128 := j.isLt
    have h198 : lowPort j ≠ 198 := by intro h; rw [h] at hv; norm_num at hv
    have h199 : lowPort j ≠ 199 := by intro h; rw [h] at hv; norm_num at hv
    have h200j : lowPort j ≠ 200 := by intro h; rw [h] at hv; norm_num at hv
    simp [d2,d1,lowState,moveOut,h8j,h198,h199,h200j]
  have h102 : lowPort (102 : Fin 128) = (102 : Fin 256) := by apply Fin.ext; rfl
  have h103 : lowPort (103 : Fin 128) = (103 : Fin 256) := by apply Fin.ext; rfl
  have h104 : lowPort (104 : Fin 128) = (104 : Fin 256) := by apply Fin.ext; rfl
  have h112 : lowPort (112 : Fin 128) = (112 : Fin 256) := by apply Fin.ext; rfl
  have h113 : lowPort (113 : Fin 128) = (113 : Fin 256) := by apply Fin.ext; rfl
  have h114 : lowPort (114 : Fin 128) = (114 : Fin 256) := by apply Fin.ext; rfl
  have h115 : lowPort (115 : Fin 128) = (115 : Fin 256) := by apply Fin.ext; rfl
  have h116 : lowPort (116 : Fin 128) = (116 : Fin 256) := by apply Fin.ext; rfl
  have h117 : lowPort (117 : Fin 128) = (117 : Fin 256) := by apply Fin.ext; rfl
  have h118 : lowPort (118 : Fin 128) = (118 : Fin 256) := by apply Fin.ext; rfl
  have hsmall : ∀ i : Fin 20, (lowState d2).stacks (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i) =
      (DensePolynomialLoop.ready ((lowState d2).regs ∘ SubexponentialSAT.SubexpJetCellProgram.regPorts)
        M.bits (RingProgram.flat product) [] scalarWidth [] frame).stacks i := by
    intro i
    have hi := H.low i
    fin_cases i <;> simp [d2,d1,lowState,moveOut,lowPort,SubexponentialSAT.SubexpJetCellProgram.scalarPorts,
      DensePolynomialLoop.ready,DensePolynomialLoop.state,DensePolynomialLoop.stackArray,
      Fin.addCases] at hi ⊢ <;> exact hi
  obtain ⟨n3,hn3,e3,he3,hs3,hr3⟩ := Cell.updateCell_eval p t M cache hB ops hadd
    (lowState d2) product c earlier rest widthWord indexWord scalarWidth frame
    (by simpa only [hf 102 (by decide), h102] using H.array)
    (by simpa only [hf 103 (by decide), h103] using H.index) H.indexLength
    (by simpa only [hf 104 (by decide), h104] using H.width) H.widthLength H.rows
    H.scalarWidthLength hsmall
    (by simpa only [hf 112 (by decide), h112] using H.work 112 (by decide) (by decide))
    (by simpa only [hf 113 (by decide), h113] using H.work 113 (by decide) (by decide))
    (by simpa only [hf 114 (by decide), h114] using H.work 114 (by decide) (by decide))
    (by simpa only [hf 115 (by decide), h115] using H.work 115 (by decide) (by decide))
    (by simpa only [hf 116 (by decide), h116] using H.work 116 (by decide) (by decide))
    (by simpa only [hf 117 (by decide), h117] using H.work 117 (by decide) (by decide))
    (by simpa only [hf 118 (by decide), h118] using H.work 118 (by decide) (by decide))
  let record := earlier.flatten ++ (RingProgram.flat (ops.addRun product c).1 ++ rest)
  have hcall := eval_call_lifted Cell.program id lowPort d2
    Function.injective_id lowPort_injective
    (a := lowState d2) (b := e3) (compiled_halt_trace he3 8 102)
  rw [embed_low_input, embed_low_output d2 e3 record hs3] at hcall
  have hlast : Function.update (Function.update d2.stacks (lowPort 8) []) (lowPort 102) record =
      Function.update (Function.update (Function.update s 198 []) 199 []) 102 record := by
    funext j
    by_cases hj8 : j = 8 <;> by_cases hj200 : j = 200 <;>
      simp [d2,d1,moveOut,lowPort,Function.update_apply,hj8,hj200,h8,h200]
  rw [hlast] at hcall
  refine ⟨n1+((6*(d1.stacks 200).length+6)+(n3+1)), e3.regs, ?_, he1.seq (he2.seq hcall)⟩
  rw [hlen]
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run_oai
