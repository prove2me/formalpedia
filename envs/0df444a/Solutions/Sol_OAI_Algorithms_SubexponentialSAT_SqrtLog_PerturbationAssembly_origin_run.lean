-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:26:16.998659+00:00
-- url     : https://prove2.me/submissions/7345ca15-5068-46bd-8edd-1ba634a129e2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S150
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationEmitProgram_emit_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- One stack update in the local result becomes the same update at its
assigned caller port. This is an equality of state descriptions. -/
theorem embedState_update_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (hs : Function.Injective stack)
    (k : Fin s) (word : List Bool) :
    embedState register stack frame { d with «stacks» := Function.update d.stacks k word } =
      { embedState register stack frame d with
        «stacks» := Function.update (embedState register stack frame d).stacks (stack k) word } := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · exact ProgramLinking.extend_update hs d.stacks frame.stacks k word

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramKey
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native construction of a positive-Z singleton key from its runtime unary
exponent and support mask. The reversed result feeds the sparse record emitter. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Key
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem pushFalse_run (s : Store) : ExecutesIn pushFalse 2 s
    (Function.update s 222 (false::s 222)) := by
  intro regs
  refine ⟨2,Function.update regs 0 false,le_refl _,?_⟩
  simpa [pushFalse,Subexp.TupleProgram.pushedState] using
    Subexp.TupleProgram.pushConst_eval (222 : Fin 256) (0 : Fin 16) false
      (⟨regs,s⟩ : Data)

theorem command_run (s : Store) (unary mask : List Bool)
    (hu : s 221=unary) (hm : s 220=mask) (h120 : s 120=[])
    (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[]) :
    ExecutesIn command (16*(unary.length+mask.length)+39) s
      (Function.update s 222 (bits unary mask).reverse) := by
  let s1 := Function.update s 222 mask
  let s2 := Function.update s 222 (false::mask)
  let s3 := Function.update s 222 (unary++false::mask)
  let s4 := Function.update s 222 (bits unary mask)
  have h1 : ExecutesIn (copy 220 222) (7*mask.length+5) s s1 := by
    simpa [s1,hm,h222] using copy_run 220 222 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn pushFalse 2 s1 s2 := by
    simpa [s1,s2] using pushFalse_run s1
  have h3 : ExecutesIn (copy 221 222) (7*unary.length+5) s2 s3 := by
    simpa [s2,s3,hu] using copy_run 221 222 s2 (by decide) (by decide) (by decide)
      (by simp [s2,h120])
  have h4 : ExecutesIn pushFalse 2 s3 s4 := by
    simpa [s3,s4,bits] using pushFalse_run s3
  have h5 : ExecutesIn (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
      (9*(unary.length+mask.length+2)+7) s4
      (Function.update s 222 (bits unary mask).reverse) := by
    intro regs
    have h := reverse_eval (⟨regs,s4⟩ : Data) 222 223 224 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [s4,h223]) (by simp [s4,h224])
    refine ⟨9*(bits unary mask).length+7,readRegs regs 0 1 none,?_,?_⟩
    · simp [bits]; omega
    · simpa [s4,afterReverse,StackRoutines.reverseStacks] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first | omega | rfl

end SubexponentialSAT.SqrtLog.PerturbationProgram.Key

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

private theorem embed_same (map : Fin 256 → Fin 256) (hm : Function.Injective map)
    (r rf : Fin 16 → Bool) (s : Store) :
    embedState id map (⟨r,s⟩ : Data) ⟨rf,s ∘ map⟩ = (⟨rf,s⟩ : Data) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hm
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; rfl
  · intro i hi; rfl

theorem key_run (s : Store) (mask : List Bool) (j : ℕ)
    (hm : s 214=mask) (hj : s 221=List.replicate j true)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[]) :
    ExecutesIn keyCommand (16*(j+mask.length)+40) s
      (Function.update s 222 (keyBits mask j).reverse) := by
  intro regs
  have hk221 : keyMap 221 = 221 := by decide
  have hk120 : keyMap 120 = 120 := by decide
  have hk222 : keyMap 222 = 222 := by decide
  have hk223 : keyMap 223 = 223 := by decide
  have hk224 : keyMap 224 = 224 := by decide
  have h := PerturbationProgram.Key.command_run (s ∘ keyMap)
    (List.replicate j true) mask
    (by simpa [Function.comp_def, hk221] using hj)
    (by simpa [Function.comp_def,keyMap] using hm)
    (by simpa [Function.comp_def, hk120] using h120)
    (by simpa [Function.comp_def, hk222] using h222)
    (by simpa [Function.comp_def, hk223] using h223)
    (by simpa [Function.comp_def, hk224] using h224)
  obtain ⟨n,rf,hn,he⟩ := h regs
  have hl := eval_liftCommand_from_state PerturbationProgram.Key.command 0 0
    id keyMap (⟨regs,s⟩ : Data) Function.injective_id keyMap.injective he
  have hout : embedState id keyMap (⟨regs,s⟩ : Data)
      ⟨rf,Function.update (s ∘ keyMap) 222 (keyBits mask j).reverse⟩ =
      (⟨rf,Function.update s 222 (keyBits mask j).reverse⟩ : Data) := by
    rw [embedState_update_stack id keyMap _ (⟨rf,s ∘ keyMap⟩ : Data)
      keyMap.injective 222 (keyBits mask j).reverse,embed_same keyMap keyMap.injective]
    rw [show keyMap 222=222 from by decide]
  change Eval keyCommand (n+1) (⟨regs,s⟩ : Data)
    (embedState id keyMap (⟨regs,s⟩ : Data)
      ⟨rf,Function.update (s ∘ keyMap) 222 (keyBits mask j).reverse⟩) at hl
  rw [hout] at hl
  refine ⟨n+1,rf,?_,?_⟩
  · simp only [List.length_replicate] at hn
    omega
  · exact hl

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

private theorem zero_visits (s : Store) (count out : List Bool) (regs : Fin 16 → Bool) :
    ∃ rr, UnaryForPrograms.Visits zeroPorts (pushBit false)
      (List.replicate count.length 2) (4*count.length+2)
      (⟨regs,fill s count out⟩ : Data)
      (⟨rr,fill s [] (List.replicate count.length false++out)⟩ : Data) := by
  induction count generalizing out regs with
  | nil =>
      refine ⟨readRegs regs 0 1 none,?_⟩
      simpa [zeroPorts,UnaryForPrograms.popped] using
        (UnaryForPrograms.Visits.done (p := zeroPorts) (body := pushBit false)
          (⟨regs,fill s [] out⟩ : Data) (by simp [zeroPorts,fill]))
  | cons bit count ih =>
      let rp := readRegs regs 0 1 (some bit)
      let rb := Function.update rp 0 false
      have hb : Eval (pushBit false) 2
          (UnaryForPrograms.popped zeroPorts (⟨regs,fill s (bit::count) out⟩ : Data))
          (⟨rb,fill s count (false::out)⟩ : Data) := by
        simpa [pushBit,Subexp.TupleProgram.pushedState,UnaryForPrograms.popped,
          zeroPorts,rp,rb] using
          Subexp.TupleProgram.pushConst_eval (214 : Fin 256) (0 : Fin 16) false
            (⟨rp,fill s count out⟩ : Data)
      obtain ⟨rr,ht⟩ := ih (false::out) rb
      have he := UnaryForPrograms.Visits.step
        (p := zeroPorts) (body := pushBit false)
        (by simp [zeroPorts,fill] : (fill s (bit::count) out) zeroPorts.counter ≠ [])
        hb (by simp [zeroPorts,fill,UnaryForPrograms.popped]) ht
      have hout : List.replicate count.length false ++ (false::out) =
          List.replicate (count.length+1) false ++ out := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      rw [hout] at he
      refine ⟨rr,?_⟩
      convert he using 1 <;> simp [List.replicate_succ] ; omega

theorem zeroLoop_run (s : Store) (count out : List Bool)
    (hc : s 221=count) (ho : s 214=out) :
    ExecutesIn zeroLoop (4*count.length+2) s
      (Function.update (Function.update s 221 []) 214
        (List.replicate count.length false++out)) := by
  intro regs
  obtain ⟨rr,hv⟩ := zero_visits s count out regs
  have hs : fill s count out=s := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [fill]
  refine ⟨4*count.length+2,rr,le_rfl,?_⟩
  have he := hv.eval
  rw [hs] at he
  exact he

/-- Zero-mask construction retains the count master and all unrelated stacks. -/
theorem zero_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (h120 : s 120=[]) (h221 : s 221=[]) (h214 : s 214=[]) :
    ExecutesIn zeroCommand (11*n+7) s
      (Function.update s 214 (List.replicate n false)) := by
  let mid := Function.update s 221 (s 212)
  have h1 : ExecutesIn (copy 212 221) (7*n+5) s mid := by
    simpa [mid,hn,h221] using copy_run 212 221 s (by decide) (by decide) (by decide) h120
  have h2 := zeroLoop_run mid (s 212) [] (by simp [mid]) (by simp [mid,h214])
  have he : Function.update (Function.update mid 221 []) 214
      (List.replicate (s 212).length false++[]) =
      Function.update s 214 (List.replicate n false) := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [mid]
  rw [he] at h2
  have h := h1.seq h2
  convert h using 1 ; simp only [hn] ; omega

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Emit the computed beta at the actual all-zero sparse key. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

theorem origin_run_oai (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (he : ∀ i ∈ originScratch,s i=[]) :
    ExecutesIn origin (33*n+20*(s 220).length+83) s
      (Function.update s 217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217)) := by
  let s1 := Function.update s 214 (List.replicate n false)
  let s2 := Function.update s1 222 (originKey n).reverse
  let s3 := Function.update s2 228 (s 220)
  let s4 := Function.update s2 228 (s 220).reverse
  let s5 := Function.update s1 217
    (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217)
  have hl : (originKey n).length=n+2 := by
    simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits]
  have h1 : ExecutesIn PerturbationMaskProgram.zeroCommand (11*n+7) s s1 :=
    PerturbationMaskProgram.zero_run s n hn (he 120 (by simp [originScratch]))
      (he 221 (by simp [originScratch])) (he 214 (by simp [originScratch]))
  have h2 : ExecutesIn PerturbationEmitProgram.keyCommand (16*n+40) s1 s2 := by
    have h := PerturbationEmitProgram.key_run s1 (List.replicate n false) 0
      (by simp [s1]) (by simpa [s1] using he 221 (by simp [originScratch]))
      (by simpa [s1] using he 120 (by simp [originScratch]))
      (by simpa [s1] using he 222 (by simp [originScratch]))
      (by simpa [s1] using he 223 (by simp [originScratch]))
      (by simpa [s1] using he 224 (by simp [originScratch]))
    simpa [s2,originKey] using h
  have h3 : ExecutesIn (copy 220 228) (7*(s 220).length+5) s2 s3 := by
    simpa [s3,s2,s1,he 228 (by simp [originScratch])] using
      copy_run 220 228 s2 (by decide) (by decide) (by decide)
        (by simpa [s2,s1] using he 120 (by simp [originScratch]))
  have h4 : ExecutesIn (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (9*(s 220).length+7) s3 s4 := by
    intro regs
    have h := reverse_eval (⟨regs,s3⟩ : Data) 228 226 227 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s3,s2,s1] using he 226 (by simp [originScratch]))
      (by simpa [s3,s2,s1] using he 227 (by simp [originScratch]))
    exact ⟨9*(s 220).length+7,_,le_rfl,by simpa [s4,s3,afterReverse,StackRoutines.reverseStacks] using h⟩
  have hout : Function.update (Function.update (Function.update s4 222 []) 228 [])
      217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s4 217)=s5 := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;> by_cases h222 : i=222 <;>
      by_cases h228 : i=228 <;>
      simp [s5,s4,s2,s1,h214,h217,h222,h228,
        he 222 (by simp [originScratch]),he 228 (by simp [originScratch])]
  have h5 : ExecutesIn PerturbationEmitProgram.emitCommand
      (4*(n+2)+4*(s 220).length+13) s4 s5 := by
    have h := PerturbationEmitProgram.emit_run s4 (originKey n) (s 220)
      (by simp [s4,s2]) (by simp [s4])
    rw [hout,hl] at h
    exact h
  have hout2 : Function.update s5 214 []=Function.update s 217
      (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217) := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;>
      simp [s5,s1,h214,h217,he 214 (by simp [originScratch])]
  have h6 := clear_run 214 s5
  rw [hout2] at h6
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert h using 1 <;> first | rfl | (simp [s5, s1] ; ring)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run_oai
