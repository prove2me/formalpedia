-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:08:04.044381+00:00
-- url     : https://prove2.me/submissions/211bd5fd-6cb4-402e-9bb9-887bb72fbc57

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S184
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationBetaProgram_step_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramFraming
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preserving copies of every beta master and explicit scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

theorem prepareInput_run (s : Store) (h120 : s 120=[])
    (h230 : s 230=[]) (h231 : s 231=[]) (h220 : s 220=[])
    (h247 : s 247=[]) (h250 : s 250=[]) :
    ExecutesIn prepareInput (initBudget s) s (initialized s) := by
  let s1 := Function.update s 230 (s 205)
  let s2 := Function.update s1 231 (s 206)
  let s3 := Function.update s2 220 (s 207)
  let s4 := Function.update s3 247 (s 209)
  let s5 := Function.update s4 250 (s 211)
  have h1 : ExecutesIn (copy 205 230) (7*(s 205).length+5) s s1 := by
    simpa [s1,h230] using copy_run 205 230 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 206 231) (7*(s 206).length+5) s1 s2 := by
    simpa [s2,s1,h231] using copy_run 206 231 s1
      (by decide) (by decide) (by decide) (by simp [s1,h120])
  have h3 : ExecutesIn (copy 207 220) (7*(s 207).length+5) s2 s3 := by
    simpa [s3,s2,s1,h220] using copy_run 207 220 s2
      (by decide) (by decide) (by decide) (by simp [s2,s1,h120])
  have h4 : ExecutesIn (copy 209 247) (7*(s 209).length+5) s3 s4 := by
    simpa [s4,s3,s2,s1,h247] using copy_run 209 247 s3
      (by decide) (by decide) (by decide) (by simp [s3,s2,s1,h120])
  have h5 : ExecutesIn (copy 211 250) (7*(s 211).length+5) s4 s5 := by
    simpa [s5,s4,s3,s2,s1,h250] using copy_run 211 250 s4
      (by decide) (by decide) (by decide) (by simp [s4,s3,s2,s1,h120])
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first | (simp only [initBudget]; omega) | rfl

theorem finish_run (s : Store) : ExecutesIn finish (finishBudget s) s (finished s) := by
  have h1 := clear_run 230 s
  have h2 := clear_run 231 (Function.update s 230 [])
  have h3 := clear_run 247 (Function.update (Function.update s 230 []) 231 [])
  have h4 := clear_run 250 (Function.update (Function.update (Function.update s 230 []) 231 []) 247 [])
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | (simp [finishBudget]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid outer traversal. Every row frame and matching assignment bit is
consumed; selected rows call the actual scalar Horner and addition programs. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

theorem peekRow_eval {t d : ℕ} (regs : Fin 16 → Bool) (base : Store)
    (rows : List (List (Coeff t d) × Bool)) (acc : Coeff t d) :
    Eval peekRow 1 (⟨regs,ready base rows acc⟩ : Data) (peekReady regs base rows acc) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem loop_eval (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=L) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[])
    (regs : Fin 16 → Bool) :
    ∃ ns rf, ns ≤ rows.length*(stepBudget L t d+2)+1 ∧
      Eval loop ns (peekReady regs base rows acc)
        (⟨rf,ready base [] (rows.foldl (stepValue t a M cache theta) acc)⟩ : Data) := by
  induction rows generalizing regs acc with
  | nil =>
    refine ⟨1,(peekReady regs base [] acc).regs,by simp,?_⟩
    exact Eval.while_false (by simp [peekReady,rowsBits,Encoding.encodeList,readRegs])
  | cons row rows ih =>
    rcases row with ⟨P,b⟩
    have hl : P.length=L := hL (P,b) (by simp)
    obtain ⟨ns,rs,hns,hes⟩ := step_run t a M cache hz base hready theta acc P b rows
      hx hz0 (hc.trans hl.symm) hw h232 h240 h246 h248 h241 h244 h245 h251 h252
      (peekReady regs base ((P,b)::rows) acc).regs
    obtain ⟨nt,rt,hnt,het⟩ := ih (stepValue t a M cache theta acc (P,b))
      (fun row hr => hL row (by simp [hr])) rs
    have hg : (peekReady regs base ((P,b)::rows) acc).regs 0=true := by
      simp [peekReady,rowsBits,Encoding.encodeList,readRegs]
    have hp := peekRow_eval rs base rows (stepValue t a M cache theta acc (P,b))
    have h := Eval.while_true hg (hes.seq hp) het
    refine ⟨ns+1+nt+1,rt,?_,?_⟩
    · rw [hl] at hns
      simp only [List.length_cons]
      nlinarith
    · simpa only [loop, body, List.foldl_cons] using h

theorem traversal_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=L) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
    ExecutesIn (.seq peekRow loop) (rows.length*(stepBudget L t d+2)+2)
      (ready base rows acc)
      (ready base [] (rows.foldl (stepValue t a M cache theta) acc)) := by
  intro regs
  obtain ⟨ns,rf,hns,he⟩ := loop_eval t a M cache hz base hready theta acc rows L hL
    hx hz0 hc hw h232 h240 h246 h248 h241 h244 h245 h251 h252 regs
  exact ⟨1+ns,rf,by omega,(peekRow_eval regs base rows acc).seq he⟩

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed native beta scan from preserved row/choice masters. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

theorem betaCommand_run_oai (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h209 : base 209=RingProgram.flat theta)
    (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
    (he : WorkEmpty base) :
    ExecutesIn betaCommand (runBudget base rows.length L t d) base
      (Function.update base 220 (RingProgram.flat (runValue t a M cache theta rows))) := by
  have hemp (i : Fin 256) (hi : i∈workPorts) := he i hi
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  have hinit : initialized base=ready (staged base) rows z := by
    funext i
    by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=220 <;>
      by_cases h3 : i=247 <;> by_cases h4 : i=250 <;>
      simp [initialized,ready,staged,Function.update_apply,h0,h1,h2,h3,h4,h205,h206,h207,z]
  have h1 := prepareInput_run base hready.workspace.1
    (hemp 230 (by simp [workPorts])) (hemp 231 (by simp [workPorts]))
    (hemp 220 (by simp [workPorts])) (hemp 247 (by simp [workPorts]))
    (hemp 250 (by simp [workPorts]))
  rw [hinit] at h1
  have hframe : LowFrame base (staged base) :=
    lowFrame_update (lowFrame_update (lowFrame_refl base) 247 (by decide) _) 250 (by decide) _
  have h2 := traversal_run t a M cache hz (staged base) (hready.frame hframe) theta z rows L hL
    (by simp [staged,h209]) (by simp [staged,h207])
    (by simp [staged,h210]) (by simp [staged,h211])
    (by simpa [staged] using hemp 232 (by simp [workPorts]))
    (by simpa [staged] using hemp 240 (by simp [workPorts]))
    (by simpa [staged] using hemp 246 (by simp [workPorts]))
    (by simpa [staged] using hemp 248 (by simp [workPorts]))
    (by simpa [staged] using hemp 241 (by simp [workPorts]))
    (by simpa [staged] using hemp 244 (by simp [workPorts]))
    (by simpa [staged] using hemp 245 (by simp [workPorts]))
    (by simpa [staged] using hemp 251 (by simp [workPorts]))
    (by simpa [staged] using hemp 252 (by simp [workPorts]))
  let out := runValue t a M cache theta rows
  let last := ready (staged base) [] out
  have hend : finished last=Function.update base 220 (RingProgram.flat out) := by
    funext i
    by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=220 <;>
      by_cases h3 : i=247 <;> by_cases h4 : i=250 <;>
      simp [finished,last,ready,staged,h0,h1,h2,h3,h4,
        hemp 230 (by simp [workPorts]),hemp 231 (by simp [workPorts]),
        hemp 247 (by simp [workPorts]),hemp 250 (by simp [workPorts])]
  have hcost : finishBudget last=4*(d*baseWidth 3 t)+14 := by
    simp [finishBudget,last,ready,staged,rowsBits,Encoding.encodeList,h209,h211,RingProgram.flat_length]
    ring
  have h3 := finish_run last
  rw [hend,hcost] at h3
  have hall := h1.seq (h2.seq h3)
  convert hall using 1 <;> first | (simp only [runBudget]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run_oai
