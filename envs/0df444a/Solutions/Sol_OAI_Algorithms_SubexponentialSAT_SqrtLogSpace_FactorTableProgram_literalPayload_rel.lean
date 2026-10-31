-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:28:36.540961+00:00
-- url     : https://prove2.me/submissions/fd0a9b7f-9d14-453d-b15f-e3e1dddc4b23

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_origin_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

theorem cost_le (index bits : List Bool) : cost index bits ≤ 3 * index.length + 2 * bits.length + 6 := by
  induction index generalizing bits with
  | nil => simp only [cost,List.length_nil,Nat.mul_zero,Nat.zero_add,List.length_tail]; omega
  | cons b index ih =>
      have h := ih bits.tail
      have ht : bits.tail.length ≤ bits.length := by simp only [List.length_tail]; omega
      simp only [cost,List.length_cons]
      omega

theorem trace (index bits : List Bool) (regs : Fin 3 → Bool) :
    Trace program (cost index bits) (cfg (some 0) regs index bits)
      (cfg none (resultRegs (bits.getD index.length false)) [] []) := by
  induction index generalizing bits regs with
  | nil =>
      let r1 := readRegs regs 0 1 none
      let r2 := readRegs r1 2 1 bits.head?
      have ht := StackRoutines.clear_trace program 1 0 1 4 5 6 rfl rfl r2
        (ParserProgram.pair [] bits.tail)
      have hh := StackRoutines.halt_after_trace program ht 6 rfl rfl
      have hf : ⟨none, readRegs r2 0 1 none,
          StackRoutines.clearStacks 1 (ParserProgram.pair [] bits.tail)⟩ =
          cfg none (resultRegs (bits.getD 0 false)) [] [] := by
        apply congrArg₂ (fun (rs : Fin 3 → Bool) (ss : Fin 2 → List Bool) => (⟨none,rs,ss⟩ : Cfg 3 2 7))
        · funext i
          fin_cases i <;> simp [r2,r1,readRegs,resultRegs,List.getD_eq_getElem?_getD]
          cases bits <;> rfl
        · funext i
          fin_cases i <;> simp [StackRoutines.clearStacks,ParserProgram.pair]
      have hh' : Trace program (2 * bits.tail.length + 3) (cfg (some 4) r2 [] bits.tail)
          (cfg none (resultRegs (bits.getD 0 false)) [] []) := by
        simpa only [cfg,StackRoutines.clearResult,ParserProgram.pair,Matrix.cons_val_one,
          Matrix.head_cons, hf, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), Nat.add_assoc] using hh
      have hs : Trace program 3 (cfg (some 0) regs [] bits) (cfg (some 4) r2 [] bits.tail) := by
        refine .cons (b := cfg (some 1) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 3) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      simpa [cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans hh'
  | cons b index ih =>
      let r1 := readRegs regs 0 1 (some b)
      let r2 := readRegs r1 0 1 bits.head?
      have hs : Trace program 3 (cfg (some 0) regs (b :: index) bits)
          (cfg (some 0) r2 index bits.tail) := by
        refine .cons (b := cfg (some 1) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 2) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      have hg : bits.tail.getD index.length false = bits.getD (b :: index).length false := by
        cases bits <;> simp
      simpa only [cost,hg] using hs.trans (ih bits.tail r2)

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

theorem bitRead_eval (s : Store) (regs : Fin 16 → Bool) :
    ∃ rf, Eval bitRead (Subexp.TypeBitProgram.cost (s 222) (s 223))
      (⟨regs,s⟩ : Data) (⟨rf,Function.update (Function.update s 222 []) 223 []⟩ : Data) ∧
      rf 15=(s 223).getD (s 222).length false := by
  let d : Data := ⟨regs,s⟩
  let a := projectState flagRegs flagStacks d
  let b : State 3 2 := ⟨Subexp.TypeBitProgram.resultRegs ((s 223).getD (s 222).length false),![[],[]]⟩
  have ht := Subexp.TypeBitProgram.trace (s 222) (s 223) a.regs
  have ha : a.withPC (some Subexp.TypeBitProgram.program.entry)=
      Subexp.TypeBitProgram.cfg (some 0) a.regs (s 222) (s 223) := by
    apply congrArg (fun ss : Fin 2 → List Bool => (⟨some 0,a.regs,ss⟩ : Cfg 3 2 7))
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hb : b.withPC none=Subexp.TypeBitProgram.cfg none b.regs [] [] := by
    apply congrArg (fun ss : Fin 2 → List Bool => (⟨none,b.regs,ss⟩ : Cfg 3 2 7))
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have ht' : Trace Subexp.TypeBitProgram.program
      (Subexp.TypeBitProgram.cost (s 222) (s 223))
      (a.withPC (some Subexp.TypeBitProgram.program.entry)) (b.withPC none) := by
    rw [ha,hb]
    exact ht
  have he := eval_call_from_state Subexp.TypeBitProgram.program flagRegs flagStacks d
    (by decide) (by decide) ht'
  let rf := Function.extend flagRegs b.regs regs
  have hout : embedState flagRegs flagStacks d b =
      (⟨rf,Function.update (Function.update s 222 []) 223 []⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ (by decide) (by decide)
    · intro i; exact (show Function.Injective flagRegs from by decide).extend_apply b.regs regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,flagStacks]
    · intro i hi
      have h222 : i≠222 := by intro h; subst i; exact hi ⟨0,rfl⟩
      have h223 : i≠223 := by intro h; subst i; exact hi ⟨1,rfl⟩
      simp [d,h222,h223]
  rw [hout] at he
  refine ⟨rf,he,?_⟩
  change Function.extend flagRegs b.regs regs (flagRegs 2)=_
  rw [(show Function.Injective flagRegs from by decide).extend_apply]
  rfl

theorem readFlag_eval (s : Store) (source : Fin 256)
    (hsrc : source≠222) (hsrc' : source≠223) (h120s : source≠120)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (regs : Fin 16 → Bool) :
    ∃ k rf, k ≤ 10*(s 233).length+9*(s source).length+16 ∧
      Eval (readFlag source) k (⟨regs,s⟩ : Data) (⟨rf,s⟩ : Data) ∧
      rf 15=(s source).getD (s 233).length false := by
  let s1 := Function.update s 222 (s 233)
  let s2 := Function.update s1 223 (s source)
  have h1 : ExecutesIn (copy 233 222) (7*(s 233).length+5) s s1 := by
    simpa [s1,h222] using copy_run 233 222 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy source 223) (7*(s source).length+5) s1 s2 := by
    simpa [s1,s2,hsrc,h223] using copy_run source 223 s1 hsrc' h120s (by decide)
      (by simp [s1,h120])
  obtain ⟨n1,r1,hn1,he1⟩ := h1 regs
  obtain ⟨n2,r2,hn2,he2⟩ := h2 r1
  obtain ⟨rf,he3,hflag⟩ := bitRead_eval s2 r2
  have hout : Function.update (Function.update s2 222 []) 223 []=s := by
    funext i
    by_cases h222' : i=222 <;> by_cases h223' : i=223 <;>
      simp [s2,s1,h222',h223',h222,h223]
  rw [hout] at he3
  refine ⟨n1+(n2+Subexp.TypeBitProgram.cost (s2 222) (s2 223)),rf,?_,?_,?_⟩
  · have hc : Subexp.TypeBitProgram.cost (s2 222) (s2 223) ≤
        3*(s 233).length+2*(s source).length+6 := by
      simpa [s2,s1] using Subexp.TypeBitProgram.cost_le (s2 222) (s2 223)
    omega
  · exact he1.seq (he2.seq he3)
  · simpa [s2,s1] using hflag


theorem highConstant_run (s : Store) (n W : ℕ)
    (hn : (s 212).length=n) (hm : (s 235).length=n)
    (hzero : (s 207).length=W) (hone : (s 208).length=W)
    (h220 : s 220=[]) (he : ∀ i∈originScratch,s i=[]) :
    ExecutesIn highConstant (10*(s 233).length+42*n+29*W+108) s
      (Function.update s 217 (Encoding.frame (originKey n)++
        Encoding.frame (if (s 235).getD (s 233).length false then s 208 else s 207)++s 217)) := by
  intro regs
  let b := (s 235).getD (s 233).length false
  let value := if b then s 208 else s 207
  let s1 := Function.update s 220 value
  let s2 := Function.update s1 217 (Encoding.frame (originKey n)++Encoding.frame value++s 217)
  have hv : value.length=W := by cases hb:b <;> simp [value,hb,hzero,hone]
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_eval s 235 (by decide) (by decide) (by decide)
    (he 120 (by simp [originScratch])) (he 222 (by simp [originScratch]))
    (he 223 (by simp [originScratch])) regs
  have hcopy : ∃ nc rc, nc ≤ 7*W+6 ∧
      Eval (.ite 15 (copy 208 220) (copy 207 220)) nc
        (⟨rr,s⟩ : Data) (⟨rc,s1⟩ : Data) := by
    cases hb:b with
    | false =>
      obtain ⟨nc,rc,hnc,hc⟩ := copy_run 207 220 s (by decide) (by decide) (by decide)
        (he 120 (by simp [originScratch])) rr
      refine ⟨nc+1,rc,by simpa [hzero] using Nat.add_le_add_right hnc 1,?_⟩
      have hf : rr 15=false := hbit.trans hb
      have hh := Eval.ite_false (yes:=copy 208 220) hf hc
      simpa [s1,value,hb,h220] using hh
    | true =>
      obtain ⟨nc,rc,hnc,hc⟩ := copy_run 208 220 s (by decide) (by decide) (by decide)
        (he 120 (by simp [originScratch])) rr
      refine ⟨nc+1,rc,by simpa [hone] using Nat.add_le_add_right hnc 1,?_⟩
      have hf : rr 15=true := hbit.trans hb
      have hh := Eval.ite_true (no:=copy 207 220) hf hc
      simpa [s1,value,hb,h220] using hh
  obtain ⟨nc,rc,hnc,hc⟩ := hcopy
  have hs1 : ∀ i∈originScratch,s1 i=[] := by
    intro i hi
    have hi220 : i ≠ 220 := by
      intro h
      subst i
      simp [originScratch] at hi
    simpa [s1,hi220] using he i hi
  have horigin : ExecutesIn origin (33*n+20*W+83) s1 s2 := by
    simpa [s2,s1,hv] using origin_run s1 n (by simpa [s1] using hn) hs1
  obtain ⟨no,ro,hno,ho⟩ := horigin rc
  have hout : Function.update s2 220 []=Function.update s 217
      (Encoding.frame (originKey n)++Encoding.frame value++s 217) := by
    funext i
    by_cases h217' : i=217 <;> by_cases h220' : i=220 <;>
      simp [s2,s1,h217',h220',h220]
  have hclear := clear_run 220 s2
  rw [hout] at hclear
  obtain ⟨nf,rf,hnf,hf⟩ := hclear ro
  refine ⟨nr+(nc+(no+nf)),rf,?_,hr.seq (hc.seq (ho.seq hf))⟩
  simp only [s2,s1,Function.update_same,Function.update_of_ne (by decide : (220:Fin 256)≠217),hv] at hnf
  rw [hm] at hnr
  omega


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

theorem replaceInner_project (s : OuterStore) : replaceInner s (projectInner s)=s := by
  have h := embedState_project id innerPort (⟨fun _=>false,s⟩ : OuterData)
    Function.injective_id innerPort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceInner_update (s : OuterStore) (u : Store) (i : Fin 256) (bits : List Bool) :
    replaceInner s (Function.update u i bits)=Function.update (replaceInner s u) (innerPort i) bits :=
  ProgramLinking.extend_update innerPort_injective _ _ _ _

theorem liftInner_run (s : OuterStore) (code : Code) (K : ℕ) (u : Store)
    (h : ExecutesIn code K (projectInner s) u) :
    ExecutesOuter (liftInner code) (K+1) s (replaceInner s u) := by
  constructor
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id innerPort (⟨regs,s⟩ : OuterData)
    Function.injective_id innerPort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  unfold liftInner
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · simp [embedState]
  · rfl

/-- A common single-result service remains a single-result service after
relocation, with the exact one-step compiled-call overhead. -/
theorem liftInner_update_run (s : OuterStore) (code : Code) (K : ℕ)
    (i : Fin 256) (bits : List Bool)
    (h : ExecutesIn code K (projectInner s) (Function.update (projectInner s) i bits)) :
    ExecutesOuter (liftInner code) (K+1) s (Function.update s (innerPort i) bits) := by
  have hh := liftInner_run s code K _ h
  simpa only [replaceInner_update,replaceInner_project] using hh


theorem readFlag_outer (s : OuterStore) (source : Fin 256)
    (hsrc : source≠222) (hsrc' : source≠223) (h120s : source≠120)
    (h120 : s 460=[]) (h222 : s 562=[]) (h223 : s 563=[])
    (regs : Fin 16 → Bool) :
    ∃ k rf,k≤10*(s 573).length+9*(s (innerPort source)).length+17 ∧
      Eval (liftInner (readFlag source)) k (⟨regs,s⟩ : OuterData) (⟨rf,s⟩ : OuterData) ∧
      rf 15=(s (innerPort source)).getD (s 573).length false := by
  obtain ⟨k,rf,hk,he,hf⟩ := readFlag_eval (projectInner s) source hsrc hsrc' h120s
    (by simpa [projectInner,Function.comp_def,innerPort] using h120)
    (by simpa [projectInner,Function.comp_def,innerPort] using h222)
    (by simpa [projectInner,Function.comp_def,innerPort] using h223) regs
  have hl := eval_liftCommand_from_state (readFlag source) 0 0 id innerPort
    (⟨regs,s⟩ : OuterData) Function.injective_id innerPort_injective he
  have hout : embedState id innerPort (⟨regs,s⟩ : OuterData)
      (⟨rf,projectInner s⟩ : Data)=(⟨rf,s⟩ : OuterData) := by
    apply state_ext
    · simp [embedState]
    · exact replaceInner_project s
  rw [hout] at hl
  refine ⟨k+1,rf,?_,hl,?_⟩
  · simpa [projectInner,Function.comp_def,innerPort] using Nat.add_le_add_right hk 1
  · simpa [projectInner,Function.comp_def,innerPort] using hf


theorem literalPayload_rel_oai (s : OuterStore) (n W Klow Lrows Lpayload : ℕ) (Good : List Bool → Prop)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h545 : s 545=[]) (h557 : s 557=[]) (h220 : s 560=[])
    (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hlow : (s 574).getD (s 573).length false=false →
      ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k≤Klow ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval lowPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData))
    (hhigh : (s 574).getD (s 573).length false=true →
      Good (Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)))
    (hhighLength : (Encoding.frame (originKey n)++
      Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)).length≤Lpayload)
    (regs : Fin 16 → Bool) :
    ∃ words payload k rf,
      k≤10*(s 573).length+9*(s 574).length+18+
        (10*(s 573).length+42*n+29*W+109)+Klow ∧
      words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval literalPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData) := by
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_outer s 234 (by decide) (by decide) (by decide)
    (by simpa [innerPort] using he 120 (by simp [originScratch]))
    (by simpa [innerPort] using he 222 (by simp [originScratch]))
    (by simpa [innerPort] using he 223 (by simp [originScratch])) regs
  change nr≤10*(s 573).length+9*(s 574).length+17 at hnr
  change rr 15=(s 574).getD (s 573).length false at hbit
  cases hb:(s 574).getD (s 573).length false with
  | false =>
      obtain ⟨words,payload,nl,rl,hnl,hw,hp,hgood,hel⟩ := hlow hb rr
      have hflag : rr 15=false := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_false (yes:=liftInner highConstant) hflag hel)
      refine ⟨words,payload,nr+(nl+1),rl,by omega,hw,hp,hgood,?_⟩
      simpa [literalPayload,innerPort] using hrun
  | true =>
      let payload := Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)
      have hh := highConstant_run (projectInner s) n W
        (by simpa [projectInner,Function.comp_def,innerPort] using hn)
        (by simpa [projectInner,Function.comp_def,innerPort] using hm)
        (by simpa [projectInner,Function.comp_def,innerPort] using hzero)
        (by simpa [projectInner,Function.comp_def,innerPort] using hone)
        (by simpa [projectInner,Function.comp_def,innerPort] using h220)
        (by simpa [projectInner,Function.comp_def] using he)
      obtain ⟨nh,rh,hnh,heh⟩ := (liftInner_update_run s highConstant _ 217 _ hh).run rr
      change nh≤(10*(s 573).length+42*n+29*W+108)+1 at hnh
      have hflag : rr 15=true := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_true (no:=lowPayload) hflag heh)
      refine ⟨[],payload,nr+(nh+1),rh,by omega,by simp,hhighLength,hhigh hb,?_⟩
      have hz : Function.update s 545 []=s := by simpa only [←h545] using Function.update_eq_self 545 s
      simpa [literalPayload,innerPort,projectInner,Function.comp_def,payload,h557,hz] using hrun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel_oai
