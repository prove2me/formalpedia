-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:06:00.297106+00:00
-- url     : https://prove2.me/submissions/1dc55907-99e7-47ee-82f7-61debc5c6fea

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_findOwner_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTupleCheckRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw natural-field reader. Its stopping delimiter is consumed, while
all subsequent fields and all other bank are preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read
open SubexponentialSAT.BitProgram

theorem zero {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (tail : List Bool)
    (hs : bank src = false :: tail) :
    Trace (program src dst value present) 3 (start regs bank)
      (finish src dst value present regs bank 0 tail) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, start, finish,
    hs, readRegs, hvp, Ne.symm hsd ]

theorem tick {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (tail : List Bool)
    (hs : bank src = true :: tail) :
    Trace (program src dst value present) 3 (start regs bank)
      (start (readRegs regs value present (some true))
        (Function.update (Function.update bank src tail) dst (true :: bank dst))) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, start,
    hs, readRegs, hvp, Ne.symm hsd]

theorem replicate_push (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons true) ih

theorem run {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (n : ℕ) (tail : List Bool)
    (hs : bank src = Encoding.encodeNat n ++ tail) :
    Trace (program src dst value present) (3 * n + 3) (start regs bank)
      (finish src dst value present regs bank n tail) := by
  induction n generalizing regs bank with
  | zero => exact zero src dst value present hvp hsd regs bank tail (by simpa [Encoding.encodeNat] using hs)
  | succ n ih =>
    have hs' : bank src = true :: (Encoding.encodeNat n ++ tail) := by
      simpa [Encoding.encodeNat, List.replicate_succ, List.append_assoc] using hs
    let mid := Function.update (Function.update bank src (Encoding.encodeNat n ++ tail)) dst
      (true :: bank dst)
    have ht := tick src dst value present hvp hsd regs bank _ hs'
    have hh := ih (readRegs regs value present (some true)) mid
      (by simp [mid, hsd])
    have hf : finish src dst value present (readRegs regs value present (some true)) mid n tail =
        finish src dst value present regs bank (n + 1) tail := by
      apply congrArg₂ (Cfg.mk none)
      · funext i; simp only [readRegs, Function.update_apply]; split_ifs <;> simp_all
      · funext i
        simp [ mid, Function.update_apply, List.replicate_succ]
        split_ifs <;> simp_all [replicate_push]
    rw [hf] at hh
    convert ht.trans hh using 1 ; omega
end SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem ExecutesIn.seq {a b : Code} {A B : ℕ} {s t u : Store}
    (ha : ExecutesIn a A s t) (hb : ExecutesIn b B t u) :
    ExecutesIn (.seq a b) (A+B) s u := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesIn.mono {c : Code} {A B : ℕ} {s t : Store}
    (h : ExecutesIn c A s t) (hab : A ≤ B) : ExecutesIn c B s t := by
  intro regs
  obtain ⟨n,rf,hn,he⟩ := h regs
  exact ⟨n,rf,hn.trans hab,he⟩

theorem transfer_run (src dst : Fin 340) (s : Store) (h : src ≠ dst) :
    ExecutesIn (transfer src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.transfer_eval (⟨regs,s⟩ : Data) src dst 0 1 h (by decide)
  exact ⟨_,_,le_rfl,he⟩

theorem clear_run (src : Fin 340) (s : Store) :
    ExecutesIn (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro regs
  have ht := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 regs s) 2 rfl rfl
  refine ⟨_,readRegs regs 0 1 none,le_rfl,Eval.call _ ?_⟩
  simpa [StackRoutines.clearProgram,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,Nat.add_assoc] using ht

theorem push_run (dst : Fin 340) (b : Bool) (s : Store) :
    ExecutesIn (push dst b) 2 s (Function.update s dst (b::s dst)) := by
  intro regs
  exact ⟨2,Function.update regs 0 b,le_rfl,Subexp.TupleProgram.pushConst_eval dst 0 b ⟨regs,s⟩⟩

theorem readIndex_run (s : Store) (i : ℕ) (tail : List Bool)
    (hs : s 329=Encoding.encodeNat i++tail) (hc : s 305=[]) :
    ExecutesIn readIndex (3*i+3) s
      (Function.update (Function.update s 329 tail) 305 (List.replicate i true)) := by
  intro regs
  have h := RowSelectionProgramTupleCheck.Read.run (329 : Fin 340) 305 (0 : Fin 16) 1
    (by decide) (by decide) regs s i tail hs
  refine ⟨_,readRegs regs 0 1 (some false),le_rfl,Eval.call _ ?_⟩
  simpa [RowSelectionProgramTupleCheck.Read.start,RowSelectionProgramTupleCheck.Read.finish,
    StructuredProgram.State.withPC,hc] using h

theorem appendSource_run (s : Store) :
    ExecutesIn appendSource (3*(s 287).length+7) s (appendResult s) := by
  let s1 := Function.update (Function.update s 287 []) 333 ((s 287).reverse++s 333)
  let s2 := Function.update s1 333 (true::s1 333)
  have h1 := transfer_run 287 333 s (by decide)
  have h2 := push_run 333 true s1
  have h3 := push_run 333 false s2
  have he : Function.update s2 333 (false::s2 333)=appendResult s := by
    funext i
    by_cases hi : i=333
    · subst i
      simp [s2,s1,appendResult,List.reverse_append,List.reverse_cons,List.append_assoc]
    · simp [s2,s1,appendResult,hi]
  rw [he] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem zeroSource_run (s : Store) (h : s 333=[]) :
    ExecutesIn zeroSource 4 s (Function.update s 333 [false,false]) := by
  have h1 := push_run 333 false s
  have h2 := push_run 333 false (Function.update s 333 (false::s 333))
  have he : Function.update (Function.update s 333 (false::s 333)) 333
      (false::(Function.update s 333 (false::s 333)) 333)=Function.update s 333 [false,false] := by
    simp [h]
  rw [he] at h2
  exact h1.seq h2

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem fiber_popped (base : Store) (ids : List ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped fiberPorts (⟨regs,fiberState base ids acc⟩ : Data) =
      (⟨readRegs regs 14 15 (List.replicate ids.length true).head?,
        Function.update (fiberState base ids acc) 328
          (List.replicate ids.length true).tail⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,fiberPorts,fiberState]
  · simp [UnaryForPrograms.popped,fiberPorts,fiberState]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

theorem finishSource_run (base : Store) (h305 : base 305=[]) (h287 : base 287=[])
    (i : ℕ) (ids : List ℕ) (acc bytes : List Bool) :
    ExecutesIn (.seq appendSource (clear 305)) (3*bytes.length+2*i+10)
      (Function.update (Function.update (fiberState base ids acc) 305
        (List.replicate i true)) 287 bytes)
      (fiberState base ids ((bytes++[true,false]).reverse++acc)) := by
  let u := Function.update (Function.update (fiberState base ids acc) 305
    (List.replicate i true)) 287 bytes
  have h1 := appendSource_run u
  have h2 := clear_run 305 (appendResult u)
  have he : Function.update (appendResult u) 305 []=
      fiberState base ids ((bytes++[true,false]).reverse++acc) := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;> by_cases hh287 : j=287 <;>
      simp [u,appendResult,fiberState,Function.update_apply,h328,h329,h333,hh305,hh287,
        h305,h287,List.reverse_append,List.append_assoc]
  rw [he] at h2
  apply (h1.seq h2).mono
  simp [u,appendResult,fiberState]
  omega

theorem fiberBody_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (i : ℕ) (hi : i ≤ I) (ids : List ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ w n rf, R i w ∧ n ≤ K+5*I+3*L+13 ∧
      Eval (fiberBody source) n
        (⟨regs,Function.update (fiberState base (i::ids) acc) 328
          (List.replicate ids.length true)⟩ : Data)
        (⟨rf,fiberState base ids ((encode w++[true,false]).reverse++acc)⟩ : Data) := by
  let s := Function.update (fiberState base (i::ids) acc) 328 (List.replicate ids.length true)
  let t := Function.update (fiberState base ids acc) 305 (List.replicate i true)
  have h1 := readIndex_run s i (indexBytes ids)
    (by simp [s,fiberState,indexBytes]) (by simp [s,fiberState,h305])
  have he1 : Function.update (Function.update s 329 (indexBytes ids)) 305
      (List.replicate i true)=t := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;>
      simp [s,t,fiberState,Function.update_apply,h328,h329,h333,hh305]
  rw [he1] at h1
  obtain ⟨n1,r1,hn1,he1⟩ := h1 regs
  obtain ⟨w,n2,r2,hw,hl,hn2,he2⟩ := spec i hi ids acc r1
  obtain ⟨n3,r3,hn3,he3⟩ := finishSource_run base h305 h287 i ids acc (encode w) r2
  exact ⟨w,n1+(n2+n3),r3,hw,by omega,he1.seq (he2.seq he3)⟩

theorem fiber_visits_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i∈ids, i ≤ I) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ ws costs n rf, List.Forall₂ R ids ws ∧ n ≤ ids.length*(K+5*I+3*L+15)+2 ∧
      UnaryForPrograms.Visits fiberPorts (fiberBody source) costs n
        (⟨regs,fiberState base ids acc⟩ : Data)
        (⟨rf,fiberState base [] ((emittedBytes encode ws).reverse++acc)⟩ : Data) := by
  induction ids generalizing acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,List.Forall₂.nil,by simp,?_⟩
    have he : Function.update (fiberState base [] acc) 328 []=fiberState base [] acc := by
      funext j
      by_cases hj : j=328 <;> simp [fiberState,Function.update_apply,hj]
    simpa [fiber_popped,he,emittedBytes] using
      UnaryForPrograms.Visits.done (p := fiberPorts) (body := fiberBody source)
        (⟨regs,fiberState base [] acc⟩ : Data) (by simp [fiberPorts,fiberState])
  | cons i ids ih =>
    obtain ⟨w,nb,rb,hw,hnb,hb⟩ := fiberBody_rel source base encode R I K L spec h305 h287
      i (hI i (by simp)) ids acc (readRegs regs 14 15 (some true))
    obtain ⟨ws,costs,nt,rt,hws,hnt,ht⟩ := ih (by intro j hj; exact hI j (by simp [hj]))
      ((encode w++[true,false]).reverse++acc) rb
    refine ⟨w::ws,nb::costs,nb+nt+2,rt,List.Forall₂.cons hw hws,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := fiberPorts) (body := fiberBody source)
        (d := (⟨regs,fiberState base (i::ids) acc⟩ : Data))
        (by simp [fiberPorts,fiberState])
        (by simpa [fiber_popped,List.replicate_succ] using hb)
        (by simp [fiberState,fiberPorts,UnaryForPrograms.popped]) ht
      simpa [emittedBytes,List.reverse_append,List.append_assoc] using h

theorem fiberLoop_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i∈ids, i ≤ I) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ ws n rf, List.Forall₂ R ids ws ∧ n ≤ ids.length*(K+5*I+3*L+15)+2 ∧
      Eval (fiberLoop source) n (⟨regs,fiberState base ids acc⟩ : Data)
        (⟨rf,fiberState base [] ((emittedBytes encode ws).reverse++acc)⟩ : Data) := by
  obtain ⟨ws,costs,n,rf,hws,hn,he⟩ := fiber_visits_rel source base encode R I K L spec
    h305 h287 ids hI acc regs
  exact ⟨ws,n,rf,hws,hn,he.eval⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

theorem sourceForOwner_run_oai (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, List.Forall₂ R (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws ∧
      n ≤ LayoutOwnerFiberProgram.budget query ps+
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
      Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 333 ([false,false]++emittedBytes encode ws).reverse⟩ : Data) := by
  let ids := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  let b := Function.update (Function.update base 328 (List.replicate ids.length true))
    329 (indexBytes ids)
  obtain ⟨n1,hn1,r1,he1⟩ := findOwner_eval (⟨regs,base⟩ : Data) query ps hq hs hclean
  have he1' : Eval findOwner n1 (⟨regs,base⟩ : Data) (⟨r1,b⟩ : Data) := by
    simpa [ownerResult,b,ids,indexBytes,LayoutOwnerFiberProgram.encodeIndices,
      LayoutOwnerFiberProgram.unary] using he1
  obtain ⟨n2,r2,hn2,he2⟩ := zeroSource_run b (by simp [b,h333]) r1
  have he2' : Eval zeroSource n2 (⟨r1,b⟩ : Data)
      (⟨r2,fiberState base ids [false,false]⟩ : Data) := by
    simpa [fiberState,b] using he2
  obtain ⟨ws,n3,r3,hr,hn3,he3⟩ := fiberLoop_rel source base encode R I K L spec
    h305 h287 ids hI [false,false] r2
  have h328 : base 328=[] := hclean 9 (by decide)
  have h329 : base 329=[] := hclean 10 (by decide)
  have hout : fiberState base [] ((emittedBytes encode ws).reverse++[false,false])=
      Function.update base 333 ([false,false]++emittedBytes encode ws).reverse := by
    funext j
    by_cases hh328 : j=328 <;> by_cases hh329 : j=329 <;> by_cases hh333 : j=333 <;>
      simp [fiberState,indexBytes,hh328,hh329,hh333,h328,h329]
  rw [hout] at he3
  exact ⟨ws,n1+(n2+n3),r3,hr,by dsimp only [ids] at hn3; omega,he1'.seq (he2'.seq he3)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run_oai.{u_1}
