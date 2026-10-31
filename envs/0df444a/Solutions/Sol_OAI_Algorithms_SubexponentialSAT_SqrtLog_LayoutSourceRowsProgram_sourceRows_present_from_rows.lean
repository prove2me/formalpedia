-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:43.897367+00:00
-- url     : https://prove2.me/submissions/ec1ad1fc-a5f1-4efe-a5e0-a27a8b0a1602

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup_Native_command_eval_found
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_initializeSource_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SeedIndexFormulas
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Numeric seed positions in the explicit finite-index enumeration -/

namespace SubexponentialSAT.Subexp.SeedIndexFormulas

open AssignmentEnumeration
open SubexponentialSAT.LocalExpectation (indexCode)

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (x : A) :
    (xs.map f).idxOf (f x) = xs.idxOf x := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons]
    by_cases h : y = x
    · subst y
      simp
    · rw [List.idxOf_cons_ne _ (fun hh => h (hf hh)), List.idxOf_cons_ne _ h, ih]

end SubexponentialSAT.Subexp.SeedIndexFormulas

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem pairPayload_original (v f : ℕ) :
    pairPayload v f=SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [v,f] := rfl

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stream_original (ps : List (ℕ × ℕ)) :
    stream ps=ProgramEncoding.encodeRecords
      (ps.map fun p => SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [p.1,p.2]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa only [stream,ProgramEncoding.encodeRecords,List.map_cons,Encoding.encodeList,
        pairPayload_original, Function.id_def] using congrArg
          (fun tail => true::(Encoding.frame (pairPayload p.1 p.2)++tail)) ih

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

theorem frame_injective : Function.Injective Encoding.frame := by
  intro a b h
  exact (Encoding.frame_append_injective (rest := []) (rest' := []) (by simpa using h)).1

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

theorem payload_injective : Function.Injective payload := by
  intro a b h
  have hf := Subexp.PackingMetadata.frame_injective h
  change Encoding.encodeList id [unary a.1,unary a.2] =
    Encoding.encodeList id [unary b.1,unary b.2] at hf
  have hp := Encoding.encodeList_injective Function.injective_id hf
  have hh : unary a.1=unary b.1 ∧ unary a.2=unary b.2 := by simpa using hp
  apply Prod.ext
  · simpa using congrArg List.length hh.1
  · simpa using congrArg List.length hh.2

theorem records_stream (ps : List (ℕ × ℕ)) :
    ProgramEncoding.encodeRecords (records ps)=LayoutOwnerFiberProgram.stream ps := by
  rw [LayoutOwnerFiberProgram.stream_original]
  rfl

theorem records_idxOf (ps : List (ℕ × ℕ)) (v f : ℕ) :
    (records ps).idxOf (pairKey (unary v) (unary f))=ps.idxOf (v,f) := by
  simpa only [List.idxOf,beq_eq_decide,records,payload] using
    Subexp.SeedIndexFormulas.idxOf_map_injective payload payload_injective ps (v,f)

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full pair-plan lookup at the source-row ABI. All query construction, record
comparison, index increments and cleanup are native paid instructions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

theorem pair_budget_eq (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f) :
    Native.budget d (records ps)+1=pairBudget v n f ps := by
  simp only [Native.budget,Local.budget,SubexpNodeIndexProgram.Internal.budget,
    hv,hn,hf,pairKey_length,List.length_append,List.length_replicate,records_stream,pairBudget]
  ring

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupFound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The same frozen pair-lookup program exposes its native found bit in register4.
No extra scan, metadata value, or runtime instruction is introduced. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem pairKey_mem_records (ps : List (ℕ × ℕ)) (v f : ℕ) :
    pairKey (unary v) (unary f) ∈ records ps ↔ (v,f) ∈ ps := by
  change payload (v,f) ∈ ps.map payload ↔ (v,f) ∈ ps
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    have hpeq := payload_injective he
    simpa only [hpeq] using hp
  · intro h
    exact List.mem_map.mpr ⟨(v,f),h,rfl⟩

/-- Register4 is the actual full-pair membership result, including the miss case.
This strengthens the frozen native command without adding an instruction. -/
theorem pair_command_eval_found (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f)
    (hmaster : d.stacks 337=LayoutOwnerFiberProgram.stream ps) (hc : Native.Clean d) :
    ∃ k, k+1 ≤ pairBudget v n f ps ∧ ∃ e : Native.Data,
      Eval Native.command k d e ∧
      e.stacks=Function.update d.stacks 304 (unary (ps.idxOf (v,n+f))) ∧
      e.regs 4=decide ((v,n+f) ∈ ps) := by
  have hm : d.stacks 337=ProgramEncoding.encodeRecords (records ps) := by
    simpa only [records_stream] using hmaster
  obtain ⟨k,hk,e,he,hs,hflag⟩ := Native.command_eval_found d (records ps) hm hc
  have hu : unary n++unary f=unary (n+f) := (List.replicate_add n f true).symm
  rw [hv,hn,hf,hu,records_idxOf] at hs
  simp only [hv,hn,hf,hu,pairKey_mem_records] at hflag
  refine ⟨k,?_,e,he,hs,hflag⟩
  rw [←pair_budget_eq d ps v n f hv hn hf]
  omega

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

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

theorem copy_run (src dst : Fin 340) (s : Store) (hsd : src ≠ dst)
    (hst : src ≠ 339) (hdt : 339 ≠ dst) (ht : s 339=[]) :
    ExecutesIn (copy src dst) (7*(s src).length+5) s
      (Function.update s dst (s src++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.copy_eval (⟨regs,s⟩ : Data) src dst 339 0 1
    hsd hst hdt (by decide) ht
  refine ⟨_,readRegs regs 0 1 none,le_rfl,?_⟩
  simpa [copy,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using he

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

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem frameBody_eval (regs : Fin 3 → Bool) (b : Bool)
    (source output : List Bool) (htrue : regs 2 = true) :
    Eval frameBody 3 (frameReady regs (b :: source) output)
      (frameReady (readRegs regs 0 1 (some b)) source (true :: b :: output)) := by
  let d := frameReady regs (b :: source) output
  let d1 := (Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have hh := Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (0 : Fin 3)) d)
    (Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) d1)
      (Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) d2))
  convert hh using 1 ;
    simp [ frameReady, frameData, d, d1, d2, Atom.eval, Atom.instr,
      State.ofCfg, execInstr, readRegs, htrue] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem frameLoop_eval (source output : List Bool) (regs : Fin 3 → Bool)
    (htrue : regs 2 = true) :
    ∃ final, final 2 = true ∧ Eval frameLoop (4 * source.length + 1)
      (frameReady regs source output) (frameData final [] (emitPairs source output)) := by
  induction source generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 none, by simpa [readRegs] using htrue, ?_⟩
    apply Eval.while_false
    simp [frameReady, frameData, readRegs]
  | cons b bs ih =>
    have hr : (readRegs regs 0 1 (some b)) 2 = true := by simpa [readRegs] using htrue
    obtain ⟨final, hf, he⟩ := ih (true :: b :: output) (readRegs regs 0 1 (some b)) hr
    refine ⟨final, hf, ?_⟩
    have hh := Eval.while_true
      (by simp [frameReady, frameData, readRegs] : (frameReady regs (b :: bs) output).regs 1 = true)
      (frameBody_eval regs b bs output htrue) he
    have hc : 3 + (4 * bs.length + 1) + 1 = 4 * (b :: bs).length + 1 := by simp; omega
    rw [hc] at hh
    exact hh

theorem emitPairs_append (a b out : List Bool) :
    emitPairs (a ++ b) out = emitPairs b (emitPairs a out) := by
  induction a generalizing out with
  | nil => rfl
  | cons x xs ih => simpa [emitPairs] using ih (true :: x :: out)

theorem emitPairs_frame (source out : List Bool) :
    emitPairs source.reverse (false :: out) = Encoding.frame source ++ out := by
  induction source with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, emitPairs_append, emitPairs, ih, Encoding.frame ]

theorem frameEmit_eval (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Eval frameEmit (4 * source.length + 5)
      (frameData regs source.reverse output)
      (frameData final [] (Encoding.frame source ++ output)) := by
  let r0 := Function.update regs (2 : Fin 3) false
  let r1 := Function.update r0 (2 : Fin 3) true
  have h0 : Eval (.atom (.set 2 false)) 1 (frameData regs source.reverse output)
      (frameData r0 source.reverse output) := Eval.atom _ _
  have h1 : Eval (.atom (.push 1 2)) 1 (frameData r0 source.reverse output)
      (frameData r0 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) (frameData r0 source.reverse output) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, r0]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h2 : Eval (.atom (.set 2 true)) 1 (frameData r0 source.reverse (false :: output))
      (frameData r1 source.reverse (false :: output)) := Eval.atom _ _
  have h3 : Eval (.atom (.pop 0 0 1)) 1 (frameData r1 source.reverse (false :: output))
      (frameReady r1 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) (frameData r1 source.reverse (false :: output)) using 1
    all_goals try with_reducible_and_instances rfl
    cases source.reverse <;>
      simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, frameReady] ;
      (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨final, _, hf⟩ := frameLoop_eval source.reverse (false :: output) r1 (by simp [r1])
  rw [emitPairs_frame] at hf
  refine ⟨final, ?_⟩
  have hh := h0.seq (h1.seq (h2.seq (h3.seq hf)))
  convert hh using 1 ; simp [] ; omega

theorem frameEmit_trace (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Trace frameEmitProgram (4 * source.length + 6)
      ((frameData regs source.reverse output).withPC (some frameEmitProgram.entry))
      ((frameData final [] (Encoding.frame source ++ output)).withPC none) := by
  obtain ⟨final,hf⟩ := frameEmit_eval source output regs
  refine ⟨final, ?_⟩
  simpa [frameEmitProgram, Nat.add_assoc] using compiled_halt_trace hf 0 1
end SubexponentialSAT.SqrtLog.Squarefree.Program

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

theorem frameRegisters_injective : Function.Injective frameRegisters := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by decide

theorem frameRow_run (s : Store) :
    ExecutesIn frameRow (4*(s 330).length+6) s
      (Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334)) := by
  intro regs
  let a : Data := ⟨regs,s⟩
  let small := projectState frameRegisters frameStacks a
  obtain ⟨rf,ht⟩ := Squarefree.Program.frameEmit_trace (s 330).reverse (s 334) small.regs
  have heq : Squarefree.Program.frameData small.regs ((s 330).reverse).reverse (s 334)=small := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,frameStacks]
  rw [heq] at ht
  have he := eval_call_from_state Squarefree.Program.frameEmitProgram frameRegisters frameStacks a
    frameRegisters_injective frameStacks_injective ht
  let out := Squarefree.Program.frameData rf [] (Encoding.frame (s 330).reverse++s 334)
  have hs : out.stacks=Function.update (Function.update small.stacks 0 []) 1
      (Encoding.frame (s 330).reverse++s 334) := by
    funext i; fin_cases i <;> simp [out,Squarefree.Program.frameData]
  have hh : (embedState frameRegisters frameStacks a out).stacks =
      Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334) := by
    change Function.extend frameStacks out.stacks s = _
    rw [hs,ProgramLinking.extend_update frameStacks_injective,
      ProgramLinking.extend_update frameStacks_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project frameRegisters frameStacks a frameRegisters_injective frameStacks_injective)
    change Function.extend frameStacks small.stacks s=s at hb
    rw [hb]
    rfl
  change Eval frameRow (4*(s 330).reverse.length+6) a
    (embedState frameRegisters frameStacks a out) at he
  have hout : embedState frameRegisters frameStacks a out=
      (⟨(embedState frameRegisters frameStacks a out).regs,
        Function.update (Function.update s 330 []) 334
          (Encoding.frame (s 330).reverse++s 334)⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hh
  rw [hout] at he
  exact ⟨4*(s 330).length+6,(embedState frameRegisters frameStacks a out).regs,
    le_rfl,by simpa [a] using he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem emitRow_run (s : Store) (h330 : s 330=[]) (h334 : s 334=[]) :
    ExecutesIn emitRow (13*(s 240).length+20) s
      (Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332)) := by
  let s1 := Function.update (Function.update s 240 []) 330 (s 240).reverse
  let s2 := Function.update (Function.update s1 330 []) 334 (Encoding.frame (s 240))
  let s3 := Function.update s2 334 (rowRecord (s 240))
  have h1 : ExecutesIn (transfer 240 330) (3*(s 240).length+3) s s1 := by
    simpa [s1,h330] using transfer_run 240 330 s (by decide)
  have h2 : ExecutesIn frameRow (4*(s 240).length+6) s1 s2 := by
    simpa [s1,s2,h334] using frameRow_run s1
  have h3 : ExecutesIn (push 334 true) 2 s2 s3 := by
    simpa [s3,s2,rowRecord] using push_run 334 true s2
  have h4 := transfer_run 334 332 s3 (by decide)
  have he : Function.update (Function.update s3 334 []) 332
      ((s3 334).reverse++s3 332)=
        Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h332 : i=332 <;>
      by_cases hh330 : i=330 <;> by_cases hh334 : i=334 <;>
      simp [s3,s2,s1,h240,h332,hh330,hh334,h330,h334]
  rw [he] at h4
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp [s3,s2,rowRecord]
  omega

theorem finishRows_run (s : Store) (h205 : s 205=[]) :
    ExecutesIn finishRows (3*(s 332).length+8) s
      (Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false])) := by
  have h1 := push_run 332 false s
  have h2 := transfer_run 332 205 (Function.update s 332 (false::s 332)) (by decide)
  have he : Function.update (Function.update (Function.update s 332 (false::s 332)) 332 [])
      205 ((Function.update s 332 (false::s 332) 332).reverse ++
      (Function.update s 332 (false::s 332) 205))=
        Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false]) := by
    simp [h205,List.reverse_cons]
  rw [he] at h2
  exact (h1.seq h2).mono (by simp; omega)

theorem row_popped (base : Store) (j : ℕ) (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped rowPorts (⟨regs,rowState base j remaining acc⟩ : Data)=
      (⟨readRegs regs 14 15 remaining.head?,rowState base j remaining.tail acc⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,rowPorts,rowState]
  · funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [UnaryForPrograms.popped,rowPorts,rowState,h320,h331,h332]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

theorem records_length (encode : Witness → List Bool) (R : ℕ → Witness → Prop)
    (W j : ℕ) (ws : List Witness) (h : RowProperty encode R W j ws) :
    (records encode ws).length=ws.length*(2*W+2) := by
  induction ws generalizing j with
  | nil => simp [records]
  | cons w ws ih =>
      obtain ⟨_,hw,ht⟩ := h
      change (rowRecord (encode w)++records encode ws).length=(w::ws).length*(2*W+2)
      rw [List.length_append,ih (j+1) ht]
      simp only [rowRecord,List.length_cons,Encoding.length_frame,hw]
      ring

theorem records_encoding (encode : Witness → List Bool) (ws : List Witness) :
    records encode ws++[false]=Encoding.encodeList encode ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simpa [records,rowRecord,Encoding.encodeList,List.append_assoc] using
        (congrArg (fun b => rowRecord (encode w)++b) ih)

theorem rowTail_run (base : Store) (j : ℕ) (remaining acc bits : List Bool)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[]) :
    ExecutesIn (.seq emitRow (push 320 true)) (13*bits.length+22)
      (Function.update (rowState base j remaining acc) 240 bits)
      (rowState base (j+1) remaining ((rowRecord bits).reverse++acc)) := by
  let s1 := Function.update (rowState base j remaining acc) 240 bits
  let s2 := rowState base j remaining ((rowRecord bits).reverse++acc)
  have he1 : Function.update (Function.update s1 240 []) 332
      ((rowRecord (s1 240)).reverse++s1 332)=s2 := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;>
      by_cases h332 : i=332 <;> by_cases hh240 : i=240 <;>
      simp [s2,s1,rowState,Function.update_apply,h320,h331,h332,hh240,h240]
  have h1 : ExecutesIn emitRow (13*bits.length+20) s1 s2 := by
    have h := emitRow_run s1 (by simp [s1,rowState,h330]) (by simp [s1,rowState,h334])
    rw [he1] at h
    simpa [s1] using h
  have h2 := push_run 320 true s2
  have he2 : Function.update s2 320 (true::s2 320)=
      rowState base (j+1) remaining ((rowRecord bits).reverse++acc) := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [s2,rowState,h320,h331,h332,List.replicate_succ]
  rw [he2] at h2
  exact (h1.seq h2).mono (by omega)

theorem rowBody_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (j : ℕ) (hj : j < N) (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ w n rf, R j w ∧ (encode w).length=W ∧ n ≤ K+13*W+22 ∧
      Eval (rowBody callback) n (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+1) remaining ((rowRecord (encode w)).reverse++acc)⟩ : Data) := by
  obtain ⟨w,n1,r1,hw,hl,hn1,he1⟩ := spec j hj remaining acc regs
  obtain ⟨n2,r2,hn2,he2⟩ := rowTail_run base j remaining acc (encode w) h240 h330 h334 r1
  exact ⟨w,n1+n2,r2,hw,hl,by omega,he1.seq he2⟩

theorem row_visits_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) (regs : Fin 16 → Bool) :
    ∃ ws costs n rf, RowProperty encode R W j ws ∧ ws.length=remaining.length ∧
      n ≤ remaining.length*(K+13*W+24)+2 ∧
      UnaryForPrograms.Visits rowPorts (rowBody callback) costs n
        (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+remaining.length) [] ((records encode ws).reverse++acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,True.intro,rfl,by simp,?_⟩
    simpa only [row_popped,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,records,List.flatMap_nil,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := rowPorts) (body := rowBody callback)
        (⟨regs,rowState base j [] acc⟩ : Data) (by simp [rowState,rowPorts])
  | cons b remaining ih =>
    obtain ⟨w,nb,rb,hw,hl,hnb,hb⟩ := rowBody_rel callback base encode R N K W spec h240 h330 h334
      j (by simp only [List.length_cons] at hj; omega) remaining acc (readRegs regs 14 15 (some b))
    obtain ⟨ws,costs,nt,rt,hws,hcount,hnt,ht⟩ := ih ((rowRecord (encode w)).reverse++acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) rb
    refine ⟨w::ws,nb::costs,nb+nt+2,rt,⟨hw,hl,hws⟩,by simp [hcount],?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := rowPorts) (body := rowBody callback)
        (d := (⟨regs,rowState base j (b::remaining) acc⟩ : Data))
        (by simp [rowState,rowPorts])
        (by simpa only [row_popped,List.head?_cons,List.tail_cons] using hb)
        (by simp [rowState,rowPorts,UnaryForPrograms.popped]) ht
      simpa [List.length_cons,records,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rowsCommand_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) (regs : Fin 16 → Bool) :
    ∃ ws n rf, RowProperty encode R W 0 ws ∧ ws.length=N ∧ n ≤ N*(K+19*W+39)+18 ∧
      Eval (rowsCommand callback) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 205 (Encoding.encodeList encode ws)⟩ : Data) := by
  let s1 := rowState base 0 (base 212) []
  have he1 : Function.update base 331 (base 212++base 331)=s1 := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;> by_cases hi332 : i=332 <;>
      simp [s1,rowState,hi320,hi331,hi332,h320,h331,h332]
  obtain ⟨n1,r1,hn1,hec⟩ := copy_run 212 331 base (by decide) (by decide) (by decide) h339 regs
  rw [he1] at hec
  obtain ⟨ws,costs,n2,r2,hr,hcount,hn2,he2⟩ := row_visits_rel callback base encode R N K W spec
    h240 h330 h334 (base 212) [] 0 (by omega) r1
  let s2 := rowState base N [] (records encode ws).reverse
  have hh2 : Eval (rowLoop callback) n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := by
    simpa [rowLoop,s1,s2,hN] using he2.eval
  let s3 := Function.update s2 320 []
  obtain ⟨n3,r3,hn3,he3⟩ := clear_run 320 s2 r2
  obtain ⟨n4,r4,hn4,he4⟩ := finishRows_run s3 (by simp [s3,s2,rowState,h205]) r3
  have hout : Function.update (Function.update s3 332 []) 205 ((s3 332).reverse++[false])=
      Function.update base 205 (Encoding.encodeList encode ws) := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;>
      by_cases hi332 : i=332 <;> by_cases hi205 : i=205 <;>
      simp [s3,s2,rowState,hi320,hi331,hi332,hi205,h320,h331,h332,
        records_encoding]
  rw [hout] at he4
  have hwlen := records_length encode R W 0 ws hr
  refine ⟨ws,n1+(n2+(n3+n4)),r4,hr,hcount.trans hN,?_,hec.seq (hh2.seq (he3.seq he4))⟩
  have hn3' : n3 ≤ 2*N+3 := by simpa [s2,rowState] using hn3
  have hn4' : n4 ≤ 3*(records encode ws).length+8 := by simpa [s3,s2,rowState] using hn4
  rw [hcount,hN] at hwlen
  rw [hwlen] at hn4'
  rw [hN] at hn1 hn2
  nlinarith

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer source-row controller, including cache initialization,
actual pair-plan search, row traversal, and packed-index cleanup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem sourceRows_present_from_rows_oai {Witness : Type*}
    (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∈ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D W⟩ : Data))
    (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (K rowWidth : ℕ)
    (hspec : RelRowSpec (sourceRowWith source) (preparedSourceStore s D W ps v N f) encode R N K rowWidth)
    (hclean : RowsClean (preparedSourceStore s D W ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, RowProperty encode R rowWidth 0 ws ∧ ws.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D W+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+19*rowWidth+39)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D W) 205 (Encoding.encodeList encode ws)⟩ : Data) := by
  let s1 := initializeFinish s D W
  let p := preparedSourceStore s D W ps v N f
  obtain ⟨n1,r1,hn1,he1⟩ := initializeSource_run s D W hinit regs
  have hc : LayoutSourcePlanLookup.Native.Clean (⟨r1,s1⟩ : Data) := hlookup
  obtain ⟨n2,hn2,e2,he2,hs2,hflag⟩ := LayoutSourcePlanLookup.pair_command_eval_found
    (⟨r1,s1⟩ : Data) ps v N f
    (by simpa [s1,initializeFinish] using hv)
    (by simpa [s1,initializeFinish] using hN)
    (by simpa [s1,initializeFinish] using hf)
    (by simpa [s1,initializeFinish] using hplan) hc
  have he2' : Eval LayoutSourcePlanLookup.Native.command n2 (⟨r1,s1⟩ : Data)
      (⟨e2.regs,p⟩ : Data) := by
    have hh : e2=(⟨e2.regs,p⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hs2
    rw [hh] at he2
    exact he2
  obtain ⟨ws,n3,r3,hr,hcount,hn3,he3⟩ := rowsCommand_rel (sourceRowWith source) p encode R N K rowWidth hspec
    (by simp [p,preparedSourceStore,initializeFinish,hN,LayoutSourcePlanLookup.unary])
    (hclean 240 (by simp)) (hclean 330 (by simp)) (hclean 334 (by simp))
    (hclean 320 (by simp)) (hclean 331 (by simp)) (hclean 332 (by simp))
    (hclean 205 (by simp)) (hclean 339 (by simp)) e2.regs
  let p' := Function.update p 205 (Encoding.encodeList encode ws)
  obtain ⟨n4,r4,hn4,he4⟩ := clear_run 304 p' r3
  have h304 : s1 304=[] := hlookup 304 (by simp)
  have hout : Function.update p' 304 []=
      Function.update s1 205 (Encoding.encodeList encode ws) := by
    funext i
    by_cases h : i=304 <;>
      simp [p',p,preparedSourceStore,s1,Function.update_apply,h,h304]
  rw [hout] at he4
  have hbranch := Eval.ite_true (no := zeroRows) (by simpa [hmem] using hflag) he3
  refine ⟨ws,n1+(n2+((n3+1)+n4)),r4,hr,hcount,?_,he1.seq (he2'.seq (hbranch.seq he4))⟩
  have hn4' : n4 ≤ 2*(ps.idxOf (v,N+f))+3 := by
    simpa [p',p,preparedSourceStore,LayoutSourcePlanLookup.unary] using hn4
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows_oai.{u_1}
