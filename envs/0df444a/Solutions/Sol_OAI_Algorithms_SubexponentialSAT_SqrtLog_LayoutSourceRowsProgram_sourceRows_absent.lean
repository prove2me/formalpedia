-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:06:03.406884+00:00
-- url     : https://prove2.me/submissions/c59e2ef6-1f1c-42c4-89d6-e2b1f3433a00

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup_Native_command_eval_found
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_initializeSource_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_zeroRows_run

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

theorem clear_run (src : Fin 340) (s : Store) :
    ExecutesIn (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro regs
  have ht := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 regs s) 2 rfl rfl
  refine ⟨_,readRegs regs 0 1 none,le_rfl,Eval.call _ ?_⟩
  simpa [StackRoutines.clearProgram,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,Nat.add_assoc] using ht

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

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

theorem sourceRows_absent_oai (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∉ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D W⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s D W ps v N f)) :
    ExecutesIn (sourceRowsWith source)
      (LayoutSourceRowsProgramInitialize.budget D W+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*W)+44)+
        2*(ps.idxOf (v,N+f))+23) s
      (Function.update (initializeFinish s D W) 205
        (Encoding.encodeList id (List.replicate N (List.replicate (D*W) false)))) := by
  intro regs
  let s1 := initializeFinish s D W
  let p := preparedSourceStore s D W ps v N f
  let bits := List.replicate (D*W) false
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
  obtain ⟨n3,r3,hn3,he3⟩ := zeroRows_run p bits N
    (by simp [p,bits,preparedSourceStore,initializeFinish])
    (by simp [p,preparedSourceStore,initializeFinish,hN,LayoutSourcePlanLookup.unary])
    (hclean 240 (by simp)) (hclean 330 (by simp)) (hclean 334 (by simp))
    (hclean 320 (by simp)) (hclean 331 (by simp)) (hclean 332 (by simp))
    (hclean 205 (by simp)) (hclean 339 (by simp)) e2.regs
  let p' := Function.update p 205 (Encoding.encodeList id (List.replicate N bits))
  obtain ⟨n4,r4,hn4,he4⟩ := clear_run 304 p' r3
  have h304 : s1 304=[] := hlookup 304 (by simp)
  have hout : Function.update p' 304 []=
      Function.update s1 205 (Encoding.encodeList id (List.replicate N bits)) := by
    funext i
    by_cases h : i=304 <;>
      simp [p',p,preparedSourceStore,s1,Function.update_apply,h,h304]
  rw [hout] at he4
  have hbranch := Eval.ite_false (yes := rowsCommand (sourceRowWith source)) (by simpa [hmem] using hflag) he3
  refine ⟨n1+(n2+((n3+1)+n4)),r4,?_,he1.seq (he2'.seq (hbranch.seq he4))⟩
  have hn4' : n4 ≤ 2*(ps.idxOf (v,N+f))+3 := by
    simpa [p',p,preparedSourceStore,LayoutSourcePlanLookup.unary] using hn4
  simp only [bits,List.length_replicate] at hn3
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_oai
