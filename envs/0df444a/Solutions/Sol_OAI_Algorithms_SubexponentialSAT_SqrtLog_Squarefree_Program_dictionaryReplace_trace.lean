-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:14:46.70753+00:00
-- url     : https://prove2.me/submissions/bfe27666-8201-4d33-a0e2-95f2ab72c827

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_Program_eraseOne_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem payloadPorts_injective : Function.Injective payloadPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [payloadPorts]
theorem keyPorts_injective : Function.Injective keyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [keyPorts]

theorem embedPayload (regs rr : Fin 3 → Bool) (key coeff output coeff' output' : List Bool) :
    embedState id payloadPorts (prependData regs key coeff output) (frameData rr coeff' output') =
      prependData rr key coeff' output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id payloadPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [payloadPorts,prependData,Fin.exists_fin_succ]

theorem embedKey (regs rr : Fin 3 → Bool) (key coeff output key' output' : List Bool) :
    embedState id keyPorts (prependData regs key coeff output) (frameData rr key' output') =
      prependData rr key' coeff output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [keyPorts,prependData,Fin.exists_fin_succ]

theorem prependRecord_eval (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Eval prependRecord (4 * key.length + 4 * coeff.length + 12)
      (prependData regs key.reverse coeff.reverse output)
      (prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)) := by
  obtain ⟨r1,hp⟩ := frameEmit_trace coeff output regs
  have hp' := eval_call_lifted frameEmitProgram id payloadPorts
    (prependData regs key.reverse coeff.reverse output)
    Function.injective_id payloadPorts_injective hp
  simp only [embedPayload] at hp'
  obtain ⟨r2,hk⟩ := frameEmit_trace key (Encoding.frame coeff ++ output) r1
  have hk' := eval_call_lifted frameEmitProgram id keyPorts
    (prependData r1 key.reverse [] (Encoding.frame coeff ++ output))
    Function.injective_id keyPorts_injective hk
  simp only [embedKey] at hk'
  refine ⟨r2,?_⟩
  convert hp'.seq hk' using 1 <;> try omega
  simp [List.append_assoc]

theorem prependRecord_trace (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Trace prependRecordProgram (4 * key.length + 4 * coeff.length + 13)
      ((prependData regs key.reverse coeff.reverse output).withPC (some prependRecordProgram.entry))
      ((prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)).withPC none) := by
  obtain ⟨final,he⟩ := prependRecord_eval regs key coeff output
  exact ⟨final,by simpa [prependRecordProgram,Nat.add_assoc] using compiled_halt_trace he 0 2⟩
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

theorem embedStorage (a b : State 5 6) (saved : List Bool) :
    embedState id Fin.castSucc (extendStorage a saved) b = extendStorage b saved := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castSucc_injective 6)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hi' : ¬ i.val < 6 := by
      intro hil
      apply hi
      exact ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    have hv : i.val = 6 := by have := i.isLt; omega
    have he : i = (6 : Fin 7) := Fin.ext hv
    subst i
    rfl

theorem storageCall_eval {c : Cmd 5 6} {n : ℕ} {a b : State 5 6}
    (h : Eval c n a b) (saved : List Bool) :
    Eval (storageCall c) (n + 1) (extendStorage a saved) (extendStorage b saved) := by
  have hh := eval_liftCommand h 0 5 id Fin.castSucc (extendStorage a saved)
    Function.injective_id (Fin.castSucc_injective 6)
  simpa only [storageCall, embedStorage] using hh

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem erasePeek_eval (regs : Fin 5 → Bool) (entries : List ByteRecord) (query output : List Bool) :
    Eval erasePeek 2 (eraseData regs (rawEntries entries) query output [])
      (eraseReady regs entries query output) :=
  storageCall_eval (SubexponentialSAT.Subexp.SelectorProgram.peek_eval regs (rawEntries entries) query.reverse output) []

theorem eraseReady_nil_guard (regs : Fin 5 → Bool) (query output : List Bool) :
    (eraseReady regs [] query output).regs 1 = false := by
  simp [eraseReady,eraseData,extendStorage,readRegs,rawEntries]

theorem eraseReady_cons_guard (regs : Fin 5 → Bool) (key payload query output : List Bool)
    (entries : List ByteRecord) :
    (eraseReady regs ((key,payload)::entries) query output).regs 1 = true := by
  cases key <;> simp [eraseReady,eraseData,extendStorage,readRegs,rawEntries,Encoding.frame]

theorem eraseLoop_eval (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries, ∃ final,
      Eval eraseLoop n (eraseReady regs entries query output)
        (eraseData final [] query (erasedOutput query entries output) []) := by
  induction entries generalizing output regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 1 none,?_⟩
    exact Eval.while_false (eraseReady_nil_guard regs query output)
  | cons a entries ih =>
    rcases a with ⟨key,payload⟩
    let rr := readRegs regs 0 1 (rawEntries ((key,payload)::entries)).head?
    let out := if key=query then output else Encoding.frame key ++ Encoding.frame payload ++ output
    obtain ⟨n,hn,middle,he⟩ := eraseOne_eval rr key query payload (rawEntries entries) output
    obtain ⟨m,hm,final,ht⟩ := ih out middle
    have hp := erasePeek_eval middle entries query out
    refine ⟨(n+2)+m+1,by simp only [eraseBudget]; omega,final,?_⟩
    have hh := Eval.while_true (eraseReady_cons_guard regs key payload query output entries) (he.seq hp) ht
    exact hh

theorem eraseScan_eval (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 2, ∃ final,
      Eval eraseScan n (eraseData regs (rawEntries entries) query output [])
        (eraseData final [] query (erasedOutput query entries output) []) := by
  obtain ⟨n,hn,final,he⟩ := eraseLoop_eval entries query output regs
  exact ⟨2+n,by omega,final,(erasePeek_eval regs entries query output).seq he⟩

theorem rawEntries_append (a b : List ByteRecord) :
    rawEntries (a++b) = rawEntries a ++ rawEntries b := by
  induction a with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨k,c⟩; simp [rawEntries,ih,List.append_assoc]

theorem erasedOutput_eq (query output : List Bool) (entries : List ByteRecord) :
    erasedOutput query entries output = rawEntries (erasedEntries query entries).reverse ++ output := by
  induction entries generalizing output with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨key,payload⟩
    by_cases he : key=query <;>
      simp [erasedOutput,erasedEntries,he,ih,List.reverse_cons,rawEntries_append,rawEntries,List.append_assoc]

theorem eraseScan_trace (entries : List ByteRecord) (query output : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 3, ∃ final,
      Trace eraseScanProgram n
        ((eraseData regs (rawEntries entries) query output []).withPC (some eraseScanProgram.entry))
        ((eraseData final [] query (rawEntries (erasedEntries query entries).reverse ++ output) []).withPC none) := by
  obtain ⟨n,hn,final,he⟩ := eraseScan_eval entries query output regs
  rw [erasedOutput_eq] at he
  exact ⟨n+1,by omega,final,compiled_halt_trace he 0 5⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramReplace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem embedSeven (a b : StorageData) (coeff : List Bool) :
    embedState id Fin.castSucc (keepCoefficient a coeff) b = keepCoefficient b coeff := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castSucc_injective 7)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hnot : ¬ i.val < 7 := by
      intro hil
      exact hi ⟨⟨i.val,hil⟩,Fin.ext rfl⟩
    have hv : i.val = 7 := by have := i.isLt; omega
    have he : i = (7 : Fin 8) := Fin.ext hv
    subst i; rfl

theorem replaceRegPorts_injective : Function.Injective replaceRegPorts := Fin.castAdd_injective _ _
theorem replaceStackPorts_injective : Function.Injective replaceStackPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [replaceStackPorts]

theorem replaceTail_eval (regs : Fin 5 → Bool) (query coeff output : List Bool) :
    ∃ final, Eval replaceTail (4 * query.length + 4 * coeff.length + 13)
      (keepCoefficient (eraseData regs [] query output []) coeff.reverse)
      (replaceDone final (Encoding.frame query ++ Encoding.frame coeff ++ output)) := by
  let d := keepCoefficient (eraseData regs [] query output []) coeff.reverse
  obtain ⟨rr,ht⟩ := prependRecord_trace (regs ∘ replaceRegPorts) query coeff output
  let b := prependData rr [] [] (Encoding.frame query ++ Encoding.frame coeff ++ output)
  let final := (embedState replaceRegPorts replaceStackPorts d b).regs
  have ha : embedState replaceRegPorts replaceStackPorts d
      (prependData (regs ∘ replaceRegPorts) query.reverse coeff.reverse output) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ replaceRegPorts_injective replaceStackPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [d,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,prependData]
    · intros; rfl
  have hb : embedState replaceRegPorts replaceStackPorts d b =
      replaceDone final (Encoding.frame query ++ Encoding.frame coeff ++ output) := by
    apply embedState_eq_of_ports _ _ _ _ _ replaceRegPorts_injective replaceStackPorts_injective
    · intro i
      exact embedState_register replaceRegPorts replaceStackPorts d b replaceRegPorts_injective i
    · intro i hi
      exact embedState_register_frame replaceRegPorts replaceStackPorts d b i hi
    · intro i; fin_cases i <;> simp [b,replaceDone,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,prependData]
    · intro i hi
      fin_cases i <;> simp_all [d,replaceDone,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,Fin.exists_fin_succ]
  have he := eval_call_lifted prependRecordProgram replaceRegPorts replaceStackPorts d
    replaceRegPorts_injective replaceStackPorts_injective ht
  change Eval replaceTail _
    (embedState replaceRegPorts replaceStackPorts d (prependData (regs ∘ replaceRegPorts) query.reverse coeff.reverse output))
    (embedState replaceRegPorts replaceStackPorts d b) at he
  rw [ha,hb] at he
  exact ⟨final,he⟩

theorem dictionaryReplace_eval (entries : List ByteRecord) (query coeff : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 4 * query.length + 4 * coeff.length + 16, ∃ final,
      Eval dictionaryReplace n (replaceData regs entries query coeff)
        (replaceDone final (rawEntries ((query,coeff)::(erasedEntries query entries).reverse))) := by
  obtain ⟨n,hn,middle,he⟩ := eraseScan_trace entries query [] regs
  have hcall := eval_call_lifted eraseScanProgram id Fin.castSucc
    (replaceData regs entries query coeff) Function.injective_id (Fin.castSucc_injective 7) he
  change Eval _ n
    (embedState id Fin.castSucc (keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse)
      (eraseData regs (rawEntries entries) query [] []))
    (embedState id Fin.castSucc (keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse)
      (eraseData middle [] query (rawEntries (erasedEntries query entries).reverse ++ []) [])) at hcall
  simp only [embedSeven,List.append_nil] at hcall
  obtain ⟨final,ht⟩ := replaceTail_eval middle query coeff (rawEntries (erasedEntries query entries).reverse)
  refine ⟨n+(4*query.length+4*coeff.length+13),by omega,final,?_⟩
  exact hcall.seq ht

theorem dictionaryReplace_trace_oai (entries : List ByteRecord) (query coeff : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 4 * query.length + 4 * coeff.length + 17, ∃ final,
      Trace dictionaryReplaceProgram n
        ((replaceData regs entries query coeff).withPC (some dictionaryReplaceProgram.entry))
        ((replaceDone final (rawEntries ((query,coeff)::(erasedEntries query entries).reverse))).withPC none) := by
  obtain ⟨n,hn,final,he⟩ := dictionaryReplace_eval entries query coeff regs
  exact ⟨n+1,by omega,final,compiled_halt_trace he 0 5⟩
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace_oai
