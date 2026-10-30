-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:36:57.845325+00:00
-- url     : https://prove2.me/submissions/aa123c40-af6e-4afc-8ecf-02da6505b3d6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_initialize_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_vertexIteration_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared src d) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramFor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A bounded variant of the existing unary controller rule. Its invariant
may retain registers that the actual pop instruction does not touch. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.UnaryForPrograms

variable {R S : ℕ}

theorem bounded_visits (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (word : List Bool) :
    ∀ i d, d.stacks p.counter=word → I i d → i+word.length ≤ N →
      ∃ costs n e, Visits p body costs n d e ∧ I (i+word.length) e ∧
        n ≤ word.length*(C+2)+2 := by
  induction word with
  | nil =>
    intro i d hd hi hN
    exact ⟨[],2,popped p d,Visits.done d hd,by simpa using stable i d hi,by simp⟩
  | cons bit word ih =>
    intro i d hd hi hN
    have hiN : i < N := by simp only [List.length_cons] at hN; omega
    obtain ⟨nb,e,hnb,hbody,hcounter,hie⟩ := step i hiN (popped p d) (stable i d hi)
    have he : e.stacks p.counter=word := by rw [hcounter,popped_counter,hd]; rfl
    have htail : i+1+word.length ≤ N := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hN
    obtain ⟨costs,nt,f,ht,hif,hnt⟩ := ih (i+1) e he hie htail
    refine ⟨nb::costs,nb+nt+2,f,Visits.step (by simp [hd]) hbody hcounter ht,?_,?_⟩
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hif
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem bounded_for_eval (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (d : State R S) (hd : (d.stacks p.counter).length=N) (hi : I 0 d) :
    ∃ n e, Eval (forCmd p body) n d e ∧ I N e ∧ e.stacks p.counter=[] ∧ n ≤ N*(C+2)+2 := by
  obtain ⟨costs,n,e,hvis,hei,hn⟩ := bounded_visits p body I N C stable step
    (d.stacks p.counter) 0 d rfl hi (by omega)
  refine ⟨n,e,hvis.eval,?_,hvis.bounds.2.1,?_⟩
  · simpa [hd] using hei
  · simpa [hd] using hn

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramRepresentation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-for-byte agreement between generated candidates and arithmetic inputs.
These identities remove recoding from the search interface; they are not
assumptions that a rearrangement of an existing tape is cost-free. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem words_eq_flatMap (xs : List (List Bool)) :
    Subexp.MatrixProgramSupport.words xs = xs.flatMap Encoding.frame := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Subexp.MatrixProgramSupport.words, ih]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.Subexp

theorem matrixWords_flatMap (rows : List (List (List Bool))) :
    MatrixVectorProgram.matrixWords rows=rows.flatMap MatrixProgramSupport.words := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simpa [MatrixVectorProgram.matrixWords] using congrArg (MatrixProgramSupport.words x++·) ih

theorem matrixFrames_rows {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) :
    CodeSearchProgram.matrixFrames Q=
      (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).flatten := by
  rw [CodeSearchProgram.matrixFrames,matrixWords_flatMap]
  simp only [List.flatMap,CodeSearchProgram.scalarFrames,List.map_ofFn,Function.comp_def]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

theorem binary_scalarWord (x : ZMod 2) :
    SubexponentialSAT.Subexp.MatrixWordEncoding.word 2 x=[decide (x=1),false] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 2=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem vertexFrames {r : ℕ} (v : Cayley.Cube r) :
    CodeSearchProgram.scalarFrames (List.ofFn v)=Shift.frames (vertexBits v) := by
  simp only [CodeSearchProgram.scalarFrames,CodeSearchProgram.words_eq_flatMap,vertexBits,Shift.frames,List.flatMap,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [binary_scalarWord]
  rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem matrixFrames_shifts {r D : ℕ} (shifts : Fin D → Cayley.Cube r) :
    CodeSearchProgram.matrixFrames shifts=shiftRows (List.ofFn shifts) := by
  rw [matrixFrames_rows]
  simp only [shiftRows,List.flatMap,List.map_ofFn,Function.comp_def,vertexFrames]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem rowRecords_encodeList {m : ℕ} (b : ℕ)
    (rs : List (List (Fin m × SparseCode.F3))) :
    rowRecords b rs++[false]=Encoding.encodeList (rowPayload b m) rs := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    simpa [rowRecords,Encoding.encodeList,List.append_assoc] using
      (congrArg (fun tail => true::(Encoding.frame (rowPayload b m row)++tail)) ih)

theorem collectedRows_encodeList {m : ℕ} (b : ℕ)
    (rs : List (List (Fin m × SparseCode.F3))) :
    collectedRows b rs [false]=Encoding.encodeList (rowPayload b m) rs.reverse :=
  rowRecords_encodeList b rs.reverse

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

private theorem zeroWord_value (r : ℕ) : BinaryArithmetic.toNat (List.replicate r false)=0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ,toNat_cons,bitVal,ih]

theorem vertexPrefix_full {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    vertexPrefix m shifts Q (2^r)=chronologicalRows m shifts Q := by
  unfold vertexPrefix
  rw [List.take_of_length_le (by simp)]
  rfl

theorem VertexInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {b i : ℕ} {d : Data}
    (h : VertexInvariant (m:=m) base shifts Q b i d) :
    VertexInvariant (m:=m) base shifts Q b i (UnaryForPrograms.popped vertexLoop d) := by
  constructor
  · exact h.position
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.value
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.width
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.length
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.output
  · intro j h2 h8 h12
    simpa [UnaryForPrograms.popped,vertexLoop,h8] using h.other j h2 h8 h12

theorem vertexLoop_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b : ℕ)
    (ready : LocalReady base D m b (base.regs 12) (0 : Cayley.Cube r))
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (hN : (base.stacks 8).length=2^r)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n e, Eval (UnaryForPrograms.forCmd vertexLoop vertexStep) n base e ∧
      VertexInvariant (m:=m) base shifts Q b (2^r) e ∧ e.stacks 8=[] ∧
      n ≤ 2^r*(vertexCost base D t b+2)+2 := by
  apply bounded_for_eval vertexLoop vertexStep (VertexInvariant (m:=m) base shifts Q b)
    (2^r) (vertexCost base D t b)
  · intro i d inv; exact inv.popped
  · exact vertexIteration_eval base shifts Q b ready hq hs hD ht h0 h1 h13 h14 h15 h16
  · exact hN
  · constructor
    · omega
    · rw [ready.vertex]
      simp [vertexBits,zeroWord_value]
    · intro hi; rw [ready.vertex]; simp
    · rw [ready.vertex]; simp
    · simp [vertexPrefix]
    · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native serializer endpoint. Runtime bounds are carried in unary tapes;
source arrays and arithmetic operands are copied by the actual table. -/

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem command_eval {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
    ∃ n rf, Eval command n (inputState regs dword mword width shifts Q)
      (outputState (m:=m) rf dword mword width shifts Q) ∧
      n+1 ≤ cost dword mword width shifts Q := by
  let d := inputState regs dword mword width shifts Q
  obtain ⟨ri,hi⟩ := initialize_eval d (by simp [d,inputState]) (by simp [d,inputState])
    (by simp [d,inputState]) (by simp [d,inputState]) (by simp [d,inputState])
  let start : Data := ⟨ri,initialStacks d⟩
  have ready : LocalReady start D m width.length (start.regs 12) (0 : Cayley.Cube r) := by
    constructor
    · rfl
    · simp [start,initialStacks,d,inputState,vertexBits]
    · simpa [start,initialStacks,d,inputState] using hd
    · simpa [start,initialStacks,d,inputState] using hm
    · simp [start,initialStacks,d,inputState]
    · exact hcap
    · intro j hj hk
      have hne (k : Fin 64) (hlt : k.val < 17) : j ≠ k := by
        intro h
        have hv := congrArg Fin.val h
        omega
      simp only [start,initialStacks,d,inputState,
        Function.update_of_ne (hne 2 (by decide)),
        Function.update_of_ne (hne 12 (by decide)),
        ite_eq_right (hne 3 (by decide)),ite_eq_right (hne 4 (by decide)),
        ite_eq_right (hne 5 (by decide)),ite_eq_right (hne 6 (by decide)),
        ite_eq_right (hne 7 (by decide)),ite_eq_right (hne 8 (by decide)),
        ite_eq_right (hne 9 (by decide)),ite_eq_right (hne 10 (by decide)),
        ite_eq_right (hne 11 (by decide))]
  obtain ⟨nl,e,hl,inv,he8,hnl⟩ := vertexLoop_eval start shifts Q width.length ready
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState,matrixFrames_shifts])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
  have clear := clear_eval 2 e
  have e12 : e.stacks 12=rowStream width.length m shifts Q := by
    simpa [vertexPrefix_full,start,initialStacks,d,inputState,collectedRows_encodeList,
      rowStream,serializedRows] using inv.output
  have out : cleared 2 e=outputState (m:=m) (cleared 2 e).regs dword mword width shifts Q := by
    apply CounterForPrograms.data_ext (a := cleared 2 e)
      (b := outputState (m:=m) (cleared 2 e).regs dword mword width shifts Q)
    · rfl
    · funext j
      by_cases h2 : j=2
      · subst j; simp [cleared,outputState,inputState]
      by_cases h8 : j=8
      · subst j; simp [cleared,outputState,he8]
      by_cases h12 : j=12
      · subst j; simp [cleared,outputState,e12]
      have hj := inv.other j h2 h8 h12
      simpa [cleared,outputState,start,initialStacks,d,inputState,h2,h8,h12] using hj
  refine ⟨(11*(d.stacks 11).length+10)+(nl+(2*(e.stacks 2).length+3)),
    (cleared 2 e).regs,?_,?_⟩
  · rw [←out]
    exact hi.seq (hl.seq clear)
  · have hlen := inv.length
    have costeq : vertexCost start D t width.length=
        vertexCost ⟨(inputState (fun _ => false) dword mword width shifts Q).regs,
          initialStacks (inputState (fun _ => false) dword mword width shifts Q)⟩ D t width.length := rfl
    rw [costeq] at hnl
    have hdlen : (d.stacks 11).length=r := by simp [d,inputState]
    simp only [hdlen]
    dsimp only [cost]
    omega

theorem program_runsIn_oai {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
    ∃ rf, RunsIn program (cost dword mword width shifts Q)
      ((inputState regs dword mword width shifts Q).withPC (some program.entry))
      ((outputState (m:=m) rf dword mword width shifts Q).withPC none) := by
  obtain ⟨n,rf,he,hn⟩ := command_eval regs dword mword width shifts Q hd hm hcap
  exact ⟨rf,n+1,hn,compiled_halt_trace he 10 12⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn_oai
