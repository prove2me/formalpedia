-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:49:07.109418+00:00
-- url     : https://prove2.me/submissions/f5b0f46e-9be6-4d68-88b3-0afdc56b189f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_addEntry_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_query_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

theorem readIndex_eval (base : Data) (regs : Fin 16 → Bool) (i : ℕ)
    (queue : List Bool) (acc : WordPair) :
    Eval readIndex (3*i+3)
      (data base regs (Encoding.encodeNat i++queue) [] acc ([],[]))
      (data base (readRegs regs 0 1 (some false)) queue (unary i) acc ([],[])) := by
  apply Eval.call
  have h := RowSelectionProgramTupleCheck.Read.run (214 : Fin 256) 253
    (0 : Fin 16) 1 (by decide) (by decide) regs
    (bank base (Encoding.encodeNat i++queue) [] acc ([],[])) i queue (by simp [bank])
  convert h using 1
  · simp [RowSelectionProgramTupleCheck.Read.start, data]
  · apply congrArg₂ (Cfg.mk none)
    · rfl
    · funext j
      by_cases hq : j=214
      · subst j; simp [data,bank,unary]
      by_cases hc : j=253
      · subst j; simp [data,bank,unary]
      simp [data,bank,unary,hq,hc]

theorem clearColumn_eval (base : Data) (regs : Fin 16 → Bool)
    (queue column : List Bool) (acc : WordPair) :
    Eval clearColumn (2*column.length+3)
      (data base regs queue column acc ([],[]))
      (data base (readRegs regs 0 1 none) queue [] acc ([],[])) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (253 : Fin 256) (0 : Fin 16) 1
    (data base regs queue column acc ([],[]))
  have he : (⟨readRegs regs 0 1 none,
      StackRoutines.clearStacks 253 (bank base queue column acc ([],[]))⟩ : Data)=
      data base (readRegs regs 0 1 none) queue [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases hc : j=253
      · subst j; simp [bank,StackRoutines.clearStacks]
      simp [bank,StackRoutines.clearStacks,hc]
  change Eval clearColumn (2*column.length+3) _
    (⟨readRegs regs 0 1 none,
      StackRoutines.clearStacks 253 (bank base queue column acc ([],[]))⟩ : Data) at h
  rw [he] at h
  exact h

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem body_eval (entry : Code) (base : Data) (hb : ArithmeticReady base)
    (value : ℕ → ℤ) (T B M i L : ℕ) (hentry : EntryAt entry base value T B M i)
    (regs : Fin 16 → Bool) (queue : List Bool) (acc : WordPair) (hL : pairLength acc ≤ L) :
    ∃ n ≤ bodyBudget T B i L, ∃ rf result,
      Eval (body entry) n (data base regs (Encoding.encodeNat i++queue) [] acc ([],[]))
        (data base rf queue [] result ([],[])) ∧
      pairValue result=pairValue acc+value i ∧
      pairLength result ≤ L+B+2 ∧
      pairTotal result.1 result.2 ≤ pairTotal acc.1 acc.2+M := by
  have hr := readIndex_eval base regs i queue acc
  obtain ⟨ne,hne,re,next,he,hv,hl,hm⟩ :=
    hentry (readRegs regs 0 1 (some false)) queue acc
  obtain ⟨na,hna,ra,result,ha,hav,ham,hal⟩ :=
    addEntry_eval base hb re queue (unary i) acc next
  have hc := clearColumn_eval base ra queue (unary i) result
  have hh := hr.seq (he.seq (ha.seq hc))
  refine ⟨_,?_,readRegs ra 0 1 none,result,hh,?_,?_,?_⟩
  · have hs : (pairLength acc+pairLength next+3)^2 ≤ (L+B+3)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    simp only [unary,List.length_replicate] at hh ⊢
    unfold bodyBudget
    omega
  · simpa only [hv] using hav
  · omega
  · omega

theorem peek_nil (base : Data) (regs : Fin 16 → Bool) (acc : WordPair) :
    Eval peek 2 (data base regs [] [] acc ([],[]))
      (data base (peekRegs regs []) [] [] acc ([],[])) := by
  let a := data base regs [] [] acc ([],[])
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (214 : Fin 256) 14 15) a)
  have he : (StructuredProgram.Atom.pop (214 : Fin 256) (14 : Fin 16) 15).eval a=
      data base (peekRegs regs []) [] [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i=214
      · subst i; simp [a,data,bank,StructuredProgram.Atom.instr,execInstr]
      simp [a,data,bank,StructuredProgram.Atom.instr,execInstr,hi]
  rw [he] at hp
  exact hp.seq (Eval.ite_false rfl (.base (.skip _)))

theorem peek_cons (base : Data) (regs : Fin 16 → Bool) (bit : Bool)
    (queue : List Bool) (acc : WordPair) :
    Eval peek 3 (data base regs (bit::queue) [] acc ([],[]))
      (data base (peekRegs regs (bit::queue)) (bit::queue) [] acc ([],[])) := by
  let a := data base regs (bit::queue) [] acc ([],[])
  let b := (StructuredProgram.Atom.pop (214 : Fin 256) (14 : Fin 16) 15).eval a
  have hp : Eval (.base (.atom (.pop 214 14 15))) 1 a b := .base (.atom _ _)
  have hpush := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (214 : Fin 256) 14) b)
  have he : (StructuredProgram.Atom.push (214 : Fin 256) (14 : Fin 16)).eval b=
      data base (peekRegs regs (bit::queue)) (bit::queue) [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i=214
      · subst i; simp [a,b,data,bank,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,readRegs]
      simp [a,b,data,bank,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,readRegs,hi]
  rw [he] at hpush
  exact hp.seq (Eval.ite_true rfl hpush)

theorem loop_eval (entry : Code) (base : Data) (hb : ArithmeticReady base)
    (value : ℕ → ℤ) (T B M : ℕ) (is : List ℕ)
    (hentry : ∀ i∈is, EntryAt entry base value T B M i)
    (regs : Fin 16 → Bool) (acc : WordPair) (L : ℕ) (hL : pairLength acc ≤ L) :
    ∃ n ≤ cost T B is L, ∃ rf result,
      Eval (loop entry) n (data base regs (encodeIndices is) [] acc ([],[]))
        (data base rf [] [] result ([],[])) ∧
      pairValue result=pairValue acc+(is.map value).sum ∧
      pairLength result ≤ L+is.length*(B+2) ∧
      pairTotal result.1 result.2 ≤ pairTotal acc.1 acc.2+is.length*M := by
  induction is generalizing regs acc L with
  | nil =>
      refine ⟨3,by simp [cost],peekRegs regs [],acc,?_,?_,?_,?_⟩
      · exact (peek_nil base regs acc).seq (Eval.while_false rfl)
      · simp
      · simpa using hL
      · simp
  | cons i is ih =>
      have hnonnil : Encoding.encodeNat i++encodeIndices is ≠ [] := by
        simp [Encoding.encodeNat]
      obtain ⟨bit,tail,htail⟩ := List.exists_cons_of_ne_nil hnonnil
      have hp := peek_cons base regs bit tail acc
      rw [←htail] at hp
      obtain ⟨nt,hnt,rt,next,het,hvt,hlt,hmt⟩ := body_eval entry base hb value T B M i L
        (hentry i (by simp)) (peekRegs regs (Encoding.encodeNat i++encodeIndices is))
        (encodeIndices is) acc hL
      obtain ⟨nr,hnr,rf,result,her,hvr,hlr,hmr⟩ := ih
        (fun j hj => hentry j (by simp [hj])) rt next (L+B+2) hlt
      cases her with
      | @seq first second nx ny aa bb cc hpeek hwhile =>
          have hg : (data base (peekRegs regs (Encoding.encodeNat i++encodeIndices is))
              (Encoding.encodeNat i++encodeIndices is) [] acc ([],[])).regs 15=true := by
            rw [htail]
            rfl
          have hh := hp.seq (Eval.while_true hg (het.seq hpeek) hwhile)
          refine ⟨3+(nt+nx+ny+1),?_,rf,result,?_,?_,?_,?_⟩
          · simp only [cost]
            omega
          · simpa only [loop, encodeIndices, List.flatMap_cons] using hh
          · rw [hvr,hvt]
            simp [add_assoc]
          · simp only [List.length_cons]
            nlinarith
          · simp only [List.length_cons]
            nlinarith

theorem cost_le (T B J L : ℕ) (is : List ℕ) (hJ : ∀ i∈is, i ≤ J) :
    cost T B is L ≤ 3+is.length*(T+5*J+12+
      25000*(L+(is.length+1)*(B+2)+3)^2) := by
  induction is generalizing L with
  | nil => simp [cost]
  | cons i is ih =>
      have hi := hJ i (by simp)
      have ht := ih (L+B+2) (fun j hj => hJ j (by simp [hj]))
      have heq : L+B+2+(is.length+1)*(B+2)+3 =
          L+(is.length+1+1)*(B+2)+3 := by ring
      rw [heq] at ht
      have hs : (L+B+3)^2 ≤ (L+(is.length+1+1)*(B+2)+3)^2 :=
        Nat.pow_le_pow_left (by nlinarith) 2
      simp only [cost,bodyBudget,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem move_eval (src dst tmp : Fin 256) (a : Data)
    (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst)
    (hd : a.stacks dst=[]) (ht : a.stacks tmp=[]) :
    Eval (move src dst tmp) (9*(a.stacks src).length+8) a (moved src dst a) := by
  have h1 := SubexponentialSAT.SubexpScanPrimitives.copy_eval a src dst tmp 0 1
    hsd hst htd (by decide) ht
  let b := SubexponentialSAT.SubexpScanPrimitives.afterCopy a src dst 0 1
  have h2 := SubexponentialSAT.Subexp.TupleProgram.clear_eval src (0 : Fin 16) 1 b
  have hb : b.stacks src=a.stacks src := by
    simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hsd]
  have he : (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks src b.stacks⟩ : Data)=
      moved src dst a := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i=src
      · subst i; simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
          StackRoutines.clearStacks,StackRoutines.copyStacks,hsd]
      by_cases hj : i=dst
      · subst i; simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
          StackRoutines.clearStacks,StackRoutines.copyStacks,Ne.symm hsd,hd]
      simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
        StackRoutines.clearStacks,StackRoutines.copyStacks,hi,hj]
  change Eval _ _ b (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks src b.stacks⟩ : Data) at h2
  rw [he,hb] at h2
  have hcost : 7 * (a.stacks src).length + 5 +
      (2 * (a.stacks src).length + 3) = 9 * (a.stacks src).length + 8 := by omega
  rw [← hcost]
  exact h1.seq h2

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem parked_ready (base : Data) (hb : Ready base) (query : ℕ) :
    ArithmeticReady (parked base query) := by
  intro i hi
  have hn : i≠216 := by
    intro h
    have he : i.val=216 := congrArg Fin.val h
    omega
  simp only [parked,Function.update_of_ne hn]
  exact hb.1 i (by omega)

theorem parkColumn_eval (base : Data) (hb : Ready base) (query : ℕ)
    (regs : Fin 16 → Bool) :
    Eval parkColumn (9*query+8)
      (data base regs [] (unary query) ([],[]) ([],[]))
      (data (parked base query) (readRegs regs 0 1 none) [] [] ([],[]) ([],[])) := by
  have h216 := hb.2 216 (by decide) (by decide)
  have h224 := hb.2 224 (by decide) (by decide)
  have h := move_eval 253 216 224 (data base regs [] (unary query) ([],[]) ([],[]))
    (by decide) (by decide) (by decide) (by simp [data,bank,h216]) (by simp [data,bank,h224])
  have he : moved 253 216 (data base regs [] (unary query) ([],[]) ([],[]))=
      data (parked base query) (readRegs regs 0 1 none) [] [] ([],[]) ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h216' : i=216
      · subst i; simp [data,bank,parked]
      by_cases h253 : i=253
      · subst i; simp [data,bank]
      simp [data,bank,parked,h216',h253]
  rw [he] at h
  simpa [parkColumn,data,bank,unary] using h

theorem finish_eval (base : Data) (hb : Ready base) (query : ℕ)
    (regs : Fin 16 → Bool) (result : WordPair) :
    Eval finish (9*(pairLength result+query)+24)
      (data (parked base query) regs [] [] result ([],[]))
      (data base (readRegs regs 0 1 none) [] (unary query) ([],[]) result) := by
  let a := data (parked base query) regs [] [] result ([],[])
  let b := moved 212 254 a
  let c := moved 213 255 b
  have h224 := hb.2 224 (by decide) (by decide)
  have h1 := move_eval 212 254 224 a (by decide) (by decide) (by decide)
    (by simp [a,data,bank]) (by simp [a,data,bank,parked,h224])
  have h2 := move_eval 213 255 224 b (by decide) (by decide) (by decide)
    (by simp [b,moved,a,data,bank]) (by simp [b,moved,a,data,bank,parked,h224])
  have h3 := move_eval 216 253 224 c (by decide) (by decide) (by decide)
    (by simp [c,b,moved,a,data,bank]) (by simp [c,b,moved,a,data,bank,parked,h224])
  have he : moved 216 253 c=
      data base (readRegs regs 0 1 none) [] (unary query) ([],[]) result := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [c,b,moved,a,data,StackRoutines.readRegs_reset]
    · funext i
      by_cases h212 : i=212
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h213 : i=213
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h216 : i=216
      · subst i; simp [c,b,moved,a,data,bank,parked,hb.2 216 (by decide) (by decide)]
      by_cases h253 : i=253
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h254 : i=254
      · subst i; simp [c,b,moved,a,data,bank,parked]
      by_cases h255 : i=255
      · subst i; simp [c,b,moved,a,data,bank,parked]
      simp [c,b,moved,a,data,bank,parked,h212,h213,h216,h253,h254,h255]
  rw [he] at h3
  convert h1.seq (h2.seq h3) using 1 <;>
    simp_all [a,b,c,moved,data,bank,parked,pairLength,unary] <;>
      first | rfl | omega

/-- The whole original-column wrapper: construct the fiber from original
owner plans, compute its entries one at a time, sum them, and restore column253.
Only the concrete per-incidence command remains a stated dependency. -/
theorem command_eval_oai (entry : Code) (base : Data) (hb : Ready base)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (value : ℕ → ℤ) (T B M J : ℕ)
    (hentry : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps,
      EntryAt entry (parked base query) value T B M i)
    (hJ : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ J)
    (regs : Fin 16 → Bool) :
    ∃ n < budget T B J query ps, ∃ rf result,
      Eval (command entry) n (data base regs [] (unary query) ([],[]) ([],[]))
        (data base rf [] (unary query) ([],[]) result) ∧
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices query 0 ps).map value).sum ∧
      pairLength result ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(B+2) ∧
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*M := by
  let is := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  have hp := parkColumn_eval base hb query regs
  obtain ⟨nq,hnq,rq,hq⟩ := query_eval base hb query ps hs (readRegs regs 0 1 none)
  obtain ⟨nf,hnf,rf,result,hf,hv,hl,hm⟩ :=
    loop_eval entry (parked base query) (parked_ready base hb query) value T B M is
      hentry rq ([],[]) 0 (by simp [pairLength])
  have hh := finish_eval base hb query rf result
  have hc := cost_le T B J 0 is hJ
  simp only [Nat.zero_add] at hc hl
  have hv' : pairValue result=(is.map value).sum := by simpa [pairValue,signedValue] using hv
  have hm' : pairTotal result.1 result.2 ≤ is.length*M := by simpa [pairTotal] using hm
  refine ⟨_,?_,readRegs rf 0 1 none,result,hp.seq (hq.seq (hf.seq hh)),hv',hl,hm'⟩
  unfold budget
  dsimp only [is] at *
  nlinarith

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval_oai
