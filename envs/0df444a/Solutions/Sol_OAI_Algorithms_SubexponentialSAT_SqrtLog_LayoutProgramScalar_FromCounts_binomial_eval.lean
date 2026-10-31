-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:28:11.473513+00:00
-- url     : https://prove2.me/submissions/d6ac47c4-cf99-471b-8c57-67fba0aba230

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutBinomialProgram_cacheBuildLoop_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutBinomialProgram_finalFlatten_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramMath
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pascal's recurrence on actual little-endian words. The old row, rather
than the growing new row, supplies the carry at each position. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

open SubexponentialSAT.BinaryArithmetic

theorem scan_word_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ scan prior xs, x.length ≤ B + 1 := by
  induction xs generalizing prior with
  | nil => simp [scan]
  | cons old rest ih =>
    have ho := hx old (by simp)
    intro x h
    simp only [scan, List.mem_cons] at h
    rcases h with rfl | h
    · exact (length_add prior old).trans (by omega)
    · exact ih old ho (fun y hy => hx y (by simp [hy])) x h

theorem iterate_word_length (h : ℕ) (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ iterate h xs, x.length ≤ B + h := by
  induction h generalizing xs B with
  | zero => simpa [iterate] using hx
  | succ h ih =>
    have ht := ih (scan [] xs) (B+1) (scan_word_length [] xs B (by simp) hx)
    simpa [iterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem initial_word_length (R : ℕ) : ∀ x ∈ initial R, x.length ≤ 1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split <;> simp

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical Pascal scan computes the exact binomial row, in increasing
column order, including columns above the row index. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

open SubexponentialSAT.BinaryArithmetic

theorem scan_cell (h k : ℕ) :
    scanPrior h k + h.choose k = (h+1).choose k := by
  cases k with
  | zero => simp [scanPrior]
  | succ k => simp [scanPrior, Nat.choose_succ_succ]

theorem natScan_choose_offset (h R k : ℕ) :
    natScan (scanPrior h k) ((List.range R).map (fun j => h.choose (k+j))) =
      (List.range R).map (fun j => (h+1).choose (k+j)) := by
  induction R generalizing k with
  | zero => rfl
  | succ R ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero,
      natScan,scan_cell]
    congr 1
    simpa [scanPrior, Function.comp_def, Nat.succ_eq_add_one, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (k+1)

theorem natScan_choose (h R : ℕ) :
    natScan 0 ((List.range R).map (h.choose)) =
      (List.range R).map ((h+1).choose) := by
  simpa only [scanPrior,Nat.zero_add] using natScan_choose_offset h R 0

theorem scan_values (prior : List Bool) (xs : List (List Bool)) :
    (scan prior xs).map BinaryArithmetic.toNat = natScan (BinaryArithmetic.toNat prior) (xs.map BinaryArithmetic.toNat) := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [scan,List.map_cons,natScan,ih,toNat_add]

theorem iterate_values (n h R : ℕ) (xs : List (List Bool))
    (hx : xs.map BinaryArithmetic.toNat = (List.range R).map h.choose) :
    (iterate n xs).map BinaryArithmetic.toNat = (List.range R).map (h+n).choose := by
  induction n generalizing h xs with
  | zero => simpa [iterate] using hx
  | succ n ih =>
    have hs : (scan [] xs).map BinaryArithmetic.toNat = (List.range R).map (h+1).choose := by
      rw [scan_values,hx]
      exact natScan_choose h R
    simpa [iterate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1) _ hs

theorem initial_values (R : ℕ) :
    (initial R).map BinaryArithmetic.toNat = (List.range R).map (Nat.choose 0) := by
  cases R with
  | zero => simp
  | succ R =>
    simp [initial_succ,List.range_succ_eq_map,List.map_map,Function.comp_def,bitVal]

theorem iterate_initial_values (h R : ℕ) :
    (iterate h (initial R)).map BinaryArithmetic.toNat = (List.range R).map h.choose := by
  simpa using iterate_values h 0 R (initial R) (initial_values R)

theorem iterate_initial_word_length (h R : ℕ) :
    ∀ x ∈ iterate h (initial R), x.length ≤ h+1 := by
  simpa [Nat.add_comm] using iterate_word_length h (initial R) 1 (initial_word_length R)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

theorem zeroRecord_encoding (xs : List WordPair) :
    zeroRecord ++ pairEncoding xs = pairEncoding (([],[])::xs) := rfl

private theorem zero_stable (base : State 8 18) :
    UnaryForPrograms.FrameStable zeroPorts (ZeroInvariant base) := by
  intro i a b hab hi
  refine ⟨?_,fun j hj hk => (hab j hk).symm.trans (hi.2 j hj hk)⟩
  exact (hab 15 (by decide)).symm.trans hi.1

private theorem zero_body (base : State 8 18) :
    UnaryForPrograms.BodySpec zeroPorts zeroBody (ZeroInvariant base) (fun _ => 6) := by
  intro i d hi
  obtain ⟨r,he⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) zeroRecord d
  refine ⟨6,⟨r,Function.update d.stacks 15 (zeroRecord++d.stacks 15)⟩,le_rfl,he,by simp [zeroPorts],?_,?_⟩
  · simp only [Function.update_same,hi.1,zeroRecord_encoding,List.replicate_succ]
  · intro j hj hk
    simpa [hj] using hi.2 j hj hk

theorem zeroCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 8*counter.length+4, ∃ r,
      Eval zeroCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding (List.replicate counter.length ([],[])))) := by
  let d := state regs ([],counter) ([],[]) ([],[]) []
  obtain ⟨r₀,h₀⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false] d
  let a : State 8 18 := ⟨r₀,Function.update d.stacks 15 [false]⟩
  have hi : ZeroInvariant d 0 a := by
    constructor
    · rfl
    · intro j hj _; simp [a,hj]
  obtain ⟨t,e,he,hi',hc,ht⟩ := UnaryForPrograms.for_correct zeroPorts zeroBody
    (ZeroInvariant d) (fun _ => 6) (zero_stable d) (zero_body d) a hi
  have hc' : e.stacks 17 = [] := hc
  have hi'₁ : e.stacks 15 = pairEncoding (List.replicate counter.length ([],[])) := by
    simpa [a,d,state,zeroPorts] using hi'.1
  have heq : e = state e.regs ([],[]) ([],[]) ([],[])
      (pairEncoding (List.replicate counter.length ([],[]))) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext j
    by_cases hj : j = 15
    · subst j; exact hi'₁
    by_cases hk : j = 17
    · subst j; exact hc'
    rw [hi'.2 j hj hk]
    simp [d,state,hj,hk]
  refine ⟨2+t,?_,e.regs,?_⟩
  · have ht' : t ≤ counter.length*6+2*counter.length+2 := by
      simpa [a,d,state,zeroPorts,CounterForPrograms.budgetSum_const] using ht
    omega
  · have hh : Eval zeroCommand (2+t) d e := h₀.seq he
    rw [heq] at hh
    simpa only [d] using hh



theorem initialPop_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    Eval initialPop 1 (state regs ([],counter) ([],[]) ([],[]) [])
      (state (readRegs regs 7 6 counter.head?) ([],counter.tail) ([],[]) ([],[]) []) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (17 : Fin 18) (7 : Fin 8) 6)
    (state regs ([],counter) ([],[]) ([],[]) []))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> simp [state,StructuredProgram.Atom.instr,
execInstr]

theorem initialCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 12*counter.length+20, ∃ r,
      Eval initialCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding ((initial counter.length).map fun x => (x,[])))) := by
  have hp := initialPop_eval regs counter
  cases counter with
  | nil =>
    obtain ⟨r,hr⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false]
      (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) [])
    have hout : (⟨r,Function.update
        (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) []).stacks
        15 ([false]++[])⟩ : State 8 18) =
        state r ([],[]) ([],[]) ([],[]) (pairEncoding []) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j; fin_cases j <;> simp [state,pairEncoding]
    change Eval _ _ _ ⟨r,Function.update
      (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) []).stacks
      15 ([false]++[])⟩ at hr
    rw [hout] at hr
    refine ⟨4,by simp,r,?_⟩
    simpa [initialCommand] using hp.seq (Eval.ite_false
      (test := (6 : Fin 8)) (by simp [state,readRegs_present]) hr)
  | cons b bs =>
    obtain ⟨t,ht,r,he⟩ := zeroCommand_eval (readRegs regs 7 6 (some b)) bs
    obtain ⟨r',hr⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18)
      [true,true,true,false,false]
      (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[]))))
    have hout : (⟨r',Function.update
        (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[])))).stacks
        15 ([true,true,true,false,false]++pairEncoding (List.replicate bs.length ([],[])))⟩ :
        State 8 18) = state r' ([],[]) ([],[]) ([],[])
        (pairEncoding ((initial (bs.length+1)).map fun x => (x,[]))) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j; fin_cases j <;> simp [state,initial_succ,pairEncoding,Encoding.frame]
    change Eval _ _ _ ⟨r',Function.update
      (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[])))).stacks
      15 ([true,true,true,false,false]++pairEncoding (List.replicate bs.length ([],[])))⟩ at hr
    rw [hout] at hr
    refine ⟨1+((t+10)+1),by simp only [List.length_cons]; omega,r',?_⟩
    simpa [initialCommand] using hp.seq (Eval.ite_true
      (test := (6 : Fin 8)) (by simp [state,readRegs_present]) (he.seq hr))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

theorem initialBuildPorts_injective : Function.Injective initialBuildPorts := by decide

theorem initialBuild_eval (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ t ≤ 12*r.length+21, ∃ regs',
      Eval initialBuild t (buildState regs a r [])
        (buildState regs' a [] (pairEncoding (((initial r.length).map fun x => (x,[]))))) := by
  obtain ⟨t,ht,regs',he⟩ := initialCommand_eval regs r
  have hs : embedState id initialBuildPorts (buildState regs a r [])
      (state regs ([],r) ([],[]) ([],[]) []) = buildState regs a r [] := by
    apply embedState_eq_of_ports id initialBuildPorts _ _ _
      Function.injective_id initialBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,initialBuildPorts]
    · intro i hi; rfl
  have hf : embedState id initialBuildPorts (buildState regs a r [])
      (state regs' ([],[]) ([],[]) ([],[])
        (pairEncoding (((initial r.length).map fun x => (x,[]))))) =
      buildState regs' a [] (pairEncoding (((initial r.length).map fun x => (x,[])))) := by
    apply embedState_eq_of_ports id initialBuildPorts _ _ _
      Function.injective_id initialBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,initialBuildPorts]
    · intro i hi
      have hrange : ∀ j : Fin 19, j ≠ 17 → j ∈ Set.range initialBuildPorts := by decide
      have hj : i = 17 := by by_contra h; exact hi (hrange i h)
      subst i
      simp [buildState]
  have h := eval_call_lifted (compiled initialCommand 17 15) id initialBuildPorts
    (buildState regs a r []) Function.injective_id initialBuildPorts_injective
    (compiled_halt_trace he 17 15)
  rw [hs,hf] at h
  exact ⟨t+1,by omega,regs',h⟩

theorem buildProgram_runsIn (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)),
      RunsIn buildProgram
        (12*r.length+400*(a.length+1)*(r.length+1)*(a.length+5)+24)
        ((buildState regs a r []).withPC (some buildProgram.entry))
        ((buildState regs' [] [] (pairEncoding (xs.map fun x => (x,[])))).withPC none) ∧
      xs.length = r.length ∧
      xs.map BinaryArithmetic.toNat = (List.range r.length).map (Nat.choose a.length) ∧
      (∀ x ∈ xs, x.length ≤ a.length+1) := by
  obtain ⟨ti,hti,ri,hi⟩ := initialBuild_eval regs a r
  have hw : ∀ x ∈ initial r.length, x.length ≤ 1 := initial_word_length r.length
  obtain ⟨tc,htc,rc,hc⟩ := cacheBuildLoop_eval ri a (initial r.length) 1 hw
  refine ⟨rc,iterate a.length (initial r.length),
    ⟨ti+tc+1,?_,compiled_halt_trace (hi.seq hc) 17 15⟩,?_,?_,?_⟩
  · simp only [initial_length] at htc
    have he : 1+a.length+4 = a.length+5 := by omega
    rw [he] at htc
    omega
  · simp
  · exact iterate_initial_values a.length r.length
  · exact iterate_initial_word_length a.length r.length

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BinaryArithmetic

theorem normalizedWords_word_length (width : List Bool) (xs : List (List Bool)) :
    ∀ x ∈ normalizedWords width xs, x.length = width.length := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  exact ModularArithmetic.padTo_length width y

theorem normalizedWords_values (width : List Bool) (xs : List (List Bool))
    (hx : ∀ x ∈ xs, x.length ≤ width.length) :
    (normalizedWords width xs).map BinaryArithmetic.toNat = xs.map BinaryArithmetic.toNat := by
  rw [normalizedWords,List.map_map]
  apply List.map_congr_left
  intro x hx'
  exact ModularArithmetic.padTo_correct width x (hx x hx')

theorem flatWords_eq_flatten (width : List Bool) (xs : List (List Bool)) :
    flatWords width xs = (normalizedWords width xs).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ModularArithmetic.padTo width x ++ flatWords width xs =
      ModularArithmetic.padTo width x ++ (normalizedWords width xs).flatten
    rw [ih]

theorem padTo_nil (width : List Bool) :
    ModularArithmetic.padTo width [] = List.replicate width.length false := by
  induction width with
  | nil => rfl
  | cons b width ih => simp [ModularArithmetic.padTo,ih,List.replicate_succ]

theorem flatZeros_eq (width : List Bool) (xs : List (List Bool)) :
    flatZeros width xs = List.replicate (xs.length*width.length) false := by
  induction xs with
  | nil => simp [flatZeros]
  | cons x xs ih =>
    change ModularArithmetic.padTo width [] ++ flatZeros width xs = _
    rw [padTo_nil,ih]
    rw [List.length_cons]
    have hn : (xs.length+1)*width.length = width.length+xs.length*width.length := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [hn,List.replicate_add]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem buildFinalPorts_injective : Function.Injective buildFinalPorts := Fin.castAdd_injective _ _

theorem finalBuild_eval (regs : Fin 8 → Bool) (h r width : List Bool) :
    ∃ t ≤ 12*r.length+400*(h.length+1)*(r.length+1)*(h.length+5)+24,
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)), Eval finalBuild t (finalState regs h r width [] [] [])
      (finalState regs' [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] []) ∧
      xs.length=r.length ∧ xs.map BinaryArithmetic.toNat=(List.range r.length).map h.length.choose ∧
      (∀ x ∈ xs, x.length ≤ h.length+1) := by
  obtain ⟨rf,xs,⟨t,ht,he⟩,hlen,hval,hw⟩ := buildProgram_runsIn regs h r
  have hs : embedState id buildFinalPorts (finalState regs h r width [] [] [])
      (buildState regs h r []) = finalState regs h r width [] [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi; rfl
  have hf : embedState id buildFinalPorts (finalState regs h r width [] [] [])
      (buildState rf [] [] (pairEncoding (xs.map fun x => (x,[])))) =
      finalState rf [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi
      have hrange : ∀ j : Fin 20, j≠19 → j∈Set.range buildFinalPorts := by decide
      have hj : i=19 := by
        by_contra hn
        exact hi (hrange i hn)
      subst i; simp [finalState]
  have hh := eval_call_lifted buildProgram id buildFinalPorts
    (finalState regs h r width [] [] []) Function.injective_id buildFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,xs,hh,hlen,hval,hw⟩

theorem finalProgram_runsIn (regs : Fin 8 → Bool) (h r width : List Bool)
    (hw : h.length+1 ≤ width.length) :
    ∃ (regs' : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn finalProgram
        (12*r.length+400*(h.length+1)*(r.length+1)*(h.length+5)+
          110*(r.length+1)*(width.length+(h.length+1)+4)+32)
        ((finalState regs h r width [] [] []).withPC (some finalProgram.entry))
        ((finalState regs' [] [] width [] words.flatten
          (List.replicate (r.length*width.length) false)).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words, x.length=width.length) ∧
      words.map BinaryArithmetic.toNat=(List.range r.length).map h.length.choose := by
  obtain ⟨tb,htb,rb,xs,hb,hlen,hval,hxs⟩ := finalBuild_eval regs h r width
  obtain ⟨tf,htf,rf,hf⟩ := finalFlatten_eval rb width xs (h.length+1) hxs
  rw [hlen] at htf
  have hvalue : (normalizedWords width xs).map BinaryArithmetic.toNat=
      (List.range r.length).map h.length.choose := by
    rw [normalizedWords_values width xs (fun x hx => (hxs x hx).trans hw),hval]
  refine ⟨rf,normalizedWords width xs,?_,by simpa using hlen,
    normalizedWords_word_length width xs,hvalue⟩
  refine ⟨tb+tf+1,by omega,?_⟩
  have hh := compiled_halt_trace (hb.seq hf) 17 0
  simpa only [finalProgram,finalCommand,flatWords_eq_flatten,flatZeros_eq,hlen] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective _ _
theorem binomialPorts_injective : Function.Injective binomialPorts := by decide

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

private theorem binomial_ports_cover (j : Fin 40)
    (h : j=2 ∨ j=8 ∨ j=10 ∨ (12 ≤ j.val ∧ j.val ≤ 28)) :
    j∈Set.range binomialPorts := by
  have hc : ∀ k : Fin 40, k=2 ∨ k=8 ∨ k=10 ∨ (12 ≤ k.val ∧ k.val ≤ 28) →
      k∈Set.range binomialPorts := by decide
  exact hc j h

private theorem binomial_project (c : Saved) (regs : Fin 9 → Bool)
    (h n rc ac : List Bool) :
    projectState regs8 binomialPorts (state c regs [] h n rc ac [] [] ([],[])) =
      LayoutBinomialProgram.finalState (regs ∘ regs8) h rc c.width [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [state,binomialPorts]

private theorem binomial_embed (c : Saved) (regs : Fin 9 → Bool) (rf : Fin 8 → Bool)
    (h n rc ac bp bn : List Bool) :
    ∃ rout, embedState regs8 binomialPorts (state c regs [] h n rc ac [] [] ([],[]))
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) =
      state c rout [] [] n [] ac bp bn ([],[]) := by
  let start := state c regs [] h n rc ac [] [] ([],[])
  let target := embedState regs8 binomialPorts start
    (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn)
  refine ⟨target.regs,?_⟩
  apply embedState_eq_of_ports regs8 binomialPorts _ _ _ regs8_injective binomialPorts_injective
  · intro i; exact embedState_register regs8 binomialPorts start
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) regs8_injective i
  · intro i hi; exact embedState_register_frame regs8 binomialPorts start
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) i hi
  · intro i; fin_cases i <;> simp [state,binomialPorts,LayoutBinomialProgram.finalState]
  · intro i hi
    have hn := fun hj => hi (binomial_ports_cover i hj)
    fin_cases i <;> first | exact (hn (by decide)).elim | simp [state]

theorem binomial_eval_oai (c : Saved) (regs : Fin 9 → Bool) (h n rc ac : List Bool)
    (hw : h.length+1 ≤ c.width.length) :
    ∃ t ≤ binomialCost h.length rc.length c.width.length,
    ∃ (rf : Fin 9 → Bool) (words : List (List Bool)), Eval binomial t
      (state c regs [] h n rc ac [] [] ([],[]))
      (state c rf [] [] n [] ac words.flatten (List.replicate (rc.length*c.width.length) false) ([],[])) ∧
      words.length=rc.length ∧ (∀ x∈words,x.length=c.width.length) ∧
      words.map BinaryArithmetic.toNat=(List.range rc.length).map h.length.choose := by
  obtain ⟨rf,words,⟨t,ht,he⟩,hlen,hword,hval⟩ :=
    LayoutBinomialProgram.finalProgram_runsIn (regs ∘ regs8) h rc c.width hw
  have hh := eval_call_from_state LayoutBinomialProgram.finalProgram regs8 binomialPorts
    (state c regs [] h n rc ac [] [] ([],[])) regs8_injective binomialPorts_injective
    (by simpa only [binomial_project] using he)
  obtain ⟨rout,hrout⟩ := binomial_embed c regs rf h n rc ac words.flatten
    (List.replicate (rc.length*c.width.length) false)
  rw [hrout] at hh
  exact ⟨t,ht,rout,words,hh,hlen,hword,hval⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval_oai
