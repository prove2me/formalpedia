-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:05:30.324569+00:00
-- url     : https://prove2.me/submissions/07be18ec-ee8e-4148-a86c-d9323922fbce

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S137
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S156
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutBinomialProgram_finalFlatten_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_cacheBuildLoop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive Pascal-prefix cache for the original parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open Matrix SubexponentialSAT.BinomialInterpolation

theorem H_succ_succ (A m : ℕ) :
    H (A + 1) (m + 1) = H A (m + 1) + 2 * H (A + 1) m := by rw [H]

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrenceScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A left-to-right add/shift scan constructs each unsigned cache row. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

theorem scan_cell (A n : ℕ) :
    2 * scanPrior A n + H A n = H (A + 1) n := by
  cases n with
  | zero => simp [scanPrior]
  | succ n => simp [scanPrior, H_succ_succ, Nat.add_comm]

theorem scanDouble_H_offset (A R n : ℕ) :
    scanDouble (scanPrior A n) ((List.range R).map (fun m => H A (n + m))) =
      (List.range R).map (fun m => H (A + 1) (n + m)) := by
  induction R generalizing n with
  | zero => rfl
  | succ R ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero,
      scanDouble, scan_cell]
    congr 1
    have hfun : (fun m => H A (n + m)) ∘ Nat.succ =
        fun m => H A ((n + 1) + m) := by
      funext m
      simp only [Function.comp_apply]
      congr 1
      omega
    have hfun' : (fun m => H (A + 1) (n + m)) ∘ Nat.succ =
        fun m => H (A + 1) ((n + 1) + m) := by
      funext m
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hfun, hfun']
    simpa only [scanPrior] using ih (n + 1)

theorem scanDouble_H (A R : ℕ) :
    scanDouble 0 ((List.range R).map (H A)) =
      (List.range R).map (H (A + 1)) := by
  simpa only [scanPrior, Nat.zero_add] using scanDouble_H_offset A R 0

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheWord_value (prior old : List Bool) :
    BinaryArithmetic.toNat (cacheWord prior old) = 2*BinaryArithmetic.toNat prior+BinaryArithmetic.toNat old := by
  simp [cacheWord,toNat_add,BinaryArithmetic.toNat,bitVal]

theorem cacheWord_length (prior old : List Bool) :
    (cacheWord prior old).length ≤ max prior.length old.length+2 := by
  have h := length_add (false::prior) old
  dsimp [cacheWord]
  simp only [List.length_cons] at h
  omega

theorem cacheScan_word_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ cacheScan prior xs, x.length ≤ B+2*xs.length := by
  induction xs generalizing prior B with
  | nil => simp [cacheScan]
  | cons old rest ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have hrest : ∀ x ∈ rest, x.length ≤ B+2 := by
      intro x h
      have hh := hx x (by simp [h])
      omega
    have ht := ih (cacheWord prior old) (B+2) hn hrest
    intro x h
    simp only [cacheScan,List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.length_cons]; omega
    · have hh := ht x h
      simp only [List.length_cons]; omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheIter_word_length (n : ℕ) (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ cacheIter n xs, x.length ≤ B+2*n*xs.length := by
  induction n generalizing xs B with
  | zero => simpa [cacheIter] using hx
  | succ n ih =>
    have hs := cacheScan_word_length [] xs B (by simp) hx
    have ht := ih (cacheScan [] xs) (B+2*xs.length) hs
    simpa [cacheIter,Nat.mul_add,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

theorem cacheScan_values (prior : List Bool) (xs : List (List Bool)) :
    (cacheScan prior xs).map BinaryArithmetic.toNat = scanDouble (BinaryArithmetic.toNat prior) (xs.map BinaryArithmetic.toNat) := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [cacheScan,List.map_cons,scanDouble,ih,cacheWord_value]

theorem cacheIter_values (n A R : ℕ) (xs : List (List Bool))
    (hx : xs.map BinaryArithmetic.toNat = (List.range R).map (H A)) :
    (cacheIter n xs).map BinaryArithmetic.toNat = (List.range R).map (H (A+n)) := by
  induction n generalizing A xs with
  | zero => simpa [cacheIter] using hx
  | succ n ih =>
    have hs : (cacheScan [] xs).map BinaryArithmetic.toNat = (List.range R).map (H (A+1)) := by
      rw [cacheScan_values,hx]
      exact scanDouble_H A R
    simpa [cacheIter,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (A+1) _ hs

theorem initialCache_values (R : ℕ) :
    (initialCache R).map BinaryArithmetic.toNat = (List.range R).map (H 0) := by
  have hh : H 0 = fun _ : ℕ => 1 := funext H_zero
  simp [initialCache,hh,BinaryArithmetic.toNat,bitVal]

theorem cacheIter_initial_values (A R : ℕ) :
    (cacheIter A (initialCache R)).map BinaryArithmetic.toNat = (List.range R).map (H A) := by
  simpa using cacheIter_values A 0 R (initialCache R) (initialCache_values R)

theorem cacheIter_initial_word_length (A R : ℕ) :
    ∀ x ∈ cacheIter A (initialCache R), x.length ≤ 1+2*A*R := by
  have h := cacheIter_word_length A (initialCache R) 1 (by
    intro x hx
    simp only [initialCache,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    rfl)
  simpa using h

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem initialRecord_encoding (xs : List WordPair) :
    initialRecord ++ pairEncoding xs = pairEncoding (([true],[])::xs) := rfl

private theorem initial_stable (base : Data) :
    UnaryForPrograms.FrameStable initialPorts (InitialInvariant base) := by
  intro i a b hab hi
  refine ⟨?_,fun j hj hk => (hab j hk).symm.trans (hi.2 j hj hk)⟩
  exact (hab 15 (by decide)).symm.trans hi.1

private theorem initial_body (base : Data) :
    UnaryForPrograms.BodySpec initialPorts initialBody (InitialInvariant base) (fun _ => 10) := by
  intro i d hi
  obtain ⟨r,he⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) initialRecord d
  refine ⟨10,⟨r,Function.update d.stacks 15 (initialRecord++d.stacks 15)⟩,le_rfl,he,by simp [initialPorts],?_,?_⟩
  · simp only [Function.update_same, hi.1, initialRecord_encoding, List.replicate_succ]
  · intro j hj hk
    simpa [hj] using hi.2 j hj hk

theorem initialCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 12*counter.length+4, ∃ r,
      Eval initialCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding (List.replicate counter.length ([true],[])))) := by
  let d := state regs ([],counter) ([],[]) ([],[]) []
  obtain ⟨r₀,h₀⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false] d
  let a : Data := ⟨r₀,Function.update d.stacks 15 [false]⟩
  have hi : InitialInvariant d 0 a := by
    constructor
    · rfl
    · intro j hj _; simp [a,hj]
  obtain ⟨t,e,he,hi',hc,ht⟩ := UnaryForPrograms.for_correct initialPorts initialBody
    (InitialInvariant d) (fun _ => 10) (initial_stable d) (initial_body d) a hi
  have hc' : e.stacks 17 = [] := hc
  have hi'₁ : e.stacks 15 = pairEncoding (List.replicate counter.length ([true],[])) := by
    simpa [a,d,state,initialPorts] using hi'.1
  have heq : e = state e.regs ([],[]) ([],[]) ([],[])
      (pairEncoding (List.replicate counter.length ([true],[]))) := by
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
  · have hb : CounterForPrograms.budgetSum (fun _ => 10) 0 counter.length = 10*counter.length := by
      rw [CounterForPrograms.budgetSum_const, Nat.mul_comm]
    have ht' : t ≤ 10*counter.length+2*counter.length+2 := by
      simpa [a,d,state,initialPorts,hb] using ht
    omega
  · have hh : Eval initialCommand (2+t) d e := h₀.seq he
    rw [heq] at hh
    exact hh

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem initialBuildPorts_injective : Function.Injective initialBuildPorts := by decide

theorem initialBuild_eval (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ t ≤ 12*r.length+5, ∃ regs',
      Eval initialBuild t (buildState regs a r [])
        (buildState regs' a [] (pairEncoding (List.replicate r.length ([true],[])))) := by
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
        (pairEncoding (List.replicate r.length ([true],[])))) =
      buildState regs' a [] (pairEncoding (List.replicate r.length ([true],[]))) := by
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
        (12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+8)
        ((buildState regs a r []).withPC (some buildProgram.entry))
        ((buildState regs' [] [] (pairEncoding (xs.map fun x => (x,[])))).withPC none) ∧
      xs.length = r.length ∧
      xs.map BinaryArithmetic.toNat = (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      (∀ x ∈ xs, x.length ≤ 1+2*a.length*r.length) := by
  obtain ⟨ti,hti,ri,hi⟩ := initialBuild_eval regs a r
  have hw : ∀ x ∈ initialCache r.length, x.length ≤ 1 := by
    intro x hx
    simp only [initialCache,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    rfl
  obtain ⟨tc,htc,rc,hc⟩ := cacheBuildLoop_eval ri a (initialCache r.length) 1 hw
  have hh : (initialCache r.length).map (fun x => (x,([] : List Bool))) =
      List.replicate r.length ([true],[]) := by simp [initialCache]
  rw [hh] at hc
  refine ⟨rc,cacheIter a.length (initialCache r.length),
    ⟨ti+tc+1,?_,compiled_halt_trace (hi.seq hc) 17 15⟩,?_,?_,?_⟩
  · simp only [initialCache_length] at htc
    have hnorm : 1+2*a.length*r.length+4 = 2*a.length*r.length+5 := by omega
    rw [hnorm] at htc
    omega
  · simp
  · exact cacheIter_initial_values a.length r.length
  · exact cacheIter_initial_word_length a.length r.length

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

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

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPower
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program generates the power-of-two clearing denominator from
its unary exponent. The exponent is runtime data, never control-table size. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

private theorem powerRead_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerRead 1 (powerState regs counter output) (powerAfterRead regs counter output) := by
  have h := Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
    (.pop (0 : Fin 2) (0 : Fin 2) 1) (powerState regs counter output))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> simp [ powerState,
      StructuredProgram.Atom.instr, execInstr]

private theorem powerLoop_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerLoop (4 * counter.length + 1) (powerAfterRead regs counter output)
      (powerState (readRegs regs 0 1 none) []
        (List.replicate counter.length false ++ output)) := by
  induction counter generalizing regs output with
  | nil =>
    simpa [powerLoop, powerAfterRead, powerState] using
      (Eval.while_false (test := (1 : Fin 2))
        (body := .seq powerPutZero powerRead)
        (a := powerAfterRead regs [] output)
        (by simp [powerAfterRead, powerState, readRegs_present]))
  | cons bit counter ih =>
    let r := readRegs regs 0 1 (some bit)
    let r0 := Function.update r 0 false
    have hs : Eval (.base (.atom (.set 0 false))) 1
        (powerState r counter output) (powerState r0 counter output) :=
      .base (.atom _ _)
    have hp : Eval (.base (.atom (.push 1 0))) 1
        (powerState r0 counter output) (powerState r0 counter (false :: output)) := by
      convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
          (.push (1 : Fin 2) (0 : Fin 2)) (powerState r0 counter output))) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        fin_cases j <;> simp [powerState, r0,
          StructuredProgram.Atom.instr, execInstr]
    have hr := powerRead_eval r0 counter (false :: output)
    have ht := ih r0 (false :: output)
    have he := Eval.while_true (test := (1 : Fin 2))
      (by simp [powerState, r, readRegs_present]) ((hs.seq hp).seq hr) ht
    have hreg : readRegs r0 0 1 none = readRegs regs 0 1 none := by
      funext j
      fin_cases j <;> simp [readRegs, r0, r]
    have hrp : List.replicate counter.length false ++ false :: output =
        false :: (List.replicate counter.length false ++ output) := by
      induction counter.length with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ] using congrArg (false :: ·) ih
    convert he using 1 <;>
      simp [ powerAfterRead, powerState, r,
        hreg, List.replicate_succ, hrp] ; omega

/-- The output is the little-endian word for 2^q, prepended to its old tail. -/
theorem powerCommand_eval (regs : Fin 2 → Bool) (counter output : List Bool) :
    Eval powerCommand (4 * counter.length + 4) (powerState regs counter output)
      (powerState (readRegs regs 0 1 none) []
        (List.replicate counter.length false ++ true :: output)) := by
  let r := Function.update regs 0 true
  have hs : Eval (.base (.atom (.set 0 true))) 1
      (powerState regs counter output) (powerState r counter output) :=
    .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 1 0))) 1
      (powerState r counter output) (powerState r counter (true :: output)) := by
    convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
        (.push (1 : Fin 2) (0 : Fin 2)) (powerState r counter output))) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [powerState, r,
        StructuredProgram.Atom.instr, execInstr]
  have hr := powerRead_eval r counter (true :: output)
  have hl := powerLoop_eval r counter (true :: output)
  have hreg : readRegs r 0 1 none = readRegs regs 0 1 none := by
    funext j
    fin_cases j <;> simp [readRegs, r]
  have h := hs.seq (hp.seq (hr.seq hl))
  convert h using 1 <;> first | omega | simp [ hreg]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheFlat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The H cache builder followed by the shared physical fixed-width adapter.
Only the common width survives alongside the two flat output arrays. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutBinomialProgram (finalState buildFinalPorts buildFinalPorts_injective
  finalFlatten finalFlatten_eval normalizedWords normalizedWords_length
  normalizedWords_values normalizedWords_word_length flatWords_eq_flatten flatZeros_eq)

theorem hFlatBuild_eval (regs : Fin 8 → Bool) (a r width : List Bool) :
    ∃ t ≤ 12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+8,
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)),
      Eval hFlatBuild t (finalState regs a r width [] [] [])
        (finalState regs' [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] []) ∧
      xs.length=r.length ∧ xs.map BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      (∀ x ∈ xs, x.length ≤ 1+2*a.length*r.length) := by
  obtain ⟨rf,xs,⟨t,ht,he⟩,hlen,hval,hw⟩ := buildProgram_runsIn regs a r
  have hs : embedState id buildFinalPorts (finalState regs a r width [] [] [])
      (buildState regs a r []) = finalState regs a r width [] [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi; rfl
  have hf : embedState id buildFinalPorts (finalState regs a r width [] [] [])
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
    (finalState regs a r width [] [] []) Function.injective_id buildFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,xs,hh,hlen,hval,hw⟩

theorem hFlatProgram_runsIn (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ (regs' : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn hFlatProgram
        (12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+
          110*(r.length+1)*(width.length+(1+2*a.length*r.length)+4)+16)
        ((finalState regs a r width [] [] []).withPC (some hFlatProgram.entry))
        ((finalState regs' [] [] width [] words.flatten
          (List.replicate (r.length*width.length) false)).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words, x.length=width.length) ∧
      words.map BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  obtain ⟨tb,htb,rb,xs,hb,hlen,hval,hxs⟩ := hFlatBuild_eval regs a r width
  obtain ⟨tf,htf,rf,hf⟩ := finalFlatten_eval rb width xs (1+2*a.length*r.length) hxs
  rw [hlen] at htf
  have hvalue : (normalizedWords width xs).map BinaryArithmetic.toNat=
      (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
    rw [normalizedWords_values width xs (fun x hx => (hxs x hx).trans hw),hval]
  refine ⟨rf,normalizedWords width xs,?_,by simpa using hlen,
    normalizedWords_word_length width xs,hvalue⟩
  refine ⟨tb+tf+1,by omega,?_⟩
  have hh := compiled_halt_trace (hb.seq hf) 17 0
  simpa only [hFlatProgram,hFlatCommand,flatWords_eq_flatten,flatZeros_eq,hlen] using hh

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

private theorem flatPorts_inj : Function.Injective flatPorts := Fin.castAdd_injective _ _
private theorem powerRegs_inj : Function.Injective powerRegs := Fin.castAdd_injective _ _
private theorem powerPorts_inj : Function.Injective powerPorts := by decide

theorem copies_eval (regs : Fin 8 → Bool) (a r width : List Bool) :
    ∃ rf, Eval copies (7*(a.length+r.length+width.length)+15)
      (state regs a r width [] [] [] [] [] [] [])
      (state rf a r width a r width [] [] [] []) := by
  let s := state regs a r width [] [] [] [] [] [] []
  let s1 := SubexpScanPrimitives.afterCopy s 20 17 0 1
  let s2 := SubexpScanPrimitives.afterCopy s1 21 18 0 1
  let s3 := SubexpScanPrimitives.afterCopy s2 22 19 0 1
  have h1 := SubexpScanPrimitives.copy_eval s 20 17 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 := SubexpScanPrimitives.copy_eval s1 21 18 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks])
  have h3 := SubexpScanPrimitives.copy_eval s2 22 19 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks])
  have hs : s3 = state s3.regs a r width a r width [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  have h := h1.seq (h2.seq h3)
  change Eval copies _ s s3 at h
  rw [hs] at h
  refine ⟨s3.regs,?_⟩
  convert h using 1 ; simp [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] ; omega

theorem flat_eval (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ t ≤ flatCost a.length r.length width.length, ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
      Eval flat t (state regs a r width a r width [] [] [] [])
        (state rf a r width [] [] width words.flatten
          (List.replicate (r.length*width.length) false) [] []) ∧
      words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  obtain ⟨rf,words,⟨t,ht,he⟩,hlen,hwidth,hvalues⟩ := hFlatProgram_runsIn regs a r width hw
  let start := state regs a r width a r width [] [] [] []
  have hp : projectState id flatPorts start = LayoutBinomialProgram.finalState regs a r width [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [start,state,flatPorts]
  have h := eval_call_from_state hFlatProgram id flatPorts start Function.injective_id flatPorts_inj
    (by rw [hp]; exact he)
  have ho : embedState id flatPorts start
      (LayoutBinomialProgram.finalState rf [] [] width [] words.flatten
        (List.replicate (r.length*width.length) false)) =
      state rf a r width [] [] width words.flatten
        (List.replicate (r.length*width.length) false) [] [] := by
    apply embedState_eq_of_ports id flatPorts _ _ _ Function.injective_id flatPorts_inj
    · intro j; rfl
    · intro j hj; exact (hj ⟨j,rfl⟩).elim
    · intro j; fin_cases j <;> simp [state,flatPorts,LayoutBinomialProgram.finalState]
    · intro j hj
      have hlow : 20 ≤ j.val := by
        by_contra hn
        have hjlt : j.val < 20 := by omega
        exact hj ⟨⟨j.val,hjlt⟩,Fin.ext rfl⟩
      fin_cases j <;> simp_all [start,state]
  rw [ho] at h
  exact ⟨t,ht,rf,words,h,hlen,hwidth,hvalues⟩

theorem makePower_eval (regs : Fin 8 → Bool) (a r width p n : List Bool) :
    ∃ rf, Eval makePower (7*r.length+4*(r.length-1)+11)
      (state regs a r width [] [] width p n [] [])
      (state rf a r width [] [] width p n (denominatorWord r.length) []) := by
  let s := state regs a r width [] [] width p n [] []
  let s1 := SubexpScanPrimitives.afterCopy s 21 23 0 1
  let s2 : Data := ⟨readRegs s1.regs 0 1 r.head?,Function.update s1.stacks 23 r.tail⟩
  have h1 := SubexpScanPrimitives.copy_eval s 21 23 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 : Eval popCounter 1 s1 s2 := by
    convert (Eval.base (StructuredProgram.Eval.atom (.pop (23:Fin 24) (0:Fin 8) 1) s1)) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,
StructuredProgram.Atom.instr,
execInstr]
    · funext j
      fin_cases j <;> simp [s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,
StructuredProgram.Atom.instr,
execInstr]
  have hp : projectState powerRegs powerPorts s2 = powerState (s2.regs ∘ powerRegs) r.tail [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [powerPorts,s2,s1,s,state,
      SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  have ht := compiled_halt_trace (powerCommand_eval (s2.regs ∘ powerRegs) r.tail []) 0 1
  have h3 := eval_call_from_state powerProgram powerRegs powerPorts s2 powerRegs_inj powerPorts_inj
    (by rw [hp]; exact ht)
  let target := embedState powerRegs powerPorts s2
    (powerState (readRegs (s2.regs ∘ powerRegs) 0 1 none) []
      (List.replicate r.tail.length false ++ [true]))
  have he : target = state target.regs a r width [] [] width p n (denominatorWord r.length) [] := by
    apply embedState_eq_of_ports powerRegs powerPorts _ _ _ powerRegs_inj powerPorts_inj
    · intro j; exact embedState_register powerRegs powerPorts s2 _ powerRegs_inj j
    · intro j hj; exact embedState_register_frame powerRegs powerPorts s2 _ j hj
    · intro j; fin_cases j <;> simp [state,powerPorts,powerState,denominatorWord]
    · intro j hj
      have hneq : j≠23 ∧ j≠2 := by
        constructor
        · intro h; exact hj ⟨0,h.symm⟩
        · intro h; exact hj ⟨1,h.symm⟩
      fin_cases j <;> simp_all [s2,s1,s,state,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  change Eval powerCall _ s2 target at h3
  rw [he] at h3
  refine ⟨target.regs,?_⟩
  have h := h1.seq (h2.seq h3)
  convert h using 1 ; simp [s,state,List.length_tail] ; omega

/-- No coefficient list or denominator word is an input. Their full setup is
charged, while the three runtime unary parameters remain available. -/
theorem program_runsIn_oai (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn program
        (7*(a.length+r.length+width.length)+flatCost a.length r.length width.length+11*r.length+27)
        ((state regs a r width [] [] [] [] [] [] []).withPC (some program.entry))
        ((state rf a r width [] [] width words.flatten
          (List.replicate (r.length*width.length) false) (denominatorWord r.length) []).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (denominatorWord r.length)=2^(r.length-1) := by
  obtain ⟨r1,h1⟩ := copies_eval regs a r width
  obtain ⟨t,ht,r2,words,h2,hlen,hwidth,hvalues⟩ := flat_eval r1 a r width hw
  obtain ⟨r3,h3⟩ := makePower_eval r2 a r width words.flatten
    (List.replicate (r.length*width.length) false)
  refine ⟨r3,words,⟨_,?_,compiled_halt_trace (h1.seq (h2.seq h3)) 20 0⟩,
    hlen,hwidth,hvalues,powerWord_value _⟩
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn_oai
