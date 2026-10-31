-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:28:12.38722+00:00
-- url     : https://prove2.me/submissions/513cb6d6-8a5f-454b-891c-f13b66792246

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_FromCounts_binomial_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_FromCounts_numerator_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The scalar loop length R−d is computed by deleting actual unary tokens.
The scan's distinguished unchanged anchor is removed first. Neither natural
subtraction nor a loop-count constructor is a machine primitive. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem subtract_eval (regs : Fin 2 → Bool) (left count : List Bool) :
    ∃ steps ≤ 3*count.length+2, ∃ rf,
      Eval subtractCommand steps (state regs left count)
        (state rf (left.drop count.length) []) := by
  let I : ℕ → Data → Prop := fun i d => d.stacks 0 = left.drop i
  have hstable : SubexponentialSAT.UnaryForPrograms.FrameStable ports I := by
    intro i a b h ha
    change b.stacks 0 = left.drop i
    rw [← h 0 (by decide)]
    exact ha
  have hbody : SubexponentialSAT.UnaryForPrograms.BodySpec ports body I (fun _ => 1) := by
    intro i d hd
    let e := (SubexponentialSAT.StructuredProgram.Atom.pop (0:Fin 2) (0:Fin 2) 1).eval d
    refine ⟨1,e,le_rfl,.base (.atom _ _),?_,?_⟩
    · simp [e,SubexponentialSAT.StructuredProgram.Atom.eval,SubexponentialSAT.StructuredProgram.Atom.instr,
        SubexponentialSAT.StructuredProgram.State.ofCfg,execInstr]
    · change (d.stacks 0).tail = left.drop (i+1)
      rw [hd]
      exact List.tail_drop
  obtain ⟨steps,e,he,hi,hc,hcost⟩ := SubexponentialSAT.UnaryForPrograms.for_correct
    ports body I (fun _ => 1) hstable hbody (state regs left count) (by simp [I,state])
  have hout : e = state e.regs (left.drop count.length) [] := by
    apply congrArg₂ SubexponentialSAT.StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    · simpa [state,I] using hi
    · simpa [state,ports] using hc
  refine ⟨steps,?_,e.regs,?_⟩
  · simp only [SubexponentialSAT.CounterForPrograms.budgetSum_const] at hcost
    simp at hcost
    omega
  · exact Eq.mp (congrArg (fun out => Eval subtractCommand steps (state regs left count) out) hout) he

/-- Removes the anchor token, then computes the required saturating length. -/
theorem command_eval (regs : Fin 2 → Bool) (R d : ℕ) :
    ∃ steps ≤ 3*d+3, ∃ rf,
      Eval command steps (state regs (List.replicate R true) (List.replicate (d+1) true))
        (state rf (List.replicate (R-d) true) []) := by
  let a := state regs (List.replicate R true) (List.replicate (d+1) true)
  let mid := SubexponentialSAT.UnaryForPrograms.popped ports a
  have hp := SubexponentialSAT.UnaryForPrograms.pop_eval ports a
  have hm : mid = state mid.regs (List.replicate R true) (List.replicate d true) := by
    apply congrArg₂ SubexponentialSAT.StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a,ports,List.replicate_succ]
  obtain ⟨n,hn,rf,he⟩ := subtract_eval mid.regs (List.replicate R true) (List.replicate d true)
  rw [← hm] at he
  refine ⟨1+n,by simp only [List.length_replicate] at hn; omega,rf,?_⟩
  simpa [command,subtractCommand,a,List.drop_replicate] using hp.seq he

end SubexponentialSAT.SqrtLog.LayoutProgram.Count

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

theorem regs2_injective : Function.Injective regs2 := Fin.castAdd_injective _ _
theorem countPorts_injective : Function.Injective countPorts := by decide

theorem copies_eval (c : Saved) (regs : Fin 9 → Bool) (u h : List Bool) :
    ∃ rf, Eval copies (14*c.r.length+7*c.a.length+15)
      (state c regs u h [] [] [] [] [] ([],[]))
      (state c rf u h c.r c.r c.a [] [] ([],[])) := by
  let s := state c regs u h [] [] [] [] [] ([],[])
  let s₁ := SubexpScanPrimitives.afterCopy s 5 9 0 1
  let s₂ := SubexpScanPrimitives.afterCopy s₁ 5 10 0 1
  let s₃ := SubexpScanPrimitives.afterCopy s₂ 6 11 0 1
  have h₁ := SubexpScanPrimitives.copy_eval s 5 9 14 0 1 (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h₂ := SubexpScanPrimitives.copy_eval s₁ 5 10 14 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state])
  have h₃ := SubexpScanPrimitives.copy_eval s₂ 6 11 14 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state])
  have he : s₃ = state c s₃.regs u h c.r c.r c.a [] [] ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state]
  refine ⟨s₃.regs,?_⟩
  have hh := h₁.seq (h₂.seq h₃)
  change Eval copies _ s s₃ at hh
  rw [he] at hh
  convert hh using 1 ; simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state] ; omega

theorem count_eval (c : Saved) (regs : Fin 9 → Bool) (h rc ac : List Bool) (R d : ℕ) :
    ∃ t ≤ 3*d+4, ∃ rf, Eval count t
      (state c regs (List.replicate (d+1) true) h (List.replicate R true) rc ac [] [] ([],[]))
      (state c rf [] h (List.replicate (R-d) true) rc ac [] [] ([],[])) := by
  let start := state c regs (List.replicate (d+1) true) h (List.replicate R true) rc ac [] [] ([],[])
  obtain ⟨t,ht,rf,he⟩ := LayoutProgram.Count.command_eval (regs ∘ regs2) R d
  have hp : projectState regs2 countPorts start =
      LayoutProgram.Count.state (regs ∘ regs2) (List.replicate R true) (List.replicate (d+1) true) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [start,state,countPorts]
  have hh := eval_call_from_state LayoutProgram.Count.program regs2 countPorts start
    regs2_injective countPorts_injective (by rw [hp]; exact compiled_halt_trace he 0 0)
  let target := embedState regs2 countPorts start (LayoutProgram.Count.state rf (List.replicate (R-d) true) [])
  have hf : target = state c target.regs [] h (List.replicate (R-d) true) rc ac [] [] ([],[]) := by
    apply embedState_eq_of_ports regs2 countPorts _ _ _ regs2_injective countPorts_injective
    · intro i; exact embedState_register regs2 countPorts start
        (LayoutProgram.Count.state rf (List.replicate (R-d) true) []) regs2_injective i
    · intro i hi; exact embedState_register_frame regs2 countPorts start
        (LayoutProgram.Count.state rf (List.replicate (R-d) true) []) i hi
    · intro i; fin_cases i <;> simp [state,countPorts]
    · intro i hi
      have hn : i≠9 ∧ i≠7 := by
        constructor
        · intro e; apply hi; exact ⟨0,e.symm⟩
        · intro e; apply hi; exact ⟨1,e.symm⟩
      fin_cases i <;> simp_all [start,state]
  change Eval count (t+1) start target at hh
  rw [hf] at hh
  exact ⟨t+1,by omega,target.regs,hh⟩

theorem cleanup_eval (c : Saved) (regs : Fin 9 → Bool) (bp bn : List Bool) (result : WordPair) :
    ∃ rf, Eval cleanup (2*bp.length+2*bn.length+6)
      (state c regs [] [] [] [] [] bp bn result)
      (state c rf [] [] [] [] [] [] [] result) := by
  let s := state c regs [] [] [] [] [] bp bn result
  let s₁ : Data := ⟨readRegs regs 0 1 none,StackRoutines.clearStacks 12 s.stacks⟩
  let s₂ : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 13 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 12 0 1 s
  have h₂ := Subexp.TupleProgram.clear_eval 13 0 1 s₁
  have he : s₂ = state c s₂.regs [] [] [] [] [] [] [] result := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [s₁,s,StackRoutines.clearStacks,state]
  have hh := h₁.seq h₂
  change Eval cleanup _ s s₂ at hh
  rw [he] at hh
  refine ⟨s₂.regs,?_⟩
  convert hh using 1 ; simp [s₁,s,StackRoutines.clearStacks,state] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/

/-! One consumer-facing contract for native triple preparation. -/

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence
open SubexponentialSAT.BinaryArithmetic

theorem zeroWord_value (W : ℕ) : BinaryArithmetic.toNat (List.replicate W false) = 0 := by
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ,ih]

theorem decoded_getD (words : List (List Bool)) (f : ℕ → ℕ) (R i : ℕ)
    (hlen : words.length = R) (hv : words.map BinaryArithmetic.toNat = (List.range R).map f)
    (hi : i < R) : BinaryArithmetic.toNat (words.getD i []) = f i := by
  have hiw : i < words.length := by omega
  have him : i < (words.map BinaryArithmetic.toNat).length := by simpa using hiw
  have hir : i < ((List.range R).map f).length := by simpa using hi
  have hh := congrArg (fun xs : List ℕ => xs.getD i 0) hv
  rw [List.getD_eq_getElem _ _ him,List.getD_eq_getElem _ _ hir] at hh
  simp only [List.getElem_map,List.getElem_range] at hh
  rw [List.getD_eq_getElem _ _ hiw]
  exact hh

theorem unsignedRow_entry (words : List (List Bool)) (f : ℕ → ℕ) (R W i : ℕ)
    (hlen : words.length = R) (hv : words.map BinaryArithmetic.toNat = (List.range R).map f)
    (hi : i < R) :
    pairValue (words.getD i [],(List.replicate R (List.replicate W false)).getD i []) =
      (f i : ℤ) ∧
    wordTotal (words.getD i [],(List.replicate R (List.replicate W false)).getD i []) = f i := by
  have hh := decoded_getD words f R i hlen hv hi
  have hz : (List.replicate R (List.replicate W false)).getD i [] =
      List.replicate W false := List.getD_replicate (List.replicate W false) hi
  change ((BinaryArithmetic.toNat (words.getD i []) : ℤ) -
      (BinaryArithmetic.toNat ((List.replicate R (List.replicate W false)).getD i []) : ℤ) = (f i : ℤ)) ∧
    BinaryArithmetic.toNat (words.getD i []) + BinaryArithmetic.toNat ((List.replicate R (List.replicate W false)).getD i []) = f i
  rw [hz,zeroWord_value,hh]
  simp

/-- All representation hypotheses needed by the native preparation theorem
follow from the native H/Pascal builders' unsigned rows and the power word. -/
theorem unsignedCache_contract (Hwords Bwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (A R d h : ℕ)
    (hlen : Hwords.length = R) (blen : Bwords.length = R)
    (hw : ∀ w ∈ Hwords, w.length = width.length)
    (bw : ∀ w ∈ Bwords, w.length = width.length)
    (hv : Hwords.map BinaryArithmetic.toNat = (List.range R).map (H A))
    (bv : Bwords.map BinaryArithmetic.toNat = (List.range R).map (h.choose))
    (pv : pairValue power = (2 : ℤ)^(R-1))
    (pt : wordTotal power = 2^(R-1)) :
    let c := unsignedCache Hwords Bwords width power R
    c.Uniform ∧ c.Fits (R-d) ∧ c.Values A R h ∧ c.Totals A R h := by
  let c := unsignedCache Hwords Bwords width power R
  have hz : ∀ w ∈ List.replicate R (List.replicate width.length false), w.length = width.length := by
    intro w hw
    rcases List.mem_replicate.mp hw with ⟨_,rfl⟩
    simp
  have hhe (i : ℕ) (hi : i < R) := unsignedRow_entry Hwords (H A) R width.length i hlen hv hi
  have hbe (i : ℕ) (hi : i < R) := unsignedRow_entry Bwords (h.choose) R width.length i blen bv hi
  refine ⟨⟨hw,hz,bw,hz⟩,?_,⟨?_,pv,?_⟩,⟨?_,pt,?_⟩⟩
  · simp [Cache.Fits,unsignedCache,hlen,blen]
  · intro i hi
    exact (hhe i hi).1
  · intro i hi
    exact (hbe i hi).1
  · intro i hi
    exact (hhe i hi).2
  · intro i hi
    exact (hbe i hi).2

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

/-- Given the reusable H and power caches, the runtime unchanged/transposed
counts suffice to build all remaining operands and evaluate the numerator. -/
theorem program_runsIn_oai (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 9 → Bool) (a h : List Bool) (R d Q : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := unsignedSaved Hwords width power R a
    ∃ rf result,
      RunsIn program (totalCost a.length R d h.length width.length (pairLength power))
        ((state c regs (List.replicate (d+1) true) h [] [] [] [] [] ([],[])).withPC (some program.entry))
        ((state c rf [] [] [] [] [] [] [] result).withPC none) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨r₁,h₁⟩ := copies_eval c regs (List.replicate (d+1) true) h
  obtain ⟨t₂,ht₂,r₂,h₂⟩ := count_eval c r₁ h c.r c.a R d
  obtain ⟨t₃,ht₃,r₃,Bwords,h₃,blen,bwords,bvalues⟩ :=
    binomial_eval c r₂ h (List.replicate (R-d) true) c.r c.a hwidth
  have crlen : c.r.length=R := by simp [c,unsignedSaved]
  have calen : c.a.length=a.length := rfl
  have cwlen : c.width.length=width.length := rfl
  rw [crlen] at ht₃ blen bvalues
  change t₃ ≤ binomialCost h.length R width.length at ht₃
  let cache := unsignedCache Hwords Bwords width power R
  obtain ⟨hu,hfit,hv,hm⟩ := unsignedCache_contract Hwords Bwords width power a.length R d h.length
    hlen blen hwords bwords hvalues bvalues hp hpt
  obtain ⟨t₄,ht₄,r₄,result,h₄,hv₄,hm₄,hl₄⟩ :=
    numerator_eval c cache r₃ (List.replicate (R-d) true) c.a a.length R d h.length Q
      rfl (by simp [cache,unsignedCache,c,unsignedSaved]) rfl rfl
      (by simp) rfl hu hfit hv hm hAQ hQ hhQ
  change t₄ ≤ numeratorPrepareCost (R-d) a.length width.length (pairLength power)+
    numeratorFoldCost (R-d) width.length (pairLength power)+1 at ht₄
  have bn : cache.Bnegative.flatten=List.replicate (R*width.length) false := by
    simp [cache,unsignedCache]
  have bp : cache.Bpositive.flatten=Bwords.flatten := rfl
  rw [bp,bn] at h₄
  have h₃' : Eval binomial t₃
      (state c r₂ [] h (List.replicate (R-d) true) c.r c.a [] [] ([],[]))
      (state c r₃ [] [] (List.replicate (R-d) true) [] c.a Bwords.flatten (List.replicate (R*width.length) false) ([],[])) := by
    simpa only [crlen, cwlen] using h₃
  obtain ⟨rf,h₅⟩ := cleanup_eval c r₄ Bwords.flatten (List.replicate (R*width.length) false) result
  have bflat : Bwords.flatten.length=R*width.length := by
    rw [List.length_flatten]
    have he : Bwords.map List.length=Bwords.map (fun _ => width.length) := by
      apply List.map_congr_left
      exact bwords
    rw [he]
    simp [blen]
  refine ⟨rf,result,⟨_,?_,compiled_halt_trace (h₁.seq (h₂.seq (h₃'.seq (h₄.seq h₅)))) 7 37⟩,hv₄,hm₄,hl₄⟩
  simp only [crlen,calen,bflat,List.length_replicate]
  unfold totalCost
  omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn_oai
