-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:57:38.639894+00:00
-- url     : https://prove2.me/submissions/e903bcae-8dd1-4121-b18c-ccdb3dd65364

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S130
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_scopeCall_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem copy_eval (a : Data) (src dst : Fin 768) (h : CopyReady a src dst) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a (copied a src dst) :=
  SubexpScanPrimitives.copy_eval a src dst 679 0 1 h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem copies_eval (xs : List (Fin 768 × Fin 768)) (a : Data) (h : CopiesReady xs a) :
    Eval (copies xs) (copiesCost xs a) a (copiesState xs a) := by
  induction xs generalizing a with
  | nil => exact .base (.skip a)
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      exact (copy_eval a s d h.1).seq (ih _ h.2)

theorem copies_frame (xs : List (Fin 768 × Fin 768)) (a : Data) (i : Fin 768)
    (hi : ∀ x ∈ xs, x.2 ≠ i) : (copiesState xs a).stacks i = a.stacks i := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      rw [copiesState,ih _ (fun x hx => hi x (List.mem_cons_of_mem _ hx))]
      simp [copied_stack,Ne.symm (hi (s,d) List.mem_cons_self)]

theorem setRegs_eval (xs : List (StructuredProgram.Atom 40 768)) (a : Data) :
    Eval (setRegs xs) xs.length a (regsState xs a) :=
  .base (SubexpParameterProgram.atoms_eval xs a)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary finite-window facts for the concrete frontend port maps. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem block_not_mem {base n : ℕ} (h : base+n ≤ 768) (i : Fin 768)
    (hi : i.val < base ∨ base+n ≤ i.val) : i ∉ Set.range (block base n h) := by
  rintro ⟨j,hj⟩
  have hjv := congrArg Fin.val hj
  dsimp [block] at hjv
  have := j.isLt
  omega

theorem embedded_stack_frame {r base n : ℕ} (hr : r ≤ 40) (hs : base+n ≤ 768)
    (a : Data) (b : State r n) (i : Fin 768) (hi : i.val < base ∨ base+n ≤ i.val) :
    (embedState (registers r hr) (block base n hs) a b).stacks i = a.stacks i :=
  embedState_stack_frame _ _ _ _ _ (block_not_mem hs i hi)

theorem copies_ready_of_clean (xs : List (Fin 768 × Fin 768)) (a : Data)
    (h : ∀ x ∈ xs, x.1≠x.2 ∧ x.1≠679 ∧ x.2≠679) (ht : a.stacks 679=[]) :
    CopiesReady xs a := by
  induction xs generalizing a with
  | nil => trivial
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      have hx := h (s,d) List.mem_cons_self
      exact ⟨⟨hx.1,hx.2.1,Ne.symm hx.2.2,ht⟩,
        ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
          (by simpa [copied_stack,Ne.symm hx.2.2] using ht)⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem loadBits_eval (a : Data) (dst : Fin 768) (bits : List Bool) :
    ∃ rf, Eval (loadBits dst bits) (2*bits.length+1) a
      ⟨rf,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
  obtain ⟨rf,he⟩ := ArithmeticExpressionSupport.pushWord_eval dst bits (projectState r8 id a)
  have h := eval_liftCommand_from_state (ArithmeticExpressionSupport.pushWord dst bits) dst dst
    r8 id a (registers_injective ..) Function.injective_id he
  let b := embedState r8 id a ⟨rf,Function.update (projectState r8 id a).stacks dst
    (bits++(projectState r8 id a).stacks dst)⟩
  have hb : b = ⟨b.regs,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    exact embedState_stack r8 id a _ Function.injective_id i
  exact ⟨b.regs,by change Eval (loadBits dst bits) _ a b at h; rw [hb] at h; exact h⟩

theorem scopeReset_eval (a : Data) : Eval resetScopeRegs 11 a (scopeReset a) :=
  setRegs_eval scopeResetAtoms a

theorem scopeReset_regs (a : Data) : (scopeReset a).regs ∘ r11 = HashScopeProgram.RawTable.zeroRegs := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRawRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw scope call is fed by physical copies of the seven frontend masters. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


theorem prepareScopes_eval (a : Data) (ht : a.stacks 679=[])
    (hshape : a.stacks 515=[]) :
    ∃ n rf, n=copiesCost scopeCopies a+16 ∧
      Eval prepareScopes n a
        (scopeReset ⟨rf,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩) := by
  have hc := copies_eval scopeCopies a (copies_ready_of_clean scopeCopies a (by simp [scopeCopies]) ht)
  let b := copiesState scopeCopies a
  have hb : b.stacks 515=[] := (copies_frame scopeCopies a 515 (by simp [scopeCopies])).trans hshape
  obtain ⟨rf,hl⟩ := loadBits_eval b 515 [false,false]
  rw [hb,List.append_nil] at hl
  have hr := scopeReset_eval ⟨rf,Function.update b.stacks 515 [false,false]⟩
  refine ⟨copiesCost scopeCopies a+16,rf,rfl,?_⟩
  simpa [prepareScopes,sequence,b,Nat.add_assoc] using
    hc.seq (hl.seq (hr.seq (Eval.base (.skip _))))

theorem prepared_scope_projection (a : Data) (rf : Fin 40 → Bool)
    (he : emptyRange a 500 580)
    (clauses : List (List Bool)) (rows : HashScopeProgram.RawTable.Rows clauses.length)
    (b : ℕ) (width modulus index : List Bool) (mark : Option (Fin clauses.length))
    (h700 : a.stacks 700=Encoding.encodeList id clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
    (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
    (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
    projectState r11 scopes
      (scopeReset ⟨rf,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩) =
    HashScopeProgram.Complete.data HashScopeProgram.RawTable.zeroRegs width modulus
      (Encoding.encodeList id clauses) [false,false]
      (HashScopeProgram.RawTable.inputBits b rows) [] index [mark.isSome] := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact scopeReset_regs _
  · funext i
    have hz := he (scopes i) (by dsimp [scopes,block]; omega) (by dsimp [scopes,block]; omega)
    have hz501 := he 501 (by decide) (by decide)
    have hz507 := he 507 (by decide) (by decide)
    have hz514 := he 514 (by decide) (by decide)
    have hz546 := he 546 (by decide) (by decide)
    have hz549 := he 549 (by decide) (by decide)
    have hz550 := he 550 (by decide) (by decide)
    fin_cases i <;>
      simp_all [scopeReset_stacks,copiesState,scopeCopies,copied_stack,
        scopes,block,HashScopeProgram.Marked.tapes]

theorem rawCommand_eval_oai (a : Data) (he : emptyRange a 500 580)
    (ht : a.stacks 679=[]) (hout : a.stacks 718=[])
    (b : ℕ) (hb : 0 < b) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (h700 : a.stacks 700=Encoding.encodeList id clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
    (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
    (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
    ∃ n c, Eval rawCommand n a c ∧
      c.stacks 718=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) ∧
      n ≤ copiesCost scopeCopies a+21+
        HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index+
        7*(LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)).length ∧
      (∀ i : Fin 768, (i.val < 500 ∨ 580 ≤ i.val) → i≠718 → c.stacks i=a.stacks i) := by
  obtain ⟨np,rp,hnp,hpre⟩ := prepareScopes_eval a ht (he 515 (by decide) (by decide))
  let p := scopeReset ⟨rp,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩
  have hp := prepared_scope_projection a rp he clauses rows b width modulus index mark
    h700 h701 h705 h706 h707 h708
  obtain ⟨ns,hns,rs,hscope⟩ := scopeCall_eval p b hb clauses codes hc rows hbound mark index width modulus
    hindex hw hm hp
  let localResult := HashScopeProgram.Complete.data rs width modulus (Encoding.encodeList id clauses)
    [false,false] (LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)) [] [] []
  let z := embedState r11 scopes p localResult
  have hlocal : z.stacks 546=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) :=
    embedState_stack r11 scopes p localResult (block_injective ..) 46
  have hpframe (i : Fin 768) (hi : i.val < 500 ∨ 580 ≤ i.val) : p.stacks i=a.stacks i := by
    have h515 : i≠515 := by intro h; subst i; omega
    simp only [p,scopeReset_stacks,Function.update_of_ne h515]
    exact copies_frame scopeCopies a i (by
      intro x hx; simp only [scopeCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;> subst i <;> norm_num at hi)
  have hzframe (i : Fin 768) (hi : i.val < 500 ∨ 580 ≤ i.val) : z.stacks i=a.stacks i :=
    (embedded_stack_frame (by decide) (by decide) p localResult i hi).trans (hpframe i hi)
  have hz679 : z.stacks 679=[] := (hzframe 679 (Or.inr (by decide))).trans ht
  have hz718 : z.stacks 718=[] := (hzframe 718 (Or.inr (by decide))).trans hout
  have hcopy := copy_eval z 546 718 ⟨by decide,by decide,by decide,hz679⟩
  refine ⟨np+(ns+(7*(z.stacks 546).length+5)),copied z 546 718,
    hpre.seq (hscope.seq hcopy),?_,?_,?_⟩
  · simp [copied_stack,hlocal,hz718]
  · rw [hlocal]; omega
  · intro i hi hne
    simp only [copied_stack,ite_eq_right hne]
    exact hzframe i hi

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval_oai
