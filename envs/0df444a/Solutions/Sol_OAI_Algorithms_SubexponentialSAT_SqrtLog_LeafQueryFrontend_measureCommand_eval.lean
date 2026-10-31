-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:18:42.760204+00:00
-- url     : https://prove2.me/submissions/97e78531-b4d5-44ec-a2b2-fcd87adac3c6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_arityCall_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_statsCall_eval

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

theorem finish_injective : Function.Injective finish := by decide

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Add precisely the uncovered-variable neutral factors. Inputs are the
unary outputs of the physical scope and variable scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem peek_eval (i : Fin 3) (d : Data) : Eval (peek i) 1 d (peeked i d) := .base (.atom _ _)

theorem ensureOne_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 4 ∧ Eval ensureOne n (state r q u a) (state rf q u (max a 1)) := by
  cases a with
  | zero =>
    let b := peeked 2 (state r q u 0)
    let rf := Function.update b.regs 0 true
    have hp : Eval pushOne 2 b (state rf q u 1) := by
      have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) b)).seq
        (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) _))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [unary,b,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
    exact ⟨4,rf,by omega,(peek_eval 2 _).seq
      (Eval.ite_false (by simp [unary,readRegs]) hp)⟩
  | succ a =>
    let b := peeked 2 (state r q u (a+1))
    have hm : max (a+1) 1 = a+1 := by omega
    refine ⟨2,b.regs,by omega,?_⟩
    rw [hm]
    exact (peek_eval 2 _).seq (Eval.ite_true
      (by simp [unary,readRegs,List.replicate_succ])
      (Eval.base (StructuredProgram.Eval.skip b)))

theorem adjust_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 6 ∧ Eval adjust n (state r q u a) (state rf q u (neutralArity a u)) := by
  cases u with
  | zero =>
    let b := peeked 1 (state r q 0 a)
    refine ⟨2,b.regs,by omega,?_⟩
    have h := (peek_eval 1 (state r q 0 a)).seq
      (Eval.ite_false (yes := ensureOne) (show b.regs 1 = false by simp [b,unary,readRegs])
        (Eval.base (StructuredProgram.Eval.skip b)))
    simpa [neutralArity,b,peeked,state] using h
  | succ u =>
    let b := peeked 1 (state r q (u+1) a)
    obtain ⟨n,rf,hn,he⟩ := ensureOne_eval b.regs q (u+1) a
    refine ⟨1+(n+1),rf,by omega,?_⟩
    have h := (peek_eval 1 (state r q (u+1) a)).seq
      (Eval.ite_true (no := .base .skip) (show b.regs 1 = true by simp [b,unary,readRegs,List.replicate_succ]) he)
    simpa [neutralArity] using h

theorem command_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 3*u+9 ∧ Eval command n (state r q u a)
      (state rf (q+u) 0 (neutralArity a u)) := by
  obtain ⟨n,ri,hn,ha⟩ := adjust_eval r q u a
  let rf := readRegs ri 0 1 none
  have ht : Eval transfer (3*u+3) (state ri q u (neutralArity a u))
      (state rf (q+u) 0 (neutralArity a u)) := by
    have h := SubexpScanPrimitives.transfer_eval
      (state ri q u (neutralArity a u)) (1 : Fin 3) 0 (0 : Fin 3) 1
      (by decide) (by decide)
    convert h using 1
    · simp [ unary]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [ unary, StackRoutines.transferStacks, List.reverse_replicate, Nat.add_comm]
  exact ⟨n+(3*u+3),rf,by omega,ha.seq ht⟩

theorem program_runsIn (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ rf, RunsIn program (3*u+10)
      ((state r q u a).withPC (some program.entry))
      ((state rf (q+u) 0 (neutralArity a u)).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval r q u a
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 1⟩
end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem call_run {r s l : ℕ} (p : Program r s l) (rr : Fin r → Fin 40)
    (ss : Fin s → Fin 768) (hr : Function.Injective rr) (hs : Function.Injective ss)
    (a : Data) (b : State r s) (B : ℕ)
    (h : RunsIn p B ((projectState rr ss a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ B, Eval (.call (ProgramLinking.liftProgram p rr ss)) n a (embedState rr ss a b) := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn,eval_call_from_state p rr ss a hr hs ht⟩

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumerics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem finishCall_eval (a : Data) (q u ar : ℕ)
    (hp : projectState r3 finish a = LeafStatisticsProgram.Finalize.state (a.regs ∘ r3) q u ar) :
    ∃ n ≤ 3*u+10, ∃ rf,
      Eval finishCall n a (embedState r3 finish a
        (LeafStatisticsProgram.Finalize.state rf (q+u) 0
          (LeafStatisticsProgram.Finalize.neutralArity ar u))) := by
  obtain ⟨rf,he⟩ := LeafStatisticsProgram.Finalize.program_runsIn (a.regs ∘ r3) q u ar
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r3 finish (registers_injective ..) finish_injective a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendMeasure
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual scope/mask scans are joined before any statistic is converted. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


theorem measureCommand_eval_oai (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hrows : a.stacks 718=LeafStatisticsProgram.scopeBits rows)
    (hmask : a.stacks 719=forward) (ht : a.stacks 679=[])
    (hz : emptyRange a 612 645)
    (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length) :
    ∃ n b, Eval measureCommand n a b ∧ Measured rows forward b ∧
      n ≤ measureBudget a rows forward ∧
      (∀ i : Fin 768, (i.val < 612 ∨ 645 ≤ i.val) → b.stacks i=a.stacks i) := by
  let c := copiesState statsCopies a
  have hc := copies_eval statsCopies a (copies_ready_of_clean _ _ (by simp [statsCopies]) ht)
  have hp : projectState r10 stats c = LeafStatisticsProgram.initial (c.regs ∘ r10) rows forward := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      have hi := hz (stats i) (by dsimp [stats,block]; omega) (by dsimp [stats,block]; omega)
      have h612 := hz 612 (by decide) (by decide)
      have h632 := hz 632 (by decide) (by decide)
      fin_cases i <;> simp_all [c,copiesState,statsCopies,copied_stack,
        stats,block]
  obtain ⟨ns,hns,rs,hs⟩ := statsCall_eval c rows forward hp
  let small := LeafStatisticsProgram.variableState rs rows forward.length [] forward (totals rows forward)
  let s := embedState r10 stats c small
  have hsframe (i : Fin 768) (hi : i.val < 612 ∨ 633 ≤ i.val) : s.stacks i=a.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) c small i hi
    exact h.trans (copies_frame statsCopies a i (by
      intro x hx; simp only [statsCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> intro he <;> subst i <;> norm_num at hi))
  have hs718 : s.stacks 718=LeafStatisticsProgram.scopeBits rows := (hsframe 718 (Or.inr (by decide))).trans hrows
  have hs719 : s.stacks 719=forward := (hsframe 719 (Or.inr (by decide))).trans hmask
  have hs679 : s.stacks 679=[] := (hsframe 679 (Or.inr (by decide))).trans ht
  have hs633 : s.stacks 633=[] := (hsframe 633 (Or.inr (by decide))).trans (hz 633 (by decide) (by decide))
  have hs640 : s.stacks 640=[] := (hsframe 640 (Or.inr (by decide))).trans (hz 640 (by decide) (by decide))
  let d := copiesState arityCopies s
  have hd := copies_eval arityCopies s (copies_ready_of_clean _ _ (by simp [arityCopies]) hs679)
  let p := regsState [.set 7 false,.set 8 true,.set 9 false] d
  have hregs : Eval arityRegisters 3 d p := setRegs_eval _ d
  have hpstacks : p.stacks=d.stacks := rfl
  have hpa : projectState r10 arity p = RecordPrograms.state LeafStatisticsProgram.Arity.ports
      (LeafStatisticsProgram.Arity.state (p.regs ∘ r10) forward [] [] [] 0 0)
      false true false (LeafStatisticsProgram.scopeBits rows) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i
      have hs0 := hsframe (arity i) (Or.inr (by dsimp [arity,block]; omega))
      have hi := hz (arity i) (by dsimp [arity,block]; omega) (by dsimp [arity,block]; omega)
      fin_cases i <;>
        simp_all [projectState,d,copiesState,arityCopies,copied_stack,arity,block,
LeafStatisticsProgram.Arity.ports,LeafStatisticsProgram.Arity.state,
          LeafStatisticsProgram.Arity.unary]
  obtain ⟨na,hna,ra,ha⟩ := arityCall_eval p rows forward hv hpa
  let asmall := LeafStatisticsProgram.Arity.state ra forward [] [] []
    (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length
  let z := embedState r10 arity p asmall
  have hzframe (i : Fin 768) (hi : i.val < 633 ∨ 645 ≤ i.val) : z.stacks i=s.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) p asmall i hi
    rw [hpstacks] at h
    exact h.trans (copies_frame arityCopies s i (by
      intro x hx; simp only [arityCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> intro he <;> subst i <;> norm_num at hi))
  have hsvalue (i : Fin 21) : s.stacks (stats i)=small.stacks i :=
    embedState_stack r10 stats c small (block_injective ..) i
  have hzvalue (i : Fin 12) : z.stacks (arity i)=asmall.stacks i :=
    embedState_stack r10 arity p asmall (block_injective ..) i
  have hpf : projectState r3 finish z = LeafStatisticsProgram.Finalize.state (z.regs ∘ r3)
      rows.length (totals rows forward).uncovered (LeafStatisticsProgram.Arity.arity forward rows 0) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i
      · exact (hzframe 613 (Or.inl (by decide))).trans (hsvalue 1)
      · exact (hzframe 629 (Or.inl (by decide))).trans (hsvalue 17)
      · exact hzvalue 9
  obtain ⟨nf,hnf,rf,hf⟩ := finishCall_eval z rows.length (totals rows forward).uncovered
    (LeafStatisticsProgram.Arity.arity forward rows 0) hpf
  let fsmall := LeafStatisticsProgram.Finalize.state rf
    (rows.length+(totals rows forward).uncovered) 0 (completedArity rows forward)
  let f := embedState r3 finish z fsmall
  have hfframe (i : Fin 768) (hi : i≠613 ∧ i≠629 ∧ i≠642) : f.stacks i=z.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩; fin_cases j <;> simp [finish] at hj <;> simp_all
  have hfvalue (i : Fin 3) : f.stacks (finish i)=fsmall.stacks i :=
    embedState_stack r3 finish z fsmall finish_injective i
  refine ⟨copiesCost statsCopies a+(ns+(copiesCost arityCopies s+(3+(na+nf)))),f,?_,?_,?_,?_⟩
  · simpa [measureCommand,sequence,f,fsmall,completedArity] using
      hc.seq (hs.seq (hd.seq (hregs.seq (ha.seq (hf.seq (Eval.base (.skip _)))))))
  · refine ⟨?_,?_,?_,hfvalue 0,hfvalue 2⟩
    · exact (hfframe 626 (by decide)).trans ((hzframe 626 (Or.inl (by decide))).trans (hsvalue 14))
    · exact (hfframe 627 (by decide)).trans ((hzframe 627 (Or.inl (by decide))).trans (hsvalue 15))
    · exact (hfframe 628 (by decide)).trans ((hzframe 628 (Or.inl (by decide))).trans (hsvalue 16))
  · have hcc : copiesCost arityCopies s=7*forward.length+5+7*(LeafStatisticsProgram.scopeBits rows).length+5 := by
      simp [copiesCost,arityCopies,copied_stack,hs719,hs718]
      omega
    rw [hcc]
    dsimp [measureBudget]
    omega
  · intro i hi
    have hi' : i≠613 ∧ i≠629 ∧ i≠642 := by refine ⟨?_,?_,?_⟩ <;> intro he <;> subst i <;> norm_num at hi
    exact (hfframe i hi').trans ((hzframe i (by omega)).trans (hsframe i (by omega)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval_oai
