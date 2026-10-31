-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:59:00.489663+00:00
-- url     : https://prove2.me/submissions/4e12e645-d25b-4769-94b0-5de26f49afa5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_Prepare_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_earlyCall_eval_bounded
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_maskCall_eval

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

theorem mask_injective : Function.Injective mask := by decide

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

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

theorem highCall_eval (a : Data) (rows : List (List ℕ)) (ambient tau : List Bool)
    (hn : 0 < BinaryArithmetic.toNat ambient)
    (hp : projectState r10 high a = HighIncidenceProgram.Prepare.initial (a.regs ∘ r10) rows ambient tau) :
    ∃ n ≤ HighIncidenceProgram.Prepare.budget rows ambient tau+1, ∃ b,
      Eval highCall n a (embedState r10 high a b) ∧
      b.stacks 14 = HighIncidenceProgram.highPrefix rows
        (HighIncidenceProgram.Prepare.cut rows ambient tau) (BinaryArithmetic.toNat ambient) ∧
      b.stacks 0 = LeafStatisticsProgram.scopeBits rows ∧
      b.stacks 16 = ambient ∧ b.stacks 17 = tau := by
  obtain ⟨n,b,he,hb,h0,h16,h17,h14,_⟩ := HighIncidenceProgram.Prepare.command_eval
    (a.regs ∘ r10) rows ambient tau hn
  have ht := compiled_halt_trace he 0 14
  rw [←hp] at ht
  have hrun := eval_call_from_state HighIncidenceProgram.Prepare.program r10 high a
    (registers_injective ..) (block_injective ..) ht
  exact ⟨n+1,by omega,b,hrun,h14,h0,h16,h17⟩

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendHighBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The high mask is computed from the original ambient count and actual scope
mass. The forward mask is a paid copy/reversal of that same output. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


set_option maxHeartbeats 3200000 in
theorem highCommand_eval_bounded_oai (a : Data) (rows : List (List ℕ)) (ambient : List Bool)
    (ha : a.stacks 709=ambient) (hn : 0 < BinaryArithmetic.toNat ambient)
    (hr : a.stacks 718=LeafStatisticsProgram.scopeBits rows)
    (he : emptyRange a 417 494) (hh : emptyRange a 580 612)
    (ht : a.stacks 679=[]) (h338 : a.stacks 338=[])
    (h719 : a.stacks 719=[]) (h645 : a.stacks 645=[]) (h646 : a.stacks 646=[]) :
    ∃ n b tau, Eval highCommand n a b ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
      b.stacks 338=highMask rows (BinaryArithmetic.toNat ambient) ∧
      b.stacks 719=(highMask rows (BinaryArithmetic.toNat ambient)).reverse ∧
      n ≤ 7*ambient.length+5+EarlyThreshold.runtimeBound ambient+
        (7*(LeafStatisticsProgram.scopeBits rows).length+5+7*ambient.length+5+7*tau.length+5)+
        HighIncidenceProgram.Prepare.budget rows ambient tau+1+
        17*(highMask rows (BinaryArithmetic.toNat ambient)).length+14 ∧
      (∀ i : Fin 768, (i.val < 417 ∨ 494 ≤ i.val) → (i.val < 580 ∨ 612 ≤ i.val) →
        i≠338 → i≠719 → i≠645 → i≠646 → b.stacks i=a.stacks i) ∧
      tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1 := by
  have hc := copy_eval a 709 417 ⟨by decide,by decide,by decide,ht⟩
  let c := copied a 709 417
  have hpe : projectState r8 early c = LeafParametersProgram.Bank.state (c.regs ∘ r8)
      (EarlyThreshold.inputWords ambient) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      have hi := he (early i) (by dsimp [early,block]; omega) (by dsimp [early,block]; omega)
      have hz := he 417 (by decide) (by decide)
      fin_cases i <;> simp_all [c,copied_stack,early,block,
EarlyThreshold.inputWords]
  obtain ⟨ne,hne,re,we,hee,htau,he0,hez,htlen⟩ := earlyCall_eval_bounded c ambient hpe
  let esmall := LeafParametersProgram.Bank.state re we
  let e := embedState r8 early c esmall
  have heframe (i : Fin 768) (hi : i.val < 417 ∨ 494 ≤ i.val) : e.stacks i=a.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) c esmall i hi
    have h417 : i≠417 := by intro h; subst i; omega
    exact h.trans (by simp [c,copied_stack,h417])
  have he709 : e.stacks 709=ambient := (heframe 709 (Or.inr (by decide))).trans ha
  have he718 : e.stacks 718=LeafStatisticsProgram.scopeBits rows := (heframe 718 (Or.inr (by decide))).trans hr
  have he679 : e.stacks 679=[] := (heframe 679 (Or.inr (by decide))).trans ht
  have he433 : e.stacks 433=we 16 := embedState_stack r8 early c esmall (block_injective ..) 16
  let d := copiesState highCopies e
  have hd := copies_eval highCopies e (copies_ready_of_clean _ _ (by simp [highCopies]) he679)
  have hph : projectState r10 high d = HighIncidenceProgram.Prepare.initial (d.regs ∘ r10) rows ambient (we 16) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      have hei := heframe (high i) (Or.inr (by dsimp [high,block]; omega))
      have hhi := hh (high i) (by dsimp [high,block]; omega) (by dsimp [high,block]; omega)
      have h580 := (heframe 580 (Or.inr (by decide))).trans (hh 580 (by decide) (by decide))
      have h596 := (heframe 596 (Or.inr (by decide))).trans (hh 596 (by decide) (by decide))
      have h597 := (heframe 597 (Or.inr (by decide))).trans (hh 597 (by decide) (by decide))
      fin_cases i <;> simp_all [projectState,d,copiesState,highCopies,copied_stack,
        high,block]
  obtain ⟨nh,hnh,hs,hhe,hmask,hs0,hs16,hs17⟩ := highCall_eval d rows ambient (we 16) hn hph
  let z := embedState r10 high d hs
  have hzframe (i : Fin 768) (hi : i.val < 580 ∨ 612 ≤ i.val) : z.stacks i=e.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) d hs i hi
    exact h.trans (copies_frame highCopies e i (by
      intro x hx; simp only [highCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> intro he <;> subst i <;> norm_num at hi))
  have hz594 : z.stacks 594=highMask rows (BinaryArithmetic.toNat ambient) := by
    have h := embedState_stack r10 high d hs (block_injective ..) 14
    exact h.trans (by simpa [HighIncidenceProgram.Prepare.cut,highMask,htau] using hmask)
  have hz679 : z.stacks 679=[] := (hzframe 679 (Or.inr (by decide))).trans he679
  have hcopy := copy_eval z 594 338 ⟨by decide,by decide,by decide,hz679⟩
  let p := copied z 594 338
  have hpframe (i : Fin 768) (hi : i≠338) (he : i.val < 417 ∨ 494 ≤ i.val)
      (hh : i.val < 580 ∨ 612 ≤ i.val) : p.stacks i=a.stacks i := by
    simp only [p,copied_stack,ite_eq_right hi]
    exact (hzframe i hh).trans (heframe i he)
  have hz338 : z.stacks 338=[] := ((hzframe 338 (Or.inl (by decide))).trans
    (heframe 338 (Or.inl (by decide)))).trans h338
  have hp338 : p.stacks 338=highMask rows (BinaryArithmetic.toNat ambient) := by simp [p,copied_stack,hz338,hz594]
  have hpm : projectState r2 mask p = HighIncidenceProgram.Mask.state (p.regs ∘ r2)
      (highMask rows (BinaryArithmetic.toNat ambient)) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i
      · exact hp338
      · exact (hpframe 645 (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans h645
      · exact (hpframe 719 (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans h719
      · exact (hpframe 646 (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans h646
  obtain ⟨nm,hnm,rm,hm⟩ := maskCall_eval p (highMask rows (BinaryArithmetic.toNat ambient)) hpm
  let msmall := HighIncidenceProgram.Mask.state rm (highMask rows (BinaryArithmetic.toNat ambient)) []
    (highMask rows (BinaryArithmetic.toNat ambient)).reverse []
  let f := embedState r2 mask p msmall
  refine ⟨7*(a.stacks 709).length+5+(ne+(copiesCost highCopies e+(nh+(7*(z.stacks 594).length+5+nm)))),
    f,we 16,?_,htau,?_,?_,?_,?_,htlen⟩
  · simpa [highCommand,sequence] using hc.seq (hee.seq (hd.seq (hhe.seq (hcopy.seq (hm.seq (Eval.base (.skip _)))))))
  · exact embedState_stack r2 mask p msmall mask_injective 0
  · exact embedState_stack r2 mask p msmall mask_injective 2
  · have hcost : copiesCost highCopies e=7*(LeafStatisticsProgram.scopeBits rows).length+5+7*ambient.length+5+7*(we 16).length+5 := by
      simp [copiesCost,highCopies,copied_stack,he718,he709,he433]
      omega
    rw [ha,hz594,hcost]
    omega
  · intro i hei hhi h338 h719 h645 h646
    have hf : f.stacks i=p.stacks i := by
      apply embedState_stack_frame
      rintro ⟨j,hj⟩; fin_cases j <;> simp [mask] at hj <;> simp_all
    exact hf.trans (hpframe i h338 hei hhi)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded_oai
