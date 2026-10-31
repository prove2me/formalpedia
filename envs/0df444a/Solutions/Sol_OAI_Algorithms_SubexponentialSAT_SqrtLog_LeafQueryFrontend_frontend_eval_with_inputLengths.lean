-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:57:32.940394+00:00
-- url     : https://prove2.me/submissions/048db0b4-8aa8-40e9-bb87-5879ceaab5a1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_coreCommand_eval_bounded
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_postCommand_eval

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

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem countPorts_injective : Function.Injective countPorts := by decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendHashCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem countHashes_eval (a : Data) (records : List (List Bool))
    (hi : a.stacks 701=Encoding.encodeList id records)
    (ho : a.stacks 704=[]) (h647 : a.stacks 647=[]) (h679 : a.stacks 679=[]) :
    ∃ b, Eval countHashes (SubexpScopeCountSetup.countBudget records) a b ∧
      b.stacks 704=List.replicate records.length true ∧
      (∀ i, i≠704 → b.stacks i=a.stacks i) := by
  have hc := copy_eval a 701 647 ⟨by decide,by decide,by decide,h679⟩
  let c := copied a 701 647
  have hp : projectState r2 countPorts c=SubexpScopeCountSetup.counterState (c.regs 0) (c.regs 1)
      (Encoding.encodeList id records) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [countPorts,c,copied_stack,hi,ho,h647,
ParserProgram.pair]
  have ht := SubexpScopeCountSetup.counter_trace records (c.regs 0) (c.regs 1)
  rw [←hp] at ht
  let small := SubexpScopeCountSetup.counterState false false [] (List.replicate records.length true)
  let b := embedState r2 countPorts c small
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram r2 countPorts c
    (registers_injective ..) countPorts_injective ht
  refine ⟨b,?_,?_,?_⟩
  · simpa [countHashes,sequence,SubexpScopeCountSetup.countBudget,hi] using
      hc.seq (he.seq (Eval.base (.skip _)))
  · exact embedState_stack r2 countPorts c small countPorts_injective 1
  · intro i h704
    by_cases h647i : i=647
    · subst i
      exact (embedState_stack r2 countPorts c small countPorts_injective 0).trans h647.symm
    · have hf := embedState_stack_frame r2 countPorts c small i (by
        rintro ⟨j,hj⟩; fin_cases j <;> simp [countPorts] at hj <;> simp_all)
      exact hf.trans (by simp [c,copied_stack,h647i])

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid persistent metadata export, offset construction, mask conversion, and
scratch cleanup after the guarded numeric bank has been computed. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


theorem export_destination_not_private (i : Fin 16) :
    (Exports.destination i).val < 340 ∨ 680 ≤ (Exports.destination i).val := by
  fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram

theorem bank_projection_eight (a : Data) (w : Bank.Words)
    (hp : projectState r9 bank a=Execute.state (a.regs ∘ r9) w) :
    projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  exact congrArg StructuredProgram.State.stacks hp

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendExact
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete native frontend output certificate with its input-only length
model retained. The existing command and endpoint API remain unchanged. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- All output, frame, guard, and measured-cost facts from `frontend_eval`, with
an additional equality fixing the length model to the physical input query. -/
theorem frontend_eval_with_inputLengths_oai (q : Query) (k : ℕ) (a : Data) (hv : q.Valid)
    (ha : q.Ready a) (ho : q.OutputEmpty a) :
    ∃ n b counted prepared beforeClean tau l w,
      Eval (frontend k) n a b ∧
      n ≤ frontendBudget q k counted prepared beforeClean tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=
        2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^
          (2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i) ∧
      l=q.inputLengths k := by
  obtain ⟨c,hec,hc704,cf⟩ := countHashes_eval a
    (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length)) ha.2.1 ho.2.1
    (ha.2.2.2.2.2.2.2.1 _ (by decide) (by decide))
    (ha.2.2.2.2.2.2.2.1 _ (by decide) (by decide))
  have hc : q.Ready c := by
    rcases ha with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
    refine ⟨(cf _ (by decide)).trans h700,(cf _ (by decide)).trans h701,
      (cf _ (by decide)).trans h705,(cf _ (by decide)).trans h706,
      (cf _ (by decide)).trans h707,(cf _ (by decide)).trans h708,
      (cf _ (by decide)).trans h709,?_,(cf _ (by decide)).trans h338,
      (cf _ (by decide)).trans h718,(cf _ (by decide)).trans h719⟩
    intro i hi hj
    exact (cf i (by intro he; subst i; norm_num at hj)).trans (hz i hi hj)
  obtain ⟨nc,u,tau,l,wu,heu,hnu,htau,hu718,hu338,hu719,hup,hus,hug,hue,huz,uf,htlen,hll⟩ :=
    coreCommand_eval_bounded q k c hv hc
  have uout : Exports.OutputEmpty u := by
    intro j
    have hd := export_destination_not_private j
    exact (uf _ hd (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)).trans ((cf _ (by fin_cases j <;> decide)).trans (ho.1 j))
  have u134 : u.stacks 134=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.1)
  have u141 : u.stacks 141=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.2)
  have hr : 0 < (Execute.guardedModel (q.input k) l).val 18 := by
    rw [Execute.guardedModel_radius]
    have := produce_r_ge_two (q.input k)
    omega
  have hz : ∀ j,46 ≤ j.val → (Execute.guardedModel (q.input k) l).val j=0 := by
    intro j hj
    simp [Execute.guardedModel,show ¬j.val < 44 by omega]
  obtain ⟨np,b,prepared,beforeClean,w,hep,hnp,hex,hval,h134,hp,hs,hgr,hz,fr⟩ :=
    postCommand_eval u (Execute.guardedModel (q.input k) l) wu hus
      (bank_projection_eight u wu hup) hr hz uout huz u134 u141
      (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) hu338
  have bf (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) (h134 : i≠134) (h141 : i≠141)
      (hd : ∀ j,Exports.destination j≠i) : b.stacks i=u.stacks i := fr i hi h134 h141 hd
  refine ⟨SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))+(nc+np),
    b,c,prepared,beforeClean,tau,l,w,hec.seq (heu.seq hep),?_,htau,?_,?_,?_,?_,h134,
    hex,hval,hp,hs,?_,hz,?_,hll⟩
  · unfold frontendBudget; omega
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans
      ((uf _ (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans (by simpa using hc704))
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu718
  · exact (bf _ (Or.inl (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu338
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu719
  · simpa only [hgr] using hug
  · intro i hi h134 h141 h338 h704 h718 h719 hd
    exact (bf i hi h134 h141 hd).trans ((uf i hi h338 h718 h719).trans (cf i h704))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths_oai
