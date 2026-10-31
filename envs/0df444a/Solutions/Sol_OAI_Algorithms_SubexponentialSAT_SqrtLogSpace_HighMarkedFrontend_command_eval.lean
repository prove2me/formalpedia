-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:08:35.637905+00:00
-- url     : https://prove2.me/submissions/1b9967b9-ac9e-4e67-8a04-68ec11beef02

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval_input_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPrimeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

private theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => rfl
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have haa : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          exact congrArg Nat.succ (ih ht' hb hc)

/-- The exact instruction count of a terminating structured execution is
unique as well as its result. This allows proved execution bounds to be used
for every actual occurrence of a subroutine in a larger trace. -/
theorem eval_steps_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : n = m := by
  have h := terminal_trace_steps_unique
    (StructuredCalls.compiled_halt_trace h₁ input output)
    (StructuredCalls.compiled_halt_trace h₂ input output) rfl rfl
  omega

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem markedFlag_eval (a : Data) : Eval markedFlag 2 a (flagged a) :=
  .base (SubexpParameterProgram.atoms_eval _ a)

theorem markInput_eval (a : Data) (h698 : a.stacks 698=[]) (h699 : a.stacks 699=[]) :
    Eval markInput (10*(a.stacks 321).length+10) a (markedInput a) := by
  have hc := copy_eval a 321 699 698 0 1 (by decide) (by decide) (by decide) (by decide) h698
  have ht := transfer_eval (afterCopy a 321 699 0 1) 699 705 0 1 (by decide) (by decide)
  have hf := markedFlag_eval (afterTransfer (afterCopy a 321 699 0 1) 699 705 0 1)
  have hl : ((afterCopy a 321 699 0 1).stacks 699).length=(a.stacks 321).length := by
    simp [afterCopy,StackRoutines.copyStacks,h699]
  rw [hl] at ht
  convert hc.seq (ht.seq hf) using 1 <;> first | rfl | omega

theorem markedInput_index (a : Data) (h699 : a.stacks 699=[]) (h705 : a.stacks 705=[]) :
    (markedInput a).stacks 705=(a.stacks 321).reverse := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h699,h705]

theorem markedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (markedInput a).stacks 706=[true] := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h706]

theorem markedInput_frame (a : Data) (i : Fin 768)
    (hi : i≠699) (h705 : i≠705) (h706 : i≠706) :
    (markedInput a).stacks i=a.stacks i := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,hi,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem cleanWork_private (a : Data) (h : CleanWork a) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) : a.stacks i=[] := by
  apply h
  · intro hp
    simp only [Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    norm_num at hp
    omega
  · intro hi
    subst i
    norm_num at hlo

theorem marked_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) : q.Ready (markedInput a) := by
  have e699 := hc 699 (by decide) (by decide)
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (markedInput_frame a 700 (by decide) (by decide) (by decide)).trans hs.formula
  · exact (markedInput_frame a 701 (by decide) (by decide) (by decide)).trans hs.rows
  · simpa only [href,List.reverse_reverse] using markedInput_index a e699 e705
  · simpa only [hm] using markedInput_flag a e706
  · exact (markedInput_frame a 707 (by decide) (by decide) (by decide)).trans hs.modulus
  · exact (markedInput_frame a 708 (by decide) (by decide) (by decide)).trans hs.width
  · exact (markedInput_frame a 709 (by decide) (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    have hn (x : ℕ) (hx : 680 ≤ x) : i.val≠x := by omega
    rw [markedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (markedInput_frame a 338 (by decide) (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (markedInput_frame a 718 (by decide) (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (markedInput_frame a 719 (by decide) (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

theorem marked_outputs_empty (a : Data) (hc : CleanWork a) :
    LeafParametersProgram.Exports.OutputEmpty (markedInput a) ∧
      (markedInput a).stacks 704=[] ∧ (markedInput a).stacks 134=[] ∧
      (markedInput a).stacks 141=[] := by
  constructor
  · intro i
    have hne : ¬Protected (LeafParametersProgram.Exports.destination i) := by fin_cases i <;> decide
    have h321 : LeafParametersProgram.Exports.destination i≠321 := by fin_cases i <;> decide
    rw [markedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hc _ hne h321
  · refine ⟨?_,?_,?_⟩
    · exact (markedInput_frame a 704 (by decide) (by decide) (by decide)).trans
        (hc 704 (by decide) (by decide))
    · exact (markedInput_frame a 134 (by decide) (by decide) (by decide)).trans
        (hc 134 (by decide) (by decide))
    · exact (markedInput_frame a 141 (by decide) (by decide) (by decide)).trans
        (hc 141 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native frontend entry from an actual marked-reference reader state. All
computed-size witnesses remain explicit in the paid budget. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem marked_frontend_eval (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : CleanWork a) (hs : Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse) :
    ∃ n b counted prepared beforeClean tau l w,
      Eval (markedFrontend k) n a b ∧
      n ≤ 10*(a.stacks 321).length+10+
        LeafQueryFrontend.frontendBudget q k counted prepared beforeClean tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=
        2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^
          (2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  have hready := marked_ready q a hc hs hm href
  have hempty : q.OutputEmpty (markedInput a) := marked_outputs_empty a hc
  obtain ⟨nf,b,counted,prepared,beforeClean,tau,l,w,he,hn,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k (markedInput a) hv hready hempty
  have hmark := markInput_eval a (hc 698 (by decide) (by decide))
    (hc 699 (by decide) (by decide))
  refine ⟨10*(a.stacks 321).length+10+nf,b,counted,prepared,beforeClean,tau,l,w,
    hmark.seq he,by omega,ht,h704,h718,h338,h719,h134,hex,h141,hbank,hshape,hguard,hclean,?_⟩
  intro i hi h134 h141 h338 h704 h718 h719 h705 h706 h699 hd
  exact (hframe i hi h134 h141 h338 h704 h718 h719 hd).trans
    (markedInput_frame a i h699 h705 h706)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

private theorem marked_time_le (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : LeafProgram.Query.Data) (n : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork a) (hs : LeafProgram.Query.Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse)
    (he : Eval (LeafProgram.Query.markedFrontend k) n a b) : n+2 ≤ budget q k := by
  have hready := LeafProgram.Query.marked_ready q a hc hs hm href
  have hempty := LeafProgram.Query.marked_outputs_empty a hc
  obtain ⟨nf,bf,hfront,hbound⟩ := LeafQueryFrontend.frontend_eval_input_bound q k
    (LeafProgram.Query.markedInput a) hv hready hempty
  have hmark := LeafProgram.Query.markInput_eval a (hc 698 (by decide) (by decide))
    (hc 699 (by decide) (by decide))
  have hother := hmark.seq hfront
  have htime := SubexpPrimeProgram.eval_steps_unique he hother 321 338
  rw [href,List.length_reverse] at htime
  dsimp [budget]
  omega

/-- Actual marked frontend execution and input-dependent time do not require
a bound on suspended collector or caller words. -/
theorem command_eval_oai (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) :
    ∃ steps b tau l w,
      Eval (command k) steps a (result a b) ∧
      steps+1 ≤ budget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) := by
  have href' : (project a).stacks 321=q.index.reverse := href
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafProgram.Query.marked_frontend_eval q k (project a) hv hc hs hm href'
  have hn := marked_time_le q k (project a) b n hv hc hs hm href' he
  have htlocal : Trace (localProgram k) (n+1)
      ((project a).withPC (some (localProgram k).entry)) (b.withPC none) :=
    compiled_halt_trace he 321 338
  have hev := eval_call_from_state (localProgram k) id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) htlocal
  exact ⟨n+1,b,tau,l,w,hev,by omega,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval_oai
