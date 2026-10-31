-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_front_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:10:54.842996+00:00
-- url     : https://prove2.me/submissions/eec61feb-c346-4bc6-9f1b-508a3b99aaa2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Query_front_state

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem cleanWork_packingSpare (a : Data) (hc : CleanWork a) : PackingSpare a := by
  refine ⟨hc _ (by decide) (by decide),hc _ (by decide) (by decide),
    hc _ (by decide) (by decide),hc _ (by decide) (by decide),?_⟩
  intro i
  apply hc
  · intro h
    have hi := i.isLt
    simp [Protected,LayoutMasters.high,Fin.ext_iff] at h
    omega
  · intro h
    have hi := congrArg Fin.val h
    simp [LayoutMasters.high] at hi
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

 theorem marked_packingSpare (a : Data) (hs : PackingSpare a) : PackingSpare (markedInput a) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (markedInput_frame a 684 (by decide) (by decide) (by decide)).trans hs.1
  · exact (markedInput_frame a 133 (by decide) (by decide) (by decide)).trans hs.2.1
  · exact (markedInput_frame a 135 (by decide) (by decide) (by decide)).trans hs.2.2.1
  · exact (markedInput_frame a 136 (by decide) (by decide) (by decide)).trans hs.2.2.2.1
  · intro i
    exact (markedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)).trans (hs.2.2.2.2 i)

/-- Entry facts come from the reusable blank workspace and immutable sources;
no prepared scope or ring cache is supplied to the marked callback. -/
theorem marked_entry (q : LeafQueryFrontend.Query) (a : Data) (hc : CleanWork a)
    (hs : Sources q a) (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse) :
    Eval markInput (10*(a.stacks 321).length+10) a (markedInput a) ∧
    q.Ready (markedInput a) ∧ q.OutputEmpty (markedInput a) ∧ PackingSpare (markedInput a) := by
  exact ⟨markInput_eval a (hc _ (by decide) (by decide)) (hc _ (by decide) (by decide)),
    marked_ready q a hc hs hm href,marked_outputs_empty a hc,
    marked_packingSpare a (cleanWork_packingSpare a hc)⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete physical preparation facts derived from the actual marked and
unmarked frontend command outputs. No precomputed FrontState is supplied. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls SqrtLog

/-- The exact native output has every packing-stage field, including spare
words and canonical parameter lengths. Its base is after reference staging. -/
theorem command_front_state_oai (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) (he : Eval (command k) steps a b) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.markedInput (project a)) (project b) l w := by
  obtain ⟨hmark,hready,hempty,hspare⟩ :=
    LeafProgram.Query.marked_entry q (project a) hc hs hm href
  obtain ⟨nf,bf,l,w,hfront,_,hf⟩ := LeafProgram.Query.front_state q k
    (LeafProgram.Query.markedInput (project a)) hv hready hempty hspare
  have hwhole : Eval (LeafProgram.Query.markedFrontend k)
      (10 * ((project a).stacks 321).length + 10 + nf) (project a) bf := by
    unfold LeafProgram.Query.markedFrontend
    exact hmark.seq hfront
  have htcompiled : Trace (compiled (LeafProgram.Query.markedFrontend k) 321 338)
      (10 * ((project a).stacks 321).length + 10 + nf + 1)
      ((project a).withPC (some (compiled (LeafProgram.Query.markedFrontend k) 321 338).entry))
      (bf.withPC none) :=
    compiled_halt_trace hwhole 321 338
  have htlocal : Trace (localProgram k) (10 * ((project a).stacks 321).length + 10 + nf + 1)
      ((project a).withPC (some (localProgram k).entry)) (bf.withPC none) := by
    simpa only [localProgram] using htcompiled
  have hev : Eval (command k) _ a (result a bf) :=
    eval_call_from_state (localProgram k) id stackMap a
      Function.injective_id (Fin.castAdd_injective _ _) htlocal
  have hb := SubexpPrimeProgram.eval_result_unique he hev 321 338
  refine ⟨l,w,?_⟩
  rw [hb,project_result]
  exact hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_front_state_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_front_state_oai
