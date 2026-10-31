-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.accepted_command_front_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:08:34.498561+00:00
-- url     : https://prove2.me/submissions/2c46d415-501c-496a-9fba-0bd30c8137cb

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

theorem noMarkInput_eval (a : Data) : Eval noMarkInput 3 a (unmarkedInput a) :=
  .base (SubexpParameterProgram.atoms_eval _ a)

theorem unmarkedInput_index (a : Data) (h705 : a.stacks 705=[]) :
    (unmarkedInput a).stacks 705=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705]

theorem unmarkedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (unmarkedInput a).stacks 706=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h706]

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

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

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryAccepted
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The accepted (unmarked) query uses the same immutable source masters and
explicitly writes the two false singleton fields consumed by the frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem accepted_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark=none) (hi : q.index=[false]) :
    q.Ready (unmarkedInput a) := by
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 700 (by decide) (by decide)).trans hs.formula
  · exact (unmarkedInput_frame a 701 (by decide) (by decide)).trans hs.rows
  · rw [hi]
    exact unmarkedInput_index a e705
  · simpa only [hm,Option.isSome_none] using unmarkedInput_flag a e706
  · exact (unmarkedInput_frame a 707 (by decide) (by decide)).trans hs.modulus
  · exact (unmarkedInput_frame a 708 (by decide) (by decide)).trans hs.width
  · exact (unmarkedInput_frame a 709 (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    rw [unmarkedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (unmarkedInput_frame a 338 (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (unmarkedInput_frame a 718 (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (unmarkedInput_frame a 719 (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

theorem accepted_outputs_empty (a : Data) (hc : CleanWork a) :
    LeafParametersProgram.Exports.OutputEmpty (unmarkedInput a) ∧
      (unmarkedInput a).stacks 704=[] ∧ (unmarkedInput a).stacks 134=[] ∧
      (unmarkedInput a).stacks 141=[] := by
  constructor
  · intro i
    have hne : ¬Protected (LeafParametersProgram.Exports.destination i) := by fin_cases i <;> decide
    have h321 : LeafParametersProgram.Exports.destination i≠321 := by fin_cases i <;> decide
    rw [unmarkedInput_frame a _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hc _ hne h321
  · refine ⟨?_,?_,?_⟩
    · exact (unmarkedInput_frame a 704 (by decide) (by decide)).trans
        (hc 704 (by decide) (by decide))
    · exact (unmarkedInput_frame a 134 (by decide) (by decide)).trans
        (hc 134 (by decide) (by decide))
    · exact (unmarkedInput_frame a 141 (by decide) (by decide)).trans
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

 theorem accepted_packingSpare (a : Data) (hs : PackingSpare a) : PackingSpare (unmarkedInput a) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 684 (by decide) (by decide)).trans hs.1
  · exact (unmarkedInput_frame a 133 (by decide) (by decide)).trans hs.2.1
  · exact (unmarkedInput_frame a 135 (by decide) (by decide)).trans hs.2.2.1
  · exact (unmarkedInput_frame a 136 (by decide) (by decide)).trans hs.2.2.2.1
  · intro i
    exact (unmarkedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)).trans (hs.2.2.2.2 i)

theorem accepted_entry (q : LeafQueryFrontend.Query) (a : Data) (hc : CleanWork a)
    (hs : Sources q a) (hm : q.mark=none) (hindex : q.index=[false]) :
    Eval noMarkInput 3 a (unmarkedInput a) ∧
    q.Ready (unmarkedInput a) ∧ q.OutputEmpty (unmarkedInput a) ∧ PackingSpare (unmarkedInput a) := by
  exact ⟨noMarkInput_eval a,accepted_ready q a hc hs hm hindex,
    accepted_outputs_empty a hc,accepted_packingSpare a (cleanWork_packingSpare a hc)⟩

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

/-- The unmarked final query has the same fully computed physical packing
input, with its base after actual false-flag staging. -/
theorem accepted_command_front_state_oai (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) (he : Eval (acceptedCommand k) steps a b) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.unmarkedInput (project a)) (project b) l w := by
  obtain ⟨hmark,hready,hempty,hspare⟩ :=
    LeafProgram.Query.accepted_entry q (project a) hc hs hm hindex
  obtain ⟨nf,bf,l,w,hfront,_,hf⟩ := LeafProgram.Query.front_state q k
    (LeafProgram.Query.unmarkedInput (project a)) hv hready hempty hspare
  have hwhole : Eval (acceptedLocalCommand k) (3 + nf) (project a) bf := by
    unfold acceptedLocalCommand
    exact hmark.seq hfront
  have htcompiled : Trace (compiled (acceptedLocalCommand k) 700 338) (3 + nf + 1)
      ((project a).withPC (some (compiled (acceptedLocalCommand k) 700 338).entry))
      (bf.withPC none) :=
    compiled_halt_trace hwhole 700 338
  have htlocal : Trace (acceptedLocalProgram k) (3 + nf + 1)
      ((project a).withPC (some (acceptedLocalProgram k).entry)) (bf.withPC none) := by
    simpa only [acceptedLocalProgram] using htcompiled
  have hev : Eval (acceptedCommand k) _ a (result a bf) :=
    eval_call_from_state (acceptedLocalProgram k) id stackMap a
      Function.injective_id (Fin.castAdd_injective _ _) htlocal
  have hb := SubexpPrimeProgram.eval_result_unique he hev 700 338
  refine ⟨l,w,?_⟩
  rw [hb,project_result]
  exact hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.accepted_command_front_state_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.accepted_command_front_state_oai
