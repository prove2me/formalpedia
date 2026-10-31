-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:35:36.533924+00:00
-- url     : https://prove2.me/submissions/1e2dfaaa-57bb-468c-b8b5-c6d2a2765816

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S021
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S038
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S077
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S146
import Definitions.Def_OAIQ081S151
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S171
import Definitions.Def_OAIQ081S172
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S182
import Definitions.Def_OAIQ081S183
import Definitions.Def_OAIQ081S185
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCorrect_marked
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryReturnReplay_marked

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

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

/-- Visible words retain their complete bit strings. -/
theorem visible (a : Data) (i : Fin 896) (hi : i ∉ HighQueryProgram.Carried.words) :
    (erase a).stacks i = a.stacks i :=
  rebaseStacks_of_not_mem (fun j => j ∈ HighQueryProgram.Carried.words)
    (fun _ => []) a.stacks i hi

/-- Erasure preserves an existing blank, whether or not the word is carried. -/
theorem blank (a : Data) (i : Fin 896) (hi : a.stacks i = []) :
    (erase a).stacks i = [] := by
  by_cases hm : i ∈ HighQueryProgram.Carried.words
  · exact rebaseStacks_of_mem (fun j => j ∈ HighQueryProgram.Carried.words)
      (fun _ => []) a.stacks i hm
  · exact (visible a i hm).trans hi

/-- The actual lower-bank clean-work predicate needs only its existing blanks. -/
theorem cleanWork (a : Data)
    (hc : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)) :
    LeafProgram.Query.CleanWork (HighMarkedFrontend.project (erase a)) := by
  intro i hi h321
  exact blank a (HighMarkedFrontend.stackMap i) (hc i hi h321)

/-- All five immutable frontend source fields are visible to the shadow. -/
theorem sources (q : LeafQueryFrontend.Query) (a : Data)
    (hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)) :
    LeafProgram.Query.Sources q (HighMarkedFrontend.project (erase a)) := by
  constructor
  · exact (visible a 700 (by decide)).trans hs.formula
  · exact (visible a 701 (by decide)).trans hs.rows
  · exact (visible a 707 (by decide)).trans hs.modulus
  · exact (visible a 708 (by decide)).trans hs.width
  · exact (visible a 709 (by decide)).trans hs.ambient

theorem reference (q : LeafQueryFrontend.Query) (a : Data)
    (href : a.stacks 321 = q.index.reverse) :
    (erase a).stacks 321 = q.index.reverse :=
  (visible a 321 (by decide)).trans href

theorem scratch (a : Data) (htmp : a.stacks 767 = []) :
    (erase a).stacks 767 = [] := blank a 767 htmp

/-- The marked return restores workspace outside the five collector ports.
In particular the actual reference321 is not required to be blank. -/
theorem marked_discarded (a : Data)
    (hd : ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → a.stacks i = []) :
    ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → (erase a).stacks i = [] :=
  fun i hi hout => blank a i (hd i hi hout)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQueries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Literal marked and accepted query continuations for the actual prepared
leaf. Shadow execution preserves unrestricted caller words for time; the
same replay counts those words separately in maximum prefix storage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

/-- The actual setup prefix cap bounds its seeded endpoint independently of
its duration. No high-loop cost enters this boundary allowance. -/
theorem seeded_bound {q k input command marker budget S B Cp dp timeCap spaceCap}
    (run : NativeHashQuerySetup.SetupRun q k input command marker budget S B Cp dp timeCap spaceCap) :
    ∀ i, ((HighCountSeed.initialized (HighMarkedFrontend.result run.front run.prepared.output)
      run.prepared.seedRegs).stacks i).length ≤ max spaceCap B := by
  intro i
  exact run.space.bound _ _ (Nat.le_refl _)
    (compiled_halt_trace run.eval 778 777) i

/-- The actual scalar producer stores the field cardinality minus two on44.
Its numeric cap therefore bounds the search field cardinality polynomially. -/
theorem field_card_bound (q : LeafQueryFrontend.Query) (k S : ℕ)
    (padding : Fin 8 → ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (hv : ∀ j, (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
      (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S) :
    3 ^ ((LeafParametersProgram.Execute.guardedModel (q.input k) padding).val 34) ≤ S + 2 := by
  have h := hv 44
  rw [Query.ring_exponent _ _ hg] at h
  omega


open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources


section Replay

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : State 40 896}
  {frontBudget S Cp dp timeCap A : ℕ}

local notation "erased" => HighQueryEntryShadow.erase input

/-- Every erased word is counted in the bounded actual shadow input. -/
theorem shadow_input_bound
    {command : Cmd 40 896} {marker : State 40 768}
    (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) command marker frontBudget S 0
      Cp dp timeCap A) : ∀ i, ((erased).stacks i).length ≤ S := by
  intro i
  by_cases hi : i ∈ HighQueryProgram.Carried.words
  · simp [HighQueryEntryShadow.erase, ProgramTapeReplay.rebaseState,
      ProgramTapeReplay.rebaseStacks, hi]
  · exact run.input_visible i hi

variable (run : NativeHashQuerySetup.SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
  (Query.markedInput (project (HighQueryEntryShadow.erase input))) frontBudget S 0 Cp dp timeCap A)
  (RB RI frontCost frameBound : ℕ) (staged : State 40 896)
  (entry : MarkedEntry q staged input)
  (hindex : q.index = Encoding.encodeNat (PreparedSource.markIndex q))
  (source : RawCNF (BinaryArithmetic.toNat q.ambient))
  (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause ∈ source, clause.length ≤ k)
  (hvalues : ∀ j,
    (Circuit.result Serialization.code (Execute.guardedModel (q.input k) run.padding)).val j ≤ S ∧
    (Execute.guardedModel (q.input k) run.padding).val j ≤ S)
  (hSA : S ≤ A) (hfront : frontBudget ≤ frontCost)
  (hblank : ∀ i, HashMarkedReturn.kept i = false → (i.val < 320 ∨ 324 < i.val) →
    input.stacks i = [])
  (hhidden : ∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound)

local notation "model" => Execute.guardedModel (q.input k) run.padding
local notation "work" => CostAssembly.assembledWork k (ambient q)
  (ofPacking q k RB 1 1 RI 1 run.guard run.prepared.first run.prepared.rest)
local notation "highCost" => HighQueryCorrect.loopBudget (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A (A+S+2) work
local notation "highSpace" => HighQueryCorrect.loopSpace (BinaryArithmetic.toNat q.ambient)
  (Finset.card (highSet q)) (Circuit.Model.val model 33) (Circuit.Model.val model 34) (Circuit.Model.val model 42) A (A+S+2)

include entry hindex hwidth hvalues hSA hfront hblank hhidden in
/-- Actual complete marked execution followed by its same-step opaque-word
replay. The runtime has no suspended-word allowance; all prefixes count it. -/
theorem marked_replay_oai :
    ∃ steps output,
      Eval (HighQueryProgram.marked k) steps input output ∧
      steps+1 ≤ HighQueryCorrect.markedBudget frontCost (S+frontBudget)
        (Cp*(S+frontBudget+1)^dp) highCost (QueryHeadBudgets.compact A) ∧
      output.stacks 323 = countWord (literalCount q source hsource) ∧
      HashMassAdapter.workspace output = HashMassAdapter.workspace input ∧
      HashMassAdapter.read output = HashMassAdapter.read input ∧
      RecordPrograms.state HashMassAdapter.recordPorts output false true false
        (input.stacks 320) [] = output ∧ output.stacks 324 = [] ∧
      StageSpace (HighQueryProgram.marked k) (steps+1) input
        (max (HighQueryCorrect.space q S frontCost (S+frontBudget) 0
          (Cp*(S+frontBudget+1)^dp) highSpace (QueryHeadBudgets.compact A)) frameBound) := by
  have hr := Query.marked_ready q (project erased)
    (HighQueryEntryShadow.cleanWork input entry.clean)
    (HighQueryEntryShadow.sources q input entry.sources) entry.marked
    (HighQueryEntryShadow.reference q input entry.index)
  have hw : ∀ i, ((HighCountSeed.initialized (result run.front run.prepared.output)
      run.prepared.seedRegs).stacks i).length ≤ A := by
    simpa only [Nat.max_zero] using seeded_bound run
  have hqsize : 3^(Circuit.Model.val model 34) ≤ A+S+2 :=
    (field_card_bound q k S run.padding run.guard (fun j => (hvalues j).1)).trans (by omega)
  have hfrontendCost : run.frontendSteps ≤ frontCost := by
    change run.data.frontendSteps ≤ frontCost
    have htime : run.data.frontendSteps + 1 ≤ frontBudget := run.frontend_time
    omega
  obtain ⟨steps,output,he,ht,hcount,hws,_hread,hrecord,h324,hs⟩ :=
    HighQueryCorrect.marked run.prepared RB 1 1 RI 1 entry.valid _ run.words
      run.frontend_state hr hindex source hsource hwidth A (A+S+2) hw
      (fun j => (hvalues j).2.trans hSA) (by omega) hqsize erased
      run.frontendSteps frontCost S run.frontend hfrontendCost
      (shadow_input_bound run) run.kept (HighQueryEntryShadow.marked_discarded input hblank)
      (HighQueryEntryShadow.scratch input entry.scratch)
  have hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false := by
    have h16 := congrArg (fun a : State 40 896 => a.regs 16) hrecord
    have h17 := congrArg (fun a : State 40 896 => a.regs 17) hrecord
    have h18 := congrArg (fun a : State 40 896 => a.regs 18) hrecord
    simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using
      And.intro h16.symm (And.intro h17.symm h18.symm)
  have h321 : output.stacks 321 = [] := by
    have h := congrArg (fun a : State 40 896 => a.stacks 321) hrecord
    simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using h.symm
  obtain ⟨her,hwr,hrr,hrec,hcr,hscr,hsr⟩ :=
    HighQueryReturnReplay.marked he hws hp h321 h324 hcount hs hhidden
  exact ⟨steps,_,her,ht,hcr,hwr,hrr,hrec,hscr,hsr⟩

end Replay


open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay_oai
