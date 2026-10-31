-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:13:05.380171+00:00
-- url     : https://prove2.me/submissions/c120a232-a4b2-4d1d-9635-a9b44096e211

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
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCount_branch_kept_of_stream
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCount_branch_prepared_of_stream
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_branch_step_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryTraversal_high_loop_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem copiedHighCounter_frame (a : Data) (i : Fin 896) (h330 : i≠330) (h792 : i≠792) :
    (copiedHighCounter a).stacks i=a.stacks i := by simp [copiedHighCounter,h330,h792]

theorem copiedHighCounter_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((copiedHighCounter a).stacks i).length≤bound := by
  intro i
  by_cases h792 : i=792
  · subst i; simp [copiedHighCounter]
  · by_cases h330 : i=330
    · subst i; simpa using hb 789
    · simpa [copiedHighCounter,h330,h792] using hb i


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem parked_high (a : LocalData) (hz : ∀ i, a.stacks (high i) = []) (i : Fin 14) :
    (parked a).stacks (high i) = a.stacks (low i) := by
  have hout : high i ∉ lowPorts := by
    simp only [lowPorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j h
    have hv := congrArg Fin.val h
    change 128+j.val=730+i.val at hv
    omega
  rw [parked,clearMany_stacks,ite_eq_right hout]
  exact copyMany_value parkPairs a park_nodup
    (by intro p hp; simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨j,rfl⟩ := hp; exact hz j)
    park_sep (low i,high i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem finished_high (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (i : Fin 14) :
    (finished a).stacks (LeafProgram.LayoutMasters.high i)=
      (exported a).stacks (LeafProgram.LayoutMasters.low i) := by
  apply LeafProgram.LayoutMasters.parked_high
  intro j
  rw [exported_high,hz]

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

theorem compact_le (A : ℕ) : A+1 ≤ compactCap A := by
  unfold compactCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem frame (a : Data) (i : Fin 896) (hi : i∉changed) : (result a).stacks i=a.stacks i := by
  have hn : i≠789 := by intro h; subst i; exact hi (by decide)
  simp [result,copied,copyStacks,hn,reset_frame a i hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem result_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  have hn : ¬∃ j,stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i=(copied a).stacks i from
    embedState_stack_frame regMap stackMap (copied a) _ i hn]
  have h792 : i≠792 := by intro h; subst i; exact hi (by decide)
  simp [copied,copyStacks,h792,reset_frame a i hi]

theorem initialized_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∉([330,788,789,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=a.stacks i := by
  have hinit : i∉HighCountInit.changed := by simp only [HighCountInit.changed] ; simpa using
    (fun (h : i∈([788,789,790,323,791,792] : List (Fin 896))) => hi (List.mem_cons_of_mem _ h))
  have hseed : i∉changed := by
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  exact (HighCountInit.frame (result a rf) i hinit).trans (result_frame a rf i hseed)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem rankValue_at (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : Fin (2^H.card)) :
    rankValue H hashes marked clause r.val=NodeSemantics.ternaryFixedHighCount H
      (Rank.highEquiv (Order.highOrder H) r) hashes marked clause := by
  simp only [rankValue,dite_eq_left r.isLt]

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query arithmetic with fixed ordinary polynomial time and space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Every parked layout master survives actual arithmetic preparation. -/
theorem arithmetic_parked {base out : Data} {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {u : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (h : ArithmeticOutput base out m hd M cache u e)
    (i : Fin 768) (hlo : 730 ≤ i.val) (_hhi : i.val < 744) :
    out.stacks i = base.stacks i := by
  apply h.highFrame i (by omega)
  · intro hi
    have hv := congrArg Fin.val hi
    change i.val = 699 at hv
    omega
  · intro hi
    have hv : i.val ≤ 728 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem result_parameter (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin 14) (h5 : i≠5) (h7 : i≠7) (h8 : i≠8) :
    (result a p w tail).stacks (LeafProgram.LayoutMasters.high i)=
      a.stacks (LeafProgram.LayoutMasters.low i) := by
  rw [result,Wide.finished_high _ (middle_parked a p he w tail)]
  have hb : (LeafProgram.LayoutMasters.low i).val < 417 ∨
      481 ≤ (LeafProgram.LayoutMasters.low i).val := by
    left; change 128+i.val < 417; have := i.isLt; omega
  rw [Wide.exported_frame _ _ hb,middle_frame _ _ _ _ _ hb]
  all_goals intro h; apply_assumption; apply Fin.ext
            have hv := congrArg Fin.val h
            simp [LeafProgram.LayoutMasters.low] at hv ⊢
            omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The complete arithmetic suffix preserves every parked packing master. -/
theorem parked_result (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 14) :
    out.stacks (LeafProgram.LayoutMasters.high i) =
      (PackingCallerProgram.result front p first rest).stacks (LeafProgram.LayoutMasters.high i) := by
  rw [arithmetic_parked ho (LeafProgram.LayoutMasters.high i)
    (by change 730 ≤ 730+i.val; omega)
    (by change 730+i.val < 744; have := i.isLt; omega), hb]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

theorem numeric_Q (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :
    (numeric q k l).val 21=(produce (q.input k)).Q :=
  (Execute.guardedModel_public (q.input k) l 4).trans (Layout.model_core_values (q.input k) l).2.2.2.2.1

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual produced ring, parked layout and source bytes at the current-query
high-loop entry. Every field is derived from the same executed preparation
and initializer; no new evaluator or preparation service is supplied. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HighMarkedFrontend HighQuerySetup

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : State 40 896} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding

/-- The initializer changes only two lower words; all actual arithmetic and
parked source words have literal equality with the produced output. -/
theorem lower_frame (i : Fin 768) (h323 : i ≠ 323) (h330 : i ≠ 330) :
    (seeded).stacks (i.castAdd 128) = run.output.stacks i := by
  have hi : i.castAdd 128 ∉ ([330,788,789,790,323,791,792] : List (Fin 896)) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff,
      Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at *
    have := i.isLt
    omega
  rw [HighCountSeed.initialized_frame _ _ _ hi]
  exact result_stack front run.output i

/-- Every original ring-producer word below320 survives with the same bytes.
The statement includes both the framed and flat node tables. -/
theorem ring_word (i : Fin 320) :
    (seeded).stacks (i.castAdd 576) = run.ringState.stacks (i.castAdd 320) := by
  have hlow := run.arithmetic_output.low (i.castAdd 320) (by change i.val < 340; have := i.isLt; omega)
  have hf := lower_frame run (i.castAdd 448)
    (by intro h; have he := congrArg Fin.val h; have := i.isLt; simp only [Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at he; omega)
    (by intro h; have he := congrArg Fin.val h; have := i.isLt; simp only [Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at he; omega)
  exact hf.trans hlow

/-- Node-entry arithmetic caches are preserved as complete words. -/
theorem arithmetic_words (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
    (seeded).stacks (i.castAdd 128) = run.output.stacks i := by
  apply lower_frame run i
  all_goals
    simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The node stream and interpolation table are the two actual serializations
of the same generated nodes, in their original increasing order. -/
theorem nodes :
    (seeded).stacks 300 = Encoding.encodeList id
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)) ∧
    (seeded).stacks 256 =
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)).flatten := by
  exact ⟨(ring_word run 300).trans run.arithmetic_output.produced.framedNodes,
    (ring_word run 256).trans run.arithmetic_output.produced.flatNodes⟩

/-- Parking preserves the actual addressed layout, including offset743 and
all neutral-factor metadata. No supplied successful layout is used. -/
theorem parked (i : Fin 14) :
    (seeded).stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
      (PackingCallerProgram.result (project front) (packingProblem q k hg)
        run.first run.rest).stacks (LeafProgram.LayoutMasters.high i) := by
  have hi0 : LeafProgram.LayoutMasters.high i ≠ 323 := by
    intro h
    have he := congrArg Fin.val h
    change 730+i.val=323 at he
    omega
  have hi1 : LeafProgram.LayoutMasters.high i ≠ 330 := by
    intro h
    have he := congrArg Fin.val h
    change 730+i.val=330 at he
    omega
  exact (lower_frame run _ hi0 hi1).trans
    (NativeQueryPreparation.parked_result (project front) run.packed run.output
      (packingProblem q k hg) run.first run.rest run.packed_words run.arithmetic_output i)

/-- Source row, count and marker words remain the actual frontend's words. -/
theorem source_frame (i : Fin 768)
    (hi : i ∈ ([700,701,704,705,706,707,708,709] : List (Fin 768))) :
    (seeded).stacks (i.castAdd 128) = front.stacks (i.castAdd 128) := by
  have hlo : 660 ≤ i.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hf : run.output.stacks i = run.packed.stacks i := by
    apply run.arithmetic_output.highFrame i hlo
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [lower_frame run i (by intro h; subst i; simp at hi)
    (by intro h; subst i; simp at hi),hf,run.packed_words]
  change (PackingCallerProgram.result (project front) (packingProblem q k hg)
    run.first run.rest).stacks i = (project front).stacks i
  apply PackingCallerProgram.result_frame
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The actual frontend's row-count output survives the subsequent executed
packing, arithmetic and high-counter initialization. -/
theorem hash_count (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) :
    (seeded).stacks 704 = List.replicate q.rows.length true :=
  (source_frame run 704 (by decide)).trans hf.hashCount

private theorem frontend_source_frame (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) (i : Fin 768)
    (hi : i ∈ ([700,701,705,706,707,708,709] : List (Fin 768))) :
    front.stacks (i.castAdd 128) = base.stacks i := by
  apply hf.frame
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide

/-- These are the literal source and mark words consumed by the authentic
factor constructor. FrontState supplies the generated row count; original
entry readiness supplies only the input bytes. -/
theorem sources (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) (hr : q.Ready base) :
    (seeded).stacks 700 = Encoding.encodeList id q.clauses ∧
    (seeded).stacks 701 = HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
    (seeded).stacks 704 = List.replicate q.rows.length true ∧
    (seeded).stacks 705 = q.index ∧ (seeded).stacks 706 = [q.mark.isSome] ∧
    (seeded).stacks 707 = q.modulus ∧ (seeded).stacks 708 = q.width ∧
    (seeded).stacks 709 = q.ambient := by
  rcases hr with ⟨h0,h1,h5,h6,h7,h8,h9,_,_,_,_⟩
  have hs (i : Fin 768) (hi : i ∈ ([700,701,705,706,707,708,709] : List (Fin 768))) :
      (seeded).stacks (i.castAdd 128) = base.stacks i := by
    have hi' : i ∈ ([700,701,704,705,706,707,708,709] : List (Fin 768)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto
    exact (source_frame run i hi').trans (frontend_source_frame base w hf i hi)
  exact ⟨(hs 700 (by decide)).trans h0,(hs 701 (by decide)).trans h1,
    hash_count run base w hf,(hs 705 (by decide)).trans h5,(hs 706 (by decide)).trans h6,
    (hs 707 (by decide)).trans h7,(hs 708 (by decide)).trans h8,(hs 709 (by decide)).trans h9⟩

/-- The current physical mask, rather than a mask shared by other marks,
remains available to each actual high decoder. -/
theorem mask : (seeded).stacks 338 =
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  rw [HighCountSeed.initialized_frame _ _ 338 (by decide)]
  change (preparedOutput front run.data.output).stacks 338 = _
  exact run.mask.trans (physical_high_mask q)

/-- The actual parked unary radius is the radius of the addressed native
input used at every node. It is derived from the executed frontend export. -/
theorem packed_radius (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w)
    (node : Fin (packingProblem q k hg).Q) :
    (run.packed.stacks 740).length =
      (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg run.first run.rest node).R := by
  have he := packing_empty (project front) hf.privateEmpty hf.spare
  have hp := PackingCallerProgram.result_parameter (project front) (packingProblem q k hg)
    he run.first run.rest 10 (by decide) (by decide) (by decide)
  have hR : (model).val 29 = (produce (q.input k)).R :=
    (Execute.guardedModel_public (q.input k) padding 6).trans
      (Layout.model_core_values (q.input k) padding).2.2.2.2.2.2.1
  have hu := hf.exported.1 5
  have hw : run.packed.stacks 740 = List.replicate (produce (q.input k)).R true := by
    rw [run.packed_words]
    change (PackingCallerProgram.result (project front) (packingProblem q k hg)
      run.first run.rest).stacks (LeafProgram.LayoutMasters.high 10) = _
    rw [hp]
    simpa [Exports.destination,Exports.unaryValues,hR,LeafProgram.LayoutMasters.low] using hu
  rw [hw,List.length_replicate]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryRankCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual produced factor constructor and physical high odometer use
one source predicate and one descending rank order. Arithmetic witnesses and
interpolation nodes introduce no additional acceptance condition. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryRankCount

open OAI SqrtLog LeafProgram LeafParametersProgram
open PreparedSource PreparedBranchCount NodeConcrete
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

section Native

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3 ^ (m.val 34))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

local notation "hashes" => List.map
  (fun terms => List.map
    (fun term => (Prod.snd term,HashInputProgram.Expansion.originalClause source (Prod.fst term))) terms)
  (castRows (congrArg List.length hsource) (LeafQueryFrontend.Query.rows q))

/-- The actual native fixed-high answer is precisely the integer summand
used by the high-assignment accumulator; no coefficient or bit is tested. -/
theorem native_rank_count (H : Finset (Fin s.n)) (rank : Fin (2 ^ H.card)) :
    NodeSemantics.ternaryFixedHighCount H (Rank.highEquiv (Order.highOrder H) rank)
      (sourceHashes spec) (spec).marked (spec).markedClause =
    rankValue H hashes q.mark.isSome (source[markIndex q]?.getD []) rank.val := by
  change NodeSemantics.ternaryFixedHighCount H (Rank.highEquiv (Order.highOrder H) rank)
    hashes q.mark.isSome (source[markIndex q]?.getD []) = _
  exact (rankValue_at H hashes q.mark.isSome (source[markIndex q]?.getD []) rank).symm

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryRankCount
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem scalarCap_large (A : ℕ) : sourceSize A+1 ≤ scalarCap A := by
  have h : sourceSize A+1 ≤ (sourceSize A+1)^10 := Nat.le_self_pow (by decide) _
  unfold scalarCap
  omega

theorem original_le_scalar (A : ℕ) : A+1 ≤ scalarCap A := by
  have h1 := sourceSize_large A
  have h2 := scalarCap_large A
  omega

/-- Existing retained stacks use the compact boundary; transient space is
never fed back into the next call's input allowance. -/
theorem incoming_bound {r s : ℕ} (a : StructuredProgram.State r s) (A : ℕ)
    (ha : WordBound A a) : WordBound (compact A) a := by
  intro i
  apply (ha i).trans
  have h := original_le_scalar A
  have hp := compact_le (scalarCap A)
  change A ≤ compactCap (scalarCap A)
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

theorem preparedPorts_ranges (i : Fin 896) (hi : i∈preparedPorts) :
    i.val<744 ∧ i≠330 ∧ i≠323 ∧ i≠702 ∧ i≠703 := by
  simp only [preparedPorts,List.mem_filter,decide_eq_true_eq] at hi
  obtain ⟨hp,h307,h863,h702,h703⟩ := hi
  have hr : i.val<744 := by
    simp only [QueryNodeEvaluation.framePorts,List.mem_cons,List.not_mem_nil,or_false,
      Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    have hn : i.val≠863 := fun hv => h863 (Fin.ext hv)
    omega
  refine ⟨hr,?_,?_,h702,h703⟩
  · intro h; subst i; simp [QueryNodeEvaluation.framePorts] at hp
  · intro h; subst i; simp [QueryNodeEvaluation.framePorts] at hp

/-- The actual parked layout lies entirely in the repeated high-loop frame. -/
theorem parked_mem (i : Fin 14) :
    NativeLayoutLoad.stackMap (LayoutMasters.high i)∈preparedPorts := by
  fin_cases i <;> decide

/-- All arithmetic words consumed by the concrete node constructor are static
between high assignments. -/
theorem arithmetic_mem (i : Fin 768) (hi : i∈QueryReadyConstruction.arithmeticPorts) :
    i.castAdd 128∈preparedPorts := by
  simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- The source-local cache cap stays fixed across all high assignments;
transient caller storage is not fed into the next node's source cap. -/
theorem prepared_input_caps {initial a : Data} {A : ℕ}
    (hframe : ∀ i∈preparedPorts,a.stacks i=initial.stacks i)
    (hcache : ∀ i∈QueryNodeEvaluation.cacheInputPorts,(initial.stacks i).length≤A)
    (hparked : ∀ i : Fin 14,
      (initial.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high i))).length≤A) :
    (∀ i∈QueryNodeEvaluation.cacheInputPorts,(a.stacks i).length≤A) ∧
    (∀ i : Fin 14,(a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high i))).length≤A) := by
  constructor
  · intro i hi
    have hm : i∈preparedPorts := by
      simp only [QueryNodeEvaluation.cacheInputPorts,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hframe i hm]
    exact hcache i hi
  · intro i
    rw [hframe _ (parked_mem i)]
    exact hparked i

/-- The actual seed does not alter any prepared ring, source or layout word. -/
theorem initialized_prepared (a : Data) (rf : Fin 2 → Bool)
    (i : Fin 896) (hi : i∈preparedPorts) :
    (HighCountSeed.initialized a rf).stacks i=a.stacks i := by
  obtain ⟨hlo,h330,h323,_,_⟩ := preparedPorts_ranges i hi
  apply HighCountSeed.initialized_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at h330 h323 ⊢
  omega

/-- Refreshing the reusable lower counter retains the same prepared words. -/
theorem copied_prepared (a : Data) (i : Fin 896) (hi : i∈preparedPorts) :
    (copiedHighCounter a).stacks i=a.stacks i := by
  obtain ⟨hlo,h330,_,_,_⟩ := preparedPorts_ranges i hi
  exact copiedHighCounter_frame a i h330 (by
    intro h; have hv:=congrArg Fin.val h; simp at hv; omega)

/-- A pure physical word frame is stable under the real high odometer.
Its logical assertion contains no code, successful layout or query oracle. -/
theorem prepared_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter
      (fun _ a => ∀ i∈preparedPorts,a.stacks i=initial.stacks i) := by
  intro _ a b hframe ha i hi
  have hlo := (preparedPorts_ranges i hi).1
  rw [←hframe i
    (by intro h; have hv:=congrArg Fin.val h; change i.val=789 at hv; omega)
    (by intro h; have hv:=congrArg Fin.val h; change i.val=790 at hv; omega)]
  exact ha i hi

/-- Kept caller words are disjoint from the concrete high controller's
reusable counter and mass-adder words. This includes the parked blank767. -/
theorem kept_disjoint (i : Fin 896) (hi : HashMarkedReturn.kept i=true) :
    i≠323 ∧ i≠330 ∧ i≠788 ∧ i≠789 ∧ i≠790 ∧ i≠791 ∧ i≠792 := by
  simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at hi ⊢
  omega

/-- The complete caller frame can be carried by the same pure loop invariant. -/
theorem kept_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter
      (fun _ a => ∀ i,HashMarkedReturn.kept i=true → a.stacks i=initial.stacks i) := by
  intro _ a b hframe ha i hi
  have hd := kept_disjoint i hi
  rw [←hframe i hd.2.2.2.1 hd.2.2.2.2.1]
  exact ha i hi

/-- The concrete prepared-and-seeded run starts at the empty count and the
single zero tuple, even when there are no high coordinates. -/
theorem prepared_seed_entry {q k hg front padding S B cost}
    (run : HighQuerySetup.PreparedRun q k hg front padding S B cost) :
    let a := HighCountSeed.initialized (HighMarkedFrontend.result front run.output) run.seedRegs
    a.stacks 789=Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
    a.stacks 790=[] ∧ a.stacks 323=[] ∧ a.stacks 791=[] ∧
    BinaryArithmetic.toNat (a.stacks 788)=0 ∧ (a.stacks 788).length=0 ∧
    a.regs 21=true ∧
    (∀ i∈preparedPorts,a.stacks i=(HighMarkedFrontend.result front run.output).stacks i) := by
  let a := HighCountSeed.initialized (HighMarkedFrontend.result front run.output) run.seedRegs
  have hf : ∀ i∈preparedPorts,a.stacks i=(HighMarkedFrontend.result front run.output).stacks i :=
    initialized_prepared (HighMarkedFrontend.result front run.output) run.seedRegs
  have hz : a.stacks 788=[] := run.cleared 788 (by decide)
  have hv : BinaryArithmetic.toNat (a.stacks 788)=0 := congrArg BinaryArithmetic.toNat hz
  have hl : (a.stacks 788).length=0 := congrArg List.length hz
  exact ⟨run.counter,run.cleared 790 (by decide),run.cleared 323 (by decide),
    run.cleared 791 (by decide),hv,hl,run.high_guard,hf⟩

/-- The complete high-loop invariant combines only literal word equalities.
Both frames survive the actual odometer and the paid initial guard. -/
theorem complete_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter (fun _ a =>
      (∀ i∈preparedPorts,a.stacks i=initial.stacks i) ∧
      (∀ i,HashMarkedReturn.kept i=true → a.stacks i=initial.stacks i)) := by
  intro rank a b hf ha
  exact ⟨prepared_frame_stable initial rank a b hf ha.1,
    kept_frame_stable initial rank a b hf ha.2⟩

/-- The high counter and exact accumulator fit the compact boundary from
an independent ambient source cap. No prefix allowance enters this bound. -/
theorem compact_width {n A : ℕ} (H : Finset (Fin n)) (hn : n≤A) :
    4*H.card+1≤QueryHeadBudgets.compact A ∧ n+1≤QueryHeadBudgets.compact A := by
  have hh : H.card≤n := by simpa using Finset.card_le_univ H
  have hs := QueryHeadBudgets.original_le_scalar A
  change 4*H.card+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A) ∧
    n+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A)
  unfold HeadSumBudgets.compactCap
  omega

section PreparedInputs

open LeafParametersProgram

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (run : HighQuerySetup.PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized
  (HighMarkedFrontend.result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding

/-- Every rank reads the layout physically produced by this same preparation. -/
theorem prepared_parked (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) (j : Fin 14) :
    a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
      (PackingCallerProgram.result (HighMarkedFrontend.project front)
        (Query.packingProblem q k hg) run.first run.rest).stacks (LayoutMasters.high j) :=
  (hf _ (parked_mem j)).trans (HighQueryPreparedSource.parked run j)

/-- The arithmetic witness is the actual preparation output, with unchanged
physical cache words at each repeated branch boundary. -/
theorem prepared_arithmetic (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i)
    (i : Fin 768) (hi : i∈QueryReadyConstruction.arithmeticPorts) :
    a.stacks (i.castAdd 128)=run.output.stacks i :=
  (hf _ (arithmetic_mem i hi)).trans (HighQueryPreparedSource.arithmetic_words run i hi)

/-- Both node serializations remain the ones emitted by the same ring run. -/
theorem prepared_nodes (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) :
    a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)) ∧
    a.stacks 256=
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)).flatten :=
  ⟨(hf 300 (by decide)).trans (HighQueryPreparedSource.nodes run).1,
    (hf 256 (by decide)).trans (HighQueryPreparedSource.nodes run).2⟩

/-- A repeated branch retains this query's own computed high set. -/
theorem prepared_mask (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) :
    a.stacks 338=HighIncidenceProgram.descendingHighMask (HighMarkedFrontend.highSet q) :=
  (hf 338 (by decide)).trans (HighQueryPreparedSource.mask run)

/-- Literal source and current-marker inputs at every rank follow from the
same frontend execution and original readiness, rather than a supplied source. -/
theorem prepared_sources (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i)
    (base : Query.Data) (w : Bank.Words)
    (hfront : Query.FrontState q k base (HighMarkedFrontend.project front) padding w)
    (hr : q.Ready base) :
    a.stacks 700=Encoding.encodeList id q.clauses ∧
    a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
    a.stacks 704=List.replicate q.rows.length true ∧
    a.stacks 705=q.index ∧ a.stacks 706=[q.mark.isSome] ∧
    a.stacks 707=q.modulus ∧ a.stacks 708=q.width ∧ a.stacks 709=q.ambient := by
  obtain ⟨h700,h701,h704,h705,h706,h707,h708,h709⟩ :=
    HighQueryPreparedSource.sources run base w hfront hr
  exact ⟨(hf 700 (by decide)).trans h700,(hf 701 (by decide)).trans h701,
    (hf 704 (by decide)).trans h704,(hf 705 (by decide)).trans h705,
    (hf 706 (by decide)).trans h706,(hf 707 (by decide)).trans h707,
    (hf 708 (by decide)).trans h708,(hf 709 (by decide)).trans h709⟩

end PreparedInputs

section ActualRun

open LeafParametersProgram PreparedSource PreparedBranchCount LeafBranchProgram
open HashGreedyProgram.NativeRound

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (prepared : HighQuerySetup.PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized
  (HighMarkedFrontend.result front prepared.output) prepared.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "H" => HighMarkedFrontend.highSet q
local notation "n" => BinaryArithmetic.toNat q.ambient

/-- Actual complete enumeration of the fresh high set. Every rank invokes the
fixed streamed query, and the same run accumulates the full source count.
The input word and scalar caps are physical preparation bounds; no evaluator,
layout service, branch execution, or repeated-loop bound is assumed. -/
theorem run_oai (RB RC RD RI RE : ℕ) (hv : q.Valid)
    (frontBase : Query.Data) (bw : Bank.Words)
    (hfront : Query.FrontState q k frontBase (HighMarkedFrontend.project front) padding bw)
    (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
    (source : List (List (SAT.Literal (Fin n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (A T : ℕ) (hwords : ∀ i,((seeded).stacks i).length≤A)
    (hvalues : ∀ i,(model).val i≤A) (hAT : A≤T) (hqsize : 3^((model).val 34)≤T) :
    let hashes := (castRows (congrArg List.length hsource) q.rows).map
      (fun terms => terms.map (fun term =>
        (term.2,HashInputProgram.Expansion.originalClause source term.1)))
    let resources := ProducedQueryResources.ofPacking q k RB RC RD RI RE hg
      prepared.first prepared.rest
    let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q) resources
    let F := QueryHeadBudgets.compact A
    let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
      ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
    let D := max (max F (QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
      ((model).val 42) A T)) (20*(n+2))
    ∃ steps final, Eval HighQueryProgram.highLoop steps seeded final ∧
      steps+1≤2^(H).card*(C+28*(H).card+12)+3 ∧
      BinaryArithmetic.toNat (final.stacks 788)=
        fullCount hashes q.mark.isSome (source[markIndex q]?.getD []) ∧
      (final.stacks 788).length≤n+1 ∧ final.stacks 323=[] ∧ final.stacks 791=[] ∧
      final.stacks 789=Encoding.encodeList id (List.replicate (H).card [false]) ∧
      final.stacks 790=[] ∧ final.regs 21=false ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=(seeded).stacks i) ∧
      (∀ i,(final.stacks i).length≤F) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        ((seeded).withPC (some (compiled HighQueryProgram.highLoop 789 788).entry))
        (final.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) seeded (max D (40*((H).card+1))) := by
  classical
  dsimp only
  let node : Fin (Query.packingProblem q k hg).Q :=
    ⟨0,(Query.packingProblem q k hg).hQ⟩
  let native := LeafHeadSetupProgram.Native.queryInputsAddressed q k hg
    prepared.first prepared.rest node
  let hashes := (castRows (congrArg List.length hsource) q.rows).map
    (fun terms => terms.map (fun term =>
      (term.2,HashInputProgram.Expansion.originalClause source term.1)))
  let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
    (ProducedQueryResources.ofPacking q k RB RC RD RI RE hg prepared.first prepared.rest)
  let F := QueryHeadBudgets.compact A
  let K := QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
    ((model).val 42) A T
  let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
    ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
  let D := max (max F K) (20*(n+2))
  let I := fun a : Data =>
    (∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) ∧
    (∀ i,HashMarkedReturn.kept i=true → a.stacks i=(seeded).stacks i)
  have hn : n≤A := by
    have hh := hwords 338
    rw [HighQueryPreparedSource.mask prepared] at hh
    simpa [HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using hh
  have cap := compact_width H hn
  have hQ : (model).val 21=native.Q := numeric_Q q k padding
  have hfield : native.Q<3^((model).val 34) := numeric_field q k padding hg
  have hR : (prepared.packed.stacks 740).length=native.R :=
    HighQueryPreparedSource.packed_radius prepared frontBase bw hfront node
  have hJ : 0<(model).val 42 := QueryTargetMetadata.numeric_order_pos q k padding hg
  have branch : ∀ rank,rank<2^(H).card → ∀ words (a : Data),
      words.map List.length=List.replicate (H).card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] → a.stacks 791=[] →
      a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum
        (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤F) →
      ∃ steps b,Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=rankSum
          (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤F) ∧ StageSpace HighQueryProgram.branch steps a D := by
    intro rank hr words a shape invariant hc _hs ht _guard hvRank hacc hlen hb
    let copied := copiedHighCounter a
    have frame : ∀ i∈preparedPorts,copied.stacks i=(seeded).stacks i :=
      fun i hi => (copied_prepared a i hi).trans (invariant.1 i hi)
    have caps := prepared_input_caps frame (fun i _ => hwords i) (fun i => hwords _)
    obtain ⟨s700,s701,s704,s705,s706,s707,s708,s709⟩ :=
      prepared_sources prepared copied frame frontBase bw hfront hready
    have sources : Query.Sources q
        (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort copied) :=
      ⟨s700,s701,s707,s708,s709⟩
    have rings : ∀ i∈QueryReconstruction.ringPorts,
        copied.stacks (i.castAdd 576)=prepared.ringState.stacks (i.castAdd 320) := by
      intro i hi
      apply Eq.trans (frame _ ?_) (HighQueryPreparedSource.ring_word prepared i)
      simp only [QueryReconstruction.ringPorts,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨cacheWords,hcache,qs,middle,qe,_qt,qcount,_qblank,qbound,qframe,qkept,qtime,qspace⟩ :=
      QueryStreamCorrect.run q k RB RC RD RI RE hg hv prepared.first prepared.rest node
        model padding rfl (Query.ring_precision_pos (q.input k) padding hg)
        (Query.ring_degree_pos (q.input k) padding hg) prepared.modulus prepared.cache
        prepared.half prepared.ringState prepared.packed prepared.output
        prepared.arithmetic_output hfield hQ hR hJ source hsource A T copied
        frontBase (HighMarkedFrontend.project front) bw hfront
        (prepared_parked prepared copied frame) caps.2 caps.1 hvalues sources
        (by rw [frame 700 (by decide)]; exact hwords 700)
        (by rw [frame 701 (by decide)]; exact hwords 701)
        (by rw [frame 708 (by decide)]; exact hwords 708)
        (prepared_nodes prepared copied frame).1 (prepared_mask prepared copied frame)
        (prepared_arithmetic prepared copied frame) prepared.degree s704
        (s705.trans hindex) s706 words shape ⟨rank,hr⟩ hvRank
        ((copiedHighCounter_word a).trans hc) rings
        ((frame 256 (by decide)).trans (HighQueryPreparedSource.ring_word prepared 256))
        hwidth (copiedHighCounter_bound a F hb) hAT hqsize
        (by rw [frame 194 (by decide)]; exact (hwords 194).trans hAT)
        (by rw [frame 202 (by decide)]; exact (hwords 202).trans hAT) cap.2
    have exactCount : middle.stacks 323=countWord
        (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD []) rank) := by
      have value := HighQueryRankCount.native_rank_count native model
        (Query.ring_precision_pos (q.input k) padding hg)
        (Query.ring_degree_pos (q.input k) padding hg) cacheWords hcache
        prepared.modulus prepared.cache prepared.half prepared.ringState
        prepared.arithmetic_output.produced hfield q hv ((model).val 42) hJ
        source hsource H ⟨rank,hr⟩
      exact qcount.trans (congrArg DisjointReuse.binaryNat value)
    have qp : StageSpace QueryStreamProgram.command qs copied K :=
      ⟨fun t z hle he i => qspace.bound t z (by omega) he i⟩
    obtain ⟨steps,b,he,hcost,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
        _hguard,hbound,hprefix⟩ :=
      HighQueryLoop.branch_step_resources H hashes q.mark.isSome (source[markIndex q]?.getD [])
        rank hr a middle qs F F F K qe qp hacc hlen exactCount ht hb
        (hb 330) (hb 792) (hb 789) cap.2 (fun i _ _ _ => qbound i)
    have pf : ∀ i∈preparedPorts,middle.stacks i=copied.stacks i := by
      intro i hi
      have hm := List.mem_filter.mp hi
      have hn := of_decide_eq_true hm.2
      apply qframe i
      · exact List.mem_filter.mpr ⟨hm.1,by simpa using And.intro hn.1 hn.2.1⟩
      · exact hn.2.2.1
      · exact hn.2.2.2
    refine ⟨steps,b,he,?_,?_,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,hbound,?_⟩
    · have qt : qs≤QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
          ((model).val 21) ((model).val 42) A T work := (Nat.le_succ qs).trans qtime
      exact hcost.trans (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right qt _) _) _)
    · exact ⟨fun i hi => (branch_prepared_of_stream qe he ht pf i hi).trans (invariant.1 i hi),
        fun i hi => (branch_kept_of_stream qe he ht qkept i hi).trans (invariant.2 i hi)⟩
    · exact ⟨fun t z hle ht i => hprefix.bound t z (by omega) ht i⟩
  obtain ⟨hc,hs,_ho,ht,hacc,hlen,_hg,_frame⟩ := prepared_seed_entry prepared
  obtain ⟨steps,final,he,htime,hi,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
      hguard,hbound,htrace,hprefix⟩ :=
    HighQueryTraversal.high_loop_run H hashes q.mark.isSome (source[markIndex q]?.getD [])
      I F C D (complete_frame_stable seeded) cap.1
      ((Nat.le_max_left F K).trans (Nat.le_max_left _ _)) branch seeded
      ⟨fun _ _ => rfl,fun _ _ => rfl⟩ hc hs ht hacc (by omega)
      (QueryHeadBudgets.incoming_bound seeded A hwords)
  exact ⟨steps,final,he,htime,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
    hguard,hi.2,hbound,htrace,hprefix⟩

end ActualRun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run_oai
