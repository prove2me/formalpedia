-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:54:20.521931+00:00
-- url     : https://prove2.me/submissions/8a93dd70-fcfd-498f-8680-baa9bdfaa6c2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S184

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem pairPayload_original (v f : ℕ) :
    pairPayload v f=SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [v,f] := rfl

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stream_original (ps : List (ℕ × ℕ)) :
    stream ps=ProgramEncoding.encodeRecords
      (ps.map fun p => SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [p.1,p.2]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa only [stream,ProgramEncoding.encodeRecords,List.map_cons,Encoding.encodeList,
        pairPayload_original, Function.id_def] using congrArg
          (fun tail => true::(Encoding.frame (pairPayload p.1 p.2)++tail)) ih

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem exported_value (a : Local)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[])
    (p : Fin 768 × Fin 768) (hp : p∈exportPairs) :
    (exported a).stacks p.2=a.stacks p.1 := by
  have hd : p.2∉privatePorts := by
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> simp [mem_privatePorts]
  rw [exported,clearMany_stacks,ite_eq_right hd]
  apply copyMany_value exportPairs a (by decide) ?_ ?_ p hp
  · simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
    rintro q (rfl|rfl|rfl) <;> assumption
  · intro q hq z hz
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hq hz
    rcases hq with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl <;> decide

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

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

theorem finished_words (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 735=a.stacks (ports 62) := by
  rw [show (735 : Fin 768)=LeafProgram.LayoutMasters.high 5 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 62,133) (by simp [exportPairs])

theorem finished_metadata (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 737=a.stacks (ports 63) := by
  rw [show (737 : Fin 768)=LeafProgram.LayoutMasters.high 7 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 63,135) (by simp [exportPairs])

theorem finished_plans (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 738=a.stacks (ports 61) := by
  rw [show (738 : Fin 768)=LeafProgram.LayoutMasters.high 8 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 61,136) (by simp [exportPairs])

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem middle_words (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 62)=((p.words w tail).map ReadPlan.encodeWord).flatten := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore,selectedStore]

theorem middle_metadata (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 63)=(p.spec w tail).suffix.metadata := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore]

theorem middle_plans (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 61)=planBits p.scopes p.n p.mask := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore,selectedStore,cached,loadedStore,planStore]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem result_words (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 735=((p.words w tail).map ReadPlan.encodeWord).flatten := by
  rw [result,Wide.finished_words _ (middle_parked a p he w tail)]
  · exact middle_words a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

theorem result_metadata (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 737=(p.spec w tail).suffix.metadata := by
  rw [result,Wide.finished_metadata _ (middle_parked a p he w tail)]
  · exact middle_metadata a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

theorem result_plans (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 738=planBits p.scopes p.n p.mask := by
  rw [result,Wide.finished_plans _ (middle_parked a p he w tail)]
  · exact middle_plans a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved stream contains word addresses, so its second component is the
ambient-offset factor address. Incidence positions and owner fibers are unchanged. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp

theorem addressedEntries_plans (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).map (fun p => [p.1,p.2]) = Install.plans scopes n mask := by
  rw [Install.plans,Semantics.plans_eq]
  simp only [addressedEntries,Semantics.nativeEntries,List.map_map,Function.comp_def]

theorem addressedEntries_stream (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    LayoutOwnerFiberProgram.stream (addressedEntries scopes n mask) =
      ProgramEncoding.encodeRecords
        (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) := by
  calc
    _ = ProgramEncoding.encodeRecords
        (((addressedEntries scopes n mask).map (fun p => [p.1,p.2])).map
          PackingVertexLabels.planPayload) := by
      rw [LayoutOwnerFiberProgram.stream_original,List.map_map]
      rfl
    _ = ProgramEncoding.encodeRecords
        ((Install.plans scopes n mask).map PackingVertexLabels.planPayload) := by
      rw [addressedEntries_plans]
    _ = _ := rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeAddressedQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved runtime plan stream uses absolute word addresses: the factor
component is ambient+factor. This constructor matches those bytes while
preserving the incidence order, owner fibers, packing, and head relation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open PackingCallerProgram LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
variable (a : Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q)
variable (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q))
variable (t : Fin (LeafProgram.Query.packingProblem q k hg).Q)

/-- This is the literal byte string saved at parked master738 and loaded
into source136. It is not the raw unshifted incidence-pair serialization. -/
theorem queryInputsAddressed_stream :
    LayoutOwnerFiberProgram.stream (queryInputsAddressed q k hg a tail t).plans=
      PackingCallerProgram.planBits q.scopeRows
        (LeafProgram.Query.packingProblem q k hg).n q.forward :=
  PackingIncidenceInput.addressedEntries_stream _ _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQuerySourceBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual addressed parked-bank readback from native query preparation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query

/-- The physical parked bank contains the actual addressed plans and packing
output. The node field is supplied by the concrete node-counter load. -/
theorem sourceBank_of_parked (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base front : Data) (l : Fin 8 → ℕ) (bw : Bank.Words)
    (hf : FrontState q k base front l bw)
    (first : MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q)
    (rest : List (MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q))
    (node : Fin (packingProblem q k hg).Q) (a : State 40 896)
    (hpark : ∀ i : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        (PackingCallerProgram.result front (packingProblem q k hg) first rest).stacks
          (LeafProgram.LayoutMasters.high i))
    (hnode : a.stacks 307 = LeafHeadSetupProgram.unary node.val) :
    NativeLayoutLoad.SourceBank
      (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first rest node) a := by
  let p := packingProblem q k hg
  let m := Execute.guardedModel (q.input k) l
  have he := packing_empty front hf.privateEmpty hf.spare
  have hp (i : Fin 14) (h5 : i ≠ 5) (h7 : i ≠ 7) (h8 : i ≠ 8) :
      a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        front.stacks (LeafProgram.LayoutMasters.low i) :=
    (hpark i).trans (PackingCallerProgram.result_parameter front p he first rest i h5 h7 h8)
  have hn := (LeafQueryFrontend.exported_input_values (q.input k) l front hf.exported).1
  have hN := (LeafQueryFrontend.exported_input_values (q.input k) l front hf.exported).2.1
  have hr : m.val 18 = (produce (q.input k)).r := Execute.guardedModel_radius _ _
  have hQ : m.val 21 = (produce (q.input k)).Q :=
    (Execute.guardedModel_public (q.input k) l 4).trans
      (Layout.model_core_values (q.input k) l).2.2.2.2.1
  have hR : m.val 29 = (produce (q.input k)).R :=
    (Execute.guardedModel_public (q.input k) l 6).trans
      (Layout.model_core_values (q.input k) l).2.2.2.2.2.2.1
  have hu (i : Fin 8) := hf.exported.1 i
  constructor
  · exact (hp 0 (by decide) (by decide) (by decide)).trans hn
  · apply (hp 1 (by decide) (by decide) (by decide)).trans
    change front.stacks 129 = List.replicate p.factors true
    simpa only [p, packing_factors_eq] using hN
  · apply (hp 2 (by decide) (by decide) (by decide)).trans
    change front.stacks 130 = _
    simpa [Exports.destination, Exports.unaryValues, hr, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 2
  · apply (hp 3 (by decide) (by decide) (by decide)).trans
    change front.stacks 131 = _
    simpa [Exports.destination, Exports.unaryValues, hQ, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 3
  · apply (hp 4 (by decide) (by decide) (by decide)).trans
    change front.stacks 132 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 4
  · exact (hpark 5).trans (PackingCallerProgram.result_words front p he first rest)
  · exact (hp 6 (by decide) (by decide) (by decide)).trans hf.low
  · exact (hpark 7).trans (PackingCallerProgram.result_metadata front p he first rest)
  · exact (hpark 8).trans ((PackingCallerProgram.result_plans front p he first rest).trans
      (LeafHeadSetupProgram.Native.queryInputsAddressed_stream q k hg first rest node).symm)
  · apply (hp 10 (by decide) (by decide) (by decide)).trans
    change front.stacks 138 = _
    simpa [Exports.destination, Exports.unaryValues, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 5
  · apply (hp 11 (by decide) (by decide) (by decide)).trans
    change front.stacks 139 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 6
  · apply (hp 12 (by decide) (by decide) (by decide)).trans
    change front.stacks 140 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 7
  · change BinaryArithmetic.toNat
      (a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high 13))) = _
    rw [hp 13 (by decide) (by decide) (by decide)]
    change BinaryArithmetic.toNat (front.stacks 141) = _
    rw [hf.offset]
    have ho : m.val 3 = (q.input k).occurrence := Execute.guardedModel_input _ _ 3
    change 2 * m.val 3 * (8 * m.val 21) ^ (2 * m.val 29) = _
    rw [ho, hQ, hR]
    rfl
  · exact hnode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage


/-- The actual parked layout remains the source of every node's addressed
input. The loop changes only the unary node index in this readback. -/
theorem NodeBoundary.sourceBank_oai
    (query : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (base front : State 40 768) (lengths : Fin 8 → ℕ)
    (bw : LeafParametersProgram.Bank.Words)
    (hf : LeafProgram.Query.FrontState query k base front lengths bw)
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
    {initial a : Data} {t d Q J B : ℕ}
    (h : NodeBoundary initial t d Q J B node.val a)
    (hpark : ∀ i : Fin 14,
      initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        (PackingCallerProgram.result front (LeafProgram.Query.packingProblem query k hg)
          first tail).stacks (LeafProgram.LayoutMasters.high i)) :
    NativeLayoutLoad.SourceBank
      (LeafHeadSetupProgram.Native.queryInputsAddressed query k hg first tail node) a := by
  apply NativeQueryPreparation.sourceBank_of_parked query k hg base front lengths bw hf
    first tail node a
  · intro i
    have hi : NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)∈retainedPorts := by
      fin_cases i <;> decide
    exact (h.retained _ hi).trans (hpark i)
  · exact h.node

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank_oai
