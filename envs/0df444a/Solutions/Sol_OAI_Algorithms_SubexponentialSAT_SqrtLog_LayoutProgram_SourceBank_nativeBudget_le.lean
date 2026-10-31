-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:40:54.958448+00:00
-- url     : https://prove2.me/submissions/e9941ae0-c1c7-4bb9-82cd-03427945b851

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowSourceBound_source_bound_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Filtered row records for the physical interpolation-code emitter

Inactive zero terms and unit factors are omitted from the emitted records.
This is proved as a polynomial identity, without identifying the two different
expression trees or assuming a desired evaluator result.
-/

namespace SubexponentialSAT.Subexp.UniversalRowSource

open scoped BigOperators
open SubexpSymbolicCost SubexpRowInterpolation SubexpRepresentedRows
open UniversalRowProgram

variable {C E : Type*} {Q : ℕ}

theorem selected_nodup (s : Finset (Fin Q)) : (selected s).Nodup :=
  (List.nodup_finRange Q).filter _

end SubexponentialSAT.Subexp.UniversalRowSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTableSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Indexed cache tables and the represented interpolation row

The physical producer reads natural-number indexed lists. This adapter
identifies those reads with the finite-indexed row specification, including
the mismatch filter and the cardinality guard. Its premises concern only
individual input cache entries, the delta word, and the limit's length.
-/

namespace SubexponentialSAT.Subexp.UniversalRowTableSource

open SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowSource
open UniversalRowProgram (Row rowExpression)

variable {C E A B : Type*} {Q : ℕ}

theorem positions_mismatch {V G : Type*} [DecidableEq G]
    (head : V → Fin Q → G) (σ : Fin Q → G) (y : V) :
    positions (mismatchPositions head σ y) =
      ((List.finRange Q).filter (fun i => decide (head y i ≠ σ i))).map Fin.val := by
  simp [positions, UniversalRowSource.selected]

@[simp] theorem positions_length (s : Finset (Fin Q)) :
    (positions s).length = s.card := by
  rw [positions, List.length_map,
    ← List.toFinset_card_of_nodup (UniversalRowSource.selected_nodup s), selected_toFinset]

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageTypes_stacks (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    (Staging.result 0 1 stageTypesOps a).stacks=
      Function.update (Function.update a.stacks 23 (a.stacks 289)) 24 (a.stacks 292) := by
  simp [stageTypesOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h23,h24]

theorem stageTypes_cost (a : Data) : Staging.cost 0 1 stageTypesOps a=
    7*((a.stacks 289).length+(a.stacks 292).length)+10 := by
  simp [stageTypesOps,Staging.cost,Staging.actionCost,Staging.actionResult,StackRoutines.copyStacks]
  ring

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem emitterSize_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    emitterSize a ≤ 10*B := by
  have h67 := hB 67
  have h308 := hB 308
  have h309 := hB 309
  have h310 := hB 310
  have h71 := hB 71
  have h311 := hB 311
  have h312 := hB 312
  have h313 := hB 313
  have h314 := hB 314
  have h47 := hB 47
  unfold emitterSize
  omega

theorem stageTypes_cost_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    Staging.cost 0 1 stageTypesOps a ≤ 14*B+10 := by
  have h1 := hB 289
  have h2 := hB 292
  rw [stageTypes_cost]
  omega

theorem finishBound_le (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (a : Data) (B E : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B)
    (hE : UniversalRowSourceProgram.bound tables width rowWidth positions
      (deltaWord a) (a.stacks 47) (a.stacks 313) (a.stacks 314) ≤ E) :
    finishBound tables width rowWidth positions a B ≤ 224*B+E+271 := by
  have h23 := hB 23
  have h24 := hB 24
  have hs := emitterSize_le a B hB
  unfold finishBound
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual scalar producer's numerator input already contains precisely
all low type-extractor inputs. No second pre-expanded input is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem nativeIndices_eq {r Q : ℕ} (u y : UniversalType r Q 1) :
    nativeIndices u y=UniversalRowTermProgram.indices (nativePositions u y) := by rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact table shapes and read validity for finite typed interpolation
caches. Flattening is a specification of the arrays produced natively. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

private theorem getD_ofFn {A : Type*} (f : Fin Q → A) (default : A) (i : Fin Q) :
    (List.ofFn f).getD i.val default=f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem position_lt (s : Finset (Fin Q)) (i : ℕ) (hi : i∈positions s) : i < Q := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact j.isLt

/-- Each native fixed-width read is in range, including the inner row reads.
The validity proof comes from actual finite cache dimensions. -/
theorem tables_valid (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
    (hwidth : ∀ c,(encode c).length=width.length)
    (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q)) :
    UniversalRowLoop.Valid (tables encode values inverse negative difference) width rowWidth (positions s) := by
  constructor
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    simp only [List.length_flatten,List.map_ofFn,hrow]
    have he : (List.length ∘ fun j => encode (difference i j)) = fun _ : Fin Q => width.length := by
      funext j
      exact hwidth _
    rw [he]
    simp
  · intro i hi
    have h := position_lt s i hi
    simpa only [tables,List.length_ofFn] using And.intro h (And.intro h h)
  · intro i hi word hw
    have hii : i < Q := position_lt s i hi
    change word∈(List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i [] at hw
    rw [getD_ofFn _ _ (⟨i,hii⟩:Fin Q)] at hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro i hi j hj
    have hii : i < Q := position_lt s i hi
    have hjj : j < Q := position_lt s j hj
    change j < ((List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i []).length ∧
      j < (List.ofFn (fun i => encode (negative i))).length
    rw [getD_ofFn _ _ (⟨i,hii⟩:Fin Q)]
    simpa using And.intro hjj hjj

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bind the actual integer-to-ring vector producer to the actual source-row
program. The coefficient table is obtained from its execution, not supplied
as an expanded table premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram
open RowSelectionProgram (WordPair pairValue pairLength)

theorem nativePositions_eq {r Q : ℕ} (u y : UniversalType r Q 1) :
    nativePositions u y=UniversalRowTableSource.positions
      (SubexpRowInterpolation.mismatchPositions (fun v => v.head) (u.slot 0) y) := by
  symm
  exact UniversalRowTableSource.positions_mismatch (fun v => v.head) (u.slot 0) y

theorem branch_length_le (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (B : ℕ)
    (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∀ j,((branchState a rf bits indices).stacks j).length ≤ B+bits.length+indices.length := by
  intro j
  simp only [branchState,stageTypes_stacks a h23 h24,Function.update_apply]
  split_ifs <;> first | omega | exact (hB _).trans (by omega)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

theorem index_records_size (positions : List ℕ) (S : ℕ)
    (hpos : ∀ i ∈ positions, i ≤ S) :
    ∀ w ∈ positions.reverse.map indexWord, w.length ≤ S := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  simpa only [UniversalRowFactorLoop.indexWord_length] using
    hpos i (List.mem_reverse.mp hi)

theorem indices_length_le (positions : List ℕ) (S : ℕ)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S) :
    (UniversalRowTermProgram.indices positions).length ≤ indicesBound S := by
  have h := Encoding.length_encodeList_upper id (positions.reverse.map indexWord) S
    (index_records_size positions S hpos)
  simp only [List.length_map, List.length_reverse] at h
  exact h.trans (by unfold indicesBound; gcongr)

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform byte and running-time bounds for each actually emitted finite
source row. The bound uses the full table width, not the rational rank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

theorem positions_length_le (s : Finset (Fin Q)) : (positions s).length ≤ Q := by
  rw [positions_length]
  simpa using Finset.card_le_univ s

theorem positions_value_le (s : Finset (Fin Q)) (i : ℕ) (hi : i∈positions s) : i ≤ Q := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact Nat.le_of_lt j.isLt

/-- The native mismatch-index stream is itself polynomial-sized. -/
theorem indices_length_le (s : Finset (Fin Q)) :
    (UniversalRowTermProgram.indices (positions s)).length ≤ UniversalRowSourceBound.indicesBound Q :=
  UniversalRowSourceBound.indices_length_le _ Q (positions_length_le s) (positions_value_le s)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial resource bounds for the concrete universal source
branch. Typed table entries contribute their actual d*B bit width. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

private theorem bits_length (p : Parameters r Q d) (codes : Fin Q → ModelCode p.t d) :
    (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten.length=Q*(d*SubexpLiftRing.baseWidth 3 p.t) := by
  rw [List.length_flatten,List.map_ofFn]
  have hf : (List.length ∘ fun i=>RingProgram.flat (codes i))=
      fun _ : Fin Q=>d*SubexpLiftRing.baseWidth 3 p.t := by
    funext i
    exact RingProgram.flat_length _
  rw [hf]
  simp

private theorem indices_length (u y : UniversalType r Q 1) :
    (nativeIndices u y).length ≤ UniversalRowSourceBound.indicesBound Q := by
  rw [nativeIndices_eq,nativePositions_eq]
  exact SourceTyped.indices_length_le _

theorem nativeBudget_le_oai (p : Parameters r Q d) (S : ℕ) (a : Data)
    (codes : Fin Q → ModelCode p.t d) (u y : UniversalType r Q 1)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (hS : ∀ j,(a.stacks j).length ≤ S) (hQ : Q ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    nativeBudget p S a codes u y ≤ universalBudget p S u y := by
  let bits := (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
  let idx := nativeIndices u y
  let z := branchState a (fun _=>false) bits idx
  let B := S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+idx.length
  have hsB : S ≤ B := by dsimp [B]; omega
  have hBS : B ≤ sourceWorkspace p S := by
    have hi := indices_length u y
    dsimp [B,idx,sourceWorkspace]
    omega
  have hz : ∀ j,(z.stacks j).length ≤ B := by
    have hh := branch_length_le a (fun _=>false) bits idx h23 h24 S hS
    simpa only [bits,bits_length] using hh
  let ts := SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference
  have hvalid := SourceTyped.tables_valid RingProgram.flat codes p.inverse p.negative p.difference
    p.ringWidth p.rowWidth (fun c=>(RingProgram.flat_length c).trans p.hringWidth.symm) p.hrowWidth
    (SubexpRowInterpolation.mismatchPositions (fun v=>v.head) (u.slot 0) y)
  have hdelta : (deltaWord z).length ≤ sourceWorkspace p S := by
    unfold deltaWord
    split_ifs <;> exact (hz _).trans hBS
  have hE := UniversalRowSourceBound.source_bound_le ts p.ringWidth p.rowWidth
    (nativePositions u y) (deltaWord z) (z.stacks 47) (z.stacks 313) (z.stacks 314)
    (sourceWorkspace p S) (by simpa only [nativePositions_eq] using hvalid)
    (by rw [nativePositions_eq]; exact (SourceTyped.positions_length_le _).trans (hQ.trans (hsB.trans hBS)))
    (by intro i hi; rw [nativePositions_eq] at hi
        exact (SourceTyped.positions_value_le _ i hi).trans (hQ.trans (hsB.trans hBS)))
    (hW.trans (hsB.trans hBS)) (hRW.trans (hsB.trans hBS)) hdelta
    ((hz 47).trans hBS) ((hz 313).trans hBS) ((hz 314).trans hBS)
  have hf := finishBound_le ts p.ringWidth p.rowWidth (nativePositions u y) z B
    (UniversalRowSourceBound.sourceBound (sourceWorkspace p S)) hz hE.1
  have ht := stageTypes_cost_le a S hS
  dsimp [nativeBudget,universalBudget]
  change Staging.cost 0 1 stageTypesOps a+_+_+finishBound ts _ _ _ z B ≤ _
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le_oai
