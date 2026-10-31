-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:40:56.31812+00:00
-- url     : https://prove2.me/submissions/5d68d0b1-2f94-4bb3-9bb7-c48d17369207

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_finish_universal_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_native_mismatch_branch
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram_Native_tableProgram_runsIn

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

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

theorem action_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (action v pr tmp op) (actionCost op a) a (actionResult v pr op a) := by
  cases op with
  | copy src dst => exact TupleProgram.copy_eval src dst tmp v pr hv.1 hv.2.1 hv.2.2 hvp a ht
  | clear dst => exact TupleProgram.clear_eval dst v pr a
  | push dst b => exact TupleProgram.pushConst_eval dst v b a

theorem action_temp (v pr : Fin r) (tmp : Fin s)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    (actionResult v pr op a).stacks tmp=[] := by
  cases op with
  | copy src dst => simp [actionResult,StackRoutines.copyStacks,hv.2.2,ht]
  | clear dst => by_cases h : tmp=dst <;> simp [actionResult,StackRoutines.clearStacks,h,ht]
  | push dst b => simp only [Action.Valid] at hv; simp [actionResult,TupleProgram.pushedState,hv,ht]

theorem sequence_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (ops : List (Action s)) (a : State r s)
    (hv : ∀ op∈ops,op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (sequence v pr tmp ops) (cost v pr ops a) a (result v pr ops a) := by
  induction ops generalizing a with
  | nil => exact .base (.skip _)
  | cons op ops ih =>
    have hop := hv op (by simp)
    exact (action_eval v pr tmp hvp op a hop ht).seq
      (ih (actionResult v pr op a) (fun x hx=>hv x (by simp [hx]))
        (action_temp v pr tmp op a hop ht))

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact joint-membership meaning of the three selected-color comparisons. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

theorem anchorValid_iff_joint (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    anchorValid i t u y ↔ u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i := by
  simp [anchorValid, and_assoc]

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageTypes_valid : ∀ op∈stageTypesOps,op.Valid (319:Fin 320) := by decide
theorem stageTypes_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval stageTypes (Staging.cost 0 1 stageTypesOps a) a (Staging.result 0 1 stageTypesOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) stageTypesOps a stageTypes_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

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

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem vectorPorts_inj : Function.Injective vectorPorts := Fin.castAdd_injective _ _

/-- This premise is an actual execution of the fixed native scalar-table
producer. It is supplied by Native.tableProgram_runsIn, never by a value oracle. -/
theorem vector_lifted (a : Data) (bits : List Bool) (rf : Fin 16 → Bool) {n : ℕ}
    (he : Trace LayoutSourceValuesProgram.Native.tableProgram n
      ((projectState id vectorPorts a).withPC (some LayoutSourceValuesProgram.Native.tableProgram.entry))
      ((⟨rf,Function.update (projectState id vectorPorts a).stacks 67 bits⟩ : State 16 256).withPC none)) :
    ∃ b : Data, Eval vector n a b ∧ b.stacks=Function.update a.stacks 67 bits ∧ b.regs=rf := by
  let z : State 16 256 := ⟨rf,Function.update (projectState id vectorPorts a).stacks 67 bits⟩
  let b := embedState id vectorPorts a z
  refine ⟨b,eval_call_from_state _ id vectorPorts a Function.injective_id vectorPorts_inj he,?_,?_⟩
  · change Function.extend vectorPorts z.stacks a.stacks=_
    dsimp only [z]
    rw [ProgramLinking.extend_update vectorPorts_inj]
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id vectorPorts a Function.injective_id vectorPorts_inj)
    change Function.extend vectorPorts (projectState id vectorPorts a).stacks a.stacks=a.stacks at h
    rw [h]
    rfl
  · funext j
    exact embedState_register id vectorPorts a z Function.injective_id j

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem prepend_cleanup {first second : Code} {n m : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval (.seq second cleanup) m b c) :
    Eval (.seq (.seq first second) cleanup) (n+m) a c := by
  cases hs with
  | seq hg hc => simpa [Nat.add_assoc] using (hf.seq hg).seq hc

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem clearedStacks_eq (a b : Data)
    (h : ∀ j,j∉cleanupPorts → b.stacks j=a.stacks j) : clearedStacks b=clearedStacks a := by
  funext j
  by_cases hj : j∈cleanupPorts <;> simp [clearedStacks,hj,h]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition for the actual SourceBank. Premises about table and mismatch
execution are traces of their fixed native programs, not free callbacks. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem branch_cleared (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    clearedStacks (branchState a rf bits indices)=clearedStacks a := by
  apply clearedStacks_eq
  intro j hj
  have hn (i : Fin 320) (hi : i∈cleanupPorts) : j≠i := by
    intro he; subst j; exact hj hi
  simp [branchState,stageTypes_stacks a h23 h24,
    hn 23 (by decide),hn 24 (by decide),hn 67 (by decide),hn 71 (by decide)]

theorem branch_sourceWord (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (tables : UniversalRowLoop.Tables) (positions : List ℕ) :
    sourceWord tables positions (branchState a rf bits indices)=
      UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
        (UniversalRowDataProgram.row tables positions
          (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47)) := by
  simp [sourceWord,deltaWord,branchState,stageTypes_stacks a h23 h24]

/-- Fully measured prepare/native-table/native-mismatch/compare/emitter/cleanup
composition, with an exact frame on every caller stack. -/
theorem universal_cleanup_eval (a : Data) (ht : a.stacks 319=[])
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (bits indices : List Bool) (rv rm : Fin 16 → Bool) (nv nm : ℕ)
    (hvector : Trace LayoutSourceValuesProgram.Native.tableProgram nv
      ((projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).withPC
        (some LayoutSourceValuesProgram.Native.tableProgram.entry))
      ((⟨rv,Function.update (projectState id vectorPorts
        (Staging.result 0 1 stageTypesOps a)).stacks 67 bits⟩ : State 16 256).withPC none))
    (hmismatch : Eval mismatches nm (vectorState a rv bits) (branchState a rm bits indices))
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hclean : EmitterClean (branchState a rm bits indices))
    (h274 : (branchState a rm bits indices).stacks 274=[])
    (h0 : (branchState a rm bits indices).stacks 0=[])
    (h1 : (branchState a rm bits indices).stacks 1=[])
    (h2 : (branchState a rm bits indices).stacks 2=[])
    (h3 : (branchState a rm bits indices).stacks 3=[])
    (hv : bits=tables.values.flatten)
    (hi : a.stacks 308=tables.inverses.flatten) (hn : a.stacks 309=tables.negatives.flatten)
    (hr : a.stacks 310=tables.rows.flatten)
    (hp : indices=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,((branchState a rm bits indices).stacks j).length ≤ B) :
    ∃ n ≤ Staging.cost 0 1 stageTypesOps a+nv+nm+
        finishBound tables width rowWidth positions (branchState a rm bits indices) B,
      ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287
          (sourceWord tables positions (branchState a rm bits indices)) := by
  let p := Staging.result 0 1 stageTypesOps a
  obtain ⟨q,hq,hqs,hqr⟩ := vector_lifted p bits rv hvector
  have hqeq : q=vectorState a rv bits := SubexpScanPrimitives.state_ext hqr hqs
  rw [hqeq] at hq
  let z := branchState a rm bits indices
  have hz319 : z.stacks 319=[] := by
    simp [z,branchState,stageTypes_stacks a h23 h24,ht]
  obtain ⟨nf,hnf,b,hf,hbs⟩ := finish_universal_eval z hz319 hclean h274 h0 h1 h2 h3
    tables width rowWidth positions valid
    (by simpa [z,branchState] using hv)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hi)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hn)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hr)
    (by simpa [z,branchState] using hp)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hw)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hrw) B hB
  have he := prepend_cleanup (stageTypes_eval a ht)
    (prepend_cleanup hq (prepend_cleanup hmismatch hf))
  dsimp only [z] at hnf
  refine ⟨Staging.cost 0 1 stageTypesOps a+(nv+(nm+nf)),by omega,b,he,?_⟩
  simpa only [z,branch_cleared a rm bits indices h23 h24] using hbs

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

/-- Translate the relational loop certificate to the emitter's per-node
getD interface without assuming an input scalar table. -/
theorem generated_word_at {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words)
    (node : Fin Q) :
    ∃ out : ModelCode t d, words.getD node.val [] = RingProgram.flat out ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value A R node u y : ℤ) : a.O t) := by
  have hw : node.val < words.length := by simp [hlen]
  have h := hvalid.get (by simp) hw
  simp only [List.get_eq_getElem,List.getElem_range',Nat.zero_add,Nat.one_mul] at h
  obtain ⟨hj,out,he,hv⟩ := h
  refine ⟨out,?_,?_⟩
  · rw [List.getD_eq_getElem words [] hw]
    exact he
  · exact hv

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT MulticolorTypes SubexpSymbolicCost IntegerRingLiftProgram

theorem sourceValue_scaled {C O : Type*} [CommRing O] {r Q : ℕ}
    (ops : RepresentedRing C O) (integerWord : ℤ → C)
    (hinteger : ∀ z, ops.decode (integerWord z) = (z : O)) (invDenom : C)
    (A R : ℕ) (node : Fin Q) (u y : UniversalType r Q 1) :
    ops.decode (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y node) =
      -ops.decode invDenom * ((LayoutProgram.Numerator.value A R node u y : ℤ) : O) := by
  unfold LayoutProgram.sourceValue
  by_cases h : Subexp.MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) node u y
  · rw [ite_eq_left ((Subexp.MatrixExtendedEntryProgram.anchorValid_iff_joint (0 : Fin 1) node u y).mp h)]
    simp [LayoutProgram.Numerator.value,h,
ops.neg_correct,ops.mul_correct,hinteger,neg_mul]
  · have hj : ¬(u ∈ joint node (y.head node) (0 : Fin 1) ∧ y ∈ joint node (y.head node) (0 : Fin 1)) :=
      fun hj => h ((Subexp.MatrixExtendedEntryProgram.anchorValid_iff_joint (0 : Fin 1) node u y).mpr hj)
    rw [ite_eq_right hj]
    simp [LayoutProgram.Numerator.value,h,
ops.zero_correct]

/-- The generated byte table consists of actual model codes, in node order.
This witness can be passed to typed source-expression and row constructors. -/
theorem generated_codes {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words) :
    ∃ codes : Fin Q → ModelCode t d,
      words = List.ofFn (fun node => RingProgram.flat (codes node)) ∧
      ∀ node, (RingProgram.modelRing t ht hd a M cache).decode (codes node) =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value A R node u y : ℤ) : a.O t) := by
  classical
  choose codes hbytes hvalues using
    (fun node => generated_word_at A R t ht hd a M cache invDenom u y words hlen hvalid node)
  refine ⟨codes,?_,hvalues⟩
  apply List.ext_getElem (by simp [hlen])
  intro j hj hj'
  have h := hbytes ⟨j,by omega⟩
  rw [List.getD_eq_getElem words [] hj] at h
  simpa using h

/-- Typed source values obtained from the executed table, without a supplied
table or a free byte-decoding premise. -/
theorem generated_source_codes {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z, (RingProgram.modelRing t ht hd a M cache).decode (integerWord z) = (z : a.O t))
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words) :
    ∃ codes : Fin Q → ModelCode t d,
      words = List.ofFn (fun node => RingProgram.flat (codes node)) ∧
      ∀ node, (RingProgram.modelRing t ht hd a M cache).decode (codes node) =
        (RingProgram.modelRing t ht hd a M cache).decode
          (LayoutProgram.sourceValue (RingProgram.modelRing t ht hd a M cache).program
            integerWord invDenom A R u 0 y node) := by
  obtain ⟨codes,hwords,hvalues⟩ := generated_codes A R t ht hd a M cache invDenom u y words hlen hvalid
  refine ⟨codes,hwords,fun node => ?_⟩
  rw [hvalues,sourceValue_scaled _ integerWord hinteger]

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

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

theorem branch_emitterClean (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (hc : EmitterClean a) :
    EmitterClean (branchState a rf bits indices) := by
  intro j hj hk hn
  have h23' : j≠23 := by intro h; subst j; norm_num at hj
  have h24' : j≠24 := by intro h; subst j; norm_num at hj
  have h67' : j≠67 := by intro h; subst j; norm_num at hj
  have h71' : j≠71 := by intro h; subst j; norm_num at hj
  simpa [branchState,stageTypes_stacks a h23 h24,h23',h24',h67',h71'] using hc j hj hk hn

/- Exact prepare/call/export/cleanup trace with actual generated model codes.
Only the already prepared arithmetic and node caches are inputs. -/
theorem native_universal_cleanup_eval_oai {r Q d : ℕ}
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (as : List Bool) (R : ℕ) (start : Fin Q) (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power=(2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd model M cache).decode zero=0)
    (hone : (RingProgram.modelRing t ht hd model M cache).decode one=1)
    (hminus : (RingProgram.modelRing t ht hd model M cache).decode minusOne= -1)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z,(RingProgram.modelRing t ht hd model M cache).decode (integerWord z)=
      (z:model.O t))
    (a : Data) (htemp : a.stacks 319=[]) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (ready : CachedReady t model M cache zero one minusOne
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks)
    (hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
      RingProgram.flat invDenom)
    (hinput : ∀ i,(projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
      (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _=>false) start u y [] [] ([],[])).stacks i)
    (hq : (a.stacks 22).length=Q) (h37 : a.stacks 37=[])
    (h64 : a.stacks 64=[]) (h65 : a.stacks 65=[]) (h67 : a.stacks 67=[]) (h71 : a.stacks 71=[])
    (hc : EmitterClean a) (h274 : a.stacks 274=[])
    (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[]) (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (inverse negative : Fin Q → ModelCode t d) (difference : Fin Q → Fin Q → ModelCode t d)
    (ringWidth rowWidth : List Bool) (hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t)
    (hrowWidth : rowWidth.length=Q*ringWidth.length)
    (hi : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (inverse i))).flatten)
    (hn : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (negative i))).flatten)
    (hr : a.stacks 310=(List.ofFn (fun i=>
      (List.ofFn (fun j=>RingProgram.flat (difference i j))).flatten)).flatten)
    (hw : a.stacks 311=ringWidth) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ codes : Fin Q → ModelCode t d,
      (∀ node,(RingProgram.modelRing t ht hd model M cache).decode (codes node)=
        (RingProgram.modelRing t ht hd model M cache).decode
          (sourceValue (RingProgram.modelRing t ht hd model M cache).program
            integerWord invDenom as.length R u 0 y node)) ∧
      ∃ n ≤ Staging.cost 0 1 stageTypesOps a+
          LayoutSourceValuesProgram.Native.tableBudget as.length R width.length (pairLength power) t d u y+
          (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
            UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
          finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
            ringWidth rowWidth (nativePositions u y)
            (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
              (nativeIndices u y))
            (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length),
        ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
          b.stacks=Function.update (clearedStacks a) 287
            (UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
              (UniversalRowDataProgram.row
                (SourceTyped.tables RingProgram.flat codes inverse negative difference)
                (nativePositions u y)
                (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47))) := by
  let p := projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)
  have hpfield (j : Fin 256) (hj23 : j≠23) (hj24 : j≠24) :
      p.stacks j=a.stacks (vectorPorts j) := by
    have hn23 : vectorPorts j≠23 := by
      intro h; apply hj23; apply vectorPorts_inj; exact h
    have hn24 : vectorPorts j≠24 := by
      intro h; apply hj24; apply vectorPorts_inj; exact h
    simp [p,projectState,stageTypes_stacks a h23 h24,hn23,hn24]
  obtain ⟨words,rv,hwlen,hwsize,hwvalid,nv,hnv,hvector⟩ :=
    LayoutSourceValuesProgram.Native.tableProgram_runsIn Hwords width power as R start u y
      hlen hwords hvalues hp hpt hwidth hAQ hQ t ht hd model M cache hz
      zero one minusOne invDenom hzero hone hminus p.stacks ready hinv hinput
      (by simpa [hpfield 22 (by decide) (by decide),vectorPorts] using hq)
      (by simpa [hpfield 37 (by decide) (by decide),vectorPorts] using h37)
      (by simpa [hpfield 64 (by decide) (by decide),vectorPorts] using h64)
      (by simpa [hpfield 65 (by decide) (by decide),vectorPorts] using h65)
      (by simpa [hpfield 67 (by decide) (by decide),vectorPorts] using h67) p.regs
  obtain ⟨codes,hcodes,hmeaning⟩ := LayoutSourceValuesProgram.Native.generated_source_codes
    as.length R t ht hd model M cache invDenom integerWord hinteger u y words hwlen hwvalid
  let tables := SourceTyped.tables RingProgram.flat codes inverse negative difference
  obtain ⟨nm,hnm,rm,hmismatch⟩ := native_mismatch_branch a
    (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as) start u y
    words.flatten rv h23 h24 h71 hinput
  have hvalid : UniversalRowLoop.Valid tables ringWidth rowWidth (nativePositions u y) := by
    rw [nativePositions_eq]
    exact SourceTyped.tables_valid RingProgram.flat codes inverse negative difference ringWidth rowWidth
      (fun c=>(RingProgram.flat_length c).trans hringWidth.symm) hrowWidth _
  have hsize : words.flatten.length=Q*(d*SubexpLiftRing.baseWidth 3 t) := by
    rw [List.length_flatten]
    have hmap : words.map List.length=List.replicate words.length (d*SubexpLiftRing.baseWidth 3 t) :=
      List.map_eq_replicate_iff.mpr hwsize
    simp only [hmap,List.sum_replicate,hwlen,smul_eq_mul]
  have hzfield (j : Fin 320) (hj23 : j≠23) (hj24 : j≠24) (hj67 : j≠67) (hj71 : j≠71) :
      (branchState a rm words.flatten (nativeIndices u y)).stacks j=a.stacks j := by
    simp [branchState,stageTypes_stacks a h23 h24,hj23,hj24,hj67,hj71]
  obtain ⟨n,hnfinal,b,he,hbs⟩ := universal_cleanup_eval a htemp h23 h24 words.flatten
    (nativeIndices u y) rv rm nv nm hvector hmismatch tables ringWidth rowWidth (nativePositions u y)
    hvalid (branch_emitterClean a rm _ _ h23 h24 hc)
    (by simpa [hzfield 274 (by decide) (by decide) (by decide) (by decide)] using h274)
    (by simpa [hzfield 0 (by decide) (by decide) (by decide) (by decide)] using h0)
    (by simpa [hzfield 1 (by decide) (by decide) (by decide) (by decide)] using h1)
    (by simpa [hzfield 2 (by decide) (by decide) (by decide) (by decide)] using h2)
    (by simpa [hzfield 3 (by decide) (by decide) (by decide) (by decide)] using h3)
    (by simp [tables,SourceTyped.tables,hcodes]) hi hn
    (by
      rw [hr]
      simp [tables, SourceTyped.tables, UniversalRowLoop.Tables.rows]
      rfl)
    (nativeIndices_eq u y) hw hrw (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length)
    (by simpa only [hsize] using branch_length_le a rm words.flatten (nativeIndices u y) h23 h24 B hB)
  refine ⟨codes,hmeaning,n,?_,b,he,?_⟩
  · have hwordsflat := congrArg List.flatten hcodes
    rw [hwordsflat] at hnfinal
    have hfinish : finishBound tables ringWidth rowWidth (nativePositions u y)
        (branchState a rm (List.ofFn (fun node => RingProgram.flat (codes node))).flatten
          (nativeIndices u y))
        (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length) =
      finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
        ringWidth rowWidth (nativePositions u y)
        (branchState a (fun _ => false) (List.ofFn (fun node => RingProgram.flat (codes node))).flatten
          (nativeIndices u y))
        (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length) := rfl
    rw [hfinish] at hnfinal
    omega
  · simpa only [branch_sourceWord a rm words.flatten (nativeIndices u y) h23 h24 tables (nativePositions u y)] using hbs

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval_oai
