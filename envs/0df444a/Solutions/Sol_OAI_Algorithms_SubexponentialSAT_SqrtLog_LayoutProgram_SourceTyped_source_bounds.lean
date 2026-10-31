-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:44:04.516983+00:00
-- url     : https://prove2.me/submissions/7feb12cf-5b19-46fd-9982-cac0baf6eec7

import Mathlib
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

@[simp] theorem positions_length (s : Finset (Fin Q)) :
    (positions s).length = s.card := by
  rw [positions, List.length_map,
    ← List.toFinset_card_of_nodup (UniversalRowSource.selected_nodup s), selected_toFinset]

end SubexponentialSAT.Subexp.UniversalRowTableSource

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

/-- The scalar table and inverse tables have been materialized. The audited
emitter bound now applies to the actual finite row, including all reads. -/
theorem source_bounds_oai (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
    (hwidth : ∀ c,(encode c).length=width.length)
    (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q))
    (delta limit zero one : List Bool) (S : ℕ)
    (hQ : Q ≤ S) (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound (tables encode values inverse negative difference)
      width rowWidth (positions s) delta limit zero one ≤ UniversalRowSourceBound.sourceBound S ∧
    (UniversalRowProgram.rowCode zero one (zero++one)
      (UniversalRowDataProgram.row (tables encode values inverse negative difference)
        (positions s) delta limit)).length ≤ UniversalRowSourceBound.sourceLengthBound S := by
  exact UniversalRowSourceBound.source_bound_le _ width rowWidth (positions s)
    delta limit zero one S
    (tables_valid encode values inverse negative difference width rowWidth hwidth hrow s)
    ((positions_length_le s).trans hQ)
    (fun i hi => (positions_value_le s i hi).trans hQ) hw hr hd hl hz ho

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds_oai.{u_1}
