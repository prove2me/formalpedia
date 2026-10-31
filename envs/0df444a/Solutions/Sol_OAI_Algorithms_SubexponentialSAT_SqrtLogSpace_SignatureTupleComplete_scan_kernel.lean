-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:59:13.86789+00:00
-- url     : https://prove2.me/submissions/4da11ece-45e0-4521-a0c2-0b142fc5be57

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_naturalKey_eq_iff

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

theorem shift_value_integer (W N P : ℕ) (hNW : N ≤ W) :
    ((W-N+P : ℕ) : ℤ) = (W : ℤ) + ((P : ℤ)-(N : ℤ)) := by
  rw [Nat.cast_add, Int.natCast_sub hNW]
  ring

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWord_integer (W : List Bool) (a : SignedWord) (word : List Bool)
    (h : shiftedWord W a word)
    (hNW : SubexponentialSAT.BinaryArithmetic.toNat a.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W) :
    (SubexponentialSAT.BinaryArithmetic.toNat word : ℤ) = (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) +
      ((SubexponentialSAT.BinaryArithmetic.toNat a.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat a.2 : ℤ)) := by
  rw [h.1]
  exact shift_value_integer _ _ _ hNW

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The physical shifted rows retain every incidence and the exact emitted
column order, including empty matrices and empty heads. -/
theorem shiftedMatrix_typed (W : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B D : ℕ)
    (js : List ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys) :
    ∃ c : Fin D → Fin js.length → List Bool,
      ys = List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i, ∃ p, Rel j.val (js.get i) p ∧
        LayoutMatrixProgram.pairLength p ≤ B ∧ BucketProgram.shiftedWord W p (c j i) := by
  obtain ⟨hlen, hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hylen : ys.length = D := hy.length_eq.symm.trans hlen
  have hyrow : ∀ row ∈ ys, row.length = js.length :=
    BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  let rowAt (j : Fin D) : List (List Bool) := ys.get ⟨j.val, by omega⟩
  have hrowAt (j : Fin D) : (rowAt j).length = js.length :=
    hyrow _ (List.get_mem _ _)
  let c (j : Fin D) (i : Fin js.length) : List Bool :=
    (rowAt j).get ⟨i.val, by rw [hrowAt]; exact i.isLt⟩
  refine ⟨c, ?_, ?_⟩
  · apply List.ext_get
    · simp [hylen]
    · intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply List.ext_get
      · simp [← hrowAt ⟨j, by simpa using hj'⟩, rowAt]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        rfl
  · intro j i
    have hjraw : j.val < raw.length := by omega
    have hjrange : j.val < (List.range D).length := by simp
    have hrawrow := hr.get hjrange hjraw
    simp only [List.get_eq_getElem, List.getElem_range] at hrawrow
    have hshiftrow := hy.get hjraw (by omega)
    have hiraw : i.val < (raw.get ⟨j.val,hjraw⟩).length := by
      change i.val < (raw[j.val]'hjraw).length
      rw [← hrawrow.length_eq]
      exact i.isLt
    have hiy : i.val < (ys.get ⟨j.val,by omega⟩).length := by
      exact (hrowAt j).symm ▸ i.isLt
    have hp := hrawrow.get i.isLt hiraw
    have hs := hshiftrow.get hiraw hiy
    exact ⟨_, hp.1, hp.2, hs⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankFiber
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal equality between the runtime owner-fiber sum and an integer
matrix column. Both use the original incidence order and original owner IDs. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators

/-- The executable fiber scanner selects exactly the matching indices.
No nodup or arbitrary re-enumeration premise is needed. -/
theorem fiber_sum_ofFn {D : ℕ} (ps : Fin D → ℕ × ℕ) (value : ℕ → ℤ)
    (query start : ℕ) :
    ((LayoutOwnerFiberProgram.fiberIndices query start (List.ofFn ps)).map value).sum=
      ∑ i : Fin D,if (ps i).1=query then value (start+i.val) else 0 := by
  induction D generalizing start with
  | zero => simp [LayoutOwnerFiberProgram.fiberIndices]
  | succ D ih =>
      rw [List.ofFn_succ,LayoutOwnerFiberProgram.fiberIndices,Fin.sum_univ_succ]
      by_cases h : (ps 0).1=query
      · simp only [h,ite_true, if_true,List.map_cons,List.sum_cons]
        rw [ih]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp [Nat.add_left_comm,Nat.add_comm]
      · simp only [h,ite_false,zero_add]
        rw [ih]
        apply Finset.sum_congr rfl
        intro i _
        simp [Nat.add_left_comm,Nat.add_comm]

theorem fiber_sum_eq_matrix {D n : ℕ} (owner : Fin D → Fin n)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val)
    (entry : Fin D → Fin D → ℤ) (value : ℕ → ℕ → ℤ)
    (hv : ∀ j i,value j.val i.val=entry j i) (j : Fin D) (v : Fin n) :
    ((LayoutOwnerFiberProgram.fiberIndices v.val 0 (List.ofFn ps)).map (value j.val)).sum=
      fiberMatrix owner entry j v := by
  rw [fiber_sum_ofFn]
  unfold fiberMatrix
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.zero_add,hp,hv]
  have he : (owner i).val=v.val ↔ owner i=v := Fin.ext_iff.symm
  simp only [he]

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native fiber relation realizes the literal owner-sum matrix. Signed
component mass bounds imply both safe shifting and a signature-height bound. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q D n : ℕ}

theorem fiber_value_literal (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val)
    (j : Fin D) (v : Fin n) :
    ((LayoutOwnerFiberProgram.fiberIndices v.val 0 (List.ofFn ps)).map
      (entryNat P A R t j.val)).sum=LayoutProducedMatrix.literalNat P owner A R t j.val v.val := by
  rw [LayoutProducedMatrix.literalNat_fin]
  exact fiber_sum_eq_matrix owner ps hp (LayoutProgram.localEntry P A R t)
    (entryNat P A R t) (by intro j i; simp [entryNat]) j v

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Readout uses the full signed integer incidence coefficient. The physical
negative word is dominated by W because the native relation bounds both
components together, not merely the absolute difference. -/
theorem native_shifted_integer (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset) (j v : ℕ)
    (pair : LayoutMatrixProgram.Pair) (y : List Bool)
    (hp : s.relation j v pair) (hy : BucketProgram.shiftedWord W pair y) :
    (BinaryArithmetic.toNat y : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
      ((LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).map
        (BucketProgram.ProducedRank.entryNat s.packing s.height.length s.R s.node j)).sum := by
  have hmass : RowSelectionProgram.pairTotal pair.1 pair.2 ≤ s.offset := hp.2
  have hneg : BinaryArithmetic.toNat pair.2 ≤ BinaryArithmetic.toNat W := by
    rw [hW]
    unfold RowSelectionProgram.pairTotal at hmass
    omega
  have hshift := BucketProgram.shiftedWord_integer W pair y hy hneg
  have hvalue := hp.1
  change RowSelectionProgram.pairValue pair=_ at hvalue
  change (BinaryArithmetic.toNat y : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
    RowSelectionProgram.pairValue pair at hshift
  rw [hvalue] at hshift
  exact hshift

/-- Each typed physical coefficient is the literal owner-sum entry in the
actual ascending head order. Every original incidence row is retained. -/
theorem native_shiftedMatrix_typed (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset)
    (owner : Fin s.D → Fin s.n) (ps : Fin s.D → ℕ × ℕ)
    (hplans : s.plans=List.ofFn ps) (hp : ∀ i,(ps i).1=(owner i).val)
    (z : ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    ∃ c : Fin s.D → Fin (selectedHeads s.n s.rows s.low z).length → List Bool,
      shifted=List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
        LayoutProducedMatrix.literalNat s.packing owner s.height.length s.R s.node
          j.val ((selectedHeads s.n s.rows s.low z).get i) := by
  obtain ⟨c,hc,hentry⟩ := shiftedMatrix_typed W s.relation s.columnLength s.D
    (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  refine ⟨c,hc,?_⟩
  intro j i
  obtain ⟨pair,hpair,_,hshift⟩ := hentry j i
  have hv : (selectedHeads s.n s.rows s.low z).get i < s.n :=
    HeadIdentifierProgram.chosenIds_bound _ _ _ (List.get_mem _ _)
  have hvalue := native_shifted_integer s W hW j.val _ pair (c j i) hpair hshift
  rw [hplans] at hvalue
  exact hvalue.trans (congrArg (fun x : ℤ => (BinaryArithmetic.toNat W : ℤ)+x)
    (BucketProgram.ProducedRank.fiber_value_literal s.packing owner s.height.length s.R
      s.node ps hp j ⟨_,hv⟩))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Equality of the physically generated whole keys is exactly equality of
full integer signatures. Candidate indices are unchanged. -/
theorem shifted_key_kernel (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset)
    (owner : Fin s.D → Fin s.n) (ps : Fin s.D → ℕ × ℕ)
    (hplans : s.plans=List.ofFn ps) (hp : ∀ i,(ps i).1=(owner i).val)
    (z : ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted)
    (i j : Fin (2^(selectedHeads s.n s.rows s.low z).length)) :
    AttainedSignatureProgram.Rescan.naturalKey W shifted
        (selectedHeads s.n s.rows s.low z).length i=
      AttainedSignatureProgram.Rescan.naturalKey W shifted
        (selectedHeads s.n s.rows s.low z).length j ↔
      AttainedSignatures.integerKey (integerMatrix s owner z) i=
        AttainedSignatures.integerKey (integerMatrix s owner z) j := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.native_shiftedMatrix_typed s W hW
    owner ps hplans hp z raw shifted hr hy
  rw [hc]
  exact AttainedSignatureProgram.Rescan.naturalKey_eq_iff W c (integerMatrix s owner z) hentry i j


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace ProducedSource

theorem offset_value (s : ProducedSource) : BinaryArithmetic.toNat (s.source.stacks 141)=s.input.offset :=
  s.ready.offset

end ProducedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

/-- Every probe compares exactly the literal full integer signature of this
head; the finite-key model has no invented coordinate tuples. -/
theorem scan_kernel_oai (s : ProducedSource) (depth : ℕ)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
      (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted)
    (i j : Fin (2^s.headSize depth)) :
    AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) i=
      AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) j ↔
      s.key depth i=s.key depth j :=
  shifted_key_kernel s.input (s.source.stacks 141) s.offset_value s.owner s.plans
    s.plans_eq s.owners_eq (s.base+depth) raw shifted hr hy i j

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel_oai
