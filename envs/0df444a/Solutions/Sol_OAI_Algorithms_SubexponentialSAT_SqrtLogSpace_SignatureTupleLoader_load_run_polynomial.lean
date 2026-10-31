-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:01:28.734948+00:00
-- url     : https://prove2.me/submissions/630448b2-0596-48f6-a3c0-f24d27956941

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadLoaderBudgets_leafWork_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_nonoutput_length
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_outputs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_native_leafFrom_run_space

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

theorem shiftedWords_totalLength {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) :
    (ys.map List.length).sum ≤ preOutputLength W xs := by
  induction h with
  | nil => simp [preOutputLength]
  | cons h hs ih =>
      simp only [List.map_cons,List.sum_cons,preOutputLength] at *
      exact Nat.add_le_add h.2 ih

theorem preWords_length (ys : List (List Bool)) :
    (words ys).length=2*(ys.map List.length).sum+ys.length := by
  induction ys with
  | nil => simp [words]
  | cons y ys ih => simp [words,Encoding.length_frame,ih]; omega

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_lengths {W : List Bool} {rows : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys) :
    rows.length=ys.length ∧ ((ys.map words).map List.length).sum ≤ preMatrixPayload W rows := by
  induction h with
  | nil => simp [preMatrixPayload]
  | cons h hs ih =>
      have hl := shiftedWords_totalLength h
      have hn := shiftedWords_length h
      simp only [List.length_cons,List.map_cons,List.sum_cons,preWords_length,preMatrixPayload] at *
      constructor <;> omega

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

theorem preStepCost_le (W : List Bool) (a : SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hP : a.1.length ≤ L) (hN : a.2.length ≤ L) :
    preStepCost W a ≤ 6000*(L+1)^2 := by
  have hsum : W.length+a.2.length+a.1.length+1 ≤ 3*L+1 := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  dsimp [preStepCost]
  nlinarith

theorem preRow_inputs (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preScanCost W xs ≤ (xs.length+1)*(6000*(L+1)^2+2) ∧
    preOutputLength W xs ≤ xs.length*(3*L+1) ∧
    (signedWords xs).length ≤ xs.length*(4*L+2) := by
  induction xs with
  | nil => simp [preScanCost,preOutputLength,signedWords]
  | cons a xs ih =>
      have ha := hb a (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      have hc := preStepCost_le W a L hW ha.1 ha.2
      rcases a with ⟨P,N⟩
      simp only [preScanCost,preOutputLength,List.map_cons,List.sum_cons,
        List.length_cons,signedWords,List.length_append,Encoding.length_frame] at *
      constructor
      · nlinarith [ht.1]
      constructor
      · nlinarith [ht.2.1]
      · nlinarith [ht.2.2]

theorem preRowCost_le (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preRowCost W xs ≤ 7000*(xs.length+1)*(L+1)^2 := by
  have h := preRow_inputs W xs L hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left xs.length hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left xs.length hs
  dsimp [preRowCost]
  nlinarith [h.1,h.2.1]

theorem preMatrixStepCost_le (W : List Bool) (row : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L row) :
    preMatrixStepCost W row ≤ 8000*(row.length+1)*(L+1)^2 := by
  have h := preRow_inputs W row L hW hb
  have hr := preRowCost_le W row L hW hb
  have hlin : 4*L+2 ≤ 4*(L+1)^2 := by nlinarith
  have hlin' : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left row.length hlin
  have hh' := Nat.mul_le_mul_left row.length hlin'
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left row.length hs
  dsimp [preMatrixStepCost]
  nlinarith [h.2.1,h.2.2]

theorem preMatrix_inputs (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixScanCost W rows ≤ (rows.length+1)*(8000*(h+1)*(L+1)^2+2) ∧
    preMatrixPayload W rows ≤ rows.length*(2*h*(3*L+1)+h) := by
  induction rows with
  | nil => simp [preMatrixScanCost,preMatrixPayload]
  | cons row rows ih =>
      have hr := hb row (by simp)
      have ht := ih (fun r hr' => hb r (by simp [hr']))
      have hc := preMatrixStepCost_le W row L hW hr.1
      have hc' : preMatrixStepCost W row ≤ 8000*(h+1)*(L+1)^2 :=
        hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
      have hl := (preRow_inputs W row L hW hr.1).2.1
      have hl' := Nat.mul_le_mul_right (3*L+1) hr.2
      simp only [preMatrixScanCost,preMatrixPayload,List.map_cons,List.sum_cons,List.length_cons] at *
      constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

theorem write_length (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    (write mask j bit).length = mask.length := by
  simp [write, List.length_take, List.length_drop, Nat.min_eq_left hj.le]
  omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem scatter_length (js : List ℕ) (bits mask : List Bool)
    (hb : ∀ j ∈ js, j < mask.length) :
    (scatter js bits mask).length = mask.length := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have ht : ∀ k ∈ js, k < (write mask j b).length := by
            intro k hk; rw [hw]; exact hb k (by simp [hk])
          exact (ih bits _ ht).trans hw

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

theorem mask_length (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hb : ∀ j ∈ js, j < n) : (mask n js bits).length = n := by
  simpa [mask] using scatter_length js bits (List.replicate n false) (by simpa using hb)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem indices_length_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    (indices js).length ≤ js.length*(2*n+2)+1 := by
  induction js with
  | nil => simp [indices,ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [indices,List.map_cons,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.length_cons,List.length_append,Encoding.length_frame, id_eq, unary,List.length_replicate]
      change 2*j+1+(indices js).length+1 ≤ (js.length+1)*(2*n+2)+1
      nlinarith

end SubexponentialSAT.SqrtLog.HeadScatterProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

theorem encodedIds_length_bound (p : ℕ → Bool) (n : ℕ) :
    (HeadScatterProgram.indices (chosenIds p n)).length ≤ n*(2*n+2)+1 := by
  calc
    _ ≤ (chosenIds p n).length*(2*n+2)+1 :=
      HeadScatterProgram.indices_length_bound n _ (chosenIds_bound p n)
    _ ≤ n*(2*n+2)+1 := Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*n+2) (count_le p n)) 1

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

variable {I : Type*} [Fintype I] [DecidableEq I] {A N r Q : ℕ}

theorem chosenIds_bound (p : ℕ → Bool) (N : ℕ) : ∀ f ∈ chosenIds p N, f < N := by
  intro f hf
  exact List.mem_range.mp (List.mem_of_mem_filter hf)

theorem encodedIds_length_bound (p : ℕ → Bool) (N : ℕ) :
    (ProgramEncoding.encodeRecords ((chosenIds p N).map Encoding.encodeNat)).length ≤
      1 + (2 * N + 2) * N := by
  have h := ProgramEncoding.encodeRecords_length_le
    ((chosenIds p N).map Encoding.encodeNat) N (by
      intro payload hp
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      simpa using Nat.succ_le_of_lt (chosenIds_bound p N f hf))
  have hc : (chosenIds p N).length ≤ N := by
    simpa [chosenIds] using List.length_filter_le p (List.range N)
  simp only [List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) 1)

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem headOutputs_protected : ∀ p ∈ headOutputs,Protected p.2 := by simp [headOutputs,Protected,temporary]

theorem headResult_count (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (headResult a n rows low W z).stacks 651=
      zeros (HeadIdentifierProgram.count (HeadIdentifierProgram.predicate rows low z) n) := by
  exact returned_word id (by decide) headInputs headOutputs a _ headOutputs_protected
    (by decide) (1,651) (by simp [headOutputs])

theorem factorResult_frame (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h671 : i≠671) :
    (factorResult a A N rows W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) factorInputs factorOutputs a _ i hi
  intro p hp
  simp only [factorOutputs,List.mem_singleton] at hp
  subst p
  exact h671

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countOutputs_protected : ∀ p∈countOutputs,Protected p.2 := by simp [countOutputs,Protected,temporary]

theorem countResult_value (a : Data) : (countResult a).stacks 652=List.replicate (a.stacks 651).length true :=
  returned_word countRegs (by decide) countInputs countOutputs a _ countOutputs_protected
    (by decide) (1,652) (by simp [countOutputs])

theorem scatterResult_frame (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ)
    (i : Fin 768) (hi : Protected i) (h670 : i≠670) :
    (scatterResult a regs n js).stacks i=a.stacks i := by
  apply returned_frame scatterRegs (by decide) scatterInputs scatterOutputs a _ i hi
  intro p hp
  simp only [scatterOutputs,List.mem_singleton] at hp
  subst p
  exact h670

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
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

theorem shiftOutputs_protected : ∀ p∈shiftOutputs,Protected p.2 := by
  simp [shiftOutputs,Protected,temporary]

private theorem forallTwo_member {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {y : β} (hy : y∈ys) :
    ∃ x∈xs,R x y := by
  induction h with
  | nil => simp at hy
  | cons hxy ht ih =>
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ⟨_,by simp,hxy⟩
      · obtain ⟨x,hx,hr⟩ := ih hy
        exact ⟨x,by simp [hx],hr⟩

theorem raw_pair_bounds {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∀ row∈rows,BucketProgram.preWordsBounded B row := by
  intro row hrow p hp
  obtain ⟨j,_,hjr⟩ := forallTwo_member hr hrow
  obtain ⟨v,_,hvp⟩ := forallTwo_member hjr hp
  have hlen := hvp.2
  unfold LayoutMatrixProgram.pairLength at hlen
  exact ⟨by omega,by omega⟩

/-- The retained shifted matrix has D rows and every original head column.
Its size depends on physical coefficient word lengths, not their integer values. -/
theorem shifted_matrix_word_length (W : List Bool) {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys) :
    (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)).length ≤
      D*(12*js.length*(B+W.length)+6*js.length+1) := by
  have hpairs := raw_pair_bounds hr
  obtain ⟨hrows,hwrows⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hinputs := BucketProgram.preMatrix_inputs W rows (B+W.length) js.length
    (Nat.le_add_left _ _) (by
      intro row hrow
      refine ⟨?_,(hwrows row hrow).le⟩
      intro pair hpair
      have h := hpairs row hrow pair hpair
      exact ⟨h.1.trans (Nat.le_add_right _ _),h.2.trans (Nat.le_add_right _ _)⟩)
  obtain ⟨hlen,hpayload⟩ := BucketProgram.shiftedMatrix_lengths hy
  rw [BucketProgram.preWords_length,List.length_map,←hlen,hrows]
  rw [hrows] at hinputs
  nlinarith [hinputs.2]


theorem localResult_countWord (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 652 =
      List.replicate (selectedHeads n rows low z).length true := by
  unfold localResult
  simp only [clearState, Function.update_of_ne (by decide : (652 : Fin 768) ≠ 669)]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ 652
    (by decide) (by simp [shiftOutputs])]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ 652
    (by decide) (by simp [rawOutputs])]
  rw [preparedHead, factorResult_frame _ _ _ _ _ _ 652 (by decide) (by decide),
    scatterResult_frame _ _ _ _ 652 (by decide) (by decide), countResult_value,
    headResult_count]
  simp [zeros, selectedHeads, HeadIdentifierProgram.count]

theorem localResult_matrixWord (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 668 =
      Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) := by
  unfold localResult
  simp only [clearState, Function.update_of_ne (by decide : (668 : Fin 768) ≠ 669)]
  exact returned_word shiftRegs (by decide) shiftInputs shiftOutputs _ _
    shiftOutputs_protected (by decide) (15,668) (by simp [shiftOutputs])

/-- A fixed output envelope is reused at every head reload; caller storage
enters only through max, not through a recurrent enlargement. -/
theorem localResult_retained_bound (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z A D B L : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (ha : WordBound A a) (hW : (a.stacks 141).length ≤ L)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted) :
    WordBound (max A (retainedOutputBound n N D B L))
      (localResult a rp rm rs n N W z rows low raw shifted) := by
  obtain ⟨h650,h651,h670,h671⟩ := localResult_outputs a rp rm rs n N W z rows low raw shifted
  have hj : (selectedHeads n rows low z).length ≤ n := Bounds.selectedHeads_length n rows low z
  have hsmall : n ≤ retainedOutputBound n N D B L := by
    have hn : n ≤ n*(2*n+2) := by
      calc
        n = n*1 := (Nat.mul_one _).symm
        _ ≤ n*(2*n+2) := Nat.mul_le_mul_left n (by omega)
    unfold retainedOutputBound
    omega
  have hmatrix := shifted_matrix_word_length (a.stacks 141) hr hy
  have hproduct : 12*(selectedHeads n rows low z).length*(B+(a.stacks 141).length) ≤
      12*n*(B+L) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 12 hj) (Nat.add_le_add_left hW B)
  have hm : (Subexp.MatrixProgramSupport.words
      (shifted.map Subexp.MatrixProgramSupport.words)).length ≤
      D*(12*n*(B+L)+6*n+1) := hmatrix.trans (Nat.mul_le_mul_left D (by omega))
  have hmax : retainedOutputBound n N D B L ≤ max A (retainedOutputBound n N D B L) :=
    Nat.le_max_right _ _
  intro i
  by_cases hi : i = 650
  · subst i
    rw [h650]
    exact (HeadIdentifierProgram.encodedIds_length_bound
      (HeadIdentifierProgram.predicate rows low z) n).trans (by
        apply le_trans _ hmax
        unfold retainedOutputBound
        omega)
  by_cases hi' : i = 651
  · subst i
    rw [h651, List.length_replicate]
    exact (hj.trans hsmall).trans hmax
  by_cases hi'' : i = 652
  · subst i
    rw [localResult_countWord, List.length_replicate]
    exact (hj.trans hsmall).trans hmax
  by_cases hm' : i = 668
  · subst i
    rw [localResult_matrixWord]
    exact hm.trans (by apply le_trans _ hmax; unfold retainedOutputBound; omega)
  by_cases hh : i = 670
  · subst i
    rw [h670, HeadScatterProgram.mask_length n (selectedHeads n rows low z) _
      (HeadIdentifierProgram.chosenIds_bound (HeadIdentifierProgram.predicate rows low z) n)]
    exact hsmall.trans hmax
  by_cases hf : i = 671
  · subst i
    rw [h671]
    exact (LeafHeadFactorsProgram.encodedIds_length_bound
      (LeafHeadFactorsProgram.predicate rows n z) N).trans (by
        apply le_trans _ hmax
        unfold retainedOutputBound
        omega)
  exact ((localResult_nonoutput_length a rp rm rs n N W z rows low raw shifted i
    hi hi' hi'' hm' hh hf).trans (ha i)).trans (Nat.le_max_left _ _)


theorem addressStateFrom_value (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks 649=a.stacks src := by
  simp only [addressStateFrom,copyState,StackRoutines.copyStacks,Function.update_self,
    clearMany_stacks, hs, show (649:Fin 896)∈[649,659,846,847] by decide,
    ite_false, ite_true, if_true, List.append_nil]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem addressStateFrom_wordBound (src : Fin 896) (a : State 16 896) (A : ℕ)
    (hs : src∉([649,659,846,847] : List (Fin 896))) (ha : WordBound A a) :
    WordBound A (addressStateFrom src a) := by
  have hc := clearMany_wordBound [649,659,846,847] a A ha
  intro i
  by_cases hi : i=649
  · subst i
    rw [addressStateFrom_value src a hs]
    exact ha src
  · simpa only [addressStateFrom,copyState_frame _ _ _ _ hi] using hc i

/-- Export copies into the destination already emptied by address setup. -/
theorem exportedState_wordBound (a : State 16 896) (B : ℕ)
    (h847 : a.stacks 847 = []) (ha : WordBound B a) :
    WordBound B (exportedState a) := by
  apply clearMany_wordBound [668,669,846] _ B
  have hc := clearState_wordBound 659 a B ha
  intro i
  by_cases hi : i = 847
  · subst i
    simpa [copyState, StackRoutines.copyStacks, clearState, h847] using ha 668
  · rw [copyState_frame _ _ _ _ hi]
    exact hc i

theorem lowResultFrom_empty847 (src : Fin 896) (a : State 16 896) (b : Data) :
    (lowResultFrom src a b).stacks 847 = [] := by
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b 847 (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 847 at hv
    have := j.isLt
    omega)]
  simp only [addressStateFrom, copyState_frame _ _ _ _
    (by decide : (847 : Fin 896) ≠ 649), clearMany_stacks,
    show (847 : Fin 896) ∈ [649,659,846,847] by decide, ite_true, if_true]

theorem exportedLowResultFrom_wordBound (src : Fin 896) (a : State 16 896) (b : Data)
    (A B : ℕ) (hs : src ∉ ([649,659,846,847] : List (Fin 896)))
    (hAB : A ≤ B) (ha : WordBound A a) (hb : WordBound B b) :
    WordBound B (exportedState (lowResultFrom src a b)) := by
  have had := addressStateFrom_wordBound src a A hs ha
  have hl : WordBound B (lowResultFrom src a b) :=
    embedState_wordBound id lowStacks (addressStateFrom src a) b B lowStacks.injective
      (fun i => (had i).trans hAB) hb
  exact exportedState_wordBound _ B (lowResultFrom_empty847 src a b) hl

theorem leafInputFrom_wordBound (src : Fin 896) (frame : State 40 896) (A : ℕ)
    (hs : src ∉ ([649,659,846,847] : List (Fin 896))) (ha : WordBound A frame) :
    WordBound A (leafInputFrom src frame) := by
  have had := addressStateFrom_wordBound src (projectState leafRegs id frame) A hs
    (fun i => ha i)
  intro i
  exact had (lowStacks i)

theorem leafOutputFrom_wordBound (src : Fin 896) (frame : State 40 896) (b : Data)
    (A B : ℕ) (hs : src ∉ ([649,659,846,847] : List (Fin 896)))
    (hAB : A ≤ B) (ha : WordBound A frame) (hb : WordBound B b) :
    WordBound B (leafOutputFrom src frame b) := by
  have he := exportedLowResultFrom_wordBound src (projectState leafRegs id frame) b A B hs hAB
    (fun i => ha i) hb
  intro i
  have hstack : (leafOutputFrom src frame b).stacks i =
      (exportedState (lowResultFrom src (projectState leafRegs id frame) b)).stacks i :=
    embedState_stack leafRegs id frame _ Function.injective_id i
  rw [hstack]
  exact he i


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

private theorem eval_loadHead_of_trace
    (p : Program 40 896 (StructuredCalls.size (SignatureHeadLoader.commandFrom headAddress) + 1))
    (hp : SignatureHeadLoader.programFrom headAddress = p)
    {steps : ℕ} {a b : State 40 896}
    (h : Trace p steps (a.withPC (some p.entry)) (b.withPC none)) :
    Eval loadHead steps a b := by
  have hc : loadHead = .call (SignatureHeadLoader.programFrom headAddress) := rfl
  have hcp : loadHead = .call p :=
    hc.trans (congrArg (fun q => Cmd.call q) hp)
  rw [hcp]
  exact .call p h

/-- The retained bound is restored exactly; the transient loader envelope is
never fed into the next boundary bound. -/
theorem result_wordBound (s : Native.Inputs) (z F L : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hf : WordBound F frame) (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted) :
    WordBound F (result s z frame rp rm rs raw shifted) := by
  have hin := SignatureHeadLoader.leafInputFrom_wordBound headAddress frame F (by decide) hf
  have hw : (SignatureHeadLoader.leafInputFrom headAddress frame).stacks 141=frame.stacks 141 :=
    SignatureHeadLoader.addressStateFrom_frame headAddress _ 141 (by decide)
  have hb := SignatureHeadLoader.localResult_retained_bound
    (SignatureHeadLoader.leafInputFrom headAddress frame) rp rm rs s.n s.N (s.Q*s.r) z F s.D
    s.columnLength L s.rows s.low raw shifted s.relation hin (by simpa only [hw] using hW)
    hr (by simpa only [hw] using hy)
  rw [Nat.max_eq_left hout] at hb
  exact SignatureHeadLoader.leafOutputFrom_wordBound headAddress frame _ F F
    (by decide) le_rfl hf hb

/-- The complete loader run is obtained from actual native inputs and paid
cache values. No successful matrix execution is an input to this theorem. -/
theorem load_run (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks headAddress=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval loadHead total frame (result s z frame rp rm rs raw shifted) ∧
      total≤36*F+22*(SignatureHeadLoader.localWork s z F+1)+35 ∧
      WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom headAddress) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry)) intermediate →
        dataBits intermediate≤1000*(F+(SignatureHeadLoader.localWork s z F+1)+1) := by
  obtain ⟨rp,rm,rs,raw,shifted,total,ht,htr,hr,hy,hprefix⟩ :=
    SignatureHeadLoader.native_leafFrom_run_space headAddress s a ha ra rd rc words hw frame hm
      z F (by decide) hz hf
  refine ⟨rp, rm, rs, raw, shifted, total, ?_, ht, ?_, hr, hy, hprefix⟩
  · have hpack : ∃ output,
        output = result s z frame rp rm rs raw shifted ∧
        Trace (SignatureHeadLoader.programFrom headAddress) total
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry))
          (output.withPC none) := by
      refine ⟨_, ?_, htr⟩
      rw [result]
    obtain ⟨_, rfl, hresult⟩ := hpack
    generalize hp : SignatureHeadLoader.programFrom headAddress = p at hresult
    exact eval_loadHead_of_trace p hp hresult
  · exact result_wordBound s z F L frame rp rm rs raw shifted hf hW hout hr hy

theorem load_run_polynomial_oai (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (B : ℕ) (hB : WordBound B a) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks headAddress=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval loadHead total frame (result s z frame rp rm rs raw shifted) ∧
      total ≤ runEnvelope B F ∧ WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom headAddress) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry)) intermediate →
        dataBits intermediate ≤ runEnvelope B F := by
  obtain ⟨rp,rm,rs,raw,shifted,total,he,ht,hbound,hraw,hshift,hprefix⟩ :=
    load_run s a ha ra rd rc words hw frame hm z F L hz hf hW hout
  have hzF : z≤F := by simpa [hz,unary] using hf headAddress
  have hbudget := HeadLoaderBudgets.leafWork_le s a B F z ha hB hrows hzF
  let C := 10000000000000000*HeadLoaderBudgets.sizeCoefficient^8
  let X := (F+B+2)^64
  have hX : 1≤X := one_le_pow₀ (by omega)
  have hFX : F≤X := by
    apply (show F≤F+B+2 by omega).trans
    simpa only [pow_one] using pow_le_pow_right₀ (show 1≤F+B+2 by omega) (by decide : 1≤64)
  have hsmall : C*X ≤ runEnvelope B F := by
    change C*X≤1000*(C+3)*X
    exact Nat.mul_le_mul_right X (by omega)
  have hlocal : SignatureHeadLoader.localWork s z F≤C*X := by
    change 36*F+22*(SignatureHeadLoader.localWork s z F+1)+35≤C*X at hbudget
    omega
  refine ⟨rp,rm,rs,raw,shifted,total,he,(ht.trans hbudget).trans hsmall,
    hbound,hraw,hshift,?_⟩
  intro p q hp hq
  apply (hprefix p q hp hq).trans
  change 1000*(F+(SignatureHeadLoader.localWork s z F+1)+1)≤1000*(C+3)*X
  calc
    _≤1000*(X+C*X+2*X) := by omega
    _=1000*(C+3)*X := by
      have hfactor (x c : ℕ) : 1000*(x+c*x+2*x)=1000*(c+3)*x := by ring
      exact hfactor X C

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial_oai
