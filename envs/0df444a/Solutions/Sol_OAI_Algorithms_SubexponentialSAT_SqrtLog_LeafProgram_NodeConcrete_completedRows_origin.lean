-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:03:28.321345+00:00
-- url     : https://prove2.me/submissions/885f43ad-2c0c-4474-8318-18db30523fff

import Mathlib
import Definitions.Def_OAIQ081S181

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramBlockCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal block-lookup and incidence-fiber circuits for the ring source rows.
The branches are exactly those implemented by the packing metadata lookup;
this file identifies their polynomial meanings without any field assumption. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpRowInterpolation SubexponentialSAT.SubexpTaylorExecution
open LayoutPullback

variable {I U C O : Type*} [Fintype I] [DecidableEq I]
  [Fintype U] [DecidableEq U] [CommRing O]

omit [Fintype I] in
theorem packedValue_eq (P : PackingData I U) (rows : U → U → Polynomial O) (v w : I) :
    packedValue P rows v w = LayoutBlocks.assembledRow P.completeBlocks rows v w := by
  cases hv : P.lookup v with
  | none =>
      rw [LayoutBlocks.assembledRow_outside _ _ _ ((P.lookup_none_iff v).mp hv)]
      simp only [packedValue, hv]
      split_ifs <;> simp
  | some z =>
      rcases z with ⟨j,u⟩
      have hv' := (P.lookup_some_iff v (j,u)).mp hv
      rw [← hv', LayoutBlocks.assembledRow_apply]
      cases hw : P.lookup w with
      | none =>
          have hout : w ∉ Set.range (P.completeBlocks.blockEmbedding j) := by
            rintro ⟨a,ha⟩
            exact (P.lookup_none_iff w).mp hw ⟨(j,a),ha⟩
          rw [row_eq_zero _ _ _ hout]
          simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hw]
      | some z =>
          rcases z with ⟨k,y⟩
          have hw' := (P.lookup_some_iff w (k,y)).mp hw
          rw [← hw']
          by_cases hj : j = k
          · subst k
            change packedValue P rows (P.completeBlocks.embed (j,u))
              (P.completeBlocks.embed (j,y)) = _
            rw [show P.completeBlocks.embed (j,y) = P.completeBlocks.blockEmbedding j y from rfl,
              row_apply_injective _ (P.completeBlocks.blockEmbedding j).injective]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at,
              SubexponentialSAT.BlockPacking.CompleteBlocks.blockEmbedding]
          · have hout : P.completeBlocks.embed (k,y) ∉
                Set.range (P.completeBlocks.blockEmbedding j) := by
              rintro ⟨a,ha⟩
              have he := P.completeBlocks.embed.injective ha
              exact hj (congrArg Prod.fst he)
            rw [row_eq_zero _ _ _ hout]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hj]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

theorem fiber_sum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner index : ℕ) (value : ℕ → A) :
    ((LayoutOwnerFiberProgram.fiberIndices owner index ps).map value).sum=
      ((ps.zipIdx index).map (fun x => if x.1.1=owner then value x.2 else 0)).sum := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=owner <;>
        simp [LayoutOwnerFiberProgram.fiberIndices,h,ih]

theorem ownerSum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A) :
    ownerSum ps owner value=
      ((ps.zipIdx).map (fun x => if x.1.1=owner then value x.2 else 0)).sum :=
  fiber_sum_zipIdx ps owner 0 value

theorem ownerSum_pullback [AddCommMonoid A] {n : ℕ} (ps : Fin n → ℕ × ℕ)
    (owner : ℕ) (value : ℕ → A) :
    ownerSum (List.ofFn ps) owner value=
      LayoutPullback.row (fun i : Fin n => (ps i).1) (fun i => value i.val) owner := by
  have hzip : (List.ofFn ps).zipIdx=List.ofFn (fun i : Fin n => (ps i,i.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [ownerSum_zipIdx,hzip]
  simp [LayoutPullback.row,List.map_ofFn,List.sum_ofFn]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Total original-coordinate source family computed by the native controller.
The missing-incidence branch is zero; required factor-scope incidences use
the exact packed row selected by the actual plan lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem sourceRowFamily_present {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ)
    (h : (literal,ambient+factor) ∈ ps) :
    sourceRowFamily ps ambient factor literal source owner=
      ownerSum ps owner (source (ps.idxOf (literal,ambient+factor))) := by
  simp [sourceRowFamily,h]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source rows used by the native factor callback retain their concrete
origin, degree, and original-coordinate support after incidence pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly

variable {r Q d : ℕ}

theorem packed_origin (p : SourceBank.Parameters r Q d) {D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (i j : Fin D) :
    (packedValue P p.rows i j).eval 0 = if j=i then 1 else 0 := by
  rw [packedValue_eq]
  exact (copied p P).row_origin i j

/-- Repeated incidences are allowed. The actual first matching lookup selects
one Kronecker row, whose owner is still the original literal. -/
theorem fixedSourceRow_origin (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) (hj : (j,n+f) ∈ ps) :
    (fixedSourceRow p ps P n f j v).eval 0 = if v.val=j then 1 else 0 := by
  let i : Fin ps.length := ⟨ps.idxOf (j,n+f), by
    simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr hj⟩
  have hi : ps.get i = (j,n+f) := by
    simpa only [i,List.idxOf,beq_eq_decide] using
      List.idxOf_get (List.idxOf_lt_length_iff.mpr hj)
  have hr : fixedSourceRow p ps P n f j v =
      LayoutPullback.row (fun a : Fin ps.length => (ps.get a).1)
        (fun a => packedValue P p.rows i a) v.val := by
    unfold fixedSourceRow
    rw [sourceRowFamily_present _ _ _ _ _ _ hj]
    have hs := ownerSum_pullback (fun a : Fin ps.length => ps.get a) v.val
      (totalPackedSource p P i.val)
    rw [List.ofFn_get] at hs
    rw [hs]
    congr 1
    funext a
    simp only [totalPackedSource,packedSourceValue,dite_eq_left i.isLt,dite_eq_left a.isLt]
  rw [hr]
  simp only [LayoutPullback.row,Polynomial.eval_finsetSum,apply_ite,
    Polynomial.eval_zero]
  simp_rw [packed_origin]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, if_true,hi]
    by_cases hv : v.val=j
    · simp only [hv,ite_true, if_true]
    · have hv' : j ≠ v.val := Ne.symm hv
      simp only [hv,hv',ite_false]
  · intro a _ hai
    simp [hai]
  · simp

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A total source target with the original variable IDs. Missing incidences
are filled by identity rows only in this mathematical totalization; scoped
factor evaluation never reads those rows. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

theorem completedRows_origin_oai (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j v : ResidualEmbedding.Free H) :
    (completedRows p ps P H f j.val v).eval 0 = if v=j then 1 else 0 := by
  by_cases hj : (j.val.val,n+f)∈ps
  · simp only [completedRows,ite_eq_left hj]
    rw [fixedSourceRow_origin p ps P n f j.val.val v.val hj]
    simp only [Subtype.ext_iff,Fin.ext_iff]
  · simp only [completedRows,ite_eq_right hj,Polynomial.eval_C,Subtype.ext_iff]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin_oai
