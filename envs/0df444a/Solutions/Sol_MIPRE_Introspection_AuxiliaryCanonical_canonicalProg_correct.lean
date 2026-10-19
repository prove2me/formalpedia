-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:06.115138+00:00
-- url     : https://prove2.me/submissions/406dbe90-7ac8-4450-9c40-839a4872d86c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean (solution of MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_linearIndependent
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_insertRow_pivotBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- A raw XOR step is the corresponding operation on both typed vectors. -/
theorem reduceStep_rowBits {n t : ℕ} (r : Row n t) (p : Pivot n t) :
    reduceStep (rowBits r) (pivotBits p) = rowBits (typedReduceStep r p) := by
  unfold reduceStep pivotBits rowBits
  rw [getD_vectorBits]
  simp only [bit, decide_eq_true_eq, typedReduceStep]
  split_ifs
  · rw [xorBits_vectorBits, xorBits_vectorBits]
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- The entire executable reduction agrees with typed binary elimination. -/
theorem reduceRows_rowBits {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) :
    reduceRows (b.map pivotBits) (rowBits r) = rowBits (typedReduce b r) := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change reduceRows (b.map pivotBits) (reduceStep (rowBits r) (pivotBits p)) = _
    rw [reduceStep_rowBits, ih]
    rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
theorem firstOne_getD (v : BitStr) (h : firstOne v < v.length) :
    v.getD (firstOne v) false = true := by
  have hbit := List.findIdx_getElem (xs := v) (p := id) (w := h)
  change v[firstOne v]?.getD false = true
  rw [List.getElem?_eq_getElem h]
  exact hbit
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_pivot_zero (r : Row n t) (p : Pivot n t)
    (hp : p.2.1 p.1 = 1) : (typedReduceStep r p).1 p.1 = 0 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp only [typedReduceStep, h, if_true, Pi.add_apply, hp]
    decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_preserves_zero (r : Row n t) (p : Pivot n t) (j : Fin n)
    (hr : r.1 j = 0) (hp : p.2.1 j = 0) : (typedReduceStep r p).1 j = 0 := by
  unfold typedReduceStep
  split <;> simp [hr, hp]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduce_preserves_zero (b : List (Pivot n t)) (r : Row n t) (j : Fin n)
    (hr : r.1 j = 0) (hb : ∀ p ∈ b, p.2.1 j = 0) : (typedReduce b r).1 j = 0 := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (typedReduceStep_preserves_zero r p j hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
/-- Reducing against a triangular basis zeros all of its pivot coordinates. -/
theorem typedReduce_pivots_zero (b : List (Pivot n t)) (hb : IsPivotBasis b)
    (r : Row n t) : ∀ p ∈ b, (typedReduce b r).1 p.1 = 0 := by
  induction b generalizing r with
  | nil => simp
  | cons p b ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hq
    · subst q
      exact typedReduce_preserves_zero b (typedReduceStep r p) p.1
        (typedReduceStep_pivot_zero r p hb.1) hb.2.1
    · exact ih hb.2.2 (typedReduceStep r p) q hq
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem firstOne_vectorBits_one (v : Fin n → ZMod 2)
    (h : firstOne (vectorBits v) < n) : v ⟨firstOne (vectorBits v), h⟩ = 1 := by
  have hh := firstOne_getD (vectorBits v) (by simpa [vectorBits] using h)
  change (vectorBits v).getD (⟨firstOne (vectorBits v), h⟩ : Fin n) false = true at hh
  rw [getD_vectorBits] at hh
  simpa [bit] using hh
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Insertion maintains the triangular pivot invariant. -/
theorem IsPivotBasis.typedInsert {b : List (Pivot n t)} (hb : IsPivotBasis b) (r : Row n t) :
    IsPivotBasis (typedInsert b r) := by
  unfold MIPRE.LowDegree.BinaryLinear.typedInsert
  dsimp only
  split
  · rename_i h
    exact hb.append_reduced r _ (firstOne_vectorBits_one _ h)
  · exact hb
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_insertRow_pivotBits (rows : List (Row n t)) (b : List (Pivot n t)) :
    (rows.map rowBits).foldl insertRow (b.map pivotBits) =
      (rows.foldl typedInsert b).map pivotBits := by
  induction rows generalizing b with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.foldl_cons, insertRow_pivotBits, ih]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- The actual ambient program constructs precisely the typed binary basis. -/
theorem basisRowsProg_correct (rows : List (Row n t)) :
    basisRowsProg (rows.map rowBits) = (typedBasis rows).map pivotBits :=
  fold_insertRow_pivotBits rows []
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_typedInsert_isPivotBasis (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : IsPivotBasis b) : IsPivotBasis (rows.foldl typedInsert b) := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih => exact ih _ (hb.typedInsert r)
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem typedBasis_isPivotBasis (rows : List (Row n t)) : IsPivotBasis (typedBasis rows) :=
  fold_typedInsert_isPivotBasis rows [] trivial
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem leading_insert {b : List (Pivot n t)} (hb : Leading b) (r : Row n t) :
    Leading (typedInsert b r) := by
  unfold typedInsert
  dsimp only
  split
  · intro p hp i hi
    rcases List.mem_append.mp hp with hp | hp
    · exact hb p hp i hi
    · obtain rfl := List.mem_singleton.mp hp
      exact firstOne_vector_before _ i hi
  · exact hb
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem typedBasis_leading (rows : List (Row n t)) : Leading (typedBasis rows) := by
  suffices h : ∀ b, Leading b → Leading (rows.foldl typedInsert b) from h [] (by simp [Leading])
  induction rows with
  | nil => exact fun _ h => h
  | cons r rows ih => exact fun b hb => ih _ (leading_insert hb r)
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem pivot_one {b : List (Pivot n t)} (hb : IsPivotBasis b) (p : Pivot n t)
    (hp : p ∈ b) : p.2.1 p.1 = 1 := by
  induction b with
  | nil => simp at hp
  | cons q b ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hb.1
    · exact ih hb.2.2 hp
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem pivot_nodup {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    (b.map Prod.fst).Nodup := by
  induction b with
  | nil => simp
  | cons p b ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hb.2.2⟩
    intro hm
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    have hz := hb.2.1 q hq
    have ho := pivot_one hb.2.2 q hq
    rw [he] at ho
    exact zero_ne_one (hz.symm.trans ho)
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem pivotSpan_range (b : List (Pivot n t)) :
    pivotSpan b = Submodule.span (ZMod 2) (Set.range (pivotVectors b)) := by
  unfold pivotSpan
  congr 1
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    exact ⟨⟨i,hi⟩,by simpa [pivotVectors] using congrArg (fun p : Pivot n t => p.2.1) he⟩
  · rintro ⟨i,rfl⟩
    exact ⟨b[i],List.getElem_mem i.isLt,rfl⟩
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem finrank_pivotSpan {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    finrank (ZMod 2) (pivotSpan b) = b.length := by
  rw [pivotSpan_range,finrank_span_eq_card hb.linearIndependent,Fintype.card_fin]
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
/-- A leading nonzero coordinate of a subspace vector is a canonical pivot. -/
theorem leading_mem_pivots (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∈ S) (j : Fin n) (hj : v j ≠ 0)
    (hprev : ∀ i : Fin n, i < j → v i = 0) : j ∈ CL.pivots S := by
  have hm : v ∈ S ⊓ CL.tail (F := ZMod 2) n j.val :=
    ⟨hv,CL.mem_tail.mpr hprev⟩
  have hn : v ∉ S ⊓ CL.tail (F := ZMod 2) n (j.val+1) := by
    intro h
    exact hj (CL.mem_tail.mp h.2 j (Nat.lt_succ_self _))
  have hlt : S ⊓ CL.tail (F := ZMod 2) n (j.val+1) < S ⊓ CL.tail n j.val :=
    lt_of_le_of_ne (inf_le_inf_left _ (CL.tail_mono (Nat.le_succ _)))
      (fun he => hn (he ▸ hm))
  exact CL.mem_pivots.mpr (Submodule.finrank_lt_finrank_of_lt hlt)
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
/-- The program's stored pivot indices equal the source's canonical pivot set. -/
theorem pivot_set_canonical {b : List (Pivot n t)} (hb : IsPivotBasis b) (hl : Leading b) :
    (b.map Prod.fst).toFinset = CL.pivots (pivotSpan b) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact leading_mem_pivots (pivotSpan b) p.2.1 (Submodule.subset_span ⟨p,hp,rfl⟩)
      p.1 (by rw [pivot_one hb p hp]; exact one_ne_zero) (hl p hp)
  · rw [CL.card_pivots,finrank_pivotSpan hb,List.toFinset_card_of_nodup (pivot_nodup hb),
      List.length_map]
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem typedReduce_canonLin {b : List (Pivot n t)} (hb : IsPivotBasis b) (hl : Leading b)
    (r : Row n t) : (typedReduce b r).1 = CL.canonLin (pivotSpan b) r.1 := by
  have hm : (typedReduce b r).1 ∈ CL.canonCompl (pivotSpan b) := by
    intro j hj
    rw [← pivot_set_canonical hb hl] at hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact typedReduce_pivots_zero b hb r p hp
  have hs := reduce_sub_mem (pivotSpan b) b
    (fun p hp => Submodule.subset_span ⟨p,hp,rfl⟩) r
  have hz : CL.canonLin (pivotSpan b) (r.1-(typedReduce b r).1) = 0 := by
    exact (CL.ker_canonLin (pivotSpan b) ▸ hs : _ ∈ (CL.canonLin (pivotSpan b)).ker)
  rw [map_sub,show CL.canonLin (pivotSpan b) (typedReduce b r).1 = (typedReduce b r).1 from
    Submodule.projection_apply_of_mem_left (CL.isCompl_canonCompl (pivotSpan b)).symm hm] at hz
  exact (sub_eq_zero.mp hz).symm
end
end MIPRE.Introspection.AuxiliaryCanonical

namespace MIPRE.Introspection.AuxiliaryCanonical
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
/-- Canonical reduction for an arbitrary finite generating family. -/
theorem typedBasis_canonLin (rows : List (Row n t)) (v : Fin n → ZMod 2) :
    (typedReduce (typedBasis rows) (v,0)).1 = CL.canonLin (rowSpan rows) v := by
  rw [typedReduce_canonLin (typedBasis_isPivotBasis rows) (typedBasis_leading rows),typedBasis_span]
end
end MIPRE.Introspection.AuxiliaryCanonical

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryCanonical
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}
theorem _root_.solution (vs : List (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    canonicalProg (vs.map vectorBits,vectorBits v) =
      vectorBits (CL.canonLin (Submodule.span (ZMod 2) {x | x ∈ vs}) v) := by
  let rows : List (Row n 0) := vs.map (fun x => (x,0))
  have he : (vs.map vectorBits).map (fun x => (x,([] : BitStr))) = rows.map rowBits := by
    simp [rows,rowBits,vectorBits,List.map_map]
  change (reduceRows (basisRowsProg ((vs.map vectorBits).map (fun x => (x,([] : BitStr)))))
    (vectorBits v,[])).1 = _
  rw [he,basisRowsProg_correct]
  change (reduceRows ((typedBasis rows).map pivotBits) (rowBits (v,(0 : Fin 0 → ZMod 2)))).1 = _
  rw [reduceRows_rowBits]
  change vectorBits (typedReduce (typedBasis rows) (v,0)).1 = _
  rw [typedBasis_canonLin]
  congr 2
  unfold rowSpan rows
  congr 1
  ext x
  simp
end MIPRE.Introspection.AuxiliaryCanonical
