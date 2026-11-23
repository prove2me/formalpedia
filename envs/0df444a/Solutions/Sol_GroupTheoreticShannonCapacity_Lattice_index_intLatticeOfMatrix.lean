-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.index_intLatticeOfMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:59.369867+00:00
-- url     : https://prove2.me/submissions/0194279c-7269-4ff3-ae67-9d55757f5380

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_intLatticeOfMatrix_toSubmodule

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hdetA : A.det ≠ 0) :
    (intLatticeOfMatrix n A).index = A.det.natAbs := by
  -- Standard basis for ℤ^n
  let bE := Pi.basisFun ℤ (Fin n)
  -- The columns of A are linearly independent when det ≠ 0
  have hli : LinearIndependent ℤ A.col := Matrix.linearIndependent_cols_of_det_ne_zero hdetA
  -- Basis for the span of columns (using fully qualified name)
  let bSpan : Module.Basis (Fin n) ℤ (Submodule.span ℤ (Set.range A.col)) := Module.Basis.span hli
  -- The intLatticeOfMatrix equals the span of columns (via range of mulVecLin)
  have hrange : (intLatticeOfMatrix n A).toIntSubmodule = Submodule.span ℤ (Set.range A.col) := by
    rw [intLatticeOfMatrix_toSubmodule, Matrix.range_mulVecLin]
  -- Convert bSpan to a basis for the AddSubgroup
  let hbN : Module.Basis (Fin n) ℤ (intLatticeOfMatrix n A) :=
    bSpan.map (LinearEquiv.ofEq _ _ hrange.symm)
  -- Apply AddSubgroup.index_eq_natAbs_det
  rw [AddSubgroup.index_eq_natAbs_det bE (intLatticeOfMatrix n A) hbN]
  -- Now we need to show that bE.det (fun i => (hbN i).val) = A.det
  congr 1
  -- Use Pi.basisFun_det_apply: bE.det v = (Matrix.of v).det
  rw [Pi.basisFun_det_apply]
  -- Goal: (Matrix.of (fun x => (hbN x).val)).det = A.det
  -- The matrix of columns is actually Aᵀ, so use det(Aᵀ) = det(A)
  rw [← Matrix.det_transpose A]
  congr 1
  -- Show that the matrix formed equals Aᵀ
  ext i j
  simp only [Matrix.of_apply, Matrix.transpose_apply]
  -- Need: (hbN i).val j = A j i
  -- hbN i = (bSpan.map equiv) i, so (hbN i).val = (bSpan i).val by LinearEquiv.coe_ofEq_apply
  -- And (bSpan i).val = A.col i by Basis.span_apply
  -- So (hbN i).val j = A.col i j = A j i ✓
  simp only [hbN, Module.Basis.map_apply]
  -- Goal: ↑((LinearEquiv.ofEq ...) (bSpan i)) j = A j i
  -- By coe_ofEq_apply and span_apply, this equals A.col i j = A j i
  calc (↑((LinearEquiv.ofEq _ _ hrange.symm) (bSpan i)) : Fin n → ℤ) j
      = (↑(bSpan i) : Fin n → ℤ) j := congrFun (LinearEquiv.coe_ofEq_apply _ _) j
    _ = A.col i j := congrFun (congrArg Subtype.val (Module.Basis.span_apply hli i)) j
    _ = A j i := rfl
end GroupTheoreticShannonCapacity.Lattice
