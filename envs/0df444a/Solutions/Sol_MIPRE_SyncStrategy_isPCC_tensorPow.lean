-- Prove2me | solution 1 for MIPRE.SyncStrategy.isPCC_tensorPow
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:43.338975+00:00
-- url     : https://prove2.me/submissions/43a1c522-00fe-4f0a-986d-e4503bc6f04a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TensorPower.lean (solution of MIPRE.SyncStrategy.isPCC_tensorPow);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Matrix
variable {k : ℕ} {ι : Type*}
theorem tensorFamily_mul [Fintype ι] (M N : Fin k → Matrix ι ι ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun i => M i * N i := by
  ext v w
  simp only [Matrix.mul_apply, tensorFamily_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm
end
end MIPRE

namespace MIPRE.SyncStrategy
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {H : SynchronousGame X A}
/-- A positive product weight has positive factors. -/
theorem μ_pos_of_repeat_pos {k : ℕ} {x y : Fin k → X} (h : 0 < (H.repeat k).μ x y) (i : Fin k) :
    0 < H.μ (x i) (y i) := by
  rcases (H.μ_nonneg (x i) (y i)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have : (H.repeat k).μ x y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) heq.symm
    rw [this] at h
    exact lt_irrefl 0 h
end
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SyncStrategy
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {H : SynchronousGame X A}
theorem _root_.solution {S : SyncStrategy H} (hS : S.IsPCC) (k : ℕ) : (S.tensorPow k).IsPCC := by
  intro x y hxy a b
  have hpos := μ_pos_of_repeat_pos hxy
  have h : ∀ i, S.P.M (x i) (a i) * S.P.M (y i) (b i) = S.P.M (y i) (b i) * S.P.M (x i) (a i) :=
    fun i => hS _ _ (hpos i) _ _
  change ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M x a *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M y b =
    ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M y b *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M x a
  rw [ProjectiveMeasurement.reindexMat_M, ProjectiveMeasurement.reindexMat_M,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ProjectiveMeasurement.tensorPow_M,
    ProjectiveMeasurement.tensorPow_M, tensorFamily_mul, tensorFamily_mul]
  congr 2
  funext i
  exact h i
end MIPRE.SyncStrategy
