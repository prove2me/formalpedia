-- Prove2me | solution 1 for MIPRE.tensorFamily_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:34.884952+00:00
-- url     : https://prove2.me/submissions/ac1bee68-f5f9-4d0d-aff9-b81fe8bb23a9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (solution of MIPRE.tensorFamily_mul_self);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Definitions.Def_MIPRE_Foundations_TensorFamily

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
variable {k : ℕ} {ι : Type*}
theorem _root_.solution [Fintype ι] {M : Fin k → Matrix ι ι ℂ} (h : ∀ i, M i * M i = M i) :
    tensorFamily M * tensorFamily M = tensorFamily M := by
  rw [tensorFamily_mul]; congr 1; funext i; exact h i
end MIPRE
