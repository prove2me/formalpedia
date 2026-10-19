-- Prove2me | solution 1 for MIPRE.tensorFamily_star
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:57.175188+00:00
-- url     : https://prove2.me/submissions/ad73f996-d085-490a-9928-59dc9a80bb34

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (solution of MIPRE.tensorFamily_star);
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
theorem tensorFamily_conjTranspose (M : Fin k → Matrix ι ι ℂ) :
    (tensorFamily M)ᴴ = tensorFamily fun i => (M i)ᴴ := by
  ext v w
  simp only [Matrix.conjTranspose_apply, tensorFamily_apply, star_prod]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
variable {k : ℕ} {ι : Type*}
theorem _root_.solution {M : Fin k → Matrix ι ι ℂ} (h : ∀ i, star (M i) = M i) :
    star (tensorFamily M) = tensorFamily M := by
  rw [Matrix.star_eq_conjTranspose, tensorFamily_conjTranspose]; congr 1; funext i
  rw [← Matrix.star_eq_conjTranspose]; exact h i
end MIPRE
