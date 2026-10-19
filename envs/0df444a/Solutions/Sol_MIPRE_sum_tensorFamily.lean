-- Prove2me | solution 1 for MIPRE.sum_tensorFamily
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:25.819229+00:00
-- url     : https://prove2.me/submissions/631224f3-c4d7-423e-8bc1-b2efa9209382

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (solution of MIPRE.sum_tensorFamily);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Definitions.Def_MIPRE_Foundations_TensorFamily

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
variable {k : ℕ} {ι : Type*}
theorem _root_.solution {A : Type*} [Fintype A] (M : Fin k → A → Matrix ι ι ℂ) :
    ∑ a : Fin k → A, tensorFamily (fun i => M i (a i)) = tensorFamily fun i => ∑ a, M i a := by
  ext v w
  simp only [Matrix.sum_apply, tensorFamily_apply]
  rw [Fintype.prod_sum]
end MIPRE
