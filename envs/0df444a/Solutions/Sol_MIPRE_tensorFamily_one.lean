-- Prove2me | solution 1 for MIPRE.tensorFamily_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:25.075394+00:00
-- url     : https://prove2.me/submissions/118ea41f-c140-43bb-b7ba-475e9d490ce7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (solution of MIPRE.tensorFamily_one);
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
theorem _root_.solution [DecidableEq ι] : tensorFamily (fun _ : Fin k => (1 : Matrix ι ι ℂ)) = 1 := by
  ext v w
  simp only [tensorFamily_apply, Matrix.one_apply, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  by_cases h : v = w
  · subst h; simp
  · have h' : ¬ ∀ i, v i = w i := fun h' => h (funext h')
    simp [h, h']
end MIPRE
