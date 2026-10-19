-- Prove2me | solution 1 for MIPRE.LCS.Pauli.X_anticomm_Z
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:38:54.049603+00:00
-- url     : https://prove2.me/submissions/3a59090d-b0fd-4084-bb0f-ed67b0bfb6e3

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Pauli.lean (solution of MIPRE.LCS.Pauli.X_anticomm_Z);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Pauli

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma X_mul_Z : X * Z = (-Complex.I) • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma Z_mul_X : Z * X = Complex.I • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]
end
end MIPRE.LCS.Pauli

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LCS.Pauli
open Matrix
open scoped Kronecker
theorem _root_.solution : X * Z = -(Z * X) := by
  rw [Z_mul_X, X_mul_Z]
  simp
end MIPRE.LCS.Pauli
