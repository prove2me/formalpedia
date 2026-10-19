-- Prove2me | solution 2 for OAI.CirculantHadamard.rowCirculant_gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:11:06.351265+00:00
-- url     : https://prove2.me/submissions/94d94f03-25bd-4e60-bc4b-d0244c7aa9bd

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean:L30-L45
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.rowCirculant_gram_apply. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

-- ---- from OAI.LinearAlgebra.CirculantHadamard.MatrixBridge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR

/-!
# From real sign matrices to integer cyclic autocorrelation

The Gram entry is reindexed using translation in `Fin n`. The real/integer
bridge uses the injective coefficient map `ℤ → ℝ`; it does not assume any
classification or any group-ring norm statement.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- The Gram entry at `(i,a)` is the cyclic autocorrelation at `a-i`. -/
theorem rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := fun j => sub_add_cancel j i
      right_inv := fun j => add_sub_cancel_right j i }
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  apply Fintype.sum_equiv e
  intro j
  change h (j - i) * h (j - a) = h (j - i) * h ((j - i) - (a - i))
  simp only [sub_sub_sub_cancel_right]

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.rowCirculant_gram_apply.{uR} := @_root_.OAI.CirculantHadamard.rowCirculant_gram_apply.{uR}
