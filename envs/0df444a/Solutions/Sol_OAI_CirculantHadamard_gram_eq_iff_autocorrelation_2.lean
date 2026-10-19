-- Prove2me | solution 2 for OAI.CirculantHadamard.gram_eq_iff_autocorrelation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:12:30.445707+00:00
-- url     : https://prove2.me/submissions/100d97d8-439a-4c8c-9e3e-23a792c97ef6

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean:L47-L66
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.gram_eq_iff_autocorrelation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Theorems.Thm_OAI_CirculantHadamard_rowCirculant_gram_apply

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

/-- The full Gram equation is exactly the cyclic autocorrelation system. -/
theorem gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  classical
  constructor
  · intro hGram a
    have ha := congrArg (fun M : Matrix (Fin n) (Fin n) R => M 0 a) hGram
    rw [rowCirculant_gram_apply] at ha
    simpa [Matrix.smul_apply, Matrix.one_apply, eq_comm] using ha
  · intro hCorr
    ext i a
    rw [rowCirculant_gram_apply, hCorr]
    by_cases hia : i = a
    · subst a
      simp
    · have hai : a - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hia)
      simp [hia, hai, Matrix.smul_apply]

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.gram_eq_iff_autocorrelation.{uR} := @_root_.OAI.CirculantHadamard.gram_eq_iff_autocorrelation.{uR}
