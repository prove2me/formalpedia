-- Prove2me | solution 2 for OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:13:56.267604+00:00
-- url     : https://prove2.me/submissions/74992713-101c-49f2-849c-dd41fe835a3e

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean:L113-L136
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

-- ---- from OAI.LinearAlgebra.CirculantHadamard.MatrixBridge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- Casting the integer Gram matrix agrees entry by entry with taking the
Gram matrix after casting the row. -/
theorem intCast_gram_apply (h : Fin n → ℤ) (i j : Fin n) :
    ((rowCirculant h * (rowCirculant h).transpose) i j : ℝ) =
      (rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant, Int.cast_sum,
    Int.cast_mul]

private theorem intCast_scaled_identity_apply (i j : Fin n) :
    (((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℝ) =
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- The real coefficient embedding preserves and reflects the entire Gram
identity, including the diagonal value. -/
theorem gram_intCast_iff (h : Fin n → ℤ) :
    rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose =
        (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor
  · intro hGram
    ext i j
    apply Int.cast_injective (α := ℝ)
    rw [intCast_gram_apply, intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram
  · intro hGram
    ext i j
    rw [← intCast_gram_apply, ← intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hGram

/-- A real sign matrix determines an integer sign row without approximation. -/
theorem ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  classical
  rcases hH with ⟨H, ⟨h, hrow⟩, hsign, hGram⟩
  have hsignRow : ∀ j, IsSign (h j) := by
    intro j
    simpa only [hrow, sub_zero] using hsign 0 j
  let z : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hzcast : ∀ j, (z j : ℝ) = h j := by
    intro j
    by_cases hj : h j = 1
    · simp [z, hj]
    · have hneg := (hsignRow j).resolve_left hj
      simp only [z, ite_eq_right hj, Int.cast_neg, Int.cast_one, hneg]
  have hzsign : ∀ j, IsSign (z j) := by
    intro j
    dsimp [z, IsSign]
    split_ifs <;> simp
  have hzH : rowCirculant (fun j => (z j : ℝ)) = H := by
    ext i j
    rw [rowCirculant_apply, hzcast, hrow]
  refine ⟨z, hzsign, (gram_intCast_iff z).mp ?_⟩
  simpa only [hzH] using hGram

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow := @_root_.OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow
