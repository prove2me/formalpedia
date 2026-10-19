-- Prove2me | solution 1 for OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:45.812419+00:00
-- url     : https://prove2.me/submissions/139b8671-8dcd-4ccd-8071-9c1565bcea44

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}
theorem solution [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  obtain ⟨H, ⟨h, hc⟩, hs, hg⟩ := hH
  classical
  let g : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hgh : ∀ j, ((g j : ℤ) : ℝ) = h j := by
    intro j
    have := hs 0 j
    rw [hc, sub_zero] at this
    simp only [g]
    rcases this with h1 | h1
    · simp [h1]
    · have : h j ≠ 1 := by rw [h1]; norm_num
      simp [h1]; norm_num
  have hHg : H = (rowCirculant g).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [rowCirculant, hc, hgh]
  refine ⟨g, fun j => ?_, ?_⟩
  · simp only [g]; split_ifs
    · left; rfl
    · right; rfl
  · ext i j
    have := congrFun (congrFun hg i) j
    rw [hHg] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at this ⊢
    split_ifs at this ⊢
    · have h2 : ((∑ x, rowCirculant g i x * rowCirculant g j x : ℤ) : ℝ) = ((n : ℤ) : ℝ) := by
        push_cast; simpa using this
      simpa using (Int.cast_injective h2)
    · have h2 : ((∑ x, rowCirculant g i x * rowCirculant g j x : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
        push_cast; simpa using this
      simpa using (Int.cast_injective h2)
