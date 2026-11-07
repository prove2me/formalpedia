-- Prove2me | solution 1 for ModernConvex.Relaxations.posSemidef_iff_schurStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:57:16.357429+00:00
-- url     : https://prove2.me/submissions/c8ccf816-1232-4b53-95e9-d25d2fa6999f

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm
import Definitions.Def_ModernConvex_SchurStep
import Theorems.Thm_ModernConvex_Relaxations_quadform_eq_schurForm
import Theorems.Thm_ModernConvex_Relaxations_schurForm_extendAt

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The Schur form does not depend on the `i`-th coordinate of `v`. -/
theorem schurForm_update_local {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : Fin n → ℝ) (s : ℝ) :
    schurForm M i (Function.update v i s) = schurForm M i v := by
  have h : ∀ j ∈ Finset.univ.erase i, Function.update v i s j = v j := by
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) s v
  have hinner : ∀ j ∈ Finset.univ.erase i,
      (∑ k ∈ Finset.univ.erase i, Function.update v i s j * (M j k * Function.update v i s k))
        = ∑ k ∈ Finset.univ.erase i, v j * (M j k * v k) := by
    intro j hj
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h j hj, h k hk]
  have houter : ∀ j ∈ Finset.univ.erase i, M i j * Function.update v i s j = M i j * v j := by
    intro j hj
    rw [h j hj]
  simp only [schurForm]
  rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl houter]

/-- **The Schur step, on the level of positive semidefiniteness.** At a positive pivot, `M` is
positive semidefinite exactly when its Schur complement at that pivot is. -/
theorem posSemidef_iff_schurStep_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) :
    M.PosSemidef ↔ (schurStep M i).PosSemidef := by
  constructor
  · -- reject: a negative direction for the Schur complement extends to one for `M`
    intro hS
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨schurStep_isHermitian hM i, fun w => ?_⟩
    set c : ℝ := -(M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * extendAt i w j) with hc
    have hkill : c + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i,
        M i j * Function.update (extendAt i w) i c j) = 0 := by
      have hfix : ∀ j ∈ Finset.univ.erase i,
          Function.update (extendAt i w) i c j = extendAt i w j := by
        intro j hj
        exact Function.update_of_ne (Finset.ne_of_mem_erase hj) c (extendAt i w)
      have hsum : (∑ j ∈ Finset.univ.erase i,
          M i j * Function.update (extendAt i w) i c j)
          = ∑ j ∈ Finset.univ.erase i, M i j * extendAt i w j :=
        Finset.sum_congr rfl fun j hj => by rw [hfix j hj]
      rw [hsum, hc]
      ring
    have hnn := hS.dotProduct_mulVec_nonneg (Function.update (extendAt i w) i c)
    rw [star_trivial, quadform_eq_schurForm hM i ha.ne', Function.update_self, hkill,
      zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_add, schurForm_update_local,
      schurForm_extendAt hM i w] at hnn
    exact hnn
  · -- accept: a nonnegative Schur form gives semidefiniteness
    intro hS
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, fun v => ?_⟩
    have h1 : Function.update v i 0 = extendAt i (fun j : {j : Fin n // j ≠ i} => v j.1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [extendAt]
      · simp [extendAt, Function.update, hj]
    have hform : schurForm M i v
        = schurForm M i (extendAt i (fun j : {j : Fin n // j ≠ i} => v j.1)) := by
      rw [← h1, ← schurForm_update_local]
    rw [star_trivial, quadform_eq_schurForm hM i ha.ne']
    have hsq : (0:ℝ) ≤ (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2 :=
      sq_nonneg _
    have hfirst : (0:ℝ) ≤ M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2 :=
      mul_nonneg ha.le hsq
    have hsecond : (0:ℝ) ≤ schurForm M i v := by
      rw [hform, schurForm_extendAt hM i (fun j : {j : Fin n // j ≠ i} => v j.1)]
      simpa using hS.dotProduct_mulVec_nonneg _
    linarith

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) :
    M.PosSemidef ↔ (schurStep M i).PosSemidef :=
  ModernConvex.Relaxations.posSemidef_iff_schurStep_proof hM i ha
