-- Prove2me | solution 1 for NoHair.spin_alignment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:16:34.470079+00:00
-- url     : https://prove2.me/submissions/657c8f28-b3de-4c76-aeac-5b756f37c5ed

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

lemma spinAlign_rot_mem (u v s t : ℝ) (huv : u ^ 2 + v ^ 2 = 1) (hst : s ^ 2 + t ^ 2 = 1) :
    !![u, -v, 0; s * v, s * u, -t; t * v, t * u, s] ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      nlinarith [huv, hst, congrArg (fun x => s * t * x) huv,
        congrArg (fun x => s * x) huv, congrArg (fun x => t * x) huv]
  · rw [Matrix.det_fin_three]
    simp
    nlinarith [huv, hst]

lemma spinAlign_exists_uv (a b : ℝ) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ u * a - v * b = 0 ∧
      v * a + u * b = Real.sqrt (a ^ 2 + b ^ 2) := by
  set r := Real.sqrt (a ^ 2 + b ^ 2) with hr
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  by_cases h0 : r = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact ⟨1, 0, by norm_num, by simp [ha, hb], by simp [ha, hb, h0]⟩
  · refine ⟨b / r, a / r, ?_, ?_, ?_⟩
    · field_simp
      linarith
    · field_simp
      ring
    · field_simp
      linarith

open Set Matrix in
theorem solution (J : Fin 3 → ℝ) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      R *ᵥ J = ![0, 0, Real.sqrt (J 0 ^ 2 + J 1 ^ 2 + J 2 ^ 2)] := by
  obtain ⟨u, v, huv, h1, h2⟩ := spinAlign_exists_uv (J 0) (J 1)
  set r := Real.sqrt (J 0 ^ 2 + J 1 ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = J 0 ^ 2 + J 1 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨s, t, hst, h3, h4⟩ := spinAlign_exists_uv (J 2) r
  have hρ : Real.sqrt (J 2 ^ 2 + r ^ 2) = Real.sqrt (J 0 ^ 2 + J 1 ^ 2 + J 2 ^ 2) := by
    rw [hr2]; ring_nf
  refine ⟨!![u, -v, 0; t * v, t * u, -s; s * v, s * u, t], ?_, ?_⟩
  · have := spinAlign_rot_mem u v t s huv (by linarith [hst])
    exact this
  · ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination h1
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination t * h2 - h3
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [← hρ]
      linear_combination s * h2 + h4
