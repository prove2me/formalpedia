-- Prove2me | solution 1 for NoHair.rest_frame_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:06:49.492325+00:00
-- url     : https://prove2.me/submissions/6d5a7649-e8a6-4a36-b24a-c155116466fb

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

/-- Explicit boost to the rest frame of the unit timelike vector `(g, x, y, z)`. -/
noncomputable def restBoost281 (g x y z c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![g, -x, -y, -z;
     -x, 1 + c * x * x, c * x * y, c * x * z;
     -y, c * y * x, 1 + c * y * y, c * y * z;
     -z, c * z * x, c * z * y, 1 + c * z * z]

lemma restBoost281_lorentz (g x y z c : ℝ) (h1 : c * (1 + g) = 1)
    (h2 : g ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) = 1) :
    (restBoost281 g x y z c)ᵀ * NoHair.minkowski * restBoost281 g x y z c = NoHair.minkowski := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [restBoost281, NoHair.minkowski, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal] <;>
    first
    | linear_combination (-1 : ℝ) * h2
    | linear_combination (-(x) * (g - 1)) * h1 + c * x * h2
    | linear_combination (-(y) * (g - 1)) * h1 + c * y * h2
    | linear_combination (-(z) * (g - 1)) * h1 + c * z * h2
    | linear_combination (x * (g - 1)) * h1 - c * x * h2
    | linear_combination (y * (g - 1)) * h1 - c * y * h2
    | linear_combination (z * (g - 1)) * h1 - c * z * h2
    | linear_combination (x * x) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)
    | linear_combination (x * y) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)
    | linear_combination (x * z) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)
    | linear_combination (y * y) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)
    | linear_combination (y * z) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)
    | linear_combination (z * z) * ((c * (1 + g) + 1 - 2 * c) * h1 - c ^ 2 * h2)

lemma restBoost281_det (g x y z c : ℝ) (h1 : c * (1 + g) = 1)
    (h2 : g ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) = 1) :
    (restBoost281 g x y z c).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [restBoost281, Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  first
  | linear_combination g * (g - 1) * h1 - (c * g - 1) * h2

lemma restBoost281_mulVec (g x y z c : ℝ) (h1 : c * (1 + g) = 1)
    (h2 : g ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) = 1) :
    restBoost281 g x y z c *ᵥ ![g, x, y, z] = ![1, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    simp [restBoost281, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first
    | linear_combination h2
    | linear_combination (-(x) * (g - 1)) * h1 + c * x * h2
    | linear_combination (-(y) * (g - 1)) * h1 + c * y * h2
    | linear_combination (-(z) * (g - 1)) * h1 + c * z * h2
    | linear_combination (x * (g - 1)) * h1 - c * x * h2
    | linear_combination (y * (g - 1)) * h1 - c * y * h2
    | linear_combination (z * (g - 1)) * h1 - c * z * h2

open Set Matrix in
theorem solution (P : Fin 4 → ℝ) (hP : P ⬝ᵥ (NoHair.minkowski *ᵥ P) < 0) (hP0 : 0 < P 0) :
    ∃ Λ : Matrix (Fin 4) (Fin 4) ℝ, Λᵀ * NoHair.minkowski * Λ = NoHair.minkowski ∧ Λ.det = 1 ∧
      1 ≤ Λ 0 0 ∧ Λ *ᵥ P = ![Real.sqrt (-(P ⬝ᵥ (NoHair.minkowski *ᵥ P))), 0, 0, 0] := by
  have hQ : P ⬝ᵥ (NoHair.minkowski *ᵥ P) = -P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 := by
    simp [NoHair.minkowski, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
    ring
  set m := Real.sqrt (-(P ⬝ᵥ (NoHair.minkowski *ᵥ P))) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by linarith)
  have hm2 : m ^ 2 = P 0 ^ 2 - (P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2) := by
    rw [hm, Real.sq_sqrt (by linarith), hQ]; ring
  have hmle : m ≤ P 0 := by
    nlinarith [sq_nonneg (P 1), sq_nonneg (P 2), sq_nonneg (P 3)]
  set g := P 0 / m with hg
  have hg1 : 1 ≤ g := by rw [hg, le_div_iff₀ hmpos]; linarith
  set c := 1 / (1 + g) with hc
  have h1 : c * (1 + g) = 1 := by rw [hc]; field_simp
  have h2 : g ^ 2 - ((P 1 / m) ^ 2 + (P 2 / m) ^ 2 + (P 3 / m) ^ 2) = 1 := by
    rw [hg]; field_simp; linarith
  refine ⟨restBoost281 g (P 1 / m) (P 2 / m) (P 3 / m) c,
    restBoost281_lorentz _ _ _ _ _ h1 h2, restBoost281_det _ _ _ _ _ h1 h2, ?_, ?_⟩
  · simpa [restBoost281] using hg1
  · have hPv : P = m • ![g, P 1 / m, P 2 / m, P 3 / m] := by
      ext i
      fin_cases i <;> simp [hg] <;> field_simp
    have hmv : restBoost281 g (P 1 / m) (P 2 / m) (P 3 / m) c *ᵥ P =
        restBoost281 g (P 1 / m) (P 2 / m) (P 3 / m) c *ᵥ (m • ![g, P 1 / m, P 2 / m, P 3 / m]) := by
      exact congrArg _ hPv
    rw [hmv, Matrix.mulVec_smul, restBoost281_mulVec _ _ _ _ _ h1 h2]
    ext i
    fin_cases i <;> simp
