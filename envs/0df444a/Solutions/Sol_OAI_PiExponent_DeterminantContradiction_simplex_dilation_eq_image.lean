-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_dilation_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:17:24.832079+00:00
-- url     : https://prove2.me/submissions/0b30e9fd-5d82-48a6-af38-302fc5081301

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ({x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r} : Set (Fin n → ℝ)) =
      (fun x : Fin n → ℝ => r • x) ''
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)} := by
  ext x
  constructor
  · rintro ⟨hx_nonneg, hx_sum⟩
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · constructor
      · intro i
        exact mul_nonneg (inv_nonneg.mpr hr.le) (hx_nonneg i)
      · have hsum :
            (∑ i : Fin n, (r⁻¹ • x) i) = r⁻¹ * ∑ i : Fin n, x i := by
          simp [Finset.mul_sum]
        rw [hsum]
        calc
          r⁻¹ * ∑ i : Fin n, x i ≤ r⁻¹ * r :=
            mul_le_mul_of_nonneg_left hx_sum (inv_nonneg.mpr hr.le)
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    · funext i
      simp [smul_smul, hr.ne']
  · rintro ⟨y, ⟨hy_nonneg, hy_sum⟩, hxy⟩
    have hsum :
        (∑ i : Fin n, (r • y) i) = r * ∑ i : Fin n, y i := by
      simp [Finset.mul_sum]
    have hsumxy :
        (∑ i : Fin n, x i) = ∑ i : Fin n, (r • y) i :=
      congrArg (fun z : Fin n → ℝ => ∑ i : Fin n, z i) hxy.symm
    constructor
    · intro i
      have hxyi : (r • y) i = x i := congrFun hxy i
      rw [← hxyi]
      exact mul_nonneg hr.le (hy_nonneg i)
    · rw [hsumxy, hsum]
      calc
        r * ∑ i : Fin n, y i ≤ r * 1 :=
          mul_le_mul_of_nonneg_left hy_sum hr.le
        _ = r := by ring