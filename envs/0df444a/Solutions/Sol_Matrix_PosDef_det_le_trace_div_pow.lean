-- Prove2me | solution 1 for Matrix.PosDef.det_le_trace_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:19.667622+00:00
-- url     : https://prove2.me/submissions/84c54605-4f83-44ca-8713-2693fa96e6c9

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

-- carved verbatim out of submission 028e111f-382d-40d0-8008-127228d5e6cf, lines 209-216

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_amgm {d : ℕ} (hd : 0 < d) (z : Fin d → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / d) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => ((d : ℝ))⁻¹) z
    (fun _ _ => by positivity) (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (fun i _ => hz i)
  calc ∏ i, z i = ∏ i, (z i ^ ((d : ℝ))⁻¹) ^ d := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Real.rpow_inv_natCast_pow (hz i) hd.ne']
    _ = (∏ i, z i ^ ((d : ℝ))⁻¹) ^ d := Finset.prod_pow _ _ _
    _ ≤ (∑ i, ((d : ℝ))⁻¹ * z i) ^ d :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _) h d
    _ = ((∑ i, z i) / d) ^ d := by rw [← Finset.mul_sum, div_eq_inv_mul]

open MeasureTheory ProbabilityTheory Matrix NNReal in
theorem solution {d : ℕ} (hd : 0 < d) {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) :
    V.det ≤ (V.trace / d) ^ d := by
  rw [hV.isHermitian.det_eq_prod_eigenvalues, hV.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact e5_amgm hd _ fun i => (hV.eigenvalues_pos i).le
