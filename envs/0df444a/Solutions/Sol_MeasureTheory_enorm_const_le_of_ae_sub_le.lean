-- Prove2me | solution 1 for MeasureTheory.enorm_const_le_of_ae_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:37:26.499139+00:00
-- url     : https://prove2.me/submissions/005804be-2097-479a-b62b-04e30a1230ce

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ENNReal}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (hμ0 : μ Set.univ ≠ 0) (hμt : μ Set.univ ≠ ⊤)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (c : ℝ) (K : ENNReal)
    (hK : ∀ᵐ y ∂μ, ‖c - f y‖ₑ ≤ K) :
    ‖c‖ₑ ≤ K + (μ Set.univ ^ (1 / p.toReal))⁻¹ * eLpNorm f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  let m := μ Set.univ ^ (1 / p.toReal)
  have hm0 : m ≠ 0 := by simp [m, ENNReal.rpow_eq_zero_iff, hμ0, hμt]
  have hmt : m ≠ ⊤ := by simp [m, ENNReal.rpow_eq_top_iff, hμ0, hμt]
  have hdiff : eLpNorm (fun y => c - f y) p μ ≤ K * m := by
    simpa [m, one_div] using eLpNorm_le_of_ae_enorm_bound hK
  have htri : ‖c‖ₑ * m ≤ eLpNorm f p μ + K * m := by
    calc
      _ = eLpNorm (fun _ : X => c) p μ := (eLpNorm_const' c hp0 hpt).symm
      _ = eLpNorm (f + (fun y => c - f y)) p μ := by congr 1; funext y; simp
      _ ≤ eLpNorm f p μ + eLpNorm (fun y => c - f y) p μ :=
        eLpNorm_add_le hf (aestronglyMeasurable_const.sub hf) hp
      _ ≤ _ := add_le_add_right hdiff _
  have hcancel := mul_le_mul_left htri m⁻¹
  change ‖c‖ₑ ≤ K + m⁻¹ * eLpNorm f p μ
  simpa only [add_mul, mul_assoc, ENNReal.mul_inv_cancel hm0 hmt, mul_one,
    mul_comm m⁻¹, add_comm] using hcancel
