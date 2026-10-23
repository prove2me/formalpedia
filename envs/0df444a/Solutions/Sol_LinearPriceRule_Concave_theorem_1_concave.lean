-- Prove2me | solution 1 for LinearPriceRule.Concave.theorem_1_concave
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:03.013138+00:00
-- url     : https://prove2.me/submissions/9714bd15-ae8a-4f73-a573-6a6ac00b265f

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

set_option autoImplicit false

namespace LinearPriceRule.Concave

theorem concave_price_proof (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q) :
    linPrice M ≤ M.PA Q := by
  by_contra h
  have hp : M.PA Q < (M.Pm + M.c) / 2 := by
    simpa only [linPrice] using lt_of_not_ge h
  have hQnonneg : 0 ≤ Q := hQ.1.1
  have hQpos : 0 < Q := by
    by_contra hpos
    have hzero : Q = 0 := by linarith
    rw [hzero, hM.PA_zero] at hp
    linarith [hM.c_lt_Pm]
  have hgap : 0 < M.Pm - M.PA Q := by linarith [hM.c_lt_Pm]
  have hmargin : 0 < M.Pm - M.c := sub_pos.mpr hM.c_lt_Pm
  let t : ℝ := (M.Pm - M.c) / (2 * (M.Pm - M.PA Q))
  have hden : 0 < 2 * (M.Pm - M.PA Q) := by positivity
  have htpos : 0 < t := div_pos hmargin hden
  have htlt : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hteq : t * (M.Pm - M.PA Q) = (M.Pm - M.c) / 2 := by
    dsimp [t]
    field_simp
  have htQ : t * Q ∈ Set.Icc 0 M.Qmax := by
    constructor
    · positivity
    · have hle : t * Q ≤ Q := by nlinarith
      exact hle.trans hQ.1.2
  have hzero : (0 : ℝ) ∈ Set.Icc 0 M.Qmax := ⟨le_rfl, hM.Qmax_pos.le⟩
  have hc := hconc.2 hzero hQ.1
    (show 0 ≤ 1 - t by linarith) htpos.le (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hM.PA_zero] at hc
  have hopt := hQ.2 (t * Q) htQ
  have hbound : ((1 - t) * M.Pm + t * M.PA Q - M.c) * t ≤ M.PA Q - M.c := by
    refine le_of_mul_le_mul_right ?_ hQpos
    calc
      (((1 - t) * M.Pm + t * M.PA Q - M.c) * t) * Q =
          ((1 - t) * M.Pm + t * M.PA Q - M.c) * (t * Q) := by ring
      _ ≤ (M.PA (t * Q) - M.c) * (t * Q) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hc M.c) htQ.1
      _ ≤ (M.PA Q - M.c) * Q := hopt
  have hgain : 0 < (1 - t) * (t * (M.Pm - M.PA Q) - (M.PA Q - M.c)) := by
    apply mul_pos (by linarith)
    rw [hteq]
    linarith
  nlinarith

end LinearPriceRule.Concave

open LinearPriceRule.Concave

theorem solution (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q) :
    linPrice M ≤ M.PA Q := by
  exact concave_price_proof M hM hconc Q hQ
