-- Prove2me | solution 1 for NonconvexSaddle.PGDVar.volume_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:15:19.541465+00:00
-- url     : https://prove2.me/submissions/69854ea4-c5e1-4844-9ed4-b2ae68dd5035

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open NonconvexSaddle.PGDVar in
theorem solution {d : ℕ} (hd : 1 ≤ d) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    w * (MeasureTheory.volume (Metric.ball (0 : NonconvexSaddle.PSGD.E (d - 1)) a)).toReal /
        (MeasureTheory.volume (Metric.ball (0 : NonconvexSaddle.PSGD.E d) a)).toReal =
      w / (a * Real.sqrt Real.pi) *
        (Real.Gamma ((d : ℝ) / 2 + 1) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) ∧
    w / (a * Real.sqrt Real.pi) *
        (Real.Gamma ((d : ℝ) / 2 + 1) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) ≤
      w / a * Real.sqrt ((d : ℝ) / Real.pi) := by
  have hV : ∀ k : ℕ, (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) a)).toReal =
      a ^ k * (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) a = Set.univ := by
        ext x
        simp only [Metric.mem_ball, Set.mem_univ, iff_true]
        rw [Subsingleton.elim x 0, dist_self]
        exact ha
      rw [hb]
      have hpre := (PiLp.volume_preserving_ofLp (ι := Fin 0)).measure_preimage
        (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
      rw [Set.preimage_univ] at hpre
      rw [hpre]
      rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
      simp
    · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal]
      apply div_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg (by positivity))
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hG1 : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG0 : 0 < Real.Gamma ((d : ℝ) / 2 + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
  constructor
  · rw [hV (d - 1), hV d]
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hm : m + 1 - 1 = m := by omega
    rw [hm]
    have harg : (m : ℝ) / 2 + 1 = ((m + 1 : ℕ) : ℝ) / 2 + 1 / 2 := by push_cast; ring
    rw [harg]
    rw [pow_succ, pow_succ]
    field_simp
  · -- log-convexity bound
    set x : ℝ := (d : ℝ) / 2 with hx
    have hx0 : 0 < x + 1 / 2 := by positivity
    have hlc := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + 1 / 2)
      (t := x + 3 / 2) (a := 1 / 2) (b := 1 / 2) hx0 (by positivity) (by norm_num) (by norm_num)
      (by norm_num)
    have e1 : 1 / 2 * (x + 1 / 2) + 1 / 2 * (x + 3 / 2) = x + 1 := by ring
    have e2 : x + 3 / 2 = (x + 1 / 2) + 1 := by ring
    rw [e1, e2, Real.Gamma_add_one hx0.ne', Real.mul_rpow hx0.le hG0.le, ← mul_assoc,
      mul_comm (Real.Gamma (x + 1 / 2) ^ (1 / 2 : ℝ)), mul_assoc, ← Real.rpow_add hG0,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one, ← Real.sqrt_eq_rpow] at hlc
    have hratio : Real.Gamma (x + 1) / Real.Gamma (x + 1 / 2) ≤ Real.sqrt d := by
      rw [div_le_iff₀ hG0]
      refine hlc.trans ?_
      apply mul_le_mul_of_nonneg_right _ hG0.le
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [hx]; linarith
    have hc : 0 ≤ w / (a * Real.sqrt Real.pi) := by positivity
    calc w / (a * Real.sqrt Real.pi) * (Real.Gamma (x + 1) / Real.Gamma (x + 1 / 2))
        ≤ w / (a * Real.sqrt Real.pi) * Real.sqrt d := mul_le_mul_of_nonneg_left hratio hc
      _ = w / a * Real.sqrt ((d : ℝ) / Real.pi) := by
        rw [Real.sqrt_div hdpos.le]
        field_simp
