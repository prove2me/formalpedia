-- Prove2me | solution 1 for MultiUnitProphet.eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:36:32.258425+00:00
-- url     : https://prove2.me/submissions/3357b89b-341b-4e72-abfb-6611c23b6c68

import Mathlib
import Definitions.Def_MultiUnitProphet_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

open MultiUnitProphet in
theorem solution (k n : ℕ) (hk : 1 ≤ k) (F : Fin n → Measure ℝ) (hF : IsInstance F) (p : ℝ)
    (hp : k ≤ n ∨ 0 ≤ p) :
    opt k F + ENNReal.ofReal (-((k : ℝ) * p)) ≤ ENNReal.ofReal ((k : ℝ) * p) + surplus F p := by
  classical
  haveI : ∀ t, IsProbabilityMeasure (F t) := fun t => (hF t).1
  set s := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k) with hs
  have hsne : s.Nonempty := ⟨∅, by simp [hs]⟩
  have hae : ∀ᵐ v ∂(Measure.pi F), ∀ t, 0 ≤ v t := by
    rw [ae_all_iff]
    intro t
    have h1 : ∀ᵐ x ∂(F t), 0 ≤ x := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
      rw [this]; exact (hF t).2
    exact Measure.tendsto_eval_ae_ae.eventually h1
  -- rewrite both sides as lintegrals
  unfold opt surplus
  rw [← lintegral_finset_sum _ (fun t _ => by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_pi_apply t).sub measurable_const)]
  have hc1 : ∀ c : ℝ≥0∞, c = ∫⁻ _, c ∂(Measure.pi F) := by
    intro c; rw [lintegral_const, measure_univ, mul_one]
  rw [hc1 (ENNReal.ofReal (-((k : ℝ) * p))), hc1 (ENNReal.ofReal ((k : ℝ) * p)),
    ← lintegral_add_right _ measurable_const, ← lintegral_add_left measurable_const]
  apply lintegral_mono_ae
  filter_upwards [hae] with v hv
  obtain ⟨S0, hS0, hsup⟩ := Finset.exists_mem_eq_sup s hsne (fun S => ∑ t ∈ S, ENNReal.ofReal (v t))
  rw [hsup]
  have hS0k : S0.card ≤ k := (Finset.mem_filter.1 hS0).2
  rcases le_or_gt 0 p with hp0 | hp0
  · rw [ENNReal.ofReal_of_nonpos (by nlinarith), add_zero]
    calc ∑ t ∈ S0, ENNReal.ofReal (v t)
        ≤ ∑ t ∈ S0, (ENNReal.ofReal p + ENNReal.ofReal (v t - p)) := by
          apply Finset.sum_le_sum
          intro t _
          calc ENNReal.ofReal (v t) = ENNReal.ofReal (p + (v t - p)) := by ring_nf
            _ ≤ ENNReal.ofReal p + ENNReal.ofReal (v t - p) := ENNReal.ofReal_add_le
      _ = S0.card * ENNReal.ofReal p + ∑ t ∈ S0, ENNReal.ofReal (v t - p) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * ENNReal.ofReal p + ∑ t, ENNReal.ofReal (v t - p) := by
          gcongr
          all_goals first | exact_mod_cast hS0k | exact Finset.subset_univ _
      _ = ENNReal.ofReal ((k : ℝ) * p) + ∑ t, ENNReal.ofReal (v t - p) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
  · have hkn : k ≤ n := by
      rcases hp with h | h
      · exact h
      · linarith
    rw [ENNReal.ofReal_of_nonpos (by nlinarith : (k : ℝ) * p ≤ 0), zero_add]
    have e : ∀ t, ENNReal.ofReal (v t - p) = ENNReal.ofReal (v t) + ENNReal.ofReal (-p) := by
      intro t
      rw [← ENNReal.ofReal_add (hv t) (by linarith)]
      ring_nf
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [show -((k : ℝ) * p) = (k : ℝ) * (-p) by ring, ENNReal.ofReal_mul (Nat.cast_nonneg k),
      ENNReal.ofReal_natCast]
    gcongr
    all_goals first | exact_mod_cast hkn | exact Finset.subset_univ _
