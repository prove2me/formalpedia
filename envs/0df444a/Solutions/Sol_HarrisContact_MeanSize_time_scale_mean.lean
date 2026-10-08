-- Prove2me | solution 1 for HarrisContact.MeanSize.time_scale_mean
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:24:22.76407+00:00
-- url     : https://prove2.me/submissions/836f682f-2617-4fc2-bbb2-d4a6a88aefaa

import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory
open scoped ENNReal

private lemma scale_integral (c t : ℝ) (hc : 0 < c) (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal c * F (c * s)) =
      ∫⁻ s in Set.Icc 0 (c * t), F s := by
  let e := (Homeomorph.mulLeft₀ c (ne_of_gt hc)).toMeasurableEquiv
  have hp : e ⁻¹' Set.Icc 0 (c * t) = Set.Icc 0 t := by
    ext s
    change (0 ≤ c * s ∧ c * s ≤ c * t) ↔ (0 ≤ s ∧ s ≤ t)
    constructor
    · intro h
      exact ⟨(mul_nonneg_iff_of_pos_left hc).mp h.1, (mul_le_mul_iff_right₀ hc).mp h.2⟩
    · intro h
      exact ⟨mul_nonneg hc.le h.1, mul_le_mul_of_nonneg_left h.2 hc.le⟩
  have hm : ENNReal.ofReal c • Measure.map e volume = volume := by
    simpa [e, abs_of_pos hc] using Real.smul_map_volume_mul_left (ne_of_gt hc)
  calc
    _ = ENNReal.ofReal c * ∫⁻ s in Set.Icc 0 t, F (e s) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; rfl
    _ = ∫⁻ s in Set.Icc 0 (c * t), F s ∂(ENNReal.ofReal c • Measure.map e volume) := by
      rw [Measure.restrict_smul, lintegral_smul_measure,
        Measure.restrict_map e.measurable measurableSet_Icc, hp,
        e.measurableEmbedding.lintegral_map]
      rfl
    _ = _ := by rw [hm]

open HarrisContact.Extinction

private lemma exit_scale {d : ℕ} (μ c : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    exitRate (c * μ) (fun k => c * lam k) ξ = c * exitRate μ lam ξ := by
  simp only [exitRate, mul_add, Finset.mul_sum, mul_assoc]

private lemma rate_scale {d : ℕ} (μ c : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) :
    rate (c * μ) (fun k => c * lam k) ξ η = c * rate μ lam ξ η := by
  classical
  simp only [rate, mul_add, Finset.mul_sum, mul_ite, mul_zero]

private lemma transN_scale {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (n : ℕ) (t : ℝ) (ξ η : Config d) :
    transN (c * μ) (fun k => c * lam k) n t ξ η = transN μ lam n (c * t) ξ η := by
  induction n generalizing t ξ η with
  | zero => simp only [transN, exit_scale]; congr 3 <;> ring
  | succ n ih =>
    simp only [transN, exit_scale, rate_scale, ih]
    congr 1
    · congr 3 <;> ring
    · have he (s : ℝ) : c * (t - s) = c * t - c * s := by ring
      have hr (s : ℝ) : c * exitRate μ lam ξ * s = exitRate μ lam ξ * (c * s) := by ring
      simp only [hr, he, ENNReal.ofReal_mul hc.le, mul_assoc, ← Finset.mul_sum]
      conv_lhs => arg 2; ext s; rw [mul_left_comm]
      exact scale_integral c t hc (fun s => ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (c * t - s) ζ η)

theorem solution {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t)
    (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize (c * μ) (fun k => c * lam k) t ξ = HarrisContact.Extinction.meanSize μ lam (c * t) ξ := by
  simp only [meanSize, HarrisContact.Extinction.trans, transN_scale μ lam c hc]

#print axioms solution
