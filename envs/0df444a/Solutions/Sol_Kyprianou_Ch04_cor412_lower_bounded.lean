-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_lower_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:36:39.345491+00:00
-- url     : https://prove2.me/submissions/0e1fb9ac-eee1-4d64-a80c-37ef89dc55db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_positiveMeanClassification
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0) :
    (¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w))) ∧
      (∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w))) := by
  let : IsProbabilityMeasure P := L.isProbability
  obtain ⟨hlo, hp⟩ := Kyprianou.Ch04.cor412_positive_exponent P F L hm
  have hanti : ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)) := by
    intro ha
    obtain ⟨hi, he⟩ := L.laplace 1 1 (by norm_num)
    have hle : ∀ᵐ w ∂P, Real.exp (1 * L.X 1 w) ≤ (1 : ℝ) := by
      filter_upwards [ha] with w hw
      have h := hw (show (0 : NNReal) ≤ 1 from by norm_num)
      change L.X 1 w ≤ L.X 0 w at h
      rw [L.X_zero] at h
      exact Real.exp_le_one_iff.mpr (by simpa using h)
    have H := integral_mono_ae hi (integrable_const (1 : ℝ)) hle
    change (∫ w, Real.exp (1 * L.X 1 w) ∂P) ≤ _ at H
    rw [he] at H
    have HH : Real.exp (L.ψ 1) ≤ 1 := by
      simpa [SpectrallyNegativeLevy.ψ] using H
    exact (not_le_of_gt (hp 1 (by norm_num))) (Real.exp_le_one_iff.mp HH)
  refine ⟨hanti, ?_⟩
  have hn : ¬ (∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ L.ψ θ < ε * θ) := by
    intro h
    obtain ⟨b,hb,hlt⟩ := h _ hm
    exact (not_lt_of_ge ((le_div_iff₀ hb).mp (hlo b hb))) hlt
  let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
  have hB : MeasurableSet B :=
    (Kyprianou.Ch04.infimumLimitSupport P F L 1 (by norm_num)).1
  have hmass : (P B).toReal = 1 :=
    Kyprianou.Ch04.limitingDrawdown_positiveMeanClassification P F L hanti hn
  have hmass1 : P B = 1 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P B) ENNReal.one_ne_top).mp
      (by simpa using hmass)
  apply ae_iff.mpr
  change P Bᶜ = 0
  rw [measure_compl hB (measure_ne_top P B), hmass1, measure_univ, tsub_self]
