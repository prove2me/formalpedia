-- Prove2me | solution 1 for Kyprianou.Ch02.positiveSmallTimeFirstMomentBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:55.09679+00:00
-- url     : https://prove2.me/submissions/f6c0593b-7f1f-40c2-a61c-2022f7ccafaf

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_interiorLinearCutoffSequenceV1
import Theorems.Thm_Kyprianou_Ch02_positiveSmallTimeTestBoundV1
import Theorems.Thm_Kyprianou_Ch02_levyBoundedContinuousVanishingNearZeroIntegrableV1
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hM : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (ts : ℕ → {t : ℝ // 0 < t})
    (hb : Tendsto (fun n => (ts n).val⁻¹ *
      ∫ x in {x : ℝ | |x| < r}, x ∂(M (ts n) : Measure ℝ)) atTop (nhds b))
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ δ > 0, ∀ x, |x| < δ → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ * ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν))) :
    Integrable (fun x : ℝ => x) (ν.restrict (Set.Ioo (0 : ℝ) r)) ∧
      (∫ x in Set.Ioo (0 : ℝ) r, x ∂ν) ≤ b := by
  obtain ⟨f, hf0, hfle, hzero, hlim⟩ := Kyprianou.Ch02.interiorLinearCutoffSequenceV1 r hr
  let g : ℝ → ℝ := (Ioo (0 : ℝ) r).indicator id
  have hg0 (x : ℝ) : 0 ≤ g x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) r
    · simpa [g, hx] using hx.1.le
    · simp [g, hx]
  have hfm (n : ℕ) : Integrable (fun x => f n x) ν := by
    obtain ⟨δ, hδ, hz⟩ := hzero n
    exact Kyprianou.Ch02.levyBoundedContinuousVanishingNearZeroIntegrableV1
      ν hν (f n) δ hδ hz
  have hbound (n : ℕ) : (∫ x, f n x ∂ν) ≤ b :=
    Kyprianou.Ch02.positiveSmallTimeTestBoundV1 M ν hν hM r b hr ts hb hjump
      (f n) (hfle n) (hzero n)
  have hlin (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f n x) ∂ν) ≤ ENNReal.ofReal b := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfm n) (Eventually.of_forall (hf0 n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hliminf (x : ℝ) : liminf (fun n => ENNReal.ofReal (f n x)) atTop =
      ENNReal.ofReal (g x) :=
    ((ENNReal.continuous_ofReal.tendsto (g x)).comp (hlim x)).liminf_eq
  have hfat := lintegral_liminf_le (μ := ν) (u := atTop)
    (f := fun n x => ENNReal.ofReal (f n x))
    (fun n => ENNReal.measurable_ofReal.comp (f n).continuous.measurable)
  simp_rw [hliminf] at hfat
  have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤ ENNReal.ofReal b := by
    refine hfat.trans ?_
    refine liminf_le_of_le (h := ?_)
    intro c hc
    obtain ⟨n, hn⟩ := hc.exists
    exact hn.trans (hlin n)
  have hgi : Integrable g ν := by
    refine ⟨(measurable_id.indicator measurableSet_Ioo).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using
      hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).mp hgi, ?_⟩
  have h0 : 0 ≤ b := (integral_nonneg (hf0 0)).trans (hbound 0)
  rw [← integral_indicator measurableSet_Ioo]
  apply (ENNReal.ofReal_le_ofReal_iff h0).mp
  change ENNReal.ofReal (∫ x, g x ∂ν) ≤ ENNReal.ofReal b
  rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)]
  exact hle
