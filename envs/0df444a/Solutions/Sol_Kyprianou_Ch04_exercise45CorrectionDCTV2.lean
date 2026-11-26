-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CorrectionDCTV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:17:22.687581+00:00
-- url     : https://prove2.me/submissions/3c1bb136-7a57-4471-b178-b06dac1c3060

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45NonnegativeTimeExtensionV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (μ : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z : ℝ × ℝ ∂μ, 0 < z.1)
    (henergy : Integrable (fun z : ℝ × ℝ => z.2^2) μ)
    (f g : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ))
    (hb : ∀ s x z : ℝ, 0 ≤ s → |f s (x+z)-f s x-z*g s x| ≤ K*z^2)
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ)
    (hL : ∀ n, Measurable (L n)) (hY : Measurable Y)
    (hConv : ∀ t : NNReal, 0 < t → Tendsto (fun n => L n t) atTop (nhds (Y t)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun n => ∫ z in {z : ℝ × ℝ | e n < |z.2|},
      f z.1 (L n z.1.toNNReal+z.2)-f z.1 (L n z.1.toNNReal)-
        z.2*g z.1 (L n z.1.toNNReal) ∂μ)
      atTop (nhds (∫ z, f z.1 (Y z.1.toNNReal+z.2)-f z.1 (Y z.1.toNNReal)-
        z.2*g z.1 (Y z.1.toNNReal) ∂μ)) := by
  let F := fun z : ℝ × ℝ => f (max z.1 0) z.2
  let G := fun z : ℝ × ℝ => g (max z.1 0) z.2
  have hF : Continuous F := Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2 f hf
  have hG : Continuous G := Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2 g hg
  let R := fun (l : NNReal → ℝ) (z : ℝ × ℝ) =>
    F (z.1,l z.1.toNNReal+z.2)-F (z.1,l z.1.toNNReal)-z.2 * G (z.1,l z.1.toNNReal)
  let B := fun n => {z : ℝ × ℝ | e n < |z.2|}
  have hB (n : ℕ) : MeasurableSet (B n) := measurableSet_lt measurable_const measurable_snd.abs
  have hR (l : NNReal → ℝ) (hl : Measurable l) : Measurable (R l) := by
    have hm : Measurable (fun z : ℝ × ℝ => l z.1.toNNReal) :=
      hl.comp (measurable_real_toNNReal.comp measurable_fst)
    exact ((hF.measurable.comp (measurable_fst.prodMk (hm.add measurable_snd))).sub
      (hF.measurable.comp (measurable_fst.prodMk hm))).sub
      (measurable_snd.mul (hG.measurable.comp (measurable_fst.prodMk hm)))
  have hlim (z : ℝ × ℝ) (hz : 0 < z.1) :
      Tendsto (fun n => R (L n) z) atTop (nhds (R Y z)) := by
    have ht : 0 < z.1.toNNReal := Real.toNNReal_pos.mpr hz
    have h := hConv z.1.toNNReal ht
    exact ((hF.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds
      (h.add tendsto_const_nhds))).sub
      (hF.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds h))).sub
      (tendsto_const_nhds.mul
        (hG.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds h)))
  have hD := tendsto_integral_of_dominated_convergence
    (fun z : ℝ × ℝ => K*z.2^2) (μ := μ)
    (F := fun n => (B n).indicator (R (L n))) (f := R Y)
    (fun n => ((hR _ (hL n)).indicator (hB n)).aestronglyMeasurable)
    (henergy.const_mul K) ?_ ?_
  · have heq (n : ℕ) : (∫ z, (B n).indicator (R (L n)) z ∂μ) =
        ∫ z in B n, f z.1 (L n z.1.toNNReal+z.2)-f z.1 (L n z.1.toNNReal)-
          z.2*g z.1 (L n z.1.toNNReal) ∂μ := by
      rw [integral_indicator (hB n)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hpos (s := B n)] with z hz
      simp [R,F,G,max_eq_left hz.le]
    have hlast : (∫ z, R Y z ∂μ) =
        ∫ z, f z.1 (Y z.1.toNNReal+z.2)-f z.1 (Y z.1.toNNReal)-
          z.2*g z.1 (Y z.1.toNNReal) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpos] with z hz
      simp [R,F,G,max_eq_left hz.le]
    rw [hlast] at hD
    exact hD.congr (fun n => heq n)
  · intro n
    filter_upwards [hpos] with z hz
    by_cases hzB : z ∈ B n
    · rw [Set.indicator_of_mem hzB,Real.norm_eq_abs]
      simpa [R,F,G,max_eq_left hz.le] using hb z.1 (L n z.1.toNNReal) z.2 hz.le
    · rw [Set.indicator_of_notMem hzB,norm_zero]
      positivity
  · filter_upwards [hpos] with z hz
    by_cases hz0 : z.2 = 0
    · simp [R,hz0,Set.indicator_apply]
    · apply (hlim z hz).congr'
      filter_upwards [he.eventually (Iio_mem_nhds (abs_pos.mpr hz0))] with n hn
      exact (Set.indicator_of_mem (show z ∈ B n from hn) _).symm
