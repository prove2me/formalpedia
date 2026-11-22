-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scale_from_clock_cdf_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:56:29.437341+00:00
-- url     : https://prove2.me/submissions/4bd0d9e5-a66b-4d00-b9ad-49b76b0d5e89

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_matched_laplace
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq

open AvramDividend.Classical
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma ky4_scale_monotone {ψ w : ℝ → ℝ} {q : ℝ}
    (hW : IsQScale ψ q w) : Monotone w := by
  obtain ⟨_, hWneg, hW0, _, hWmono, _⟩ := hW
  intro y z hyz
  by_cases hy : 0 ≤ y
  · exact hWmono hy (hy.trans hyz) hyz
  · rw [hWneg y (lt_of_not_ge hy)]
    exact hW0 z

private lemma ky4_cdf_neg_zero {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hs : ν (Iio (0 : ℝ)) = 0) {x : ℝ} (hx : x < 0) : cdf ν x = 0 := by
  have hsub : Iic x ⊆ Iio (0 : ℝ) := fun _ hy => lt_of_le_of_lt hy hx
  rw [cdf_eq_real, Measure.real_def, measure_mono_null hsub hs] <;> simp

private lemma ky4_integral_neg_zero {w : ℝ → ℝ}
    (hWneg : ∀ y : ℝ, y < 0 → w y = 0) {x : ℝ} (hx : x < 0) :
    (∫ t in (0 : ℝ)..x, w t) = 0 := by
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx.le]
  have hnull : ∀ᵐ y ∂volume.restrict (Ioc x (0 : ℝ)), y ≠ 0 := by
    rw [ae_iff]
    simp
  have ha : w =ᵐ[volume.restrict (Ioc x 0)] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc, hnull] with y hy hne
    exact hWneg y (lt_of_le_of_ne hy.2 hne)
  rw [integral_congr_ae ha] <;> simp

private lemma ky4_eq_at_zero {f g : ℝ → ℝ}
    (hfcont : ContinuousOn f (Ici (0 : ℝ)))
    (hgcont0 : ContinuousWithinAt g (Ici (0 : ℝ)) 0)
    (heq : ∀ y : ℝ, 0 < y → f y = g y) : f 0 = g 0 := by
  have hmem : (0 : ℝ) ∈ Ici (0 : ℝ) := show (0 : ℝ) ≤ 0 from le_rfl
  haveI : (𝓝[Ioi (0 : ℝ)] 0).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioi]
    exact hmem
  have ha : Tendsto f (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (f 0)) :=
    (hfcont 0 hmem).mono Ioi_subset_Ici_self
  have hb : Tendsto g (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (g 0)) :=
    hgcont0.mono Ioi_subset_Ici_self
  have hfg : g =ᶠ[𝓝[Ioi (0 : ℝ)] 0] f :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => (heq y hy).symm)
  exact tendsto_nhds_unique ha (hb.congr' hfg)

theorem solution
    (ψ w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hφ : 0 < Phi ψ q)
    (hW : IsQScale ψ q w) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ν (Iio (0 : ℝ)) = 0)
    (hc : ∀ β : ℝ, Phi ψ q < β →
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
        (1 / β) * ((q / Phi ψ q) * ((Phi ψ q - β) / (q - ψ β))))
    (x : ℝ) :
    1 - cdf ν x = Zscale q w x - q / Phi ψ q * w x := by
  classical
  have hWcopy := hW
  obtain ⟨_, hWneg, hW0, hWcont, _, _⟩ := hW
  let φ := Phi ψ q
  let J := fun y : ℝ => ∫ t in (0 : ℝ)..y, w t
  let f := fun y : ℝ => q / φ * w y
  let g := fun y : ℝ => cdf ν y + q * J y
  have hWmono' : Monotone w := ky4_scale_monotone hWcopy
  have hJcont : Continuous J :=
    intervalIntegral.continuous_primitive (fun a b => hWmono'.intervalIntegrable) 0
  have hfcont : ContinuousOn f (Ici (0 : ℝ)) := continuousOn_const.mul hWcont
  have hgcont (y : ℝ) : ContinuousWithinAt g (Ici y) y :=
    ((cdf ν).right_continuous y).add ((continuous_const.mul hJcont).continuousWithinAt)
  have hgmeas : Measurable g :=
    (monotone_cdf (μ := ν)).measurable.add (continuous_const.mul hJcont).measurable
  have hf0 (y : ℝ) : 0 ≤ f y := mul_nonneg (div_nonneg hq hφ.le) (hW0 y)
  have hg0 (y : ℝ) (hy : 0 ≤ y) : 0 ≤ g y :=
    add_nonneg (cdf_nonneg (μ := ν) y)
      (mul_nonneg hq (intervalIntegral.integral_nonneg hy fun t _ => hW0 t))
  have hlap (β : ℝ) (hβφ : φ < β) :
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * f y) (Ioi 0) ∧
        IntegrableOn (fun y : ℝ => Real.exp (-β * y) * g y) (Ioi 0) ∧
        (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * f y) =
          ∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * g y :=
    source_result81_scale_matched_laplace ψ w q hφ hWcopy ν β hβφ (hc β hβφ).1 (hc β hβφ).2
  have heq : ∀ y : ℝ, 0 < y → f y = g y :=
    continuous_rightContinuous_Ioi_eq_of_laplace_eq f g φ
      (hfcont.mono Ioi_subset_Ici_self) (fun y _ => hgcont y) hgmeas.aemeasurable
      (fun y _ => hf0 y) (fun y hy => hg0 y hy.le) hlap
  have heq0 : f 0 = g 0 := ky4_eq_at_zero hfcont (hgcont 0) heq
  have hn : 0 ≤ x → f x = g x := fun hx =>
    (eq_or_lt_of_le hx).elim (fun he => he ▸ heq0) (heq x)
  change 1 - cdf ν x = 1 + q * J x - f x
  by_cases hx : 0 ≤ x
  · have h := hn hx
    change f x = cdf ν x + q * J x at h
    linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    have hc0 : cdf ν x = 0 := ky4_cdf_neg_zero hs hx'
    have hp : J x = 0 := ky4_integral_neg_zero hWneg hx'
    simp [hc0, hp, f, hWneg x hx']
