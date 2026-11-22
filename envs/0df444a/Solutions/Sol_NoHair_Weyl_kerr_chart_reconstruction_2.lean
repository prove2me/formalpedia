-- Prove2me | solution 2 for NoHair.Weyl.kerr_chart_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:26:24.398587+00:00
-- url     : https://prove2.me/submissions/8448ea1f-2b28-48c6-9ddd-85251079575c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_Weyl_kerr_radial_quadratures
import Theorems.Thm_NoHair_Weyl_kerr_metric_in_weyl_chart
import Theorems.Thm_NoHair_Weyl_kerr_normalized_charts_cover

open NoHair NoHair.Weyl Set

private theorem metric_cont (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ContinuousOn (kerrNewmanMetric m a 0) (kerrNewmanDOC m a 0) := by
  intro y hy
  have hr : 0 < ksRadius a y := by
    have hp := hm.1
    change m + Real.sqrt (m^2-a^2-0^2) < ksRadius a y at hy
    linarith [Real.sqrt_nonneg (m^2-a^2-0^2)]
  have rc := (continuous_ksRadius a).continuousAt (x := y)
  have hden : ksRadius a y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hprof : ksRadius a y ^ 4 + a ^ 2 * y 3 ^ 2 ≠ 0 := by positivity
  have hk (i : Fin 4) : ContinuousAt (fun q => ksNull a q i) y := by
    fin_cases i <;> simp only [ksNull,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Matrix.cons_val_succ] <;> fun_prop (disch := first | assumption | positivity)
  have hf : ContinuousAt (ksProfile m a 0) y := by
    unfold ksProfile
    fun_prop (disch := assumption)
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact continuousAt_const.add ((hf.mul (hk i)).mul (hk j))

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    IsWeylRepresentation m a (kerrNewmanMetric m a 0) (kerrErnst m a) ∧
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  obtain ⟨hq,values⟩ := kerr_radial_quadratures m a hm
  refine ⟨⟨hq,metric_cont m a hm,?_⟩,kerr_normalized_charts_cover m a hm⟩
  intro V C hc y hy
  rw [kerr_metric_in_weyl_chart m a hm V C hc y hy]
  have h := values (Real.log ((C y) 2),(C y) 3)
  ext i j
  simp only [kerrWeylMatrix,metricInChart,h.1,h.2]
