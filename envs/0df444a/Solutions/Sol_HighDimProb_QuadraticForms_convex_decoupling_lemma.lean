-- Prove2me | solution 1 for HighDimProb.QuadraticForms.convex_decoupling_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:14:01.458309+00:00
-- url     : https://prove2.me/submissions/09ccee32-5932-4e2c-85a0-e4fca1244672

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

end HighDimProb.QuadraticForms

open HighDimProb.QuadraticForms

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hindep : IndepFun Y Z P) (hZint : Integrable Z P) (hZmean : ∫ ω, Z ω ∂P = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hYF : Integrable (fun ω => F (Y ω)) P)
    (hYZF : Integrable (fun ω => F (Y ω + Z ω)) P) :
    ∫ ω, F (Y ω) ∂P ≤ ∫ ω, F (Y ω + Z ω) ∂P := by
  have hFc : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  set μY : Measure ℝ := P.map Y with hμY
  set μZ : Measure ℝ := P.map Z with hμZ
  have : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map hY.aemeasurable
  have : IsProbabilityMeasure μZ := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hprod : P.map (fun ω => (Y ω, Z ω)) = μY.prod μZ :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hindep
  set G : ℝ × ℝ → ℝ := fun p => F (p.1 + p.2) with hGdef
  have hGc : Continuous G := hFc.comp (continuous_fst.add continuous_snd)
  have hYZm : Measurable (fun ω => (Y ω, Z ω)) := hY.prodMk hZ
  -- integrability of G on the product
  have hGint : Integrable G (μY.prod μZ) := by
    rw [← hprod]
    exact (integrable_map_measure hGc.aestronglyMeasurable hYZm.aemeasurable).mpr hYZF
  have hFint : Integrable F μY :=
    (integrable_map_measure hFc.aestronglyMeasurable hY.aemeasurable).mpr hYF
  have hidint : Integrable (fun z : ℝ => z) μZ :=
    (integrable_map_measure continuous_id.aestronglyMeasurable hZ.aemeasurable).mpr hZint
  have hidmean : ∫ z, z ∂μZ = 0 := by
    rw [hμZ, integral_map (f := fun z : ℝ => z) hZ.aemeasurable continuous_id.aestronglyMeasurable]
    exact hZmean
  -- rewrite both sides
  have hL : ∫ ω, F (Y ω) ∂P = ∫ y, F y ∂μY := by
    rw [hμY, integral_map hY.aemeasurable hFc.aestronglyMeasurable]
  have hR : ∫ ω, F (Y ω + Z ω) ∂P = ∫ y, ∫ z, G (y, z) ∂μZ ∂μY := by
    rw [← integral_prod G hGint, ← hprod,
      integral_map hYZm.aemeasurable hGc.aestronglyMeasurable]
  rw [hL, hR]
  apply integral_mono_ae hFint hGint.integral_prod_left
  filter_upwards [hGint.prod_right_ae] with y hy
  have h1 : Integrable (fun z : ℝ => y + z) μZ := (integrable_const y).add hidint
  have h2 := hF.map_integral_le (μ := μZ) (f := fun z => y + z) hFc.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) h1 hy
  have h3 : ∫ z, (y + z) ∂μZ = y := by
    rw [integral_add (integrable_const y) hidint, hidmean]
    simp
  rw [h3] at h2
  exact h2
