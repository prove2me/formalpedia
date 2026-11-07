-- Prove2me | solution 1 for GlynnSTS.Length.display_2_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:47:37.737221+00:00
-- url     : https://prove2.me/submissions/09cacc09-dbf8-48d7-bdbd-84987e936f68

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Theorems.Thm_GlynnSTS_Length_proposition_2_8

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g) :
    ∀ x : ℝ, GlynnSTS.Length.H P B g x =
      ∫ y in Set.Ioi (0 : ℝ), cdf (gaussianReal 0 1) (x * y)
        ∂(P.map (fun ω => g (B ω))) := by
  intro x
  have hind := GlynnSTS.Length.proposition_2_8 P B hB g hg
  obtain ⟨hBm, W, hW, hBW⟩ := hB
  -- the endpoint is standard normal
  have hlaw : P.map (fun ω => B ω 1) = gaussianReal 0 1 := by
    have h1 := hW.toIsPreBrownianReal.hasLaw_eval ⟨(1 : unitInterval), (1 : unitInterval).2.1⟩
    have hfun : (fun ω => B ω 1) = W ⟨(1 : unitInterval), (1 : unitInterval).2.1⟩ := by
      funext ω; exact hBW ω 1
    rw [hfun, h1.map_eq]
    congr 1
  have hXm : AEMeasurable (fun ω => B ω 1) P :=
    ((continuous_eval_const (1 : unitInterval) : Continuous fun f : C(unitInterval, ℝ) => f 1).measurable.comp hBm).aemeasurable
  have hYm : AEMeasurable (fun ω => g (B ω)) P := (hg.1.comp hBm).aemeasurable
  set G := P.map (fun ω => g (B ω)) with hGdef
  haveI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map hYm
  have hposP : ∀ᵐ ω ∂P, 0 < g (B ω) := hg.2.2.2.1
  have hpos : ∀ᵐ y ∂G, y ∈ Set.Ioi (0 : ℝ) :=
    (ae_map_iff hYm measurableSet_Ioi).2 hposP
  rw [Measure.restrict_eq_self_of_ae_mem hpos]
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hXm hYm).1 hind
  rw [hlaw] at hprod
  -- rewrite the event
  have hset : {ω | B ω 1 / g (B ω) ≤ x} =ᵐ[P]
      (fun ω => (B ω 1, g (B ω))) ⁻¹' {q : ℝ × ℝ | q.1 ≤ x * q.2} := by
    filter_upwards [hposP] with ω hω
    change (B ω 1 / g (B ω) ≤ x) = (B ω 1 ≤ x * g (B ω))
    rw [div_le_iff₀ hω]
  have hS : MeasurableSet {q : ℝ × ℝ | q.1 ≤ x * q.2} :=
    measurableSet_le measurable_fst (measurable_const.mul measurable_snd)
  have hP : P {ω | B ω 1 / g (B ω) ≤ x} = ∫⁻ y, ENNReal.ofReal (cdf (gaussianReal 0 1) (x * y)) ∂G := by
    rw [measure_congr hset, ← Measure.map_apply_of_aemeasurable (hXm.prodMk hYm) hS, hprod,
      Measure.prod_apply_symm hS]
    refine lintegral_congr (fun y => ?_)
    rw [ofReal_cdf]
    rfl
  have hΦm : Measurable (fun y => cdf (gaussianReal 0 1) (x * y)) :=
    (monotone_cdf (gaussianReal 0 1)).measurable.comp (measurable_const_mul x)
  rw [GlynnSTS.Length.H, hP, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun y => cdf_nonneg _ _)) hΦm.aestronglyMeasurable]
