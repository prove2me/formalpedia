-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionProductKernelIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:50:11.55485+00:00
-- url     : https://prove2.me/submissions/096ab17f-7765-4101-83ac-a7765f174ffa

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (mu P : Measure Omega) [IsFiniteMeasure mu] [IsProbabilityMeasure P]
    (S : Omega → ℝ) (Y Z : Omega → (NNReal → ℝ))
    (hS : AEMeasurable S mu) (hY : AEMeasurable Y mu) (hZ : Measurable Z)
    (hLaw : Measure.map (fun w => (S w,Y w)) mu =
      (Measure.map S mu).prod (Measure.map Z P))
    (H : ℝ × (NNReal → ℝ) → ℝ) (hH : Measurable H)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |H z| ≤ C) :
    (∫ w, H (S w,Y w) ∂mu) = ∫ w, (∫ eta, H (S w,Z eta) ∂P) ∂mu := by 
  let S' := hS.mk S
  have hSm : Measurable S' := hS.measurable_mk
  have hSS' : S =ᵐ[mu] S' := hS.ae_eq_mk
  let M : Omega × Omega → ℝ := fun z => H (S' z.1,Z z.2)
  have hMap : Measurable (fun z : Omega × Omega => (S' z.1,Z z.2)) :=
    (hSm.comp measurable_fst).prodMk (hZ.comp measurable_snd)
  have hMm : Measurable M := hH.comp hMap
  obtain ⟨C,hC,hBC⟩ := hBound
  have hMi : Integrable M (mu.prod P) := Integrable.of_bound hMm.aestronglyMeasurable C
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hBC (S' z.1,Z z.2)))
  calc
    _ = ∫ z, H z ∂(mu.map (fun w => (S w,Y w))) :=
      (integral_map (hS.prodMk hY) hH.aestronglyMeasurable).symm
    _ = ∫ z, H z ∂((mu.map S').prod (P.map Z)) := by
      rw [hLaw, Measure.map_congr hSS']
    _ = ∫ z, M z ∂(mu.prod P) := by
      rw [Measure.map_prod_map mu P hSm hZ]
      exact integral_map hMap.aemeasurable hH.aestronglyMeasurable
    _ = ∫ w, (∫ eta, H (S' w,Z eta) ∂P) ∂mu := integral_prod M hMi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hSS'] with w hw
      rw [hw]
