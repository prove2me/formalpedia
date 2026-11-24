-- Prove2me | solution 1 for Kyprianou.Ch02.indepFunOfPairIdentDistribV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:58:19.710825+00:00
-- url     : https://prove2.me/submissions/c79117e7-5581-4000-a3ce-c807f53b348e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : Ω → ℝ × ℝ) (h : IdentDistrib F G P P)
    (hi : IndepFun (fun ω => (G ω).1) (fun ω => (G ω).2) P) :
    IndepFun (fun ω => (F ω).1) (fun ω => (F ω).2) P := by
  have hmF := h.aemeasurable_fst
  have hmG := h.aemeasurable_snd
  have hF1 := hmF.fst
  have hF2 := hmF.snd
  have hG1 := hmG.fst
  have hG2 := hmG.snd
  rw [indepFun_iff_map_prod_eq_prod_map_map hF1 hF2]
  have he := (indepFun_iff_map_prod_eq_prod_map_map hG1 hG2).mp hi
  have he1 := (h.comp measurable_fst).map_eq
  have he2 := (h.comp measurable_snd).map_eq
  change P.map F = (P.map (Prod.fst ∘ F)).prod (P.map (Prod.snd ∘ F))
  rw [h.map_eq, he1, he2]
  exact he
