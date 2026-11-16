-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum_stationaryIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:24:53.947755+00:00
-- url     : https://prove2.me/submissions/c50906ec-b92d-4c31-bbf6-72841d374e1b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Stationarity is preserved by independent addition via product image measures. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    HasStationaryIncrements (fun t ω => X t ω + Y t ω) P := by
  intro s h
  let xs : Ω → ℝ := increment X s (s + h)
  let ys : Ω → ℝ := increment Y s (s + h)
  let xz : Ω → ℝ := increment X 0 h
  let yz : Ω → ℝ := increment Y 0 h
  have hx : IdentDistrib xs xz P P := hX.stationary_increments s h
  have hy : IdentDistrib ys yz P P := hY.stationary_increments s h
  have hmeas (a b : ℝ≥0) :
      Measurable (fun f : ℝ≥0 → ℝ => f b - f a) :=
    (measurable_pi_apply b).sub (measurable_pi_apply a)
  have his : IndepFun xs ys P := by
    change IndepFun (fun ω => X (s + h) ω - X s ω)
      (fun ω => Y (s + h) ω - Y s ω) P
    exact hXY.comp (hmeas s (s + h)) (hmeas s (s + h))
  have hiz : IndepFun xz yz P := by
    change IndepFun (fun ω => X h ω - X 0 ω)
      (fun ω => Y h ω - Y 0 ω) P
    exact hXY.comp (hmeas 0 h) (hmeas 0 h)
  have hmap_s :
      P.map (fun ω => (xs ω, ys ω)) = (P.map xs).prod (P.map ys) :=
    his.map_prod_eq_prod_map_map hx.aemeasurable_fst hy.aemeasurable_fst
  have hmap_z :
      P.map (fun ω => (xz ω, yz ω)) = (P.map xz).prod (P.map yz) :=
    hiz.map_prod_eq_prod_map_map hx.aemeasurable_snd hy.aemeasurable_snd
  have hpair : IdentDistrib (fun ω => (xs ω, ys ω))
      (fun ω => (xz ω, yz ω)) P P := by
    refine ⟨hx.aemeasurable_fst.prodMk hy.aemeasurable_fst,
      hx.aemeasurable_snd.prodMk hy.aemeasurable_snd, ?_⟩
    rw [hmap_s, hmap_z, hx.map_eq, hy.map_eq]
  have hadd := hpair.comp (measurable_fst.add measurable_snd)
  change IdentDistrib
    (fun ω => X (s + h) ω + Y (s + h) ω - (X s ω + Y s ω))
    (fun ω => X h ω + Y h ω - (X 0 ω + Y 0 ω)) P P
  simpa [Function.comp_def, xs, ys, xz, yz,
    increment, sub_add_sub_comm] using hadd
