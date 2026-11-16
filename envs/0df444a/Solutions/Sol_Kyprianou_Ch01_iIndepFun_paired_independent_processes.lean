-- Prove2me | solution 1 for Kyprianou.Ch01.iIndepFun_paired_independent_processes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:53:43.167826+00:00
-- url     : https://prove2.me/submissions/0f2488ab-c43f-472a-bdb3-a4c243c0afae

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-- Independent vectors with internally independent coordinates yield independent pairs. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : ι → Ω → ℝ)
    (hf : iIndepFun f P) (hg : iIndepFun g P)
    (hfg : IndepFun (fun ω => fun i => f i ω)
      (fun ω => fun i => g i ω) P)
    (hfm : ∀ i, AEMeasurable (f i) P)
    (hgm : ∀ i, AEMeasurable (g i) P) :
    iIndepFun (fun i ω => (f i ω, g i ω)) P := by
  let μf : ι → Measure ℝ := fun i => P.map (f i)
  let μg : ι → Measure ℝ := fun i => P.map (g i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have hfv : AEMeasurable (fun ω => fun i => f i ω) P :=
    (aemeasurable_pi_iff).2 hfm
  have hgv : AEMeasurable (fun ω => fun i => g i ω) P :=
    (aemeasurable_pi_iff).2 hgm
  have hpv : AEMeasurable
      (fun ω => fun i => (f i ω, g i ω)) P :=
    (aemeasurable_pi_iff).2 (fun i => (hfm i).prodMk (hgm i))
  have hmarg (i : ι) :
      P.map (fun ω => (f i ω, g i ω)) =
        (μf i).prod (μg i) := by
    have hi : IndepFun (f i) (g i) P := by
      simpa only [Function.comp_def] using
        hfg.comp (measurable_pi_apply i) (measurable_pi_apply i)
    exact hi.map_prod_eq_prod_map_map (hfm i) (hgm i)
  have hwhole :
      P.map (fun ω => ((fun i => f i ω), (fun i => g i ω))) =
        (Measure.pi μf).prod (Measure.pi μg) := by
    calc
      _ = (P.map (fun ω => fun i => f i ω)).prod
            (P.map (fun ω => fun i => g i ω)) :=
        hfg.map_prod_eq_prod_map_map hfv hgv
      _ = (Measure.pi μf).prod (Measure.pi μg) := by
        rw [hf.map_fun_eq_pi_map hfm, hg.map_fun_eq_pi_map hgm]
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (hfm i).prodMk (hgm i))).2
  apply e.map_measurableEquiv_injective
  calc
    Measure.map (e : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ))
        (P.map (fun ω => fun i => (f i ω, g i ω))) =
        P.map (fun ω => ((fun i => f i ω), (fun i => g i ω))) := by
      calc
        _ = P.map (e ∘ (fun ω => fun i => (f i ω, g i ω))) :=
          AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hpv
        _ = P.map (fun ω => ((fun i => f i ω), (fun i => g i ω))) := by
          congr 1
    _ = (Measure.pi μf).prod (Measure.pi μg) := hwhole
    _ = Measure.map (e : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ))
        (Measure.pi (fun i => P.map (fun ω => (f i ω, g i ω)))) := by
      have hpres :=
        measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι μf μg
      simpa only [hmarg] using hpres.map_eq.symm
