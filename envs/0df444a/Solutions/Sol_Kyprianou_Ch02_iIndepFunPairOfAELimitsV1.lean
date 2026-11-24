-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFunPairOfAELimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:36:13.32658+00:00
-- url     : https://prove2.me/submissions/27f43218-34c2-4e3d-805f-16f9e2b3968c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (F : ℕ → Fin m → Ω → ℝ × ℝ)
    (f : Fin m → Ω → ℝ × ℝ)
    (hm : ∀ n i, AEMeasurable (F n i) P)
    (hi : ∀ n, iIndepFun (F n) P)
    (hl : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => F n i ω) atTop (nhds (f i ω))) :
    iIndepFun f P := by
  have hmf (i : Fin m) : AEMeasurable (f i) P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => hm n i) (hl i)
  let A (n : ℕ) (i : Fin m) : ProbabilityMeasure (ℝ × ℝ) :=
    ⟨P.map (F n i), Measure.isProbabilityMeasure_map (hm n i)⟩
  let a (i : Fin m) : ProbabilityMeasure (ℝ × ℝ) :=
    ⟨P.map (f i), Measure.isProbabilityMeasure_map (hmf i)⟩
  have hA : Tendsto A atTop (nhds a) := tendsto_pi_nhds.mpr (fun i =>
    (tendstoInDistribution_of_ae_tendsto (fun n => hm n i) (hmf i) (hl i)).tendsto)
  have hprod := (ProbabilityMeasure.continuous_pi.tendsto a).comp hA
  have hmJ (n : ℕ) : AEMeasurable (fun ω i => F n i ω) P :=
    aemeasurable_pi_lambda _ (hm n)
  have hmfJ : AEMeasurable (fun ω i => f i ω) P := aemeasurable_pi_lambda _ hmf
  have hlJ : ∀ᵐ ω ∂P,
      Tendsto (fun n i => F n i ω) atTop (nhds (fun i => f i ω)) := by
    filter_upwards [ae_all_iff.mpr hl] with ω hω
    exact tendsto_pi_nhds.mpr hω
  have hJ := (tendstoInDistribution_of_ae_tendsto hmJ hmfJ hlJ).tendsto
  have heq : (fun n => (⟨P.map (fun ω i => F n i ω),
      Measure.isProbabilityMeasure_map (hmJ n)⟩ :
      ProbabilityMeasure (Fin m → ℝ × ℝ))) =
      (fun n => ProbabilityMeasure.pi (A n)) := by
    funext n
    exact Subtype.ext ((iIndepFun_iff_map_fun_eq_pi_map (hm n)).mp (hi n))
  rw [heq] at hJ
  apply (iIndepFun_iff_map_fun_eq_pi_map hmf).mpr
  exact congrArg (fun μ : ProbabilityMeasure (Fin m → ℝ × ℝ) =>
    (μ : Measure (Fin m → ℝ × ℝ))) (tendsto_nhds_unique hJ hprod)
