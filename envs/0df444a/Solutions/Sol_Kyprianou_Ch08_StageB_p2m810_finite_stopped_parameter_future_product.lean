-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_finite_stopped_parameter_future_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:08.542468+00:00
-- url     : https://prove2.me/submissions/64105c79-2c15-41f5-97d7-0127150acfd1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω β : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}))
    (Y : Ω → β) (hY : Measurable Y)
    (hYs : ∀ B : Set β, MeasurableSet B → ∀ s : ℝ≥0,
      MeasurableSet[F s] (Y ⁻¹' B ∩ {ω | τ ω ≤ s})) :
    Measure.map (fun ω => (Y ω, fun t : ℝ≥0 =>
      X.X (τ ω+t) ω - X.X (τ ω) ω)) (P.restrict A) =
      (Measure.map Y (P.restrict A)).prod
        (Measure.map (fun ω => fun t : ℝ≥0 => X.X t ω) P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let V : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω+t) ω - X.X (τ ω) ω
  let U : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hV : Measurable V := levy_finiteStopping_stoppedFuturePath_measurable X τ hτ
  have hJoint : Measurable (fun ω => (Y ω,V ω)) := hY.prodMk hV
  haveI : IsFiniteMeasure (Measure.map (fun ω => (Y ω,V ω)) (P.restrict A)) :=
    Measure.isFiniteMeasure_map _ _
  change Measure.map (fun ω => (Y ω,V ω)) (P.restrict A) =
    (Measure.map Y (P.restrict A)).prod (Measure.map U P)
  apply Measure.ext_prod
  intro C D hC hD
  let B := Y ⁻¹' C ∩ A
  have hB (s : ℝ≥0) : MeasurableSet[F s] (B ∩ {ω | τ ω ≤ s}) := by
    have hh := (hYs C hC s).inter (hA s)
    convert hh using 1
    ext ω
    simp [B]
    tauto
  have hLaw := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ D)
    (levy_finiteStopping_restrictedFuturePath_mapLaw X τ hτ B hB)
  change Measure.map V (P.restrict B) D =
    ((P B) • Measure.map U P) D at hLaw
  rw [Measure.map_apply hV hD, Measure.restrict_apply (hV hD),
    Measure.smul_apply] at hLaw
  rw [Measure.map_apply hJoint (hC.prod hD), Measure.prod_prod,
    Measure.map_apply hY hC,
    Measure.restrict_apply (hJoint (hC.prod hD)),
    Measure.restrict_apply (hY hC)]
  change P ((Y ⁻¹' C ∩ V ⁻¹' D) ∩ A) =
    P (Y ⁻¹' C ∩ A) * Measure.map U P D
  simpa [B, smul_eq_mul, inter_assoc, inter_comm, inter_left_comm] using hLaw
