-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.sourceRunningSupRationalAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:42:42.376289+00:00
-- url     : https://prove2.me/submissions/e01eae21-b4be-41ba-9701-13590bbff8e9

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_cadlagRunningSupDensePrefixRepresentation
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ r : ℚ, 0 ≤ r →
      AEMeasurable
        (fun ω => runningSup D.X (r : ℝ).toNNReal ω) P := by
  classical
  let sample : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hdense : Dense (Set.range sample) := by
    simpa only [sample] using
      AvramDividend.Classical.chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range sample := by
    refine ⟨Nat.pair 0 0, ?_⟩
    simp [sample]
  have hcoord (u : ℝ≥0) : AEMeasurable (D.X u) P := by
    have hi := (D.levy.stationary_increments 0 u).aemeasurable_snd
    change AEMeasurable (fun ω => D.X u ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  intro r hr
  let t : ℝ≥0 := (r : ℝ).toNNReal
  let S : Set ℝ≥0 := {u | u ∈ Set.range sample ∧ u ≤ t}
  have hCount : S.Countable :=
    (Set.countable_range sample).mono (by
      intro u hu
      exact hu.1)
  letI : Countable S := hCount.to_subtype
  have hSupAE : AEMeasurable
      (fun ω => ⨆ u : S, D.X u.1 ω) P :=
    AEMeasurable.iSup (fun u : S => hcoord u.1)
  have hRightAE : AEMeasurable
      (fun ω => max (⨆ u : S, D.X u.1 ω) (D.X t ω)) P :=
    hSupAE.max (hcoord t)
  have hEq : ∀ᵐ ω ∂P,
      runningSup D.X t ω =
        max (⨆ u : S, D.X u.1 ω) (D.X t ω) := by
    filter_upwards [D.levy.cadlag_ae] with ω hc
    exact Kyprianou.Ch08.StageB.cadlagRunningSupDensePrefixRepresentation
      D.X ω hc (by simpa only [D.levy.start_zero])
      (Set.range sample) hdense hzero t
  have hEqSym :
      (fun ω => max (⨆ u : S, D.X u.1 ω) (D.X t ω)) =ᵐ[P]
        (fun ω => runningSup D.X t ω) := by
    filter_upwards [hEq] with ω hω
    exact hω.symm
  exact hRightAE.congr hEqSym
