-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedDenseSupFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:03:15.136531+00:00
-- url     : https://prove2.me/submissions/374ccdaf-0123-48a6-9adc-18a831cab284

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (c : ℝ) (t : NNReal) :
    ∃ H : (NNReal → ℝ) → ℝ, Measurable H ∧
      ∀ g : NNReal → ℝ,
        (∀ u, ContinuousWithinAt g (Ici u) u) →
        BddAbove ((fun u => c * g u) '' Icc 0 t) →
        H g = LevyExtrema.SBA.runSup (fun u => c * g u) t := by
  classical
  obtain ⟨D,hD,hDense⟩ := TopologicalSpace.exists_countable_dense (α := NNReal)
  let S := insert (0 : NNReal) D
  have hc : S.Countable := hD.insert _
  have hd : Dense S := hDense.mono (Set.subset_insert _ _)
  letI : Countable {u : NNReal // u ∈ S ∧ u ≤ t} :=
    (hc.mono (fun _ hu => hu.1)).to_subtype
  let H (g : NNReal → ℝ) :=
    max (⨆ u : {u : NNReal // u ∈ S ∧ u ≤ t}, c*g u.1) (c*g t)
  refine ⟨H, (Measurable.iSup fun u =>
    measurable_const.mul (measurable_pi_apply u.1)).max
      (measurable_const.mul (measurable_pi_apply t)), ?_⟩
  intro g hg hb
  have hr : Set.range (fun u : Set.Icc (0 : NNReal) t => c*g u.1) =
      (fun u => c*g u) '' Icc 0 t := by
    ext z
    exact ⟨fun ⟨u,hu⟩ => ⟨u.1,u.2,hu⟩, fun ⟨u,hu,hz⟩ => ⟨⟨u,hu⟩,hz⟩⟩
  have he := AvramDividend.Classical.dense_timeSup_with_endpoint
    (fun u => c*g u) (fun u => continuousWithinAt_const.mul (hg u))
    S hd (by simp [S]) t (by rwa [hr])
  simpa only [H, LevyExtrema.SBA.runSup, iSup, hr] using he.symm
