-- Prove2me | solution 1 for NoHair.not_hawking_analytic_nondegenerate_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:06:31.974175+00:00
-- url     : https://prove2.me/submissions/7e89417d-dd3e-45e3-8878-2f1cdcfb18d1

import Theorems.Thm_NoHair_kerrNewman_regularTensors
import Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
import Theorems.Thm_NoHair_kerrNewman_einsteinMaxwell
import Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
import Theorems.Thm_NoHair_kerr_inner_horizon_flat_end
import Theorems.Thm_NoHair_kerr_inner_horizon_relative_causality
import Theorems.Thm_NoHair_kerr_inner_horizon_geometry
import Theorems.Thm_NoHair_kerr_inner_horizon_shell_not_exterior

open NoHair Set
open scoped ContDiff Manifold

theorem solution : ¬ (∀ {M : Type} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] [IsManifold 𝓘(ℝ,E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ),
    IsStationaryBlackHole g F T φ E → (∀ x, F x = 0) → IsAnalyticBilinField g →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  intro uniqueness
  let g := kerrNewmanMetricField (5/2) 2 0
  let F := kerrNewmanFieldField 2 0
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  obtain ⟨hlor,hmetric,hfield⟩ := kerrNewman_regularTensors (5/2) 2 0
  obtain ⟨φ,_,hφ,hsym,_⟩ := kerrNewman_stationaryFlatEnd (5/2) 2 0 hp
  obtain ⟨E,hE⟩ := kerr_inner_horizon_flat_end φ hφ
  obtain ⟨T,hT,hP,hF,hGH⟩ := kerr_inner_horizon_relative_causality
  obtain ⟨han,hB,hC,hn⟩ := kerr_inner_horizon_geometry
  have hD : domainOfOuterCommunications g T E.region = A := by
    rw [domainOfOuterCommunications,hE,hP]
    exact inter_eq_right.mpr hF
  have hH : futureEventHorizon g T E.region=frontier A := by rw [futureEventHorizon,hE,hP]
  have hmat (y : E4) : kerrNewmanField 2 0 y = 0 := by
    ext μ ν
    simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
  have hzero (x : kerrNewmanSpacetime 2) : F x=0 := by
    change matrixBilin (kerrNewmanField 2 0 x.val)=0
    rw [hmat]
    ext v w
    simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  have hbh : IsStationaryBlackHole g F T φ E :=
    { lorentzian := hlor
      smooth_metric := hmetric
      smooth_field := hfield
      twoForm := by intro x v w; rw [hzero]; simp
      timeOrientation := hT
      electrovac := isElectrovac_of_coordinate_equations (kerrNewmanSpacetime 2)
        (kerrNewmanMetric (5/2) 2 0) (kerrNewmanField 2 0) (kerrNewman_einsteinMaxwell (5/2) 2 0)
      stationary := hsym
      globallyHyperbolic := hD.symm ▸ hGH
      blackHole_nonempty := by rw [blackHoleRegion,hE,hP]; exact hB
      horizon_connected := hH.symm ▸ hC }
  have hnd : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region) := by
    rw [hH,hD]
    exact hn
  obtain ⟨μ,b,hparams,hiso⟩ := uniqueness g F T φ E hbh hzero han hnd
  change IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 at hiso
  rw [hD] at hiso
  exact kerr_inner_horizon_shell_not_exterior μ b hparams hiso
