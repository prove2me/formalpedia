-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_counterexample
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:58:54.609989+00:00
-- url     : https://prove2.me/submissions/63785fd8-3a0a-4a9d-8eee-d84e18e05364
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_kerrNewman_isStationaryBlackHole
import Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
import Theorems.Thm_NoHair_kerr_inner_horizon_flat_end
import Theorems.Thm_NoHair_kerr_inner_horizon_relative_causality
import Theorems.Thm_NoHair_kerr_inner_horizon_geometry
import Theorems.Thm_NoHair_kerr_inner_horizon_shell_not_exterior

open NoHair Set
open scoped ContDiff Manifold

theorem solution :
    let g := (kerrNewmanMetricField (5/2) 2 0)
    let F := (kerrNewmanFieldField 2 0)
    ∃ (T : VecField (kerrNewmanSpacetime 2))
      (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E : AsymptoticallyFlatEnd g F φ),
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) ∧
      ¬ ∃ μ b : ℝ, IsKerrNewmanBlackHoleParams μ b 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 := by
  let g := kerrNewmanMetricField (5/2) 2 0
  let F := kerrNewmanFieldField 2 0
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  obtain ⟨_,_,_,h₀,_⟩ := kerrNewman_isStationaryBlackHole (5/2) 2 0 hp
  obtain ⟨φ,_,hφ,hsym,_⟩ := kerrNewman_stationaryFlatEnd (5/2) 2 0 hp
  obtain ⟨E,hE⟩ := kerr_inner_horizon_flat_end φ hφ
  obtain ⟨T,hT,hP,hF,hGH⟩ := kerr_inner_horizon_relative_causality
  obtain ⟨han,hB,hC,hn⟩ := kerr_inner_horizon_geometry
  have hD : domainOfOuterCommunications g T E.region = A := by
    rw [domainOfOuterCommunications,hE,hP]
    exact inter_eq_right.mpr hF
  have hH : futureEventHorizon g T E.region=frontier A := by rw [futureEventHorizon,hE,hP]
  have hbh : IsStationaryBlackHole g F T φ E :=
    { lorentzian := h₀.lorentzian
      smooth_metric := h₀.smooth_metric
      smooth_field := h₀.smooth_field
      twoForm := h₀.twoForm
      timeOrientation := hT
      electrovac := h₀.electrovac
      stationary := hsym
      globallyHyperbolic := hD.symm ▸ hGH
      blackHole_nonempty := by rw [blackHoleRegion,hE,hP]; exact hB
      horizon_connected := hH.symm ▸ hC }
  have hmat (y : E4) : kerrNewmanField 2 0 y = 0 := by
    ext μ ν
    simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
  have hzero (x : kerrNewmanSpacetime 2) : F x=0 := by
    change matrixBilin (kerrNewmanField 2 0 x.val)=0
    rw [hmat]
    ext v w
    simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  refine ⟨T,φ,E,hbh,hzero,han,?_,?_⟩
  · rw [hH,hD]; exact hn
  · rintro ⟨μ,b,hp',hdoc⟩
    change IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 at hdoc
    rw [hD] at hdoc
    exact kerr_inner_horizon_shell_not_exterior μ b hp' hdoc
