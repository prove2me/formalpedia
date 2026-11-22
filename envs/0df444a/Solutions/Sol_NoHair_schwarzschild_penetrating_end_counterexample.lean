-- Prove2me | solution 1 for NoHair.schwarzschild_penetrating_end_counterexample
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:45:50.18782+00:00
-- url     : https://prove2.me/submissions/f01f10b7-9769-4ba0-849e-a0332409c1d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_schwarzschild_unit_cutoff_end
import Theorems.Thm_NoHair_schwarzschild_unit_cutoff_causality
import Theorems.Thm_NoHair_schwarzschild_time_translation_static
import Theorems.Thm_NoHair_schwarzschild_trapped_shell_not_exterior
import Theorems.Thm_NoHair_kerrNewman_regularTensors
import Theorems.Thm_NoHair_kerrNewman_einsteinMaxwell
import Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier

open NoHair Set
open scoped ContDiff Manifold

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring

theorem solution :
    ∃ (T : VecField (kerrNewmanSpacetime 0)) (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ),
      IsStationaryBlackHole (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) T φ E ∧
      (∀ x, kerrNewmanFieldField 0 0 x = 0) ∧
      IsStaticOn (kerrNewmanMetricField 1 0 0) φ (domainOfOuterCommunications (kerrNewmanMetricField 1 0 0) T E.region) ∧
      ¬ ∃ m : ℝ, 0 < m ∧ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0)
        (domainOfOuterCommunications (kerrNewmanMetricField 1 0 0) T E.region) m 0 0 := by
  let U := kerrNewmanSpacetime 0
  let A := (Subtype.val : U → E4) ⁻¹' exteriorRegion 1
  let g := kerrNewmanMetricField 1 0 0
  let F := kerrNewmanFieldField 0 0
  obtain ⟨φ, E, hφ, hsym, _, hE⟩ := schwarzschild_unit_cutoff_end
  obtain ⟨T, hT, hp, hf, hgh⟩ := schwarzschild_unit_cutoff_causality
  have past : chronoPastSet g T E.region = A := hE ▸ hp
  have doc : domainOfOuterCommunications g T E.region = A := by
    unfold domainOfOuterCommunications
    rw [past, hE]
    exact inter_eq_right.mpr hf
  have hz : ∀ x, F x = 0 := by
    intro x
    ext v w
    change Matrix.toLinearMap₂' ℝ (kerrNewmanField 0 0 x.val) (WithLp.ofLp v) (WithLp.ofLp w) = 0
    simp [Matrix.toLinearMap₂'_apply, kerrNewmanField, kerrNewmanPotential, coordPartial]
  obtain ⟨hl, hsg, hsF⟩ := kerrNewman_regularTensors 1 0 0
  have hem : IsElectrovac g F := isElectrovac_of_coordinate_equations U
      (kerrNewmanMetric 1 0 0) (kerrNewmanField 0 0)
      (fun y hy => kerrNewman_einsteinMaxwell 1 0 0 y hy)
  have Aeq : A = {x : U | 1 < ksRadius 0 x.val} := by ext x; simp [A, exteriorRegion, radius_eq]
  obtain ⟨hfront,hlevel⟩ := ksRadius_superlevel_frontier 0 1 zero_lt_one
  have hBH : IsStationaryBlackHole g F T φ E := {
    lorentzian := hl
    smooth_metric := hsg
    smooth_field := hsF
    twoForm := by intro x v w; simp [hz]
    timeOrientation := hT
    electrovac := hem
    stationary := hsym
    globallyHyperbolic := doc ▸ hgh
    blackHole_nonempty := by
      obtain ⟨x,hx⟩ := hlevel.nonempty
      refine ⟨x, ?_⟩
      change x ∉ chronoPastSet g T E.region
      rw [past, Aeq]
      change ¬ 1 < ksRadius 0 x.val
      exact not_lt.mpr (le_of_eq hx)
    horizon_connected := by
      change IsConnected (frontier (chronoPastSet g T E.region))
      rw [past, Aeq, hfront]
      exact hlevel }
  refine ⟨T, φ, E, hBH, hz, ?_, ?_⟩
  · intro e he y hy _ l i j
    exact schwarzschild_time_translation_static φ hφ e he y hy (mem_univ _) l i j
  · rintro ⟨m, hm, hmodel⟩
    rw [doc] at hmodel
    exact schwarzschild_trapped_shell_not_exterior m hm hmodel
