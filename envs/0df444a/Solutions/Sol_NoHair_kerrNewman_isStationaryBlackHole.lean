-- Prove2me | solution 1 for NoHair.kerrNewman_isStationaryBlackHole
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T19:46:15.06871+00:00
-- url     : https://prove2.me/submissions/9bf1a724-ee99-4f9a-bcf2-4396a9fb9c45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_kerrNewman_regularTensors
import Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
import Theorems.Thm_NoHair_kerrNewman_einsteinMaxwell
import Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
import Theorems.Thm_NoHair_kerrNewman_radialEnd_chronology
import Theorems.Thm_NoHair_kerrNewman_exterior_globallyHyperbolic
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier

open NoHair Set
open scoped ContDiff Manifold BigOperators

private theorem field_isTwoForm (a e : ℝ) : IsTwoForm (kerrNewmanFieldField a e) := by
  intro x v w
  change Matrix.toLinearMap₂' ℝ (kerrNewmanField a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) =
    -Matrix.toLinearMap₂' ℝ (kerrNewmanField a e x.val) (WithLp.ofLp w) (WithLp.ofLp v)
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, Fin.sum_univ_four, kerrNewmanField]
  ring

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ (T : VecField (kerrNewmanSpacetime a))
      (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ),
      IsStationaryBlackHole (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) T φ E ∧
      Subtype.val '' domainOfOuterCommunications (kerrNewmanMetricField m a e) T E.region
        = kerrNewmanDOC m a e := by
  let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
  obtain ⟨φ, E, _, hsym, hR, hregion⟩ := kerrNewman_stationaryFlatEnd m a e hp
  obtain ⟨T, hT, hreach⟩ := kerrNewman_radialEnd_chronology m a e hp
  have hpast : chronoPastSet (kerrNewmanMetricField m a e) T E.region = D := by
    rw [hregion]
    exact (hreach E.R hR).1
  have hfuture : D ⊆ chronoFutureSet (kerrNewmanMetricField m a e) T E.region := by
    rw [hregion]
    exact (hreach E.R hR).2
  have hdoc : domainOfOuterCommunications (kerrNewmanMetricField m a e) T E.region = D := by
    rw [domainOfOuterCommunications, hpast]
    exact inter_eq_right.mpr hfuture
  have hpos : 0 < kerrNewmanOuterRadius m a e :=
    add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)
  obtain ⟨hfront, hlevel⟩ := ksRadius_superlevel_frontier a (kerrNewmanOuterRadius m a e) hpos
  obtain ⟨hlor, hmetric, hfield⟩ := kerrNewman_regularTensors m a e
  refine ⟨T, φ, E, ?_, ?_⟩
  · refine {
      lorentzian := hlor
      smooth_metric := hmetric
      smooth_field := hfield
      twoForm := field_isTwoForm a e
      timeOrientation := hT
      electrovac := isElectrovac_of_coordinate_equations (kerrNewmanSpacetime a)
        (kerrNewmanMetric m a e) (kerrNewmanField a e) (kerrNewman_einsteinMaxwell m a e)
      stationary := hsym
      globallyHyperbolic := ?_
      blackHole_nonempty := ?_
      horizon_connected := ?_ }
    · rw [hdoc]
      exact kerrNewman_exterior_globallyHyperbolic m a e hp T hT
    · obtain ⟨x, hx⟩ := hlevel.nonempty
      refine ⟨x, ?_⟩
      change x ∉ chronoPastSet (kerrNewmanMetricField m a e) T E.region
      rw [hpast]
      change ¬ kerrNewmanOuterRadius m a e < ksRadius a x.val
      exact not_lt_of_ge (show ksRadius a x.val = kerrNewmanOuterRadius m a e from hx).le
    · rw [futureEventHorizon, hpast]
      exact (show frontier D = _ from hfront).symm ▸ hlevel
  · rw [hdoc]
    apply Set.image_preimage_eq_of_subset
    intro y hy
    exact ⟨⟨y, hpos.trans hy⟩, rfl⟩
