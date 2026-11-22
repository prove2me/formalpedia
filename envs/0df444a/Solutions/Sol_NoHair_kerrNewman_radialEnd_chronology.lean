-- Prove2me | solution 1 for NoHair.kerrNewman_radialEnd_chronology
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:33:24.611573+00:00
-- url     : https://prove2.me/submissions/d7c5ccf2-ad47-4c7e-a54f-97929b0ed2a4

import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_timelikeAccess
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Set

private theorem cartesian_outside (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : kerrNewmanSpacetime a) : spatialRadius x.val ≤ ksRadius a x.val + |a| := by
  let r := ksRadius a x.val
  let k := ksNull a x.val
  have hr : 0 < r := x.property
  have hrel : k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 1 := ks_rel a x.val hr
  have hs : spatialRadius x.val ^ 2 = x.val 1 ^ 2 + x.val 2 ^ 2 + x.val 3 ^ 2 := Real.sq_sqrt (by positivity)
  rw [ks_x1 a x.val hr, ks_x2 a x.val hr, ks_x3 a x.val hr] at hs
  change spatialRadius x.val ^ 2 = (r*k 1-a*k 2)^2 + (a*k 1+r*k 2)^2 + (r*k 3)^2 at hs
  have hid : spatialRadius x.val ^ 2 = r^2 + a^2 - (a*k 3)^2 := by
    linear_combination hs + (r^2+a^2)*hrel
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hr.le (abs_nonneg a))).mp
  change spatialRadius x.val ^ 2 ≤ (r+|a|)^2
  nlinarith only [hid, sq_abs a, sq_nonneg (a*k 3), mul_nonneg hr.le (abs_nonneg a)]

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ T : VecField (kerrNewmanSpacetime a), IsTimeOrientation (kerrNewmanMetricField m a e) T ∧
      ∀ R : ℝ, kerrNewmanOuterRadius m a e + |a| < R →
        let A := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
        let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
        chronoPastSet (kerrNewmanMetricField m a e) T A = D ∧
        D ⊆ chronoFutureSet (kerrNewmanMetricField m a e) T A := by
  obtain ⟨hT,htrap⟩ := kerrNewman_outerHorizon_futureTrapped m a e hp
  refine ⟨kerrNewmanTimeDirection m a e, hT, ?_⟩
  intro R hR
  have hreach := kerrNewman_exterior_timelikeAccess m a e hp R
  refine ⟨Subset.antisymm ?_ (fun x hx => (hreach hx).1), fun x hx => (hreach hx).2⟩
  intro x hx
  rcases mem_iUnion.mp hx with ⟨z,hz⟩
  rcases mem_iUnion.mp hz with ⟨hzA, γ, hγ, h0, h1⟩
  change R < spatialRadius z.val at hzA
  have hfar : kerrNewmanOuterRadius m a e < ksRadius a z.val := by
    linarith [cartesian_outside m a e hp z]
  change kerrNewmanOuterRadius m a e < ksRadius a x.val
  by_contra! h
  have hbar := htrap γ hγ (h0 ▸ h : ksRadius a (γ 0).val ≤ kerrNewmanOuterRadius m a e)
  rw [h1] at hbar
  exact hfar.not_ge hbar
