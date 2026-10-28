-- Prove2me | solution 1 for MarginalUtility.satiation_point_is_maximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:03:38.067911+00:00
-- url     : https://prove2.me/submissions/b3ff4c92-8faf-4a1b-8646-c2ed87dc846c

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Set

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : MarginalUtility.HasDiminishingMarginalUtility U D)
    (x₀ : ℝ) (hx₀ : x₀ ∈ D) (hzero : MarginalUtility.marginalUtility U x₀ = 0) :
    IsMaxOn U D x₀ ∧ ∀ x ∈ D, x₀ < x → MarginalUtility.marginalUtility U x < 0 := by
  obtain ⟨hdU, hddU, hneg⟩ := hU
  unfold MarginalUtility.marginalUtility at *
  have hanti : StrictAntiOn (deriv U) D :=
    strictAntiOn_of_deriv_neg hDc hddU.continuousOn
      (fun x hx => hneg x (interior_subset hx))
  have hgt : ∀ x ∈ D, x₀ < x → deriv U x < 0 := fun x hx hlt => by
    simpa [hzero] using hanti hx₀ hx hlt
  have hlt : ∀ x ∈ D, x < x₀ → 0 < deriv U x := fun x hx hlt => by
    simpa [hzero] using hanti hx hx₀ hlt
  refine ⟨fun x hx => ?_, hgt⟩
  show U x ≤ U x₀
  rcases lt_trichotomy x x₀ with h | h | h
  · have hsub : Icc x x₀ ⊆ D := hDc.ordConnected.out hx hx₀
    have hmono : MonotoneOn U (Icc x x₀) :=
      monotoneOn_of_deriv_nonneg (convex_Icc x x₀) (hdU.continuousOn.mono hsub)
        ((hdU.mono hsub).mono interior_subset)
        (fun y hy => by
          rw [interior_Icc] at hy
          exact (hlt y (hsub (Ioo_subset_Icc_self hy)) hy.2).le)
    exact hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
  · rw [h]
  · have hsub : Icc x₀ x ⊆ D := hDc.ordConnected.out hx₀ hx
    have hanti' : AntitoneOn U (Icc x₀ x) :=
      antitoneOn_of_deriv_nonpos (convex_Icc x₀ x) (hdU.continuousOn.mono hsub)
        ((hdU.mono hsub).mono interior_subset)
        (fun y hy => by
          rw [interior_Icc] at hy
          exact (hgt y (hsub (Ioo_subset_Icc_self hy)) hy.1).le)
    exact hanti' ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
