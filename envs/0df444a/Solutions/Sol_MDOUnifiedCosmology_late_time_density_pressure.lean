-- Prove2me | solution 1 for MDOUnifiedCosmology.late_time_density_pressure
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:21:01.373185+00:00
-- url     : https://prove2.me/submissions/f9d68cb5-9589-42b2-97ec-326ee12ba8ab

import Theorems.Thm_MDOUnifiedCosmology_energy_density_rewrite
import Theorems.Thm_MDOUnifiedCosmology_pressure_rewrite
open MDOUnifiedCosmology Set

theorem solution (κ A φc m α : ℝ) (hA : 0 < A) (hφc : 0 < φc)
    (T : ℝ) (a φ ρb : ℝ → ℝ) (hφ : ∀ t ∈ Ioi T, φ t = φc)
    (h5 : ∀ t ∈ Ioi T, FriedmannEq κ (potential A φc m α) a φ ρb t)
    (h6 : ∀ t ∈ Ioi T, AccelerationEq κ a φ ρb (fun _ => 0) t) :
    ∀ t ∈ Ioi T,
      rhoPhi κ (potential A φc m α) a φ t =
          κ ^ 2 * φc ^ 2 / 8 * ρb t + couplingFactor κ φc * V2 m α φc ∧
      pPhi κ (potential A φc m α) a φ t = -(couplingFactor κ φc * V2 m α φc) := by
  intro t ht
  have he : φ =ᶠ[nhds t] (fun _ => φc) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) (fun s hs => hφ s hs)
  have hd : deriv φ t = 0 := by rw [he.deriv_eq]; simp
  have hv : potential A φc m α φc = V2 m α φc := by
    simp [potential, V1, ne_of_gt hφc]
  have hr := energy_density_rewrite κ (potential A φc m α) a φ ρb t (h5 t ht)
  have hp := pressure_rewrite κ (potential A φc m α) a φ ρb (fun _ => 0) t (h5 t ht) (h6 t ht)
  constructor
  · simpa [hd, hφ t ht, hv] using hr
  · simpa [hd, hφ t ht, hv] using hp



