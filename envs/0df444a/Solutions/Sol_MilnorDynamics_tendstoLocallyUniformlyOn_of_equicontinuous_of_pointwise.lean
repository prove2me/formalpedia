-- Prove2me | solution 1 for MilnorDynamics.tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T01:12:39.703758+00:00
-- url     : https://prove2.me/submissions/45baaf51-5f0d-4a2e-96a5-cd12ed8bda35

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: on each compact set, a finite cover by small balls turns pointwise
convergence at finitely many centres plus the equicontinuity and Heine-Cantor
moduli into uniform convergence. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε)
    (hcont : ContinuousOn g U)
    (hpt : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    TendstoLocallyUniformlyOn f g atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hmod K hKU hK (ε / 3) hε3
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous (hcont.mono hKU)) (ε / 3) hε3
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hmin1 : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hmin2 : δ ≤ δ₂ := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨t, hts, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (δ / 2))
    (fun x _ => Metric.ball_mem_nhds x (by linarith))
  have hall : ∀ᶠ n in atTop, ∀ x ∈ t, dist (f n x) (g x) < ε / 3 :=
    (eventually_all_finset t).mpr fun x hx =>
      (Metric.tendsto_nhds.mp (hpt x (hKU (hts x hx)))) (ε / 3) hε3
  filter_upwards [hall] with n hn
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
  have hxy : ‖y - x‖ < δ / 2 := by
    have := Metric.mem_ball.mp hyx
    rwa [dist_eq_norm] at this
  have h1 : ‖f n y - f n x‖ < ε / 3 :=
    hδ₁ n y hy x (hts x hx) (by linarith [hxy, hδpos, hmin1])
  have h2 : ‖f n x - g x‖ < ε / 3 := by
    have := hn x hx
    rwa [dist_eq_norm] at this
  have h3 : ‖g x - g y‖ < ε / 3 := by
    have hdxy : dist y x < δ / 2 := by simpa [dist_eq_norm] using hxy
    have hlt : dist x y < δ₂ := by
      rw [dist_comm]
      linarith [hdxy, hδpos, hmin2]
    have := hδ₂ x (hts x hx) y hy hlt
    rwa [dist_eq_norm] at this
  have h4 : ‖f n y - g y‖ ≤ ‖f n y - f n x‖ + ‖f n x - g x‖ + ‖g x - g y‖ := by
    have hs : f n y - g y = (f n y - f n x) + (f n x - g x) + (g x - g y) := by ring
    calc ‖f n y - g y‖ = ‖(f n y - f n x) + (f n x - g x) + (g x - g y)‖ := by rw [hs]
      _ ≤ ‖(f n y - f n x) + (f n x - g x)‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ (‖f n y - f n x‖ + ‖f n x - g x‖) + ‖g x - g y‖ := by
          linarith [norm_add_le (f n y - f n x) (f n x - g x)]
  rw [dist_eq_norm, norm_sub_rev]
  linarith
