-- Prove2me | solution 1 for MDOUnifiedCosmology.late_time_LCDM
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:19:11.725326+00:00
-- url     : https://prove2.me/submissions/e4942741-eba5-4b3e-a6b5-9599657c6c02

import Theorems.Thm_MDOUnifiedCosmology_dust_density_scaling
open MDOUnifiedCosmology Set

theorem solution (κ A φc m α : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hφc : 0 < φc)
    (T t₀ : ℝ) (ht₀ : T < t₀) (a φ ρb : ℝ → ℝ)
    (ha_pos : ∀ t ∈ Ioi T, 0 < a t) (ha_diff : DifferentiableOn ℝ a (Ioi T))
    (hρb_diff : DifferentiableOn ℝ ρb (Ioi T))
    (hφ : ∀ t ∈ Ioi T, φ t = φc)
    (ha₀ : a t₀ = 1) (hH₀ : hubble a t₀ ≠ 0)
    (hcons : ∀ t ∈ Ioi T, MatterConservation a ρb (fun _ => 0) t)
    (hfried : ∀ t ∈ Ioi T, FriedmannEq κ (potential A φc m α) a φ ρb t) :
    ∀ t ∈ Ioi T,
      hubble a t ^ 2 / hubble a t₀ ^ 2 =
        omegaB κ (hubble a t₀) (ρb t₀) / a t ^ 3
          + omegaDM κ φc (omegaB κ (hubble a t₀) (ρb t₀)) / a t ^ 3
          + omegaLambda κ (hubble a t₀) φc m α := by
  intro t ht
  have he : φ =ᶠ[nhds t] (fun _ => φc) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) (fun s hs => hφ s hs)
  have hd : deriv φ t = 0 := by rw [he.deriv_eq]; simp
  have hv : potential A φc m α φc = V2 m α φc := by
    simp [potential, V1, ne_of_gt hφc]
  have hr := dust_density_scaling T t₀ ht₀ a ρb ha_pos ha_diff hρb_diff hcons t ht
  rw [ha₀, one_pow, mul_one] at hr
  have hf := hfried t ht
  unfold FriedmannEq at hf
  rw [hd, hφ t ht, hv] at hf
  have haz := ne_of_gt (ha_pos t ht)
  have hkz := ne_of_gt hκ
  unfold omegaB omegaDM omegaLambda lambdaEff critDensity
  rw [hf]
  norm_num
  field_simp
  unfold couplingFactor
  linear_combination (8 + κ^2*φc^2) * hr



