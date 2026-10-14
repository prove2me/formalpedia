-- Prove2me | solution 1 for MDOUnifiedCosmology.dust_density_scaling
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:39.689842+00:00
-- url     : https://prove2.me/submissions/eeda6b5b-3508-4913-bae5-96156d9ae416

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (T t₀ : ℝ) (ht₀ : T < t₀) (a ρb : ℝ → ℝ)
    (ha_pos : ∀ t ∈ Ioi T, 0 < a t) (ha_diff : DifferentiableOn ℝ a (Ioi T))
    (hρb_diff : DifferentiableOn ℝ ρb (Ioi T))
    (hcons : ∀ t ∈ Ioi T, MatterConservation a ρb (fun _ => 0) t) :
    ∀ t ∈ Ioi T, ρb t * a t ^ 3 = ρb t₀ * a t₀ ^ 3 := by
  have hder (t : ℝ) (ht : t ∈ Ioi T) : HasDerivAt (fun s => ρb s * a s ^ 3) 0 t := by
    have ha := (ha_diff t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
    have hr := (hρb_diff t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
    have h := hr.hasDerivAt.mul (ha.hasDerivAt.pow 3)
    have he := hcons t ht
    dsimp [MatterConservation, hubble] at he
    have haz := ne_of_gt (ha_pos t ht)
    field_simp at he
    convert! h using 1 <;> dsimp
    linear_combination -(a t)^2 * he
  intro t ht
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi T).isPreconnected
    (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hder s hs).deriv) ht ht₀



