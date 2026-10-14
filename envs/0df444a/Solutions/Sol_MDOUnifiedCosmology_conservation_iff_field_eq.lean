-- Prove2me | solution 1 for MDOUnifiedCosmology.conservation_iff_field_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:44.739407+00:00
-- url     : https://prove2.me/submissions/73027350-c973-49da-81b0-ab63fdd98a6f

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ)
    (ha : DifferentiableAt ℝ a t) (ha' : DifferentiableAt ℝ (deriv a) t) (ha0 : a t ≠ 0)
    (hφ : DifferentiableAt ℝ φ t) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hV : DifferentiableAt ℝ V (φ t)) (hφdot : deriv φ t ≠ 0) :
    MDOConservation κ V a φ t ↔ FieldEq κ V a φ t := by
  have hC0 : couplingFactor κ (φ t) ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  have hH : HasDerivAt (hubble a) (deriv (hubble a) t) t :=
    (ha'.div ha ha0).hasDerivAt
  have hp := hφ.hasDerivAt
  have hpp := hφ'.hasDerivAt
  have hC : HasDerivAt (fun s => couplingFactor κ (φ s))
      (κ^2 * (2*φ t*deriv φ t) / 8) t := by
    unfold couplingFactor
    convert! ((((hp.pow 2).const_mul (κ^2)).div_const 8).const_add 1) using 1 <;> dsimp <;> ring
  have hρ : HasDerivAt (fun s => rhoPhi κ V a φ s)
      ((2*deriv φ t*deriv (deriv φ) t)/2 + deriv V (φ t)*deriv φ t +
        (3/8) * (((2*hubble a t*deriv (hubble a) t)*φ t^2 +
          hubble a t^2*(2*φ t*deriv φ t))*couplingFactor κ (φ t) -
          (hubble a t^2*φ t^2)*(κ^2*(2*φ t*deriv φ t)/8)) /
          couplingFactor κ (φ t)^2) t := by
    unfold rhoPhi
    convert! (((hpp.pow 2).div_const 2).add (hV.hasDerivAt.comp t hp)).add
      (((((hH.pow 2).mul (hp.pow 2)).div hC hC0).const_mul (3/8))) using 1 <;> dsimp <;> ring
  have hid : deriv (fun s => rhoPhi κ V a φ s) t +
      3*hubble a t*(rhoPhi κ V a φ t+pPhi κ V a φ t) =
      deriv φ t * (deriv (deriv φ) t + 3*hubble a t*deriv φ t + deriv V (φ t) -
        3/4*(hubble a t^2*φ t/couplingFactor κ (φ t)^2)) := by
    rw [hρ.deriv]
    unfold rhoPhi pPhi
    field_simp [hC0]
    unfold couplingFactor
    ring
  unfold MDOConservation FieldEq
  rw [hid, mul_eq_zero]
  simp [hφdot]



