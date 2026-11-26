-- Prove2me | solution 1 for Kyprianou.Ch05.reciprocalRegularVariationFactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:39:35.016879+00:00
-- url     : https://prove2.me/submissions/314d5207-6aca-4a2b-99e4-f125cbce49a2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Reciprocal regular-variation factor under inversion of the argument. -/
theorem solution
    (Phi : Real → Real) (rho : Real) (l l' : Filter Real)
    (hpos : ∀ x : Real, 0 < x → 0 < Phi x)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hr : ∀ a : Real, 0 < a → Tendsto
      (fun x : Real => Phi (a*x)/Phi x) l' (nhds (a^rho))) :
    ∃ L : Real → Real,
      (∀ x : Real, 0 < x → 0 < L x) ∧
      (∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x) ∧
      ∀ a : Real, 0 < a → Tendsto (fun x : Real => L (a*x)/L x) l (nhds 1) := by
  let L : Real → Real := fun x => x^(-rho)/Phi x⁻¹
  have hL (x : Real) (hx : 0 < x) : 0 < L x :=
    div_pos (Real.rpow_pos_of_pos hx _) (hpos _ (inv_pos.mpr hx))
  refine ⟨L,hL,?_,?_⟩
  · intro x hx
    dsimp [L]
    rw [one_div]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hx (-rho)),ne_of_gt (hpos _ (inv_pos.mpr hx))]
  · intro a ha
    have ht := (hr a⁻¹ (inv_pos.mpr ha)).comp hi
    have hh := (tendsto_const_nhds (x := a^(-rho))).div ht
      (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr ha) rho))
    have hlim : a^(-rho) / (a⁻¹)^rho = 1 := by
      rw [Real.inv_rpow ha.le,Real.rpow_neg ha.le]
      exact div_self (inv_ne_zero (ne_of_gt (Real.rpow_pos_of_pos ha rho)))
    rw [hlim] at hh
    apply hh.congr'
    filter_upwards [he] with x hx
    change a^(-rho)/(Phi (a⁻¹*x⁻¹)/Phi x⁻¹) = L (a*x)/L x
    dsimp [L]
    rw [Real.mul_rpow ha.le hx.le, mul_inv]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hx (-rho)),
      ne_of_gt (hpos _ (inv_pos.mpr hx)),
      ne_of_gt (hpos _ (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hx)))]
