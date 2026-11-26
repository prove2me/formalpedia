-- Prove2me | solution 1 for Kyprianou.Ch05.potentialAllScalesFromLaplaceRatios
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:50:22.915807+00:00
-- url     : https://prove2.me/submissions/099f7825-b3c5-4c53-b8fb-e395164d9f09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Theorems.Thm_Kyprianou_Ch05_potentialLimitFromLaplaceRatios
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Scale the base cumulative limit and multiply by the regular variation ratio. -/
theorem solution
    (U : Measure Real) (Phi : Real → Real) (rho : Real)
    (l l' : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hpos : ∀ t : Real, 0 < t → 0 < Phi t)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hRV : ∀ t : Real, 0 < t → Tendsto
      (fun z => Phi (t*z)/Phi z) l' (nhds (t^rho)))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a*x) l l) :
    Tendsto (fun x => (U (Icc 0 (a*x))).toReal * Phi (1/x)) l
      (nhds (a^rho/Real.Gamma (1+rho))) := by
  have hb := (potentialLimitFromLaplaceRatios U Phi rho l l' hrho hs hpos hLap he hi hRV).comp hScale
  have ht := (hRV a⁻¹ (inv_pos.mpr ha)).comp hi
  have hratio := (tendsto_const_nhds (x := (1 : Real))).div ht
    (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr ha) rho))
  rw [Real.inv_rpow ha.le,one_div,inv_inv] at hratio
  have h := hb.mul hratio
  rw [show 1 / Real.Gamma (1+rho) * a^rho = a^rho/Real.Gamma (1+rho) by ring] at h
  apply h.congr'
  filter_upwards [he] with x hx
  change ((U (Icc 0 (a*x))).toReal * Phi (1/(a*x))) *
    (1/(Phi (a⁻¹*x⁻¹)/Phi x⁻¹)) = _
  rw [one_div,one_div,mul_inv,inv_div]
  have hn : Phi (1/(a*x)) ≠ 0 := ne_of_gt (hpos _ (one_div_pos.mpr (mul_pos ha hx)))
  field_simp [hn]
