-- Prove2me | solution 1 for Kyprianou.Ch05.potentialLimitFromLaplaceRatios
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:47:21.956927+00:00
-- url     : https://prove2.me/submissions/12518363-640f-48f9-9cdd-6e70ecdc5e46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_karamataCumulativeFromLaplaceRatios
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exact reciprocal potential transform and regular variation imply normalised cumulative limits. -/
theorem solution
    (U : Measure Real) (Phi : Real → Real) (rho : Real)
    (l l' : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hpos : ∀ t : Real, 0 < t → 0 < Phi t)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hRV : ∀ t : Real, 0 < t → Tendsto
      (fun z => Phi (t*z)/Phi z) l' (nhds (t^rho))) :
    Tendsto (fun x => (U (Icc 0 x)).toReal * Phi (1/x)) l
      (nhds (1/Real.Gamma (1+rho))) := by
  have hf (t : Real) (ht : 0 < t) : positiveLaplace U t ≠ ⊤ := by
    rw [hLap t ht]
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (hpos t ht))
  have hc : ∀ᶠ x in l, 0 < x ∧ 0 ≤ Phi (1/x) := he.mono (fun x hx =>
    ⟨hx,(hpos _ (one_div_pos.mpr hx)).le⟩)
  have hconv (t : Real) (ht : 0 < t) : Tendsto
      (fun x => Phi (1/x) * (positiveLaplace U (t/x)).toReal) l (nhds (t^(-rho))) := by
    have h := (tendsto_const_nhds (x := (1 : Real))).div ((hRV t ht).comp hi)
      (ne_of_gt (Real.rpow_pos_of_pos ht rho))
    rw [one_div,← Real.rpow_neg ht.le] at h
    apply h.congr'
    filter_upwards [he] with x hx
    change 1 / (Phi (t*x⁻¹)/Phi x⁻¹) = _
    rw [hLap _ (div_pos ht hx),ENNReal.toReal_inv,ENNReal.toReal_ofReal (hpos _ (div_pos ht hx)).le]
    rw [one_div,inv_div,one_div,div_eq_mul_inv]
    congr 2
  simpa only [mul_comm] using karamataCumulativeFromLaplaceRatios U (fun x => Phi (1/x))
    rho l hrho hs hf hc hconv
