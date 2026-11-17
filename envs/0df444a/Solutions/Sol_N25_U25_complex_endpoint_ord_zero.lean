-- Prove2me | solution 1 for N25.U25_complex_endpoint_ord_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:58.987347+00:00
-- url     : https://prove2.me/submissions/fb0014c0-9595-4334-94ff-f349393b377b

import Mathlib
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_finite_limit_iff_nonnegative_of_normalized_leading
import Theorems.Thm_N25_unitAnalytic25_cusp_limit_of_not_twentyFive_dvd
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitAnalytic25_realizeOf
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_U25C_ne_zero
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open Filter Topology ModularCurve AlgebraicCurve

open scoped MatrixGroups

namespace N25

private theorem exponent_zero (f : UpperHalfPlane → ℂ) (a : ℝ)
    (L c : ℂ) (hL : L ≠ 0) (hc : c ≠ 0)
    (hl : Tendsto (fun τ : UpperHalfPlane => f τ /
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L))
    (hf : Tendsto f UpperHalfPlane.atImInfty (nhds c)) : a = 0 := by
  have hp : 0 ≤ a :=
    (N25.finite_limit_iff_nonnegative_of_normalized_leading f a L hL hl).mp ⟨c, hf⟩
  have he (τ : UpperHalfPlane) :
      (f τ / Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))⁻¹ =
      (f τ)⁻¹ / Complex.exp (2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ)) := by
    have hn : 2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ) =
        -(2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)) := by push_cast; ring
    rw [hn, Complex.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  have hi : Tendsto (fun τ : UpperHalfPlane => (f τ)⁻¹ /
      Complex.exp (2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L⁻¹) := by
    simpa only [he] using hl.inv₀ hL
  have hn : 0 ≤ -a :=
    (N25.finite_limit_iff_nonnegative_of_normalized_leading
      (fun τ => (f τ)⁻¹) (-a) L⁻¹ (inv_ne_zero hL) hi).mp ⟨c⁻¹, hf.inv₀ hc⟩
  linarith

/-- The actual normalized endpoint order vanishes at every non-width-one direction. -/
theorem _root_.solution (i : Fin 5)
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hx : (x : LaurentSeries ℂ) = unitSeries25 ℂ i)
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (B : SL(2, ℤ)) (hB : ¬ (25 : ℤ) ∣ B 1 0) (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ (xHFunctionField 25 N25.H25), y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto
        (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
          (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (P.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L)) : P.ord x = 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    have hz : unitSeries25 ℂ i = 0 := by simpa [h] using hx.symm
    exact U25C_ne_zero ℂ i (Subtype.ext ((coe_U25C ℂ i).trans hz))
  obtain ⟨L, hL, hl⟩ := hlead x hx0
  obtain ⟨c, hc, hf⟩ := unitAnalytic25_cusp_limit_of_not_twentyFive_dvd i B hB
  let a : ℝ := (P.ord x : ℝ) / (w : ℝ)
  have he (τ : UpperHalfPlane) :
      unitAnalytic25 i (B • τ) /
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)) =
      realizeOf (CohCarrier.GammaH 25 N25.H25) (x : LaurentSeries ℂ) (B • τ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (w : ℂ))) := by
    rw [hx, unitAnalytic25_realizeOf, div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    dsimp only [a]
    push_cast
    ring
  have hl' : Tendsto (fun τ : UpperHalfPlane => unitAnalytic25 i (B • τ) /
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L) := by simpa only [he] using hl
  have ha := exponent_zero (fun τ => unitAnalytic25 i (B • τ)) a L c hL hc hl' hf
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hz : (P.ord x : ℝ) = 0 := (div_eq_zero_iff.mp ha).resolve_right hwR
  exact_mod_cast hz

end N25
