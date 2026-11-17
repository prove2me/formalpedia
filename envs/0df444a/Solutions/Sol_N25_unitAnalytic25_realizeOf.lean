-- Prove2me | solution 1 for N25.unitAnalytic25_realizeOf
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:55.593977+00:00
-- url     : https://prove2.me/submissions/5f76621f-dfa8-4a6d-b9b1-8a488da7605d

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitNumeratorForm25
import Theorems.Thm_N25_unitDenominatorForm25
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_N25_unitDenominatorSeries25_ne_zero
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false

open UpperHalfPlane ModularCurve

namespace N25

/-- The literal Laurent quotient realizes the original unpowered analytic ratio. -/
theorem _root_.solution (i : Fin 5) (τ : UpperHalfPlane) :
    ModularCurve.realizeOf (CohCarrier.GammaH 25 N25.H25)
      (unitSeries25 ℂ i) τ = unitAnalytic25 i τ := by
  obtain ⟨F, hF, hFq⟩ := unitNumeratorForm25 i
  obtain ⟨G, hG, hGq⟩ := unitDenominatorForm25
  have hq : unitSeries25 ℂ i *
      ((qExpansion 1 (G : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (F : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [← hGq, ← hFq]
    change (intSeriesC ℂ (unitNumeratorSeries25 i) /
      intSeriesC ℂ unitDenominatorSeries25) * intSeriesC ℂ unitDenominatorSeries25 = _
    exact div_mul_cancel₀ _ (unitDenominatorSeries25_ne_zero ℂ)
  have hΔ : ModularForm.discriminant τ ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ModularForm.discriminant_ne_zero τ)
  rw [realizeOf_eq_div (CohCarrier.GammaH 25 N25.H25)
    (translation_mem_GammaH 25 N25.H25) F G (unitSeries25 ℂ i) hq τ
    (by rw [hG]; exact hΔ), hF, hG]
  exact mul_div_cancel_left₀ _ hΔ

end N25
