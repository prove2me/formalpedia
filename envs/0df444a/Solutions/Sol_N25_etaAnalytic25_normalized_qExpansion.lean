-- Prove2me | solution 1 for N25.etaAnalytic25_normalized_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:54.103468+00:00
-- url     : https://prove2.me/submissions/1cbe12bf-397c-4f1f-ab9f-37056454e485

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_normalized_hasSum
import Theorems.Thm_N25_etaAnalytic25_normalized_analyticAt

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

namespace N25

private theorem expansion_from_series (f : UpperHalfPlane → ℂ) (p : PowerSeries ℤ)
    (ha : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hf : ∀ τ : UpperHalfPlane, HasSum
      (fun n : ℕ => ((PowerSeries.coeff n p : ℤ) : ℂ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) (f τ)) :
    UpperHalfPlane.qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) p := by
  letI : FunLike (UpperHalfPlane → ℂ) UpperHalfPlane ℂ :=
    ⟨id, fun _ _ h => h⟩
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map]
  have hc := UpperHalfPlane.qExpansion_coeff_unique (h := 1) f
    (c := fun m : ℕ => ((PowerSeries.coeff m p : ℤ) : ℂ))
    (show (0 : ℝ) < 1 from zero_lt_one) ha hf n
  exact hc.symm

/-- The normalized eta q-expansion is the exact integer residue series mapped to the complex numbers. -/
theorem _root_.solution
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
    UpperHalfPlane.qExpansion 1
      (fun τ : UpperHalfPlane => etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))) =
      PowerSeries.map (Int.castRingHom ℂ) (etaResidueSeries25 g) := by
  apply expansion_from_series _ _ (etaAnalytic25_normalized_analyticAt g hg hg25)
  intro τ
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one, smul_eq_mul] using
    etaAnalytic25_normalized_hasSum g hg hg25 τ

end N25
