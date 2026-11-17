-- Prove2me | solution 1 for N25.unitNumerator_isIntegralQExp25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:10.82331+00:00
-- url     : https://prove2.me/submissions/8fe7c67e-2d25-4a23-b35b-48c10b0d303b

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_analyticAt_and_qExpansion_of_hasSum
import Theorems.Thm_N25_discriminant_normalized_hasSum
import Theorems.Thm_N25_analyticAt_and_integralQExp_invOfUnit
import Theorems.Thm_N25_etaAnalytic25_normalized_analyticAt
import Theorems.Thm_N25_etaAnalytic25_normalized_qExpansion
import Theorems.Thm_N25_etaAnalytic25_ne_zero
import Theorems.Thm_N25_etaResidueSeries25_coeff
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitAnalytic25_eq_normalized_ratio

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open UpperHalfPlane ModularCurve

namespace N25

private theorem multiply_expansions
    {f g : UpperHalfPlane → ℂ} {p r : PowerSeries ℤ}
    (hf : AnalyticAt ℂ (cuspFunction 1 f) 0 ∧
      qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) p)
    (hg : AnalyticAt ℂ (cuspFunction 1 g) 0 ∧
      qExpansion 1 g = PowerSeries.map (Int.castRingHom ℂ) r) :
    AnalyticAt ℂ (cuspFunction 1 (f * g)) 0 ∧
      qExpansion 1 (f * g) = PowerSeries.map (Int.castRingHom ℂ) (p * r) := by
  constructor
  · rw [cuspFunction_mul hf.1.continuousAt hg.1.continuousAt]
    exact hf.1.mul hg.1
  · rw [qExpansion_mul hf.1 hg.1, hf.2, hg.2, map_mul]

private theorem q_power_expansion (m : ℕ) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ m)) 0 ∧
    qExpansion 1 (fun τ : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ m) =
        PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X ^ m) := by
  apply analyticAt_and_qExpansion_of_hasSum
  intro τ
  have hs := hasSum_ite_eq m (Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ m)
  have he : (fun n : ℕ => if n = m then
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ m else 0) =
      (fun n : ℕ => ((PowerSeries.coeff n (PowerSeries.X ^ m : PowerSeries ℤ) : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n) := by
    funext n
    by_cases hn : n = m
    · subst n; simp
    · simp [PowerSeries.coeff_X_pow, hn]
  rw [he] at hs
  exact hs

/-- The actual unpowered analytic unit, multiplied by the discriminant cube, has the frozen integral numerator expansion. -/
theorem _root_.solution (i : Fin 5) :
    ModularCurve.IsIntegralQExp
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ)
      (unitNumeratorSeries25 i) := by
  let R : ℕ → UpperHalfPlane → ℂ := fun g τ => etaAnalytic25 g τ /
    Complex.exp (Real.pi * Complex.I *
      (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))
  let A : Fin 5 → UpperHalfPlane → ℂ := fun j =>
    R (unitResidues25 j).1 * R (unitResidues25 j).2
  let D : UpperHalfPlane → ℂ := fun τ => ModularForm.discriminant τ /
    Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  let e := (3 + unitQOrder25 i).toNat
  let Q : UpperHalfPlane → ℂ := fun τ => Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ e
  have hb (j : Fin 5) : 0 < (unitResidues25 j).1 ∧ (unitResidues25 j).1 < 25 ∧
      0 < (unitResidues25 j).2 ∧ (unitResidues25 j).2 < 25 := by
    fin_cases j <;> decide
  have hR (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
      AnalyticAt ℂ (cuspFunction 1 (R g)) 0 ∧
      qExpansion 1 (R g) = PowerSeries.map (Int.castRingHom ℂ) (etaResidueSeries25 g) :=
    ⟨etaAnalytic25_normalized_analyticAt g hg hg25,
      etaAnalytic25_normalized_qExpansion g hg hg25⟩
  have hA (j : Fin 5) : AnalyticAt ℂ (cuspFunction 1 (A j)) 0 ∧
      qExpansion 1 (A j) = PowerSeries.map (Int.castRingHom ℂ) (unitPairSeries25 j) :=
    multiply_expansions (hR _ (hb j).1 (hb j).2.1)
      (hR _ (hb j).2.2.1 (hb j).2.2.2)
  have hAn (j : Fin 5) (τ : UpperHalfPlane) : A j τ ≠ 0 := by
    dsimp only [A, R, Pi.mul_apply]
    exact mul_ne_zero
      (div_ne_zero (etaAnalytic25_ne_zero _ (hb j).1 (hb j).2.1 τ) (Complex.exp_ne_zero _))
      (div_ne_zero (etaAnalytic25_ne_zero _ (hb j).2.2.1 (hb j).2.2.2 τ) (Complex.exp_ne_zero _))
  have hc (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
      PowerSeries.constantCoeff (etaResidueSeries25 g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, etaResidueSeries25_coeff g hg hg25 0]
    simp
  have hAc (j : Fin 5) : PowerSeries.constantCoeff (unitPairSeries25 j) = 1 := by
    dsimp only [unitPairSeries25]
    rw [map_mul, hc _ (hb j).1 (hb j).2.1, hc _ (hb j).2.2.1 (hb j).2.2.2, one_mul]
  have hInv := analyticAt_and_integralQExp_invOfUnit (A (i + 1)) (unitPairSeries25 (i + 1))
    (hA (i + 1)).1 (hAn (i + 1)) (hAc (i + 1)) (hA (i + 1)).2
  have hI : AnalyticAt ℂ (cuspFunction 1 (fun τ => (A (i + 1) τ)⁻¹)) 0 ∧
      qExpansion 1 (fun τ => (A (i + 1) τ)⁻¹) =
        PowerSeries.map (Int.castRingHom ℂ) ((unitPairSeries25 (i + 1)).invOfUnit (1 : ℤˣ)) :=
    ⟨hInv.1, hInv.2.symm⟩
  have hD := analyticAt_and_qExpansion_of_hasSum D dedekindEtaUnit discriminant_normalized_hasSum
  have hDcube := multiply_expansions (multiply_expansions hD hD) hD
  have H := multiply_expansions
    (multiply_expansions (multiply_expansions (q_power_expansion e) hDcube) (hA i)) hI
  have hnonneg : 0 ≤ 3 + unitQOrder25 i := by fin_cases i <;> decide
  have he : (e : ℤ) = 3 + unitQOrder25 i := Int.toNat_of_nonneg hnonneg
  have hfun : ((Q * ((D * D) * D)) * A i) * (fun τ => (A (i + 1) τ)⁻¹) =
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) := by
    funext τ
    let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    change q ^ e * ((ModularForm.discriminant τ / q * (ModularForm.discriminant τ / q)) *
      (ModularForm.discriminant τ / q)) * A i τ * (A (i + 1) τ)⁻¹ = _
    rw [unitAnalytic25_eq_normalized_ratio i τ]
    change _ = ModularForm.discriminant τ ^ 3 *
      (q ^ unitQOrder25 i * (A i τ / A (i + 1) τ))
    have hp : q ^ e * ((ModularForm.discriminant τ / q * (ModularForm.discriminant τ / q)) *
        (ModularForm.discriminant τ / q)) = ModularForm.discriminant τ ^ 3 * q ^ unitQOrder25 i := by
      rw [← zpow_natCast, he, zpow_add₀ hq0]
      field_simp [hq0]
      <;> ring
    calc
      q ^ e * ((ModularForm.discriminant τ / q * (ModularForm.discriminant τ / q)) *
          (ModularForm.discriminant τ / q)) * A i τ * (A (i + 1) τ)⁻¹ =
          (q ^ e * ((ModularForm.discriminant τ / q * (ModularForm.discriminant τ / q)) *
            (ModularForm.discriminant τ / q))) * (A i τ / A (i + 1) τ) := by
              rw [div_eq_mul_inv]
              ring
      _ = (ModularForm.discriminant τ ^ 3 * q ^ unitQOrder25 i) *
          (A i τ / A (i + 1) τ) := by rw [hp]
      _ = _ := by ring
  have hseries :
      ((PowerSeries.X ^ e * ((dedekindEtaUnit * dedekindEtaUnit) * dedekindEtaUnit)) *
        unitPairSeries25 i) * (unitPairSeries25 (i + 1)).invOfUnit (1 : ℤˣ) =
      unitNumeratorSeries25 i := by
    simp only [unitNumeratorSeries25, e, pow_succ, pow_zero, one_mul]
  rw [hfun, hseries] at H
  exact H.2.symm

end N25
