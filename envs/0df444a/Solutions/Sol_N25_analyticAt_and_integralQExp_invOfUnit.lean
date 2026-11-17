-- Prove2me | solution 1 for N25.analyticAt_and_integralQExp_invOfUnit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:54.575018+00:00
-- url     : https://prove2.me/submissions/30e95473-45ee-4dd5-a571-a773d005c3fa

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Filter Topology Function UpperHalfPlane

namespace N25

/-- An integral analytic q-series with constant coefficient one has the expected integral reciprocal. -/
theorem _root_.solution
    (f : UpperHalfPlane → ℂ) (p : PowerSeries ℤ)
    (ha : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hfn : ∀ τ : UpperHalfPlane, f τ ≠ 0)
    (hc : PowerSeries.constantCoeff p = 1)
    (hq : UpperHalfPlane.qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) p) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun τ => (f τ)⁻¹)) 0 ∧
      ModularCurve.IsIntegralQExp (fun τ => (f τ)⁻¹) (p.invOfUnit (1 : ℤˣ)) := by
  have hz : UpperHalfPlane.cuspFunction 1 f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hq
    rw [UpperHalfPlane.qExpansion_coeff] at h
    simpa [PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hc] using h
  have hzn : UpperHalfPlane.cuspFunction 1 f 0 ≠ 0 := by rw [hz]; exact one_ne_zero
  have hi0 : UpperHalfPlane.cuspFunction 1 (fun τ => (f τ)⁻¹) 0 =
      (UpperHalfPlane.cuspFunction 1 f 0)⁻¹ := by
    change Function.Periodic.cuspFunction 1 ((fun τ => (f τ)⁻¹) ∘ UpperHalfPlane.ofComplex) 0 = _
    rw [Function.Periodic.cuspFunction, Function.update_self]
    exact ((Function.Periodic.tendsto_nhds_zero ha.continuousAt).inv₀ hzn).limUnder_eq
  have he : UpperHalfPlane.cuspFunction 1 (fun τ => (f τ)⁻¹) =
      fun q => (UpperHalfPlane.cuspFunction 1 f q)⁻¹ := by
    funext q
    by_cases hq0 : q = 0
    · subst q; exact hi0
    · simp [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction, hq0]
  have hi : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun τ => (f τ)⁻¹)) 0 := by
    rw [he]
    exact ha.inv hzn
  have hmul : UpperHalfPlane.qExpansion 1 f *
      UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹) = 1 := by
    rw [← UpperHalfPlane.qExpansion_mul ha hi]
    have hfun : f * (fun τ => (f τ)⁻¹) = (1 : UpperHalfPlane → ℂ) := by
      funext τ
      exact mul_inv_cancel₀ (hfn τ)
    rw [hfun, UpperHalfPlane.qExpansion_one]
  have hmul' : PowerSeries.map (Int.castRingHom ℂ) p *
      UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹) = 1 := by
    rw [← hq]
    exact hmul
  have hp : PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) *
      PowerSeries.map (Int.castRingHom ℂ) p = 1 := by
    rw [← map_mul, PowerSeries.invOfUnit_mul p (1 : ℤˣ) hc, map_one]
  refine ⟨hi, ?_⟩
  change PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) =
    UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹)
  calc
    PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) =
        PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) * 1 := (mul_one _).symm
    _ = PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) *
        (PowerSeries.map (Int.castRingHom ℂ) p *
          UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹)) := by rw [hmul']
    _ = (PowerSeries.map (Int.castRingHom ℂ) (p.invOfUnit (1 : ℤˣ)) *
        PowerSeries.map (Int.castRingHom ℂ) p) *
          UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹) := (mul_assoc _ _ _).symm
    _ = UpperHalfPlane.qExpansion 1 (fun τ => (f τ)⁻¹) := by rw [hp, one_mul]

end N25
