-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/680fa9ab-f818-5830-81dd-48c3313a7a6b

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
set_option autoImplicit false

open ModularCurve

namespace GaussQExp

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]

lemma coeffMap_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (coeffMap φ : LaurentSeries R →+* LaurentSeries S) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simp only [coeffMap_coeff] at this
  exact hφ this

lemma isIntegrallyClosed_laurentSeries [IsDomain R] [IsPrincipalIdealRing R] :
    IsIntegrallyClosed (LaurentSeries R) := by
  haveI : Nonempty (GCDMonoid (PowerSeries R)) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  haveI : IsIntegrallyClosed (PowerSeries R) := GCDMonoid.toIsIntegrallyClosed
  refine isIntegrallyClosed_of_isLocalization (LaurentSeries R)
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) ?_
  exact powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero

theorem main [IsDomain R] [IsPrincipalIdealRing R] {K : Type*} [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y := by
  set Φ : LaurentSeries R →+* LaurentSeries K := coeffMap φ with hΦ
  have hinj : Function.Injective Φ := coeffMap_injective φ hφ
  haveI := isIntegrallyClosed_laurentSeries (R := R)
  let F := FractionRing (LaurentSeries R)
  let ψ : F →+* LaurentSeries K := IsFractionRing.lift hinj
  obtain ⟨a, b, hb, rfl⟩ := hy
  set z : F := algebraMap (LaurentSeries R) F a / algebraMap (LaurentSeries R) F b with hz
  have hψz : ψ z = Φ a / Φ b := by
    simp only [hz, map_div₀, ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨p, hpm, hp⟩ := hint
  have hzint : IsIntegral (LaurentSeries R) z := by
    refine ⟨p, hpm, ?_⟩
    apply ψ.injective
    rw [map_zero, Polynomial.hom_eval₂, hψz]
    have hcomp : ψ.comp (algebraMap (LaurentSeries R) F) = Φ := by
      ext x
      simp [ψ, IsFractionRing.lift_algebraMap]
    rw [hcomp]
    exact hp
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  refine ⟨c, ?_⟩
  have := congrArg ψ hc
  rw [hψz] at this
  simpa [ψ, IsFractionRing.lift_algebraMap] using this

end GaussQExp

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y :=
  GaussQExp.main φ hφ y hy hint

end S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective (solution)
