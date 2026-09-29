-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1e82b482-dc78-5590-83a0-9894e75c381f

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Theorems.Thm_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C
import Theorems.Thm_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsDomain (UVCrossingModel W (ϖ ^ e)) ∧ IsLocalRing (UVCrossingModel W (ϖ ^ e)) ∧ IsIntegrallyClosed (UVCrossingModel W (ϖ ^ e)) := by
  have hϖu : ¬IsUnit ϖ := hϖ.not_isUnit
  set c : W := ϖ ^ e with hc
  have hcu : ¬IsUnit c := by
    rw [hc]; exact fun h => hϖu (isUnit_pow_iff (by omega) |>.mp h)
  obtain ⟨hIprime, hPID, hloc, hirr⟩ := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ e he
  set I : Ideal (PowerSeries W) := Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)} with hI
  haveI := hIprime
  haveI : IsDomain (PowerSeries W ⧸ I) := Ideal.Quotient.isDomain I
  haveI := hPID
  haveI := hloc
  set ϖ' := Ideal.Quotient.mk I (PowerSeries.C ϖ) with hϖ'
  have hϖ'm : ϖ' ∈ IsLocalRing.maximalIdeal (PowerSeries W ⧸ I) := hirr.not_isUnit
  haveI : IsDiscreteValuationRing (PowerSeries W ⧸ I) :=
    ⟨fun h => hirr.ne_zero (by rw [h] at hϖ'm; exact hϖ'm)⟩
  have hcc : Ideal.Quotient.mk I (PowerSeries.C c) = ϖ' ^ e := by
    rw [hϖ', hc, map_pow, map_pow]
  obtain ⟨eqv, -, -, -⟩ := exists_ringEquiv_adjoinRoot c
  rw [hcc] at eqv
  have h0' : ϖ' ^ e ≠ 0 := pow_ne_zero e hirr.ne_zero
  have hu' : ¬IsUnit (ϖ' ^ e) := fun h => hirr.not_isUnit (isUnit_pow_iff (by omega) |>.mp h)
  have hprime := PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C (D := PowerSeries W ⧸ I) h0' hu'
  haveI hdomA := AdjoinRoot.isDomain_of_prime hprime
  haveI hicA := PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow ϖ' hirr e he
  exact ⟨MulEquiv.isDomain _ eqv.toMulEquiv, isLocalRing_of_not_isUnit hcu, IsIntegrallyClosed.of_equiv eqv.symm⟩

end S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow (solution)
