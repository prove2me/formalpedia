-- Prove2me | solution 1 for Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2d65f8ad-e04a-569f-8e97-78aeace148fb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) (h𝔭dim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1)
    (B : Type u) [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B] :
    ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B) := by
  classical
  set Aₚ := Localization.AtPrime 𝔭 with hAₚ
  haveI : IsNoetherianRing Aₚ := IsLocalization.isNoetherianRing 𝔭.primeCompl Aₚ inferInstance
  haveI : IsDomain Aₚ := IsLocalization.isDomain_localization 𝔭.primeCompl_le_nonZeroDivisors
  haveI : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr h𝔭dim
  haveI : Ring.DimensionLEOne Aₚ := ⟨fun hne hp => Ideal.IsPrime.isMaximal_of_ne_bot hp hne⟩
  haveI : IsDedekindRing Aₚ := { (inferInstance : IsNoetherian Aₚ Aₚ), (inferInstance : Ring.DimensionLEOne Aₚ), h𝔭ic with }
  haveI : IsDedekindDomain Aₚ := {}
  haveI : IsPrincipalIdealRing Aₚ := inferInstance
  haveI : Module.IsTorsionFree A B := inferInstance
  haveI : Module.Finite Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  haveI : Module.IsTorsionFree Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  haveI : Module.Free Aₚ (LocalizedModule 𝔭.primeCompl B) := Module.free_of_finite_type_torsion_free'
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers 𝔭.primeCompl
    (LocalizedModule.mkLinearMap 𝔭.primeCompl B) (Localization.AtPrime 𝔭)
  exact ⟨r, hr, hfree⟩

end S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
end P2MW
export P2MW.S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one (solution)
