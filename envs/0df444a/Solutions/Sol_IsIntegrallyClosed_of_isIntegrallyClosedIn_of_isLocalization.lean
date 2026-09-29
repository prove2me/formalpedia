-- Prove2me | solution 1 for IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f99c900c-5695-52f6-bca2-b992a770c41e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization

namespace IsIntegrallyClosed p2m_export "IsIntegrallyClosed" "algebraMap_eq_of_integral" end IsIntegrallyClosed
p2m_open_scoped "IsIntegrallyClosed" in

theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by
  let K := FractionRing C
  have hg : ∀ y : M, IsUnit (algebraMap C K y) := fun y =>
    isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr (nonZeroDivisors.ne_zero (hM y.2)))
  letI algLK : Algebra L K := (IsLocalization.lift (M := M) (S := L) hg).toAlgebra
  haveI : IsScalarTower C L K :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := L) (A := K) (IsLocalization.lift_comp (M := M) hg).symm
  haveI : IsFractionRing L K := IsFractionRing.isFractionRing_of_isLocalization M L K hM
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
  have hxL : IsIntegral L x := hx.tower_top
  obtain ⟨l, rfl⟩ := (isIntegrallyClosed_iff K).mp inferInstance hxL
  have hl : IsIntegral C l :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom C L K) (IsFractionRing.injective L K)).mp hx
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hl
  exact ⟨c, IsScalarTower.algebraMap_apply C L K c⟩

theorem solution
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C :=
  IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization M hM L

end S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization
end P2MW
export P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization (solution)
