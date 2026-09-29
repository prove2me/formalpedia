-- Prove2me | solution 1 for NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0cf6ef7b-1b1d-51f4-88c2-94fd801e7fc9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
import Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    NeronModelInfra.NeronModelPropertyBundle R K f := by
  haveI : IsProper f := hA.proper
  have hsep : IsSeparated f := inferInstance
  refine ⟨hA.smooth, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  haveI := ht
  haveI := hqc
  haveI : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    hA.genericFibreRestrict_surjective_of_quasiCompact R K t⟩

end S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle (solution)
