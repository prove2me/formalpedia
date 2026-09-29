-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_extension_of_subset_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0a393b13-7052-574c-b29e-e2a7b3756f19

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by
  obtain ⟨G⟩ := hA.hasGroupLaw
  haveI : Smooth f := hA.smooth
  haveI : IsSeparated f := hA.proper.toIsSeparated
  obtain ⟨W, d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R G t V hVη hVs v
  exact GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R G t V hVη hVs v W d hd

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens (solution)
