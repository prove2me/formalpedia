-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/207bdf6d-79c1-59d0-8eb0-276fcb458e8f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
universe u

theorem solution
    {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hJ : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by
  haveI := hJ.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI hnoeth : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  haveI hint : IsIntegral J := hJ.isIntegral_of_field
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  algebraize [((L.schemeNsmul n).stalkMap x).hom]
  haveI : IsRegularLocalRing (J.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
  haveI : IsRegularLocalRing (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) ((L.schemeNsmul n).base x)
  haveI : IsNoetherianRing (J.presheaf.stalk x) := inferInstance
  haveI : IsLocalHom (algebraMap
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((L.schemeNsmul n).stalkMap x).hom)

  have hfib : ringKrullDim (↑(J.presheaf.stalk x) ⧸
      (maximalIdeal ↑(J.presheaf.stalk ((L.schemeNsmul n).base x))).map
        (algebraMap ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero (L.schemeNsmul n) x

  have hdim : ringKrullDim (J.presheaf.stalk x) =
      ringKrullDim (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
      (f := f) (L.schemeNsmul n) (L.schemeNsmul_over n) x

  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x) hfib hdim

end S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field (solution)
