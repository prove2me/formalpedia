-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.flat_schemeFibreEndo_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6a96247a-93ca-509d-b5bd-161a85f67f51

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace Ws6Bf75

theorem isPullback_schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    IsPullback (schemeFibreEndo f h hcomm s)
      (pullback.fst f (S.fromSpecResidueField s))
      (pullback.fst f (S.fromSpecResidueField s)) h := by
  have hright : IsPullback (pullback.snd f (S.fromSpecResidueField s))
      (pullback.fst f (S.fromSpecResidueField s)) (S.fromSpecResidueField s) f :=
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
  have hbig : IsPullback (schemeFibreEndo f h hcomm s ≫ pullback.snd f (S.fromSpecResidueField s))
      (pullback.fst f (S.fromSpecResidueField s)) (S.fromSpecResidueField s) (h ≫ f) := by
    rw [schemeFibreEndo_snd, hcomm]
    exact hright
  exact IsPullback.of_right hbig (schemeFibreEndo_fst f h hcomm s) hright

end Ws6Bf75

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : 0 < n)
    (hfin : IsFinite (L.schemeNsmul n)) (s : Spec (CommRingCat.of R)) :
    Flat (schemeFibreEndo f (L.schemeNsmul n) (L.schemeNsmul_over n) s) := by
  rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
  have hJs : AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s)
      (RelativeGroupLaw.fibreStr f s) :=
    GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
  have hfin_s : IsFinite ((L.fibre s).schemeNsmul n) := by
    rw [RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    exact MorphismProperty.of_isPullback
      (Ws6Bf75.isPullback_schemeFibreEndo f (L.schemeNsmul n) (L.schemeNsmul_over n) s).flip hfin
  exact RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_field (L.fibre s) hJs n hn hfin_s

end S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul (solution)
