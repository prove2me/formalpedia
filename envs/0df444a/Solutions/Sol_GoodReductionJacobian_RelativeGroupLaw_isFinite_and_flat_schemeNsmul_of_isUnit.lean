-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c7e7087f-4d83-5933-9741-01a1a383b48e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by
  haveI : IsProper f := hJ.proper

  have hlqf : LocallyQuasiFinite (L.schemeNsmul n) := by
    refine AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul n) (L.schemeNsmul_over n) ?_
    intro s
    rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    have hfib := GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
    haveI : Smooth (RelativeGroupLaw.fibreStr f s) := hfib.smooth
    haveI : LocallyOfFiniteType (RelativeGroupLaw.fibreStr f s) := inferInstance
    have hu : IsUnit ((n : ℕ) : RelativeGroupLaw.baseResidueField s) := by
      have h := hn.map (((Spec (CommRingCat.of R)).Γevaluation s).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      simpa only [map_natCast] using h
    exact RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s)
      (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s t' x y) n hu
  haveI := hlqf
  haveI : IsProper (L.schemeNsmul n) := by
    have : IsProper (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact IsProper.of_comp _ f
  have hfin : IsFinite (L.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine ⟨hfin, ?_⟩

  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have h01 : (0 : R) = 1 := isUnit_zero_iff.mp (by simpa using hn)
    haveI : Subsingleton R := subsingleton_of_zero_eq_one h01
    haveI : IsEmpty (Spec (CommRingCat.of R) : Scheme.{u}) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum R))
    haveI : IsEmpty J := Function.isEmpty f.base
    infer_instance
  · exact RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle L hJ
      (fun t x y => hcomm t x y) n hpos hfin

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit (solution)
