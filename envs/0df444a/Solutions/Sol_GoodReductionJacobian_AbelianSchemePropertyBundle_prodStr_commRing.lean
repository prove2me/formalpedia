-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f6f3553d-b955-5d67-86b1-06391b051f50

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw prodStr RelativeGroupLaw.prod AbelianSchemePropertyBundle.of_isPullback abelianSchemePropertyBundle_prodStr"
namespace ProdCommRingAux
p2m_open "GoodReductionJacobian"

theorem isPullback_map {T T' X X' Y Y' : Scheme.{u}} {fX : X ⟶ T} {fY : Y ⟶ T} {fX' : X' ⟶ T'} {fY' : Y' ⟶ T'}
    {pX : X' ⟶ X} {pY : Y' ⟶ Y} {t : T' ⟶ T} (hX : IsPullback pX fX' fX t) (hY : IsPullback pY fY' fY t) :
    IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) t := by
  have S1 : IsPullback (pullback.snd fX' fY') (pullback.fst fX' fY' ≫ pX) (fY' ≫ t) fX :=
    (IsPullback.of_hasPullback fX' fY').flip.paste_vert hX.flip
  have S1' : IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm ≫ pullback.fst fX fY)
      (pullback.snd fX' fY') fX (pY ≫ fY) := by
    convert S1.flip using 1
    · simp only [pullback.lift_fst]
    · exact hY.w
  have S2 : IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm) (pullback.snd fX' fY')
      (pullback.snd fX fY) pY :=
    S1'.of_right (by simp only [pullback.lift_snd]) (IsPullback.of_hasPullback fX fY)
  have S3 := S2.paste_vert hY
  convert S3 using 1
  · exact pullback.condition
  · exact pullback.condition

variable {R : Type u} [CommRing R] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  {h : C ⟶ Spec (CommRingCat.of R)}

theorem isConnected_fibre (hB : AbelianSchemePropertyBundle R g) (hC : AbelianSchemePropertyBundle R h)
    (s : Spec (CommRingCat.of R)) : _root_.IsConnected ((prodStr g h).base ⁻¹' {s}) := by

  let ι : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec (CommRingCat.of R) :=
    (Spec (CommRingCat.of R)).fromSpecResidueField s
  have hBs : AbelianSchemePropertyBundle ((Spec (CommRingCat.of R)).residueField s) (pullback.snd g ι) :=
    hB.of_isPullback (R' := (Spec (CommRingCat.of R)).residueField s) (ι := ι) (IsPullback.of_hasPullback _ _)
  have hCs : AbelianSchemePropertyBundle ((Spec (CommRingCat.of R)).residueField s) (pullback.snd h ι) :=
    hC.of_isPullback (R' := (Spec (CommRingCat.of R)).residueField s) (ι := ι) (IsPullback.of_hasPullback _ _)

  have hP := abelianSchemePropertyBundle_prodStr hBs hCs
  have hconn : ConnectedSpace ↑(pullback (pullback.snd g ι) (pullback.snd h ι)) := by
    rw [connectedSpace_iff_univ]
    convert hP.connectedFibres (IsLocalRing.closedPoint _) using 1
    refine (Set.eq_univ_of_forall fun x => ?_).symm
    change _ = _
    exact Subsingleton.elim (α := PrimeSpectrum ((Spec (CommRingCat.of R)).residueField s)) _ _

  have hsq := isPullback_map (IsPullback.of_hasPullback g ι) (IsPullback.of_hasPullback h ι)
  let e : pullback (pullback.snd g ι) (pullback.snd h ι) ≅ (prodStr g h).fiber s := hsq.isoPullback
  haveI : ConnectedSpace ↑((prodStr g h).fiber s) := by
    rw [connectedSpace_iff_univ]
    have himg := (isConnected_range (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).continuous)
    rwa [(TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).surjective.range_eq] at himg
  rw [← Scheme.Hom.range_fiberι]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem main (hB : AbelianSchemePropertyBundle R g) (hC : AbelianSchemePropertyBundle R h) :
    AbelianSchemePropertyBundle R (prodStr g h) := by
  haveI := hB.smooth
  haveI := hC.smooth
  haveI := hB.proper
  haveI := hC.proper
  obtain ⟨LB⟩ := hB.hasGroupLaw
  obtain ⟨LC⟩ := hC.hasGroupLaw
  exact
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := isConnected_fibre hB hC
      hasGroupLaw := ⟨LB.prod LC⟩ }

end GoodReductionJacobian.ProdCommRingAux

end

theorem solution
    {R : Type u} [CommRing R] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {h : C ⟶ Spec (CommRingCat.of R)} (hB : AbelianSchemePropertyBundle R g)
    (hC : AbelianSchemePropertyBundle R h) :
    AbelianSchemePropertyBundle R (prodStr g h) :=
  GoodReductionJacobian.ProdCommRingAux.main hB hC

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing (solution)
