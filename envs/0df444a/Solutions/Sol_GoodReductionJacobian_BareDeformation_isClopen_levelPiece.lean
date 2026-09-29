-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.isClopen_levelPiece
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e0ed611f-0e77-5387-bc8c-160c8b5d725d

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_isClopen_levelPiece
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing

open scoped Quaternion TensorProduct NumberField

universe u

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f] :
    IsClopen ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base)) := by
  classical

  obtain ⟨gK, hgKpb, hgK⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKerStr_of_isPullback
      (algebraMap B B₀) D.L E₀.L D.g D.cart D.hom N

  obtain ⟨_, _, hgKhomeo⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker (algebraMap B B₀) hπ hker
      (D.L.schemeKerStr N) (E₀.L.schemeKerStr N) gK hgKpb

  haveI : IsProper D.f := D.bundle.proper
  haveI hsec : IsClosedImmersion (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
    haveI : IsClosedImmersion ((D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ D.f) := by
      rw [(D.L.one (𝟙 (Spec (CommRingCat.of B)))).2]
      infer_instance
    exact IsClosedImmersion.of_comp _ D.f
  haveI hκ : IsClosedImmersion
      (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) :=
    MorphismProperty.pullback_fst _ _ hsec
  have hκinj : Function.Injective
      (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base :=
    (Scheme.Hom.isClosedEmbedding _).injective

  have hN₀ : IsUnit ((N : ℕ) : B₀) := by
    have := hN.map (algebraMap B B₀)
    rwa [map_natCast] at this
  haveI : Etale (E₀.L.schemeKerStr N) :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E₀ N hN₀).2
  haveI := E₀.lev_closed
  haveI := E₀.lev_flat
  haveI := E₀.lev_finitePresentation
  obtain ⟨U, e, hUclosed, he, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
      E₀.L N E₀.lev E₀.lev_torsion

  have hκ₀ : ∀ c : ↥E₀.C,
      (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1).base
        (U.ι.base (e.hom.base c)) = E₀.lev.base c := by
    intro c
    change (e.hom ≫ U.ι ≫ pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1) c = _
    rw [he]
  have hsq : ∀ u : ↥(E₀.L.schemeKer N),
      (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base (gK.base u)
        = D.g.base ((pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1).base u) := by
    intro u
    change (gK ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) u
      = (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1 ≫ D.g) u
    rw [hgK]
  have hmemU : ∀ c : ↥E₀.C, U.ι.base (e.hom.base c) ∈ (U : Set ↥(E₀.L.schemeKer N)) := by
    intro c
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have hset : (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹'
        (D.g.base '' Set.range E₀.lev.base)
      = gK.base '' (U : Set ↥(E₀.L.schemeKer N)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, hc⟩
      refine ⟨U.ι.base (e.hom.base c), hmemU c, hκinj ?_⟩
      rw [hsq, hκ₀]
      exact hc
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ Set.range U.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
      obtain ⟨u', rfl⟩ := hu'
      obtain ⟨c, rfl⟩ : ∃ c, e.hom.base c = u' :=
        ⟨e.inv.base u', by change (e.inv ≫ e.hom) u' = u'; rw [e.inv_hom_id]; rfl⟩
      refine ⟨E₀.lev.base c, ⟨_, rfl⟩, ?_⟩
      show D.g.base (E₀.lev.base c) = _
      rw [hsq, hκ₀]
  rw [hset]
  exact ⟨(hgKhomeo.homeomorph).isClosed_image.mpr hUclosed, (hgKhomeo.homeomorph).isOpen_image.mpr U.isOpen⟩

end S_GoodReductionJacobian_BareDeformation_isClopen_levelPiece
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_isClopen_levelPiece (solution)
