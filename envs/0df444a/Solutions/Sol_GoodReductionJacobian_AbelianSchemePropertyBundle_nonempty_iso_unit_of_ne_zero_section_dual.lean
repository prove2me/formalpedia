-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/657ffbb1-c0ad-55b5-9302-97668ebf88eb

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_ne_zero_section_dual
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace P2mWs30FibreCrit

universe u

theorem unitEnd_eq_zero_of {X : Scheme.{u}} (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (h : (show Γ(X, ⊤) from c.app ⊤ (1 : Γ(X, ⊤))) = 0) : c = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (show Γ(X, U) from c.app U m) = (show Γ(X, U) from (0 : Γ(𝟙_ X.Modules, U) ⟶ Γ(𝟙_ X.Modules, U)) m)
  rw [AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul c U m, h, map_zero, zero_mul]
  rfl

noncomputable def coSectionMap {X : Scheme.{u}} {M : X.Modules} (s' : 𝟙_ X.Modules ⟶ Scheme.Modules.dual M) :
    M ⟶ 𝟙_ X.Modules :=
  (ρ_ M).inv ≫ MonoidalClosed.uncurry s'

theorem coSectionMap_ne_zero {X : Scheme.{u}} {M : X.Modules} (s' : 𝟙_ X.Modules ⟶ Scheme.Modules.dual M)
    (hs' : s' ≠ 0) : coSectionMap s' ≠ 0 := by
  intro h
  apply hs'
  have h1 : MonoidalClosed.uncurry s' = 0 := by
    have : (ρ_ M).hom ≫ coSectionMap s' = MonoidalClosed.uncurry s' := by
      simp [coSectionMap]
    rw [← this, h, Limits.comp_zero]
  haveI : (ihom M).IsRightAdjoint := ⟨_, ⟨ihom.adjunction M⟩⟩
  rw [← MonoidalClosed.curry_uncurry s', h1, MonoidalClosed.curry_eq]
  exact (congrArg (fun g => (ihom.coev M).app (𝟙_ X.Modules) ≫ g)
    (Functor.map_zero (ihom M) _ _)).trans Limits.comp_zero

end P2mWs30FibreCrit

open P2mWs30FibreCrit in
theorem solution
    {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ A.Modules ⟶ M) (s' : 𝟙_ A.Modules ⟶ Scheme.Modules.dual M) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Nonempty (M ≅ 𝟙_ A.Modules) := by
  classical

  haveI := hA.smooth
  have hconn : ConnectedSpace A := by
    have h := hA.connectedFibres (IsLocalRing.closedPoint k)
    have huniv : f.base ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    have h' : _root_.IsConnected (Set.univ : Set A) := by
      convert h using 1
      exact huniv.symm
    exact connectedSpace_iff_univ.mpr h'
  haveI : PreconnectedSpace A := inferInstance
  haveI : Nonempty A := inferInstance
  haveI : IsIntegral A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f

  have hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom := by
    refine GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback hA (RingHom.id k) f
      (𝟙 A) ?_
    have : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ := by
      rw [show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id]
    rw [this]
    exact IsPullback.of_id_fst

  set t : M ⟶ 𝟙_ A.Modules := coSectionMap s' with ht_def
  have ht : t ≠ 0 := coSectionMap_ne_zero s' hs'
  have hc : s ≫ t ≠ 0 := AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral hM s t hs ht
  set c₀ : Γ(A, ⊤) := (show Γ(A, ⊤) from (s ≫ t).app ⊤ (1 : Γ(A, ⊤))) with hc₀_def
  have hc₀ : c₀ ≠ 0 := fun h0 => hc (unitEnd_eq_zero_of _ h0)

  have hunit : IsUnit c₀ := by
    obtain ⟨z, hz⟩ := hΓ.2 c₀
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hc₀
      rw [← hz, map_zero]
    rw [← hz]
    exact (IsUnit.mk0 z hz0).map _
  obtain ⟨u, hu⟩ := hunit.exists_left_inv

  have hsurj : ∀ (U : A.Opens) (r : Γ(𝟙_ A.Modules, U)), ∀ x ∈ U, ∃ (V : A.Opens) (i : V ≤ U),
      x ∈ V ∧ (𝟙_ A.Modules).presheaf.map (homOfLE i).op r ∈ Set.range (t.app V) := by
    intro U r x hx
    refine ⟨U, le_rfl, hx, ?_⟩
    refine ⟨s.app U (show Γ(𝟙_ A.Modules, U) from
      (A.presheaf.map (homOfLE (le_top (a := U))).op u * (show Γ(A, U) from r))), ?_⟩
    have hid : (𝟙_ A.Modules).presheaf.map (homOfLE (le_rfl : U ≤ U)).op r = r := by
      have : homOfLE (le_rfl : U ≤ U) = 𝟙 U := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [hid]
    change (show Γ(A, U) from (s ≫ t).app U _) = (show Γ(A, U) from r)
    rw [AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul, ← mul_assoc, ← map_mul]
    change A.presheaf.map (homOfLE le_top).op (c₀ * u) * (show Γ(A, U) from r) = _
    rw [mul_comm c₀ u, hu, map_one, one_mul]
  haveI : IsIso t :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_locallySurjective hM (Scheme.Modules.isInvertible_unit A) t hsurj
  exact ⟨asIso t⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_ne_zero_section_dual
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_ne_zero_section_dual (solution)
